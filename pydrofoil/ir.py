import random
from collections import defaultdict

from pydrofoil import parse, types, binaryop, operations, supportcode
from pydrofoil.bitvector import Integer

from rpython.tool.udir import udir
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck

from dotviewer.graphpage import GraphPage as BaseGraphPage


# TODOS:
# - enum reads as constants
# - remove the typ argument of side-effecting ops?

# - nested operations
# - neq -> not eq

# - lt etc one arg machine int

# - move int_to_int64 to earlier in block

# risc-v:
# mul_o_i, backwards mul_i_i_must_fit, sub_i_i_must_fit
# vector_subrange_o_i_i with smallbv argument and unknown bounds
# CSE

# - replicate
# - sub_i_o_wrapped_res

# before inlining: 4753 -> 6516
# filesize 83 MB -> 83 MB



def construct_ir(functionast, codegen, singleblock=False):
    # bring operations into a block format:
    # a dictionary {label-as-int: [list of operations]}
    # every list of operations ends with a goto, return or failure
    body = functionast.body
    if singleblock:
        body = body + [parse.JustStop()]

    # first check which ops can be jumped to
    jumptargets = {getattr(op, 'target', 0) for op in body}
    for i, op in enumerate(body):
        if isinstance(op, parse.ConditionalJump):
            jumptargets.add(i + 1)

    # now split into blocks
    blocks = {}
    for i, op in enumerate(body):
        if i in jumptargets:
            blocks[i] = block = []
        block.append(op)

    # insert goto at the end to make have no "fall throughs"
    for blockpc, block in sorted(blocks.items()):
        lastop = block[-1]
        if lastop.end_of_block:
            continue
        block.append(parse.Goto(blockpc + len(block)))

    if singleblock:
        args = []
    else:
        args = functionast.args

    return build_ssa(blocks, functionast, args, codegen)


def compute_entryblocks(blocks):
    entryblocks = defaultdict(list)
    for pc, block in blocks.iteritems():
        for op in block:
            if isinstance(op, (parse.Goto, parse.ConditionalJump)):
                entryblocks[op.target].append(pc)
    return entryblocks

class SSABuilder(object):
    def __init__(self, blocks, functionast, functionargs, codegen, startpc=0, extra_args=None):
        self.blocks = blocks
        self.functionast = functionast
        self.functionargs = functionargs
        self.codegen = codegen
        self.entryblocks = compute_entryblocks(blocks)
        self.variable_map = None # {name: Value}
        self.variable_maps_at_end = {} # {pc: variable_map}
        self.has_loop = False
        self.patch_phis = defaultdict(list)
        self.startpc = startpc
        self.extra_args = extra_args
        self.view = False

    def build(self):
        allblocks = {}
        for pc, block in self.blocks.iteritems():
            ssablock = Block()
            allblocks[pc] = ssablock
        self.allblocks = allblocks
        for pc, block in sorted(self.blocks.iteritems()):
            ssablock = allblocks[pc]
            operations = ssablock.operations
            self.curr_operations = operations
            entry = self.entryblocks[pc]
            self._setup_variable_map(entry, pc)
            self._build_block(block, ssablock)
            for phi, index, var in self.patch_phis[pc]:
                if var in self.variable_map:
                    value = self.variable_map[var]
                else:
                    value = phi.prevvalues[0]
                phi.prevvalues[index] = value
            self.patch_phis[pc] = None
            self.variable_maps_at_end[pc] = self.variable_map
            self.variable_map = None
        graph = Graph(self.functionast.name, self.args, self.allblocks[self.startpc], self.has_loop)
        #if random.random() < 0.01:
        #    self.view = 1
        simplify(graph, self.codegen)
        if self.view:
            graph.view()
        return graph

    def _setup_variable_map(self, entry, pc):
        loopblock = False
        for prevpc in entry:
            if not prevpc < pc:
                loopblock = True
                self.has_loop = True
        if entry == []:
            assert pc == self.startpc
            self.variable_map = {}
            self.args = []
            if self.functionargs:
                argtypes = self.functionast.resolved_type.argtype.elements
                self.variable_map = {var: Argument(var, typ)
                        for var, typ in zip(self.functionargs, argtypes)}
                self.args = [self.variable_map[var] for var in self.functionargs]
                if self.extra_args:
                    for var, typ in self.extra_args:
                        arg = self.variable_map[var] = Argument(var, typ)
                        self.args.append(arg)
            self.variable_map['return'] = None

        elif len(entry) == 1:
            self.variable_map = self.variable_maps_at_end[entry[0]].copy()
        elif not loopblock:
            assert len(entry) >= 2
            # merge
            self.variable_map = {}
            for var, value0 in self.variable_maps_at_end[entry[0]].iteritems():
                othervalues = [
                    self.variable_maps_at_end[prevpc].get(var)
                        for prevpc in entry[1:]
                ]
                if value0 is None or None in othervalues:
                    self.variable_map[var] = None # uninintialized along some path
                    continue
                if len(set(othervalues + [value0])) == 1:
                    self.variable_map[var] = value0
                else:
                    phi = Phi(
                        [self.allblocks[prevpc] for prevpc in entry],
                        [value0] + othervalues,
                        value0.resolved_type,
                    )
                    self._addop(phi)
                    self.variable_map[var] = phi
        else:
            assert loopblock
            # be pessimistic and insert Phi's for everything. they need
            # patching later
            prevpc = min(entry)
            assert entry[0] == prevpc # should be sorted
            assert prevpc < pc
            self.variable_map = {}
            for var, value in self.variable_maps_at_end[prevpc].iteritems():
                if value is None:
                    self.variable_map[var] = None # uninintialized along some path
                    continue
                phi = Phi(
                    [self.allblocks[otherprevpc] for otherprevpc in entry],
                    [value] + [None] * (len(entry) - 1),
                    value.resolved_type,
                )
                self._addop(phi)
                self.variable_map[var] = phi
                for index, otherprevpc in enumerate(entry):
                    if index == 0:
                        continue
                    self.patch_phis[otherprevpc].append((phi, index, var))

    def _build_block(self, block, ssablock):
        for index, op in enumerate(block):
            if isinstance(op, parse.LocalVarDeclaration):
                # weird special case for uint64c
                if op.value is not None:
                    args = self._get_args(op.value.args)
                    ssaop = Operation(op.value.name, args, op.value.resolved_type, op.value.sourcepos, op.name)
                else:
                    if isinstance(op.resolved_type, types.Struct):
                        ssaop = Allocate(op.resolved_type, op.sourcepos)
                    else:
                        const = DefaultValue(op.resolved_type)
                        self.variable_map[op.name] = const
                        continue
                self.variable_map[op.name] = self._addop(ssaop)
            elif isinstance(op, parse.Operation):
                args = self._get_args(op.args)
                if op.name == "$zinternal_vector_init":
                    ssaop = VectorInit(args[0], op.resolved_type, op.sourcepos)
                elif op.name == "$zinternal_vector_update":
                    ssaop = VectorUpdate(args, op.resolved_type, op.sourcepos)
                else:
                    ssaop = Operation(op.name, args, op.resolved_type, op.sourcepos, op.result)
                self._addop(ssaop)
                self._store(op.result, ssaop)
            elif isinstance(op, parse.Assignment):
                value = self._get_arg(op.value, op.result)
                if op.resolved_type != op.value.resolved_type:
                    # we need a cast first
                    value = Cast(value, op.resolved_type, op.sourcepos, op.result)
                    self._addop(value)
                self._store(op.result, value)
            elif isinstance(op, parse.StructElementAssignment):
                lastfield = op.fields[-1]
                firstfields = op.fields[:-1]
                obj = self._get_arg(op.obj)
                typ = obj.resolved_type
                for field in firstfields:
                    typ = typ.fieldtyps[field]
                    obj = self._addop(FieldAccess(field, [obj], typ))

                fieldval = self._get_arg(op.value)
                typ = typ.fieldtyps[lastfield]
                if fieldval.resolved_type != typ:
                    fieldval = self._addop(Cast(fieldval, typ, op.sourcepos))
                self._addop(FieldWrite(lastfield, [obj, fieldval], types.Unit(), op.sourcepos))
            elif isinstance(op, parse.GeneralAssignment):
                args = self._get_args(op.rhs.args)
                rhs = Operation(op.rhs.name, args, op.rhs.resolved_type, op.sourcepos)
                self._addop(rhs)
                if isinstance(op.lhs, parse.RefAssignment):
                    self._addop(RefAssignment([self._get_arg(op.lhs.ref), rhs], types.Unit(), op.sourcepos))
                elif isinstance(op.lhs, parse.StructElementAssignment):
                    lastfield = op.lhs.fields[-1]
                    firstfields = op.lhs.fields[:-1]
                    obj = self._get_arg(op.lhs.obj)
                    typ = obj.resolved_type
                    for field in firstfields:
                        typ = typ.fieldtyps[field]
                        obj = self._addop(FieldAccess(field, [obj], typ))
                    typ = typ.fieldtyps[lastfield]
                    if rhs.resolved_type != typ:
                        import pdb;pdb.set_trace()
                        rhs = self._addop(Cast(rhs, typ, op.sourcepos))
                    self._addop(FieldWrite(lastfield, [obj, rhs], types.Unit(), op.sourcepos))
                else:
                    import pdb; pdb.set_trace()

            elif isinstance(op, parse.End):
                value = self.variable_map['return']
                ssablock.next = Return(value, op.sourcepos)
                assert index == len(block) - 1
            elif isinstance(op, parse.Goto):
                ssablock.next = Goto(self.allblocks[op.target], None)
            elif isinstance(op, parse.ConditionalJump):
                value = self._build_condition(op.condition, op.sourcepos)
                nextop = block[index + 1]
                assert isinstance(nextop, parse.Goto)
                ssablock.next = ConditionalGoto(
                    value,
                    self.allblocks[op.target],
                    self.allblocks[nextop.target],
                    op.sourcepos
                )
                assert index + 2 == len(block)
                break
            elif isinstance(op, parse.Exit):
                ssablock.next = Raise(op.kind, op.sourcepos)
            elif isinstance(op, parse.Arbitrary):
                restyp = self.functionast.resolved_type.restype
                res = DefaultValue(restyp)
                ssablock.next = Return(res, op.sourcepos)
            elif isinstance(op, parse.JustStop):
                ssablock.next = JustStop()
            else:
                xxx

    def _get_args(self, args):
        return [self._get_arg(arg) for arg in args]

    def _get_arg(self, parseval, varname_hint=None):
        if isinstance(parseval, parse.Var):
            if parseval.name in self.variable_map:
                assert self.variable_map[parseval.name] is not None
                return self.variable_map[parseval.name]
            if parseval.name == 'true':
                return BooleanConstant.TRUE
            elif parseval.name == 'false':
                return BooleanConstant.FALSE
            if parseval.name in self.codegen.let_values:
                return self.codegen.let_values[parseval.name]
            register_read = GlobalRead(parseval.name, parseval.resolved_type)
            self._addop(register_read)
            return register_read
        elif isinstance(parseval, parse.StructConstruction):
            assert parseval.fieldnames == parseval.resolved_type.ast.names
            args = self._get_args(parseval.fieldvalues)
            for index, fieldname in enumerate(parseval.fieldnames):
                arg = args[index]
                targettyp = parseval.resolved_type.fieldtyps[fieldname]
                if arg.resolved_type != targettyp:
                    args[index] = self._addop(Cast(arg, targettyp))
            ssaop = StructConstruction(parseval.name, args, parseval.resolved_type)
            self._addop(ssaop)
            return ssaop
        elif isinstance(parseval, parse.FieldAccess):
            # this optimization is necessary, annoyingly enough
            if isinstance(parseval.obj, parse.StructConstruction):
                index = parseval.obj.fieldnames.index(parseval.element)
                return self._get_arg(parseval.obj.fieldvalues[index])
            arg = self._get_arg(parseval.obj)
            ssaop = FieldAccess(parseval.element, [arg], parseval.resolved_type)
            self._addop(ssaop)
            return ssaop
        elif isinstance(parseval, parse.Cast):
            arg = self._get_arg(parseval.expr)
            ssaop = UnionCast(parseval.variant, [arg], parseval.resolved_type)
            return self._addop(ssaop)
        elif isinstance(parseval, parse.RefOf):
            return self._addop(RefOf([self._get_arg(parseval.expr)], parseval.resolved_type))
        elif isinstance(parseval, parse.Number):
            return MachineIntConstant(parseval.number)
        elif isinstance(parseval, parse.BitVectorConstant):
            return SmallBitVectorConstant(parseval.constant, parseval.resolved_type)
        else:
            assert isinstance(parseval, (parse.Unit, parse.String))
            return AstConstant(parseval, parseval.resolved_type)

    def _build_condition(self, condition, sourcepos):
        if isinstance(condition, parse.Comparison):
            return self._addop(Operation(condition.operation, self._get_args(condition.args), types.Bool(), sourcepos))
        elif isinstance(condition, parse.ExprCondition):
            return self._get_arg(condition.expr)
        elif isinstance(condition, parse.UnionVariantCheck):
            return self._addop(UnionVariantCheck(condition.variant, [self._get_arg(condition.var)], types.Bool(), sourcepos))
        else:
            import pdb; pdb.set_trace()

    def _addop(self, op):
        assert isinstance(op, (Operation, Phi))
        self.curr_operations.append(op)
        return op

    def _store(self, result, value):
        if result not in self.variable_map and result != 'return' or result == 'current_exception':
            self._addop(GlobalWrite(result, [value], value.resolved_type))
        else:
            self.variable_map[result] = value

def build_ssa(blocks, functionast, functionargs, codegen, startpc=0, extra_args=None):
    builder = SSABuilder(blocks, functionast, functionargs, codegen, startpc, extra_args)
    return builder.build()

def extract_global_value(graph, name):
    block = graph.startblock
    if not isinstance(block.next, JustStop):
        return
    lastop = block.operations[-1]
    if not isinstance(lastop, GlobalWrite):
        return
    if name != lastop.name:
        return
    value = lastop.args[0]
    if not isinstance(value, Constant):
        return
    return value



# graph

class Block(object):
    _pc = -1 # assigned later in emitfunction

    def __init__(self, operations=None, next=None):
        if operations is None:
            operations = []
        assert isinstance(operations, list)
        self.operations = operations
        self.next = next
        
    def __repr__(self):
        return "<Block operations=%s next=%s>" % (self.operations, self.next.__class__.__name__)

    def __getitem__(self, index):
        return self.operations[index]

    def emit(self, cls, opname, args, resolved_type, sourcepos, varname_hint=None):
        op = Operation(opname, args, resolved_type, sourcepos, varname_hint)
        op.__class__ = cls
        self.operations.append(op)
        return op

    def emit_phi(self, prevblocks, prevvalues, resolved_type):
        op = Phi(prevblocks, prevvalues, resolved_type)
        self.operations.append(op)
        return op

    def replace_prev(self, block, otherblock):
        for op in self.operations:
            if not isinstance(op, Phi):
                return
            assert otherblock not in op.prevblocks
            for index, oldblock in enumerate(op.prevblocks):
                if oldblock is block:
                    op.prevblocks[index] = otherblock

    def prevblocks_from_phis(self):
        res = []
        for op in self.operations:
            if not isinstance(op, Phi):
                return res
            if res:
                assert op.prevblocks == res
            else:
                res = op.prevblocks
        return res

    def copy_operations(self, replacements, block_replacements=None):
        def replace(arg):
            if isinstance(arg, Constant):
                return arg
            return replacements[arg]
        res = []
        for op in self.operations:
            if isinstance(op, NonSSAAssignment):
                continue
            elif isinstance(op, Phi):
                newop = Phi(
                    [block_replacements[block] for block in op.prevblocks],
                    [replace(arg) for arg in op.prevvalues],
                    op.resolved_type)
            else:
                newop = Operation(op.name, [replace(arg) for arg in op.args], op.resolved_type, op.sourcepos, op.varname_hint)
                newop.__class__ = op.__class__
            replacements[op] = newop
            res.append(newop)
        return res

    def _dot(self, dotgen, seen, print_varnames):
        if self in seen:
            return str(id(self))
        seen.add(self)
        res = []
        for index, op in enumerate(self.operations):
            name = op._get_print_name(print_varnames)
            if isinstance(op, Operation):
                oprepr = "%s(%s) [%s]" % (
                    op.name,
                    ", ".join([a._repr(print_varnames) for a in op.args]),
                    op.__class__.__name__
                )
            else:
                assert isinstance(op, Phi)
                oprepr = "phi [%s]" % (
                    ", ".join([a._repr(print_varnames) for a in op.prevvalues])
                )
            res.append("%s = %s" % (name, oprepr))
        res.append(self.next._repr(print_varnames))
        label = "\\l".join(res)
        nextblocks = self.next.next_blocks()
        fillcolor = "white"
        if len(nextblocks) == 0:
            fillcolor = "yellow"
        dotgen.emit_node(
            str(id(self)),
            shape="box",
            label=label,
            fillcolor=fillcolor,
        )
        for index, nextblock in enumerate(nextblocks):
            nextid = nextblock._dot(dotgen, seen, print_varnames)
            label = ''
            if len(nextblocks) > 1:
                label = str(bool(index))
            dotgen.emit_edge(str(id(self)), nextid, label=label)
        return str(id(self))


class Graph(object):
    def __init__(self, name, args, startblock, has_loop=False):
        self.name = name
        self.args = args
        self.startblock = startblock
        self.has_loop = has_loop

    def __repr__(self):
        return "<Graph %s %s>" % (self.name, self.args)

    def view(self):
        from rpython.translator.tool.make_dot import DotGen
        from dotviewer import graphclient
        import pytest
        dotgen = DotGen('G')
        print_varnames = self._dot(dotgen)
        GraphPage(dotgen.generate(target=None), print_varnames, self.args).display()

    def _dot(self, dotgen):
        name = "graph" + self.name
        dotgen.emit_node(
            name,
            shape="box",
            fillcolor="green",
            label="\\l".join([self.name, "[" + ", ".join([a.name for a in self.args]) + "]"])
        )
        seen = set()
        print_varnames = {}
        firstid = self.startblock._dot(dotgen, seen, print_varnames)
        dotgen.emit_edge(name, firstid)
        return print_varnames

    def iterblocks(self):
        todo = [self.startblock]
        seen = set()
        while todo:
            block = todo.pop()
            if block in seen:
                continue
            yield block
            seen.add(block)
            todo.extend(block.next.next_blocks())

    def iterblockops(self):
        for block in self.iterblocks():
            for op in block.operations:
                yield op, block

    def make_entrymap(self):
        entry = defaultdict(list)
        for block in self.iterblocks():
            for next in block.next.next_blocks():
                entry[next].append(block)
        entry[self.startblock] = []
        return entry

    def check(self):
        # minimal consistency check, will add things later
        entrymap = self.make_entrymap()
        # check that phi.prevvalues only contains predecessors of a block
        defined_vars = set(self.args)
        for block in self.iterblocks():
            for op in block:
                defined_vars.add(op)
                if not isinstance(op, Phi):
                    continue
                for prevblock in op.prevblocks:
                    assert prevblock in entrymap
                    assert prevblock in entrymap[block]
        # check that all the used values are defined somewhere
        for block in self.iterblocks():
            assert len(set(block.operations)) == len(block.operations)
            for op in block:
                for value in op.getargs():
                    assert value in defined_vars or isinstance(value, Constant)
            for value in block.next.getargs():
                assert value in defined_vars or isinstance(value, Constant)

    def replace_ops(self, replacements):
        res = False
        for block in self.iterblocks():
            for op in block.operations:
                assert op not in replacements # must have been removed already
                res = op.replace_ops(replacements) or res
            res = block.next.replace_ops(replacements) or res
        return res

    def replace_op(self, oldop, newop):
        return self.replace_ops({oldop: newop})

# values

class Value(object):
    def __init__(self, resolved_type):
        self.resolved_type = resolved_type

    def _repr(self, print_varnames):
        return repr(self)

    def _get_print_name(self, print_varnames):
        if self in print_varnames:
            name = print_varnames[self]
        else:
            name = "i%s" % (len(print_varnames), )
            print_varnames[self] = name
        return name

    def getargs(self):
        return []

    def __repr__(self):
        return "<%s %x>" % (self.__class__.__name__, id(self))

class Argument(Value):
    def __init__(self, name, resolved_type):
        self.resolved_type = resolved_type
        self.name = name

    def __repr__(self):
        return "Argument(%r, %r)" % (self.name, self.resolved_type)

    def _repr(self, print_varnames):
        return self.name

class Operation(Value):
    can_have_side_effects = True

    def __init__(self, name, args, resolved_type, sourcepos=None, varname_hint=None):
        for arg in args:
            assert isinstance(arg, Value)
        self.name = name
        self.args = args
        self.resolved_type = resolved_type
        assert isinstance(sourcepos, (str, type(None)))
        self.sourcepos = sourcepos
        self.varname_hint = varname_hint

    def __repr__(self):
        return "Operation(%r, %r, %r)" % (self.name, self.args, self.sourcepos)

    def _repr(self, print_varnames):
        return self._get_print_name(print_varnames)

    def getargs(self):
        return self.args

    def replace_ops(self, replacements):
        assert self not in replacements
        res = False
        for index, arg in enumerate(self.args):
            if arg in replacements:
                self.args[index] = replacements[arg]
                res = True
        return res

class Cast(Operation):
    can_have_side_effects = False

    def __init__(self, arg, resolved_type, sourcepos=None, varname_hint=None):
        Operation.__init__(self, "$cast", [arg], resolved_type, sourcepos, varname_hint)

    def __repr__(self):
        return "Cast(%r, %r, %r)" % (self.args[0], self.resolved_type, self.sourcepos)

class Allocate(Operation):
    can_have_side_effects = False

    def __init__(self, resolved_type, sourcepos):
        Operation.__init__(self, "$allocate", [], resolved_type, sourcepos)

    def __repr__(self):
        return "Allocate(%r, %r)" % (self.resolved_type, self.sourcepos, )

class StructConstruction(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "StructConstruction(%r, %r, %r)" % (self.name, self.args, self.resolved_type)

class FieldAccess(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "FieldAccess(%r, %r, %r)" % (self.name, self.args, self.resolved_type)

class FieldWrite(Operation):
    def __repr__(self):
        return "FieldWrite(%r, %r, %r)" % (self.name, self.args, self.resolved_type)

class UnionVariantCheck(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "UnionVariantCheck(%r, %r, %r)" % (self.name, self.args, self.resolved_type)

class UnionCast(Operation):
    def __repr__(self):
        return "UnionCast(%r, %r, %r)" % (self.name, self.args, self.resolved_type)

class GlobalRead(Operation):
    can_have_side_effects = False
    def __init__(self, name, resolved_type):
        Operation.__init__(self, name, [], resolved_type, None)

    def __repr__(self):
        return "GlobalRead(%r, %r)" % (self.name, self.resolved_type)

class GlobalWrite(Operation):
    def __repr__(self):
        return "GlobalWrite(%r, %r, %r)" % (self.name, self.args, self.resolved_type)

class RefAssignment(Operation):
    def __init__(self, args, resolved_type, sourcepos):
        Operation.__init__(self, "$ref-assign", args, resolved_type, sourcepos)

    def __repr__(self):
        return "RefAssignment(%r, %r, %r)" % (self.args, self.resolved_type, self.sourcepos, )

class RefOf(Operation):
    can_have_side_effects = False

    def __init__(self, args, resolved_type, sourcepos=None):
        Operation.__init__(self, "$ref-of", args, resolved_type, sourcepos)

    def __repr__(self):
        return "RefOf(%r, %r, %r)" % (self.args, self.resolved_type, self.sourcepos, )

class VectorInit(Operation):
    can_have_side_effects = False

    def __init__(self, size, resolved_type, sourcepos):
        Operation.__init__(self, "$zinternal_vector_init", [size], resolved_type, sourcepos)

    def __repr__(self):
        return "VectorInit(%r, %r, %r)" % (self.args[0], self.resolved_type, self.sourcepos, )

class VectorUpdate(Operation):
    can_have_side_effects = False

    def __init__(self, args, resolved_type, sourcepos):
        Operation.__init__(self, "$zinternal_vector_update", args, resolved_type, sourcepos)

    def __repr__(self):
        return "VectorUpdate(%r, %r, %r)" % (self.args, self.resolved_type, self.sourcepos, )

class NonSSAAssignment(Operation):
    def __init__(self, lhs, rhs):
        Operation.__init__(self, "non_ssa_assign", [lhs, rhs], types.Unit(), None)

    def __repr__(self):
        return "NonSSAAssignment(%r, %r)" % (self.args[0], self.args[1])

class Comment(Operation):
    def __init__(self, comment):
        Operation.__init__(self, comment, [], types.Unit())

class Phi(Value):
    can_have_side_effects = False

    def __init__(self, prevblocks, prevvalues, resolved_type):
        for block in prevblocks:
            assert isinstance(block, Block)
        for value in prevvalues:
            assert isinstance(value, Value) or value is None
        self.prevblocks = prevblocks
        self.prevvalues = prevvalues
        self.resolved_type = resolved_type

    def _repr(self, print_varnames):
        return self._get_print_name(print_varnames)

    def getargs(self):
        return self.prevvalues

    def replace_ops(self, replacements):
        assert self not in replacements
        res = False
        for index, op in enumerate(self.prevvalues):
            if op in replacements:
                self.prevvalues[index] = replacements[op]
                res = True
        return res

class Constant(Value):
    pass

class AstConstant(Constant):
    def __init__(self, ast, resolved_type):
        self.ast = ast
        self.resolved_type = resolved_type

    def _repr(self, print_varnames):
        return "%s(%s, %s)" % (self.__class__.__name__, self.ast, self.resolved_type)

    def __repr__(self):
        return "AstConstant(%r, %r)" % (self.ast, self.resolved_type)

class BooleanConstant(Constant):
    def __init__(self, value):
        assert isinstance(value, bool)
        self.value = value
        self.resolved_type = types.Bool()

    def _repr(self, print_varnames):
        if self.value:
            return "BooleanConstant.TRUE"
        else:
            return "BooleanConstant.FALSE"

    def __repr__(self):
        return self._repr({})

    @staticmethod
    def frombool(value):
        return BooleanConstant.TRUE if value else BooleanConstant.FALSE

BooleanConstant.TRUE = BooleanConstant(True)
BooleanConstant.FALSE = BooleanConstant(False)


class MachineIntConstant(Constant):
    resolved_type = types.MachineInt()
    def __init__(self, number):
        assert isinstance(number, int)
        self.number = number

    def _repr(self, print_varnames):
        return repr(self)

    def __repr__(self):
        return "MachineIntConstant(%r)" % (self.number, )


class IntConstant(Constant):
    resolved_type = types.Int()
    def __init__(self, number):
        self.number = number

    def _repr(self, print_varnames):
        return repr(self)

    def __repr__(self):
        return "IntConstant(%r)" % (self.number, )


class SmallBitVectorConstant(Constant):
    def __init__(self, value, resolved_type):
        self.value = value
        self.resolved_type = resolved_type

    @staticmethod
    def from_ruint(size, val):
        if size % 4 == 0:
            value = '0x' + hex(val)[2:].rjust(size // 4, '0')
        else:
            value = '0b' + bin(val)[2:].rjust(size, '0')
        return SmallBitVectorConstant(value, types.SmallFixedBitVector(size))

    def _repr(self, print_varnames):
        return repr(self)

    def __repr__(self):
        return "SmallBitVectorConstant(%r, %s)" % (self.value, self.resolved_type)


class DefaultValue(Constant):

    def __init__(self, resolved_type):
        self.resolved_type = resolved_type

    def __repr__(self):
        return "DefaultValue(%r)" % (self.resolved_type, )



# next

class Next(object):
    def __init__(self, sourcepos):
        self.sourcepos = sourcepos

    def next_blocks(self):
        return []

    def getargs(self):
        return []

    def replace_next(self, block, otherblock):
        pass

    def replace_ops(self, replacements):
        return False

    def _repr(self, print_varnames):
        return self.__class__.__name__

class Return(Next):
    def __init__(self, value, sourcepos=None):
        assert isinstance(value, Value) or value is None
        self.value = value
        self.sourcepos = sourcepos

    def getargs(self):
        return [self.value] if self.value is not None else []

    def replace_ops(self, replacements):
        if self.value in replacements:
            self.value = replacements[self.value]
            return True
        return False

    def _repr(self, print_varnames, blocknames=None):
        return "Return(%s, %r)" % (None if self.value is None else self.value._repr(print_varnames), self.sourcepos)

class Raise(Next):
    def __init__(self, kind, sourcepos):
        self.kind = kind
        self.sourcepos = sourcepos

    def _repr(self, print_varnames, blocknames=None):
        return "Raise(%s, %r)" % (self.kind, self.sourcepos)

class JustStop(Next):
    def __init__(self):
        self.sourcepos = None

    def _repr(self, print_varnames, blocknames=None):
        return "JustStop(%r)" % (self.sourcepos, )


class Goto(Next):
    def __init__(self, target, sourcepos=None):
        assert isinstance(target, Block)
        self.target = target
        self.sourcepos = sourcepos

    def next_blocks(self):
        return [self.target]

    def replace_next(self, block, otherblock):
        if self.target is block:
            self.target = otherblock

    def _repr(self, print_varnames, blocknames=None):
        if blocknames:
            return "Goto(%s, %r)" % (blocknames[self.target], self.sourcepos)
        return "goto"


class ConditionalGoto(Next):
    def __init__(self, booleanvalue, truetarget, falsetarget, sourcepos):
        assert isinstance(truetarget, Block)
        assert isinstance(falsetarget, Block)
        assert isinstance(booleanvalue, Value)
        self.truetarget = truetarget
        self.falsetarget = falsetarget
        self.booleanvalue = booleanvalue
        self.sourcepos = sourcepos

    def getargs(self):
        return [self.booleanvalue]

    def next_blocks(self):
        return [self.falsetarget, self.truetarget]

    def replace_next(self, block, otherblock):
        if self.truetarget is block:
            self.truetarget = otherblock
        if self.falsetarget is block:
            self.falsetarget = otherblock

    def replace_ops(self, replacements):
        if self.booleanvalue in replacements:
            self.booleanvalue = replacements[self.booleanvalue]
            return True
        return False

    def _repr(self, print_varnames, blocknames=None):
        if blocknames:
            return "ConditionalGoto(%s, %s, %s, %r)" % (self.booleanvalue._repr(print_varnames), blocknames[self.truetarget], blocknames[self.falsetarget], self.sourcepos)
        return "goto if %s" % (self.booleanvalue._repr(print_varnames), )

# printing

def print_graph_construction(graph):
    res = []
    blocks = list(graph.iterblocks())
    blocknames = {block: "block%s" % i for i, block in enumerate(blocks)}
    print_varnames = {}
    for arg in graph.args:
        print_varnames[arg] = arg.name
        res.append("%s = %r" % (arg.name, arg))
    for block, name in blocknames.iteritems():
        res.append("%s = Block()" % name)
    pending_updates = defaultdict(list)
    seen_ops = set()

    for block, blockname in blocknames.iteritems():
        for op in block.operations:
            name = op._get_print_name(print_varnames)
            if isinstance(op, Operation):
                args = ", ".join([a._repr(print_varnames) for a in op.args])
                res.append("%s = %s.emit(%s, %r, [%s], %r, %r, %r)"  % (name, blockname, op.__class__.__name__, op.name, args, op.resolved_type, op.sourcepos, op.varname_hint))
            else:
                assert isinstance(op, Phi)
                blockargs = ", ".join([blocknames[b] for b in op.prevblocks])
                args = []
                for index, a in enumerate(op.prevvalues):
                    if isinstance(a, (Operation, Phi)) and a not in seen_ops:
                        args.append('None')
                        pending_updates[a].append((name, index))
                    else:
                        args.append(a._repr(print_varnames))

                args = ", ".join(args)
                res.append("%s = %s.emit_phi([%s], [%s], %s)" % (name, blockname, blockargs, args, op.resolved_type))
            if pending_updates[op]:
                for prevname, index in pending_updates[op]:
                    res.append("%s.prevvalues[%s] = %s" % (prevname, index, name))
            seen_ops.add(op)
        res.append("%s.next = %s" % (blockname, block.next._repr(print_varnames, blocknames)))
    res.append("graph = Graph(%r, [%s], block0)" % (graph.name, ", ".join(arg.name for arg in graph.args)))
    return res


class GraphPage(BaseGraphPage):
    save_tmp_file = str(udir.join('graph.dot'))

    def compute(self, source, varnames, args):
        self.source = source
        self.links = {var: str(op.resolved_type) for op, var in varnames.items()}
        for arg in args:
            self.links[arg.name] = str(arg.resolved_type)


# some simple graph simplifications

def repeat(func):
    def repeated(*args, **kwargs):
        ever_changed = False
        while 1:
            changed = func(*args, **kwargs)
            assert isinstance(changed, bool)
            if not changed:
                return ever_changed
            ever_changed = True
    return repeated

def simplify(graph, codegen):
    res = _simplify(graph, codegen)
    return res

@repeat
def _simplify(graph, codegen):
    res = False
    res = join_blocks(graph) or res
    graph.check()
    res = remove_dead(graph, codegen) or res
    graph.check()
    res = simplify_phis(graph) or res
    graph.check()
    res = inline(graph, codegen) or res
    graph.check()
    res = LocalOptimizer(graph, codegen).optimize() or res
    graph.check()
    res = remove_if_true_false(graph) or res
    graph.check()
    res = remove_empty_blocks(graph) or res
    graph.check()
    res = swap_not(graph, codegen) or res
    if res:
        graph.check()
    return res

@repeat
def remove_dead(graph, codegen):
    def can_remove_op(op):
        if not op.can_have_side_effects:
            return True
        if op.name == "@not":
            return True
        name = codegen.builtin_names.get(op.name, op.name)
        return type(op) is Operation and name in supportcode.purefunctions

    changed = False
    needed = set()
    # in theory we need a proper fix point but too annoying (Sail has very few
    # loops)
    for block in graph.iterblocks():
        for op in block.operations:
            args = op.getargs()[:]
            if isinstance(op, Phi) and op in args:
                args.remove(op)
            needed.update(args)
        needed.update(block.next.getargs())
    for block in graph.iterblocks():
        operations = [op for op in block.operations if op in needed or not can_remove_op(op)]
        if len(operations) != len(block.operations):
            changed = True
            block.operations[:] = operations
    return changed

@repeat
def remove_empty_blocks(graph):
    changed = False
    for block in graph.iterblocks():
        for nextblock in block.next.next_blocks():
            if nextblock.operations:
                continue
            if not isinstance(nextblock.next, Goto):
                continue
            if nextblock in nextblock.next.target.prevblocks_from_phis():
                continue
            block.next.replace_next(nextblock, nextblock.next.target)
            nextblock.next.target.replace_prev(nextblock, block)
            changed = True
    return changed

@repeat
def join_blocks(graph):
    entrymap = graph.make_entrymap()
    changed = False
    for block in entrymap:
        if block.operations is None:
            continue
        while 1:
            if not isinstance(block.next, Goto):
                break
            nextblock = block.next.target
            if len(entrymap[nextblock]) != 1:
                break
            for op in nextblock.operations:
                assert not isinstance(op, Phi)
            block.operations.extend(nextblock.operations)
            nextblock.operations = None
            changed = True
            block.next = nextblock.next
            for nextnextblock in block.next.next_blocks():
                nextnextblock.replace_prev(nextblock, block)
    return changed

@repeat
def swap_not(graph, codegen):
    changed = False
    for block in graph.iterblocks():
        cond = block.next
        if not isinstance(cond, ConditionalGoto) or type(cond.booleanvalue) is not Operation:
            continue
        if cond.booleanvalue.name != "@not":
            continue
        cond.booleanvalue, = cond.booleanvalue.args
        cond.truetarget, cond.falsetarget = cond.falsetarget, cond.truetarget
        changed = True
    if changed:
        remove_dead(graph, codegen)
    return changed

@repeat
def simplify_phis(graph):
    replace_phis = {}
    for block in graph.iterblocks():
        for index, op in enumerate(block.operations):
            if not isinstance(op, Phi):
                continue
            values = set(op.prevvalues)
            if len(values) == 1 or (len(values) == 2 and op in values):
                values.discard(op)
                value, = values
                block.operations[index] = None
                replace_phis[op] = value
                # this is really inefficient, but I don't want to think
                block.operations = [op for op in block.operations if op is not None]
                graph.replace_ops(replace_phis)
                return True


    return False

@repeat
def remove_if_true_false(graph):
    changed = False
    for block in graph.iterblocks():
        cond = block.next
        if not isinstance(cond, ConditionalGoto) or type(cond.booleanvalue) is not BooleanConstant:
            continue
        if cond.booleanvalue.value:
            deadblock = cond.falsetarget
            takenblock = cond.truetarget
        else:
            deadblock = cond.truetarget
            takenblock = cond.falsetarget
        block.next = Goto(takenblock)
        changed = True
    if changed:
        # need to remove Phi arguments
        reachable_blocks = set(graph.iterblocks())
        replace_phis = {}
        for block in reachable_blocks:
            for index, op in enumerate(block.operations):
                if not isinstance(op, Phi):
                    continue
                prevblocks = []
                prevvalues = []
                for prevblock, prevvalue in zip(op.prevblocks, op.prevvalues):
                    if prevblock in reachable_blocks:
                        prevblocks.append(prevblock)
                        prevvalues.append(replace_phis.get(prevvalue, prevvalue))
                op.prevblocks = prevblocks
                op.prevvalues = prevvalues
                if len(prevblocks) == 1:
                    replace_phis[op] = op.prevvalues[0]
                    block.operations[index] = None
            block.operations = [op for op in block.operations if op]
        if replace_phis:
            graph.replace_ops(replace_phis)
    return changed

class NoMatchException(Exception):
    pass

def symmetric(func):
    def optimize(self, op):
        arg0, arg1 = self._args(op)
        try:
            res = func(self, op, arg0, arg1)
        except NoMatchException:
            pass
        else:
            if res is not None:
                return res
        return func(self, op, arg1, arg0)
    return optimize

REMOVE = "REMOVE"

class LocalOptimizer(object):
    def __init__(self, graph, codegen):
        self.graph = graph
        self.codegen = codegen
        self.changed = False

    def view(self):
        self.graph.view()

    def optimize(self):
        self.replacements = {}
        for block in self.graph.iterblocks():
            self.optimize_block(block)
        if self.replacements:
            # XXX do them all in one go
            while 1:
                changed = self.graph.replace_ops(self.replacements)
                if not changed:
                    break
            self.graph.check()
            return True
        return self.changed

    def optimize_block(self, block):
        self.newoperations = []
        for i, op in enumerate(block.operations):
            newop = self._optimize_op(block, i, op)
            if newop is REMOVE:
                self.changed = True
            elif newop is not None:
                assert op.resolved_type is newop.resolved_type
                self.replacements[op] = newop
        block.operations = self.newoperations

    def newop(self, name, args, resolved_type, sourcepos=None, varname_hint=None):
        newop = Operation(
            name, args, resolved_type, sourcepos,
            varname_hint)
        self.newoperations.append(newop)
        return newop

    def newcast(self, arg, resolved_type, sourcepos=None, varname_hint=None):
        newop = Cast(arg, resolved_type, sourcepos, varname_hint)
        self.newoperations.append(newop)
        return newop

    def newphi(self, prevblocks, prevvalues, resolved_type):
        newop = Phi(prevblocks, prevvalues, resolved_type)
        self.newoperations.append(newop)
        return newop

    def _convert_to_machineint(self, arg):
        try:
            return self._extract_machineint(arg)
        except NoMatchException:
            # call int_to_int64
            return self.newop("zz5izDzKz5i64", [arg], types.MachineInt())

    def _make_int64_to_int(self, arg, sourcepos=None):
        return self.newop("zz5i64zDzKz5i", [arg], types.Int(), sourcepos)

    def _get_op_replacement(self, value):
        while value in self.replacements:
            value = self.replacements[value]
        return value

    def _args(self, op):
        return [self._get_op_replacement(value) for value in op.args]

    def _optimize_op(self, block, index, op):
        meth = getattr(self, "_optimize_" + type(op).__name__, None)
        if meth:
            try:
                res = meth(op, block, index)
            except NoMatchException:
                pass
            else:
                if res is not None:
                    return res
        self.newoperations.append(op)
        return

    def _optimize_Cast(self, op, block, index):
        arg, = self._args(op)
        if isinstance(arg, Cast):
            arg2, = self._args(arg)
            if arg2.resolved_type is op.resolved_type:
                block.operations[index] = None
                return arg2
            return self.newcast(arg2, op.resolved_type, op.sourcepos, op.varname_hint)

    def _optimize_Operation(self, op, block, index):
        name = self._builtinname(op.name)
        if name in supportcode.all_unwraps:
            specs, unwrapped_name = supportcode.all_unwraps[name]
            # these are unconditional unwraps, just rewrite them right here
            assert len(specs) == len(op.args)
            newargs = []
            for argspec, arg in zip(specs, self._args(op)):
                if argspec == "o":
                    newargs.append(arg)
                elif argspec == "i":
                    newargs.append(self._convert_to_machineint(arg))
                else:
                    assert 0, "unknown spec"
            return self.newop(
                "@" + unwrapped_name,
                newargs,
                op.resolved_type,
                op.sourcepos,
                op.varname_hint,
            )
        meth = getattr(self, "optimize_%s" % name.lstrip("@"), None)
        if meth:
            try:
                newop = meth(op)
            except NoMatchException:
                pass
            else:
                if newop is not None:
                    return newop

        # try generic constant folding
        name = name.lstrip("@")
        func = getattr(supportcode, name, None)
        if not func:
            return
        if op.resolved_type is types.Real():
            return # later
        args = self._args(op)
        if not all(isinstance(arg, Constant) for arg in args):
            return
        runtimeargs = []
        for arg in args:
            if isinstance(arg, IntConstant):
                runtimeargs.append(Integer.fromint(arg.number))
            elif isinstance(arg, MachineIntConstant):
                runtimeargs.append(arg.number)
            elif isinstance(arg, SmallBitVectorConstant):
                runtimeargs.append(r_uint(eval(arg.value)))
            elif arg.resolved_type is types.Real():
                return # later
            elif arg.resolved_type is types.Unit():
                runtimeargs.append(())
            else:
                return None
        if name not in supportcode.purefunctions:
            return
        if "undefined" in name:
            return
        res = func(None, *runtimeargs)
        if op.resolved_type is types.MachineInt():
            return MachineIntConstant(res)
        if op.resolved_type is types.Int():
            return IntConstant(int(res.tolong()))
        if isinstance(op.resolved_type, types.SmallFixedBitVector):
            return SmallBitVectorConstant.from_ruint(op.resolved_type.width, res)

    def _optimize_GlobalWrite(self, op, block, index):
        arg, = self._args(op)
        # annoying pattern matching
        if not isinstance(arg, Cast):
            return
        update_op, = self._args(arg)
        if not isinstance(update_op, Operation):
            return
        if not update_op.name == "@vector_update_o_i_o":
            return
        update_list, index, element = self._args(update_op)
        if update_list.resolved_type is types.GenericBitVector():
            return
        if not isinstance(update_list, Cast):
            import pdb;pdb.set_trace()
            return
        update_list_cast, = self._args(update_list)
        if not isinstance(update_list_cast, GlobalRead):
            import pdb;pdb.set_trace()
            return
        if update_list_cast.name != op.name:
            import pdb;pdb.set_trace()
            return
        # we read a list (from typically a register), update it, write it back.
        # that means we can do it inplace instead
        update_op.name = "@helper_vector_update_inplace_o_i_o"
        update_op.resolved_type = types.Unit()
        return REMOVE # don't need the GlobalWrite any more

    def _optimize_VectorUpdate(self, op, block, index):
        update_list, index, element = self._args(op)
        if not isinstance(update_list, VectorInit):
            return
        self.newop("@helper_vector_update_inplace_o_i_o",
            [update_list, index, element],
            types.Unit(),
            op.sourcepos,
            op.varname_hint,
        )
        return update_list # it's inplace, so the result is the same as the argument

    def _optimize_Phi(self, op, block, index):
        if op.resolved_type is types.GenericBitVector():
            bvs = []
            for arg in op.prevvalues:
                arg, typ = self._extract_smallfixedbitvector(self._get_op_replacement(arg))
                bvs.append(arg)
            return self.newcast(
                self.newphi(
                    op.prevblocks,
                    bvs,
                    typ),
                types.GenericBitVector()
            )
        if op.resolved_type is types.Int():
            machineints = []
            for arg in op.prevvalues:
                arg = self._extract_machineint(self._get_op_replacement(arg))
                machineints.append(arg)
            if all(isinstance(arg, Constant) for arg in machineints):
                return
            return self._make_int64_to_int(
                self.newphi(
                    op.prevblocks,
                    machineints,
                    types.MachineInt())
            )

    def _builtinname(self, name):
        return self.codegen.builtin_names.get(name, name)

    def _extract_smallfixedbitvector(self, arg):
        if not isinstance(arg, Cast):
            raise NoMatchException
        expr = arg.args[0]
        typ = expr.resolved_type
        if not isinstance(typ, types.SmallFixedBitVector):
            assert typ is types.GenericBitVector() or isinstance(
                typ, types.BigFixedBitVector
            )
            raise NoMatchException
        return expr, typ

    def _extract_machineint(self, arg):
        if arg.resolved_type is types.MachineInt():
            return arg
        if isinstance(arg, IntConstant):
            if isinstance(arg.number, int):
                return MachineIntConstant(arg.number)
        if (
            not isinstance(arg, Operation)
            or self._builtinname(arg.name) != "int64_to_int"
        ):
            if isinstance(arg, Cast):
                import pdb;pdb.set_trace()
            raise NoMatchException
        return arg.args[0]

    def _extract_number(self, arg):
        if isinstance(arg, MachineIntConstant):
            return arg
        num = self._extract_machineint(arg)
        if not isinstance(num, MachineIntConstant):
            raise NoMatchException
        return num

    @symmetric
    def optimize_eq_bits(self, op, arg0, arg1):
        arg0, typ = self._extract_smallfixedbitvector(arg0)
        arg1 = Cast(arg1, typ)
        self.newoperations.append(arg1)
        return self.newop(
            "@eq_bits_bv_bv", [arg0, arg1], op.resolved_type, op.sourcepos,
            op.varname_hint)

    @symmetric
    def optimize_neq_bits(self, op, arg0, arg1):
        return self.newop(
            "@not", [self.newop(
                "@eq_bits",
                [arg0, arg1], op.resolved_type, op.sourcepos, op.varname_hint
            )],
            op.resolved_type
        )

    def optimize_int64_to_int(self, op):
        (arg0,) = self._args(op)
        if isinstance(arg0, MachineIntConstant):
            return IntConstant(arg0.number)
        if (
            not isinstance(arg0, Operation)
            or self._builtinname(arg0.name) != "int_to_int64"
        ):
            return
        return arg0.args[0]

    def optimize_int_to_int64(self, op):
        (arg0,) = self._args(op)
        if isinstance(arg0, IntConstant):
            assert isinstance(arg0.number, int)
            return MachineIntConstant(arg0.number)
        if (
            not isinstance(arg0, Operation)
            or self._builtinname(arg0.name) != "int64_to_int"
        ):
            return
        return arg0.args[0]

    @symmetric
    def optimize_eq_int(self, op, arg0, arg1):
        arg1 = self._extract_machineint(arg1)
        return self.newop(
            "@eq_int_o_i", [arg0, arg1], op.resolved_type, op.sourcepos, op.varname_hint
        )

    def optimize_eq_int_o_i(self, op):
        arg0, arg1 = self._args(op)
        arg0 = self._extract_machineint(arg0)
        return self.newop(
            "@eq", [arg0, arg1], op.resolved_type, op.sourcepos, op.varname_hint
        )

    def optimize_lt(self, op):
        arg0, arg1 = self._args(op)
        if arg0.resolved_type is not types.Int():
            arg0 = self._extract_number(arg0)
            arg1 = self._extract_number(arg1)
            return BooleanConstant.frombool(arg0.number < arg1.number)
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return self.newop("@lt", [arg0, arg1], op.resolved_type, op.sourcepos,
                          op.varname_hint)

    def optimize_gt(self, op):
        arg0, arg1 = self._args(op)
        if arg0.resolved_type is not types.Int():
            arg0 = self._extract_number(arg0)
            arg1 = self._extract_number(arg1)
            return BooleanConstant.frombool(arg0.number > arg1.number)
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return self.newop("@gt", [arg0, arg1], op.resolved_type, op.sourcepos,
                          op.varname_hint)

    def optimize_lteq(self, op):
        arg0, arg1 = self._args(op)
        if arg0.resolved_type is not types.Int():
            arg0 = self._extract_number(arg0)
            arg1 = self._extract_number(arg1)
            return BooleanConstant.frombool(arg0.number <= arg1.number)
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return self.newop("@lteq", [arg0, arg1], op.resolved_type, op.sourcepos,
                          op.varname_hint)

    def optimize_gteq(self, op):
        arg0, arg1 = self._args(op)
        if arg0.resolved_type is not types.Int():
            arg0 = self._extract_number(arg0)
            arg1 = self._extract_number(arg1)
            return BooleanConstant.frombool(arg0.number >= arg1.number)
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return self.newop("@gteq", [arg0, arg1], op.resolved_type, op.sourcepos,
                          op.varname_hint)

    def optimize_vector_subrange_o_i_i(self, op):
        arg0, arg1, arg2 = self._args(op)

        arg1 = self._extract_number(arg1)
        arg2 = self._extract_number(arg2)
        width = arg1.number - arg2.number + 1
        if width > 64:
            return

        assert op.resolved_type is types.GenericBitVector()
        try:
            arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        except NoMatchException:
            res = self.newop(
                "@vector_subrange_o_i_i_unwrapped_res",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(width),
                op.sourcepos,
                op.varname_hint,
            )
        else:
            res = self.newop(
                "@vector_subrange_fixed_bv_i_i",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(width),
                op.sourcepos,
                op.varname_hint,
            )
        return self.newcast(
            res,
            op.resolved_type,
        )

    def optimize_vector_access_o_i(self, op):
        arg0, arg1 = self._args(op)
        if isinstance(arg0.resolved_type, types.Vec):
            return
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self._extract_machineint(arg1)
        return self.newop(
            "@vector_access_bv_i",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    @symmetric
    def optimize_xor_bits(self, op, arg0, arg1):
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self.newcast(arg1, typ0)
        return self.newcast(
            self.newop(
                "@xor_vec_bv_bv",
                [arg0, arg1],
                typ0,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    @symmetric
    def optimize_and_bits(self, op, arg0, arg1):
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self.newcast(arg1, typ0)
        return self.newcast(
            self.newop(
                "@and_vec_bv_bv",
                [arg0, arg1],
                typ0,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    @symmetric
    def optimize_or_bits(self, op, arg0, arg1):
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self.newcast(arg1, typ0)
        return self.newcast(
            self.newop("@or_vec_bv_bv", [arg0, arg1], typ0, op.sourcepos, op.varname_hint),
            op.resolved_type,
        )

    def optimize_not_bits(self, op):
        (arg0,) = self._args(op)
        #if isinstance(arg0, parse.OperationExpr) and arg0.name == "@zeros_i":
        #    return parse.OperationExpr("@ones_i", [arg0.args[0]], arg0.resolved_type, arg0.sourcepos)
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)

        return self.newcast(
            self.newop(
                "@not_vec_bv", [arg0, MachineIntConstant(typ0.width)], typ0, op.sourcepos
            ),
            op.resolved_type,
            op.varname_hint,
        )

    @symmetric
    def optimize_add_bits(self, op, arg0, arg1):
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self.newcast(arg1, typ0)
        return self.newcast(
            self.newop(
                "@add_bits_bv_bv",
                [arg0, arg1, MachineIntConstant(typ0.width)],
                typ0,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    def optimize_sub_bits(self, op):
        arg0, arg1 = self._args(op)
        try:
            arg0, typ = self._extract_smallfixedbitvector(arg0)
        except NoMatchException:
            try:
                arg1, typ = self._extract_smallfixedbitvector(arg1)
            except NoMatchException:
                return None
            else:
                arg0 = self.newcast(arg0, typ)
        else:
            arg1 = self.newcast(arg1, typ)
        return self.newcast(
            self.newop(
                "@sub_bits_bv_bv",
                [arg0, arg1, MachineIntConstant(typ.width)],
                typ,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    def optimize_append(self, op):
        arg0, arg1 = self._args(op)
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        reswidth = typ0.width + typ1.width
        if reswidth > 64:
            return
        res = self.newcast(
            self.newop(
                "@bitvector_concat_bv_bv",
                [arg0, MachineIntConstant(typ1.width), arg1],
                types.SmallFixedBitVector(reswidth),
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )
        return res

    def optimize_vector_update_subrange_o_i_i_o(self, op):
        arg0, arg1, arg2, arg3 = self._args(op)

        arg1 = self._extract_number(arg1)
        arg2 = self._extract_number(arg2)
        width = arg1.number - arg2.number + 1
        if width > 64:
            return

        assert op.resolved_type is types.GenericBitVector()
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg3, typ3 = self._extract_smallfixedbitvector(arg3)
        assert 0 <= arg2.number <= arg2.number < typ0.width
        assert typ3.width == width
        res = self.newop(
            "@vector_update_subrange_fixed_bv_i_i_bv",
            [arg0, arg1, arg2, arg3],
            typ0, op.sourcepos,
            op.varname_hint,
        )
        return self.newcast(
            res,
            types.GenericBitVector()
        )

    def optimize_slice_o_i_i(self, op):
        arg0, arg1, arg2 = self._args(op)
        arg1 = self._extract_machineint(arg1)
        arg2 = self._extract_number(arg2)
        length = arg2.number
        if length > 64:
            return

        try:
            assert op.resolved_type is types.GenericBitVector()
            arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        except NoMatchException:
            res = self.newop(
                "@vector_slice_o_i_i_unwrapped_res",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(length),
                op.sourcepos,
                op.varname_hint,
            )
        else:
            res = self.newop(
                "@slice_fixed_bv_i_i",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(length),
                op.sourcepos,
                op.varname_hint,
            )

        return self.newcast(
            res,
            op.resolved_type,
        )

    def optimize_set_slice_i_i_o_i_o(self, op):
        arg0, arg1, arg2, arg3, arg4 = self._args(op)
        start = self._extract_number(arg3)
        _, typ = self._extract_smallfixedbitvector(arg4)
        return self.newop(
            "@vector_update_subrange_o_i_i_o",
            [arg2, MachineIntConstant(start.number + typ.width - 1), start, arg4],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_zeros_i(self, op):
        arg0, = self._args(op)
        arg0 = self._extract_number(arg0)
        if arg0.number > 64:
            return
        resconst = SmallBitVectorConstant("0b" + "0" * arg0.number, types.SmallFixedBitVector(arg0.number))
        res = self.newcast(
            resconst,
            op.resolved_type,
        )
        return res

    def optimize_sail_signed(self, op):
        (arg0,) = self._args(op)
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        return self._make_int64_to_int(
            self.newop(
                "@signed_bv",
                [arg0, MachineIntConstant(typ0.width)],
                types.MachineInt(),
                op.sourcepos,
                op.varname_hint,
            ),
        )

    def optimize_sail_unsigned(self, op):
        (arg0,) = self._args(op)
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        width_as_num = MachineIntConstant(typ0.width)
        if typ0.width < 64:
            # will always fit into a machine signed int
            res = self.newop(
                "@unsigned_bv",
                [arg0, width_as_num],
                types.MachineInt(),
                op.sourcepos,
                op.varname_hint,
            )
            return self._make_int64_to_int(res, op.sourcepos)
        return self.newop(
            "@unsigned_bv_wrapped_res",
            [arg0, width_as_num],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_zero_extend_o_i(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        if arg1.number > 64:
            return
        return self.newcast(
            self.newop(
                "@zero_extend_o_i_unwrapped_res",
                [arg0, arg1],
                types.SmallFixedBitVector(arg1.number),
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    def optimize_zero_extend_o_i_unwrapped_res(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        assert arg1.number <= 64
        try:
            arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        except NoMatchException:
            raise
        if typ0.width == arg1.number:
            res = arg0
        else:
            res = self.newop(
                "@zero_extend_bv_i_i",
                [arg0, MachineIntConstant(typ0.width), arg1],
                types.SmallFixedBitVector(arg1.number),
                op.sourcepos,
                op.varname_hint,
            )
        return self.newcast(
            res,
            op.resolved_type,
        )

    def optimize_sign_extend_o_i(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        if arg1.number > 64:
            return
        return self.newcast(
            self.newop(
                "@sign_extend_o_i_unwrapped_res",
                [arg0, arg1],
                types.SmallFixedBitVector(arg1.number),
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    def optimize_sign_extend_o_i_unwrapped_res(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        assert arg1.number <= 64
        try:
            arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        except NoMatchException:
            raise
        if typ0.width == arg1.number:
            res = arg0
        else:
            res = self.newop(
                "@sign_extend_bv_i_i",
                [arg0, MachineIntConstant(typ0.width), arg1],
                types.SmallFixedBitVector(arg1.number),
                op.sourcepos,
                op.varname_hint,
            )
        return self.newcast(
            res,
            op.resolved_type,
        )

    @symmetric
    def optimize_add_int(self, op, arg0, arg1):
        arg1 = self._extract_machineint(arg1)
        return self.newop(
            "@add_o_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_add_o_i_wrapped_res(self, op):
        arg0, arg1 = self._args(op)
        num0 = num1 = None
        try:
            num1 = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            if num1.number == 0:
                return arg0
            if isinstance(arg0, Operation):
                # (a - b) + b == a
                if (arg0.name == "@sub_i_i_wrapped_res" and
                    self._args(arg0)[1] == num1):
                    return self._make_int64_to_int(self._args(arg0)[0], op.sourcepos)
                if (arg0.name == "@sub_o_i_wrapped_res" and
                    self._args(arg0)[1] == num1):
                    return self._args(arg0)[0]
        arg0 = self._extract_machineint(arg0)
        return self.newop(
            "@add_i_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_sub_int(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_machineint(arg1)
        return self.newop(
            "@sub_o_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_sub_o_i_wrapped_res(self, op):
        arg0, arg1 = self._args(op)
        try:
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            if arg1.number == 0:
                return arg0
        arg0 = self._extract_machineint(arg0)
        return self.newop(
            "@sub_i_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_sub_i_i_wrapped_res(self, op):
        arg0, arg1 = self._args(op)
        try:
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            if arg1.number == 0:
                return self._make_int64_to_int(arg0, op.sourcepos)

    @symmetric
    def optimize_mult_int(self, op, arg0, arg1):
        arg0 = self._extract_number(arg0)
        if arg0.number == 1:
            return arg1
        if arg0.number == 0:
            return IntConstant(0)
        if arg0.number & (arg0.number - 1) == 0:
            # power of two
            exponent = arg0.number.bit_length() - 1
            assert 1 << exponent == arg0.number
            return self.newop(
                "@shl_int_o_i",
                [arg1, MachineIntConstant(exponent)],
                op.resolved_type,
                op.sourcepos,
                op.varname_hint,
            )

    def optimize_ediv_int(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        if arg1.number == 1:
            return arg0
        arg0 = self._extract_number(arg0)
        if arg0.number >= 0 and arg1.number > 0:
            return IntConstant(arg0.number // arg1.number)

    def optimize_get_slice_int_i_o_i(self, op):
        arg0, arg1, arg2 = self._args(op)
        arg0 = self._extract_number(arg0)
        arg2 = self._extract_machineint(arg2)
        length = arg0.number
        if length > 64:
            return
        restyp = types.SmallFixedBitVector(length)
        try:
            arg1 = self._extract_machineint(arg1)
        except NoMatchException:
            res = self.newop(
                "@get_slice_int_i_o_i_unwrapped_res",
                [arg0, arg1, arg2],
                restyp,
                op.sourcepos,
                op.varname_hint,
            )
        else:
            res = self.newop(
                "@get_slice_int_i_i_i",
                [arg0, arg1, arg2],
                restyp,
                op.sourcepos,
                op.varname_hint,
            )

        return self.newcast(
            res,
            op.resolved_type,
        )

    def optimize_add_bits_int(self, op):
        arg0, arg1 = self._args(op)
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self._extract_machineint(arg1)

        return self.newcast(
            self.newop(
                "@add_bits_int_bv_i",
                [arg0, MachineIntConstant(typ0.width), arg1],
                typ0,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    def optimize_sub_bits_int(self, op):
        arg0, arg1 = self._args(op)
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self._extract_machineint(arg1)

        return self.newcast(
            self.newop(
                "@sub_bits_int_bv_i",
                [arg0, MachineIntConstant(typ0.width), arg1],
                typ0,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )


    def optimize_shiftl_o_i(self, op):
        arg0, arg1 = self._args(op)
        try:
            arg1 = self._extract_number(arg1)
            if arg1.number == 0:
                return arg0
        except NoMatchException:
            pass
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        assert arg1.resolved_type is types.MachineInt()

        return self.newcast(
            self.newop(
                "@shiftl_bv_i",
                [arg0, MachineIntConstant(typ0.width), arg1],
                typ0,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    def optimize_shiftr_o_i(self, op):
        arg0, arg1 = self._args(op)
        try:
            arg1 = self._extract_number(arg1)
            if arg1.number == 0:
                return arg0
        except NoMatchException:
            pass
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        assert arg1.resolved_type is types.MachineInt()

        return self.newcast(
            self.newop(
                "@shiftr_bv_i",
                [arg0, MachineIntConstant(typ0.width), arg1],
                typ0,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    def optimize_arith_shiftr_o_i(self, op):
        arg0, arg1 = self._args(op)
        try:
            arg1 = self._extract_number(arg1)
            if arg1.number == 0:
                return arg0
        except NoMatchException:
            pass
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        assert arg1.resolved_type is types.MachineInt()

        return self.newcast(
            self.newop(
                "@arith_shiftr_bv_i",
                [arg0, MachineIntConstant(typ0.width), arg1],
                typ0,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )

    def optimize_length(self, op):
        arg0, = self._args(op)
        res = self.newop(
                "@length_unwrapped_res",
                [arg0],
                types.MachineInt(),
                op.sourcepos,
                op.varname_hint,
        )
        return self._make_int64_to_int(res, op.sourcepos)

    def optimize_length_unwrapped_res(self, op):
        arg0, = self._args(op)
        if isinstance(arg0, Cast):
            arg0arg0, = self._args(arg0)
            realtyp = arg0arg0.resolved_type
            if isinstance(realtyp, (types.SmallFixedBitVector, types.BigFixedBitVector)):
                return MachineIntConstant(realtyp.width)


    def optimize_undefined_bitvector_i(self, op):
        arg0, = self._args(op)
        num = self._extract_number(arg0)
        if num.number > 64:
            return
        return self.newcast(
            SmallBitVectorConstant("0b" + "0" * num.number, types.SmallFixedBitVector(num.number)),
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_sail_truncate_o_i(self, op):
        arg0, arg1 = self._args(op)
        arg0, typ = self._extract_smallfixedbitvector(arg0)
        num = self._extract_number(arg1)
        if typ.width < num.number:
            return
        if typ.width == num.number:
            newop = arg0
        else:
            newop = self.newop(
                "@truncate_bv_i",
                [arg0, num],
                types.SmallFixedBitVector(num.number),
                op.sourcepos,
                op.varname_hint
            )
        return self.newcast(newop, op.resolved_type)


@repeat
def inline(graph, codegen):
    changed = False
    for block in graph.iterblocks():
        index = 0
        while index < len(block.operations):
            op = block[index]
            if isinstance(op, Operation) and op.name in codegen.inlinable_functions:
                subgraph = codegen.inlinable_functions[op.name]
                if isinstance(subgraph.startblock.next, Return) and subgraph.startblock.next.value is not None:
                    newops, res = copy_ops(op, subgraph)
                    newops = [Comment("inlined %s" % subgraph.name)] + newops
                    if newops is not None:
                        block.operations[index : index + 1] = newops
                        graph.replace_op(op, res)
                        index = 0
                        changed = True
                        continue
                elif not subgraph.has_loop:
                    # complicated case
                    # split current block
                    print "inlining", graph.name, subgraph.name
                    newblock = Block()
                    oldops = block.operations[:]
                    newblock.operations = block.operations[index + 1:]
                    del block.operations[index:]
                    block.operations.append(Comment("inlined %s" % subgraph.name))
                    newblock.next = block.next
                    for furtherblock in block.next.next_blocks():
                        furtherblock.replace_prev(block, newblock)
                    start_block, return_block = copy_blocks(subgraph, op)
                    block.next = Goto(start_block)
                    res, = return_block.operations
                    assert return_block.next is None
                    return_block.next = Goto(newblock)
                    graph.replace_op(op, return_block.operations[0])
                    graph.check()
                    simplify_phis(graph)
                    remove_empty_blocks(graph)
                    join_blocks(graph)
                    return True
            index += 1
    return changed

def copy_ops(op, subgraph):
    assert len(list(subgraph.iterblocks())) == 1
    replacements = {arg: argexpr for arg, argexpr in zip(subgraph.args, op.args)}
    ops = subgraph.startblock.copy_operations(replacements)
    res = subgraph.startblock.next.value
    return ops, replacements.get(res, res)

def copy_blocks(graph, op):
    returnphi = Phi([], [], None)
    returnblock = Block([returnphi])
    replacements = {arg: argexpr for arg, argexpr in zip(graph.args, op.args)}
    blocks = {block: Block() for block in graph.iterblocks()}
    todo_next = []
    for block in topo_order(graph):
        ops = block.copy_operations(replacements, blocks)
        newblock = blocks[block]
        newblock.operations = ops
        todo_next.append((block.next, newblock))

    while todo_next:
        next, newblock = todo_next.pop()
        if isinstance(next, Return):
            assert next.value is not None
            returnphi.prevvalues.append(replacements.get(next.value, next.value))
            returnphi.prevblocks.append(newblock)
            returnphi.resolved_type = next.value.resolved_type
            newblock.next = Goto(returnblock)
        elif isinstance(next, Goto):
            newblock.next = Goto(blocks[next.target], next.sourcepos)
        elif isinstance(next, ConditionalGoto):
            newblock.next = ConditionalGoto(
                replacements.get(next.booleanvalue, next.booleanvalue),
                blocks[next.truetarget],
                blocks[next.falsetarget],
                next.sourcepos,
            )
        elif isinstance(next, Raise):
            newblock.next = Raise(next.kind, next.sourcepos)
        else:
            assert 0, "unreachable"

    return blocks[graph.startblock], returnblock

def should_inline(graph):
    if "step_model" in graph.name:
        return False
    if "subrange_subrange" in graph.name:
        return True
    if "slice_mask" in graph.name:
        return True
    if "sail_mask" in graph.name:
        return True
    if "extzzv" in graph.name:
        return True
    if graph.has_loop:
        return False
    blocks = list(graph.iterblocks())
    if any([isinstance(block.next, Return) and block.next.value is None for block in blocks]):
        return False
    for op, _ in graph.iterblockops():
        if isinstance(op, Operation) and op.name == graph.name:
            return False # no recursive inlining
    number_ops = len([op for block in blocks for op in block.operations])
    return len(blocks) < 4 and number_ops < 25
    

def topo_order(graph):
    order = list(graph.iterblocks()) # dfs

    # do a (slighly bad) topological sort
    incoming = defaultdict(set)
    for block in order:
        for nextblock in block.next.next_blocks():
            incoming[nextblock].add(block)
    no_incoming = [order[0]]
    topoorder = []
    while no_incoming:
        block = no_incoming.pop()
        topoorder.append(block)
        for child in set(block.next.next_blocks()):
            incoming[child].discard(block)
            if not incoming[child]:
                no_incoming.append(child)
                del incoming[child]
    # check result
    assert set(topoorder) == set(order)
    assert len(set(topoorder)) == len(topoorder)
    return topoorder
