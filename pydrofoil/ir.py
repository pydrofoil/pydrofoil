import random
from collections import defaultdict
from pydrofoil import parse, types, binaryop, operations, supportcode
from rpython.tool.udir import udir

from dotviewer.graphpage import GraphPage as BaseGraphPage

# TODOS:
# - enum reads as constants
# - remove useless phis
# - remove the typ argument of side-effecting ops
# - vector_update_inplace

# - empty blocks removal (careful with critical edges)
# - constants
# - split huge functions
# - start porting optimizations
#   - inlining
#   - nesting ifs
#   - nested operations
#   - cached boxed constants
#   - neq -> not eq
#   - all the bitvector and integer optimizations

# @neq(X, Y) -> @not(@eq(X, Y))
# eq_bits(cast(Op1, gbv), cast(Op2, gbv)) -> eq_bits_bv_bv(Op1, Op2, 

# start optimization: outriscv.py is 247000 loc
# 135 kloc


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
    def __init__(self, blocks, functionast, functionargs, codegen):
        self.blocks = blocks
        self.functionast = functionast
        self.functionargs = functionargs
        self.codegen = codegen
        self.entryblocks = compute_entryblocks(blocks)
        self.variable_map = None # {name: Value}
        self.variable_maps_at_end = {} # {pc: variable_map}
        self.patch_phis = defaultdict(list)
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
        graph = Graph(self.functionast.name, self.args, self.allblocks[0])
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
        if entry == []:
            assert pc == 0
            self.variable_map = {}
            self.args = []
            if self.functionargs:
                argtypes = self.functionast.resolved_type.argtype.elements
                self.variable_map = {var: Argument(var, typ)
                        for var, typ in zip(self.functionargs, argtypes)}
                self.args = [self.variable_map[var] for var in self.functionargs]
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
                assert op.value is None
                if isinstance(op.resolved_type, types.Struct):
                    ssaop = Allocate(op.resolved_type, op.sourcepos)
                else:
                    ssaop = DefaultValue(op.resolved_type, op.sourcepos)
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
                field, = op.fields
                obj = self._get_arg(op.obj)
                fieldval = self._get_arg(op.value)
                typ = obj.resolved_type.fieldtyps[field]
                if fieldval.resolved_type != typ:
                    fieldval = self._addop(Cast(fieldval, typ, op.sourcepos))
                self._addop(FieldWrite(field, [obj, fieldval], types.Unit(), op.sourcepos))
            elif isinstance(op, parse.GeneralAssignment):
                if isinstance(op.lhs, parse.RefAssignment):
                    args = self._get_args(op.rhs.args)
                    rhs = Operation(op.rhs.name, args, op.rhs.resolved_type, op.sourcepos)
                    self._addop(rhs)
                    self._addop(RefAssignment([self._get_arg(op.lhs.ref), rhs], types.Unit(), op.sourcepos))
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
                #if isinstance(value, BooleanConstant):
                #    if "encdec" not in self.functionast.name and "execute" not in self.functionast.name:
                #        import pdb; pdb.set_trace()
                #    ssablock.next = Goto(self.allblocks[
                #        op.target if value is BooleanConstant.TRUE else nextop.target
                #    ], None)
                #    break
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
                res = self._addop(DefaultValue(restyp, op.sourcepos))
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

def build_ssa(blocks, functionast, functionargs, codegen):
    builder = SSABuilder(blocks, functionast, functionargs, codegen)
    return builder.build()


# graph

class Block(object):
    _pc = -1 # assigned later in emitfunction

    def __init__(self, operations=None):
        if operations is None:
            operations = []
        assert isinstance(operations, list)
        self.operations = operations
        self.next = None

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
    def __init__(self, name, args, startblock):
        self.name = name
        self.args = args
        self.startblock = startblock

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
            for op in block:
                for value in op.getargs():
                    assert value in defined_vars or isinstance(value, Constant)
            for value in block.next.getargs():
                assert value in defined_vars or isinstance(value, Constant)

    def replace_op(self, oldop, newop):
        for block in self.iterblocks():
            for op in block.operations:
                assert op is not oldop # must have been removed already
                op.replace_op(oldop, newop)
            block.next.replace_op(oldop, newop)

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
        self.sourcepos = sourcepos
        self.varname_hint = varname_hint

    def __repr__(self):
        return "Operation(%r, %r, %r)" % (self.name, self.args, self.sourcepos)

    def _repr(self, print_varnames):
        return self._get_print_name(print_varnames)

    def getargs(self):
        return self.args

    def replace_op(self, oldop, newop):
        assert self is not oldop
        for index, arg in enumerate(self.args):
            if arg is oldop:
                self.args[index] = newop

class Cast(Operation):
    can_have_side_effects = False

    def __init__(self, arg, resolved_type, sourcepos=None, varname_hint=None):
        Operation.__init__(self, "$cast", [arg], resolved_type, sourcepos, varname_hint)

    def __repr__(self):
        return "Cast(%r, %r, %r)" % (self.args[0], self.resolved_type, self.sourcepos)

class DefaultValue(Operation):
    can_have_side_effects = False

    def __init__(self, resolved_type, sourcepos):
        Operation.__init__(self, "$default", [], resolved_type, sourcepos)

    def __repr__(self):
        return "DefaultValue(%r, %r)" % (self.resolved_type, self.sourcepos, )

class Allocate(Operation):
    can_have_side_effects = False

    def __init__(self, resolved_type, sourcepos):
        Operation.__init__(self, "$allocate", [], resolved_type, sourcepos)

    def __repr__(self):
        return "Allocate(%r, %r)" % (self.resolved_type, self.sourcepos, )

class StructConstruction(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "StructConstruction(%r, %r, %r)" % (self.name, self.args)

class FieldAccess(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "FieldAccess(%r, %r, %r)" % (self.name, self.args)

class FieldWrite(Operation):
    def __repr__(self):
        return "FieldWrite(%r, %r, %r)" % (self.name, self.args)

class UnionVariantCheck(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "UnionVariantCheck(%r, %r, %r)" % (self.name, self.args)

class UnionCast(Operation):
    def __repr__(self):
        return "UnionCast(%r, %r, %r)" % (self.name, self.args)

class GlobalRead(Operation):
    can_have_side_effects = False
    def __init__(self, name, resolved_type):
        Operation.__init__(self, name, [], resolved_type, None)

    def __repr__(self):
        return "GlobalRead(%r, %r)" % (self.name, self.resolved_type)

class GlobalWrite(Operation):
    def __repr__(self):
        return "GlobalWrite(%r, %r, %r)" % (self.name, self.args)

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

    def replace_op(self, oldop, newop):
        assert self is not oldop
        for index, op in enumerate(self.prevvalues):
            if op is oldop:
                self.prevvalues[index] = newop

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

BooleanConstant.TRUE = BooleanConstant(True)
BooleanConstant.FALSE = BooleanConstant(False)


class MachineIntConstant(Constant):
    resolved_type = types.MachineInt()
    def __init__(self, number):
        self.number = number

    def _repr(self, print_varnames):
        return repr(self)

    def __repr__(self):
        return "MachineIntConstant(%r)" % (self.number, )


class SmallBitVectorConstant(Constant):
    def __init__(self, value, resolved_type):
        self.value = value
        self.resolved_type = resolved_type

    def _repr(self, print_varnames):
        return repr(self)

    def __repr__(self):
        return "SmallBitVectorConstant(%s, %s)" % (self.value, self.resolved_type)


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

    def replace_op(self, oldop, newop):
        pass

    def _repr(self, print_varnames):
        return self.__class__.__name__

class Return(Next):
    def __init__(self, value, sourcepos=None):
        assert isinstance(value, Value) or value is None
        self.value = value
        self.sourcepos = sourcepos

    def getargs(self):
        return [self.value] if self.value is not None else []

    def replace_op(self, oldop, newop):
        if self.value is oldop:
            self.value = newop

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

    def replace_op(self, oldop, newop):
        if self.booleanvalue is oldop:
            self.booleanvalue = newop

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
    # XXX print arguments
    for block, name in blocknames.iteritems():
        res.append("%s = Block()" % name)
    for block, blockname in blocknames.iteritems():
        for op in block.operations:
            name = op._get_print_name(print_varnames)
            if isinstance(op, Operation):
                args = ", ".join([a._repr(print_varnames) for a in op.args])
                res.append("%s = %s.emit(%s, %r, [%s], %r, %r, %r)"  % (name, blockname, op.__class__.__name__, op.name, args, op.resolved_type, op.sourcepos, op.varname_hint))
            else:
                assert isinstance(op, Phi)
                blockargs = ", ".join([blocknames[b] for b in op.prevblocks])
                args = ", ".join([a._repr(print_varnames) for a in op.prevvalues])
                res.append("%s = %s.emit_phi([%s], [%s], %s)" % (name, blockname, blockargs, args, op.resolved_type))
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

@repeat
def simplify(graph, codegen):
    res = LocalOptimizer(graph, codegen).optimize()
    res = remove_if_true_false(graph) or res
    res = remove_dead(graph, codegen) or res
    res = remove_empty_blocks(graph) or res
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
            for phi, newop in replace_phis.iteritems():
                graph.replace_op(phi, newop)
    return changed

class NoMatchException(Exception):
    pass

def symmetric(func):
    def optimize(self, op):
        arg0, arg1 = op.args
        try:
            res = func(self, op, arg0, arg1)
        except NoMatchException:
            pass
        else:
            if res is not None:
                return res
        return func(self, op, arg1, arg0)
    return optimize


class LocalOptimizer(object):
    def __init__(self, graph, codegen):
        self.graph = graph
        self.codegen = codegen

    def optimize(self):
        self.replacements = {}
        for block in self.graph.iterblocks():
            self.optimize_block(block)
        if self.replacements:
            # XXX do them all in one go
            for oldop, newop in self.replacements.iteritems():
                self.graph.replace_op(oldop, newop)
            return True
        return False

    def optimize_block(self, block):
        self.newoperations = []
        for i, op in enumerate(block.operations):
            newop = self._optimize_op(block, i, op)
            if newop is not None:
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

    def _convert_to_machineint(self, arg):
        try:
            return self._extract_machineint(arg)
        except NoMatchException:
            # call int_to_int64
            return self.newop("zz5izDzKz5i64", [arg], types.MachineInt())

    def _args(self, op):
        return [self.replacements.get(value, value) for value in op.args]

    def _optimize_op(self, block, index, op):
        if isinstance(op, Cast):
            arg, = self._args(op)
            if isinstance(arg, Cast):
                arg2, = self._args(arg)
                if arg2.resolved_type is op.resolved_type:
                    block.operations[index] = None
                    return arg2
                return self.newcast(arg2, op.resolved_type, op.sourcepos, op.varname_hint)
        elif type(op) is Operation:
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
        self.newoperations.append(op)

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
        if (
            not isinstance(arg, Operation)
            or self._builtinname(arg.name) != "int64_to_int"
        ):
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

    def optimize_int64_to_int(self, op):
        (arg0,) = self._args(op)
        if (
            not isinstance(arg0, Operation)
            or self._builtinname(arg0.name) != "int_to_int64"
        ):
            return
        return arg0.args[0]

    def optimize_int_to_int64(self, op):
        (arg0,) = self._args(op)
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

