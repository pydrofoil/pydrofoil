import random
from collections import defaultdict
from pydrofoil import parse, types, binaryop, operations, supportcode
from rpython.tool.udir import udir

from dotviewer.graphpage import GraphPage as BaseGraphPage

# TODOS:
# - casts for structconstruction arguments
# - enum reads as constants
# - remove useless phis
# - remove the typ argument of side-effecting ops
# - BACKEND!
# - empty blocks removal (careful with critical edges)
# - constants
# - start porting optimizations

def construct_ir(functionast, codegen, singleblock=False):
    # bring operations into a block format:
    # a dictionary {label-as-int: [list of operations]}
    # every list of operations ends with a goto, return or failure
    body = functionast.body
    if singleblock:
        body = body + [parse.Arbitrary()]

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
            ssablock = Block([])
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
        simplify(graph)
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
                    ssaop = Operation(op.name, args, op.resolved_type, op.sourcepos)
                self._addop(ssaop)
                self._store(op.result, ssaop)
            elif isinstance(op, parse.Assignment):
                value = self._get_arg(op.value)
                if op.resolved_type != op.value.resolved_type:
                    # we need a cast first
                    value = Cast(value, op.resolved_type, op.sourcepos)
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
                ssablock.next = Arbitrary(op.sourcepos)
            else:
                xxx

    def _get_args(self, args):
        return [self._get_arg(arg) for arg in args]

    def _get_arg(self, parseval):
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
            if parseval.resolved_type is None:
                import pdb; pdb.set_trace()
            assert parseval.resolved_type is None or parseval.fieldnames == parseval.resolved_type.ast.names
            args = self._get_args(parseval.fieldvalues)
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
        else:
            assert isinstance(parseval, (parse.BitVectorConstant, parse.Number, parse.Unit, parse.String))
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
        if self.curr_operations and self.curr_operations[-1] is op:
            import pdb; pdb.set_trace()
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

    def __init__(self, operations):
        assert isinstance(operations, list)
        self.operations = operations
        self.next = None

    def __getitem__(self, index):
        return self.operations[index]

    def replace_prev(self, block, otherblock):
        for op in self.operations:
            if not isinstance(op, Phi):
                return
            for index, oldblock in enumerate(op.prevblocks):
                if oldblock is block:
                    op.prevblocks[index] = otherblock

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
        return entry


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


class Argument(Value):
    def __init__(self, name, resolved_type):
        self.resolved_type = resolved_type
        self.name = name

    def __repr__(self):
        return "Argument(%r)" % (self.name, )

    def _repr(self, print_varnames):
        return self.name

class Operation(Value):
    can_have_side_effects = True

    def __init__(self, name, args, resolved_type, sourcepos=None):
        for arg in args:
            assert isinstance(arg, Value)
        self.name = name
        self.args = args
        self.resolved_type = resolved_type
        self.sourcepos = sourcepos

    def __repr__(self):
        return "Operation(%r, %r, %r)" % (self.name, self.args, self.sourcepos)

    def _repr(self, print_varnames):
        return self._get_print_name(print_varnames)

    def getargs(self):
        return self.args

class Cast(Operation):
    can_have_side_effects = False

    def __init__(self, arg, resolved_type, sourcepos):
        Operation.__init__(self, "$cast", [arg], resolved_type, sourcepos)

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

    def __init__(self, args, resolved_type, sourcepos):
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

class Constant(Value):
    pass

class AstConstant(Constant):
    def __init__(self, ast, resolved_type):
        self.ast = ast
        self.resolved_type = resolved_type

    def _repr(self, print_varnames):
        return "(%s)" % (self.ast, )

class BooleanConstant(Constant):
    def __init__(self, value):
        assert isinstance(value, bool)
        self.value = value
        self.resolved_type = types.Bool()

    def _repr(self, print_varnames):
        return "(%s)" % (str(self.value).lower(), )


BooleanConstant.TRUE = BooleanConstant(True)
BooleanConstant.FALSE = BooleanConstant(False)

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

    def _repr(self, print_varnames):
        return self.__class__.__name__

class Return(Next):
    def __init__(self, value, sourcepos):
        assert isinstance(value, Value) or value is None
        self.value = value
        self.sourcepos = sourcepos

    def getargs(self):
        return [self.value]

    def _repr(self, print_varnames):
        return "return %s" % ('None' if self.value is None else self.value._repr(print_varnames), )

class Raise(Next):
    def __init__(self, kind, sourcepos):
        self.kind = kind
        self.sourcepos = sourcepos

    def _repr(self, print_varnames):
        return "raise (%s)" % (self.kind, )

class Arbitrary(Next):
    def _repr(self, print_varnames):
        return "Arbitrary()"


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

    def _repr(self, print_varnames):
        return "goto if %s" % (self.booleanvalue._repr(print_varnames), )


class GraphPage(BaseGraphPage):
    save_tmp_file = str(udir.join('graph.dot'))

    def compute(self, source, varnames, args):
        self.source = source
        self.links = {var: str(op.resolved_type) for op, var in varnames.items()}
        for arg in args:
            self.links[arg.name] = str(arg.resolved_type)


# some simple graph simplifications

def simplify(graph):
    res = remove_dead(graph)
    #res = remove_empty_blocks(graph) or res
    #res = swap_not(graph) or res
    return res

def repeat(func):
    def repeated(graph):
        ever_changed = False
        while 1:
            changed = func(graph)
            assert isinstance(changed, bool)
            if not changed:
                return ever_changed
            ever_changed = True
    return repeated

@repeat
def remove_dead(graph):
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
        operations = [op for op in block.operations if op in needed or op.can_have_side_effects]
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
            block.next.replace_next(nextblock, nextblock.next.target)
            nextblock.next.target.replace_prev(nextblock, block)
            changed = True
    return changed

def swap_not(graph):
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
        remove_dead(graph)
    return changed
