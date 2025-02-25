import sys
import random
import time
from collections import defaultdict

from pydrofoil import parse, types, binaryop, operations, supportcode, bitvector

from rpython.tool.udir import udir
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck

from dotviewer.graphpage import GraphPage as BaseGraphPage


# TODOS:
# - lt etc one arg machine int

# risc-v:
# vector_subrange_o_i_i with smallbv argument and unknown bounds (hard). idea:
# check whether difference between index args is computable

# read_kind_of_flags has weird diamond patterns, needs dominance

# deal with exceptional paths better in the context of inlining (and specialization)
# zAArch64_SystemAccessTrap_specialized_o_7 is an example

# get rid of do_double_casts again

# make anticipated casts deal with phi renaming?

# emod(x, 1) == 0?

# concat(concat(x, const1), const2) -> concat(x, const1+const2)
# example:
    # i198 = block110.emit(Operation, 'zget_16_random_bits', [UnitConstant.UNIT], SmallFixedBitVector(16), '`12 827:24-827:44', 'zz42')
    # i199 = block110.emit(Operation, '@bitvector_concat_bv_bv', [SmallBitVectorConstant(0x0, SmallFixedBitVector(8)), MachineIntConstant(16), i198], SmallFixedBitVector(24), '`12 828:48-828:66', 'zz417')
    # i200 = block110.emit(Operation, '@bitvector_concat_bv_bv', [SmallBitVectorConstant(0, SmallFixedBitVector(6)), MachineIntConstant(24), i199], SmallFixedBitVector(30), '`12 828:32-828:66', 'zz414')
    # i201 = block110.emit(Operation, '@bitvector_concat_bv_bv', [SmallBitVectorConstant(0b10, SmallFixedBitVector(2)), MachineIntConstant(30), i200], SmallFixedBitVector(32), '`12 828:14-828:66', 'zz410')

# vector_update_subrange_o_i_i_o with subrange width == 1 can be turned in vector_update_o_i_o

# combine several steps of phi nodes

# filter out units from more places

# ExceptionClass shows the weird phi duplication bug

# maybe turn Operations into "OperationWithExceptionalReturn" to get rid of the
# useless control flow

# need a solution for the whole "add(sub(a, const1), const1)" with the various
# variants of addition and subtraction

# start functions with a check that have_exception is not set?


# cleanups needed
# ----------------
# is there still a tuple type?
# make phi nodes point to merge blocks, and the merge blocks have prevblocks
# make the ir construction introduce the correct supportcode names immediately


# ideas for speedups
# ---------------------
# - iterblocks and topo_order_best_attempt are most costly functions
# - _optimize_Operation, cse, replace_ops, set.union

# big tasks
# ------------
#
# - more global static analysis
# - scheduling


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


def compute_entryblocks_nextblocks(blocks):
    entryblocks = defaultdict(list)
    nextblocks = defaultdict(set)
    for pc, block in blocks.iteritems():
        for op in block:
            if isinstance(op, (parse.Goto, parse.ConditionalJump)):
                entryblocks[op.target].append(pc)
                nextblocks[pc].add(op.target)
    return entryblocks, nextblocks

class SSABuilder(object):
    def __init__(self, blocks, functionast, functionargs, codegen, startpc=0, extra_args=None):
        self.blocks = blocks
        self.functionast = functionast
        self.functionargs = functionargs
        self.codegen = codegen
        self.entryblocks, self.nextblocks = compute_entryblocks_nextblocks(blocks)
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
        #mutated_struct_types = compute_mutations_of_non_copied_structs(graph)
        graph.check()
        insert_struct_copies_for_arguments(graph, self.codegen)
        convert_sail_assert_to_exception(graph, self.codegen)
        light_simplify(graph, self.codegen)
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
            if isinstance(self.functionast.resolved_type, types.Function):
                self.variable_map['return'] = DefaultValue(self.functionast.resolved_type.restype)
            else:
                self.variable_map['return'] = None

        elif len(entry) == 1:
            variable_map = self.variable_maps_at_end[entry[0]]
            if len(self.nextblocks[entry[0]]) > 1:
                variable_map = variable_map.copy()
            self.variable_map = variable_map
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
                    if value0.resolved_type is types.Unit():
                        self.variable_map[var] = UnitConstant.UNIT
                        continue
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
                if value.resolved_type is types.Unit():
                    self.variable_map[var] = UnitConstant.UNIT
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
        if not self.has_loop:
            for prevpc in entry:
                nextblocks_of_prevpc = self.nextblocks[prevpc]
                nextblocks_of_prevpc.remove(pc)
                if not nextblocks_of_prevpc:
                    # don't keep all the variable maps alive, they are huge
                    del self.variable_maps_at_end[prevpc]

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
                ssaop = self._addop(ssaop)
                self._store(op.result, ssaop)
            elif isinstance(op, parse.Assignment):
                value = self._get_arg(op.value, op.result)
                if isinstance(op.resolved_type, types.Struct) and not op.resolved_type.tuplestruct:
                    value = StructCopy(op.resolved_type.name, value, op.resolved_type, op.sourcepos)
                    self._addop(value)
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
                    typ = typ.internalfieldtyps[field]
                    if isinstance(typ, types.Packed):
                        import pdb;pdb.set_trace()
                    obj = self._addop(FieldAccess(field, [obj], typ))

                fieldval = self._get_arg(op.value)
                typ = typ.internalfieldtyps[lastfield]
                if isinstance(typ, types.Packed):
                    if typ.typ != fieldval.resolved_type:
                        if typ.typ is types.GenericBitVector() or isinstance(typ.typ, types.BigFixedBitVector):
                            fieldval = self._addop(Cast(fieldval, typ.typ))
                        else:
                            import pdb;pdb.set_trace()
                    fieldval = self._addop(PackPackedField(fieldval))
                    assert fieldval.resolved_type == typ
                elif fieldval.resolved_type != typ:
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
                        typ = typ.internalfieldtyps[field]
                        assert not isinstance(typ, types.Packed)
                        obj = self._addop(FieldAccess(field, [obj], typ))
                    typ = typ.internalfieldtyps[lastfield]
                    if isinstance(typ, types.Packed):
                        if typ.typ != rhs.resolved_type:
                            import pdb;pdb.set_trace()
                        rhs = self._addop(PackPackedField(rhs))
                    elif rhs.resolved_type != typ:
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
                ssablock.next = Raise(StringConstant(op.kind), op.sourcepos)
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
            if parseval.name == 'bitzero':
                return SmallBitVectorConstant(0, types.Bit())
            elif parseval.name == 'bitone':
                return SmallBitVectorConstant(1, types.Bit())
            if parseval.name in self.codegen.let_values:
                res = self.codegen.let_values[parseval.name]
                if isinstance(res, StructConstruction):
                    args = []
                    for arg in res.args:
                        if isinstance(arg, Constant):
                            args.append(arg)
                        elif isinstance(arg, Cast) and isinstance(arg.args[0], Constant):
                            args.append(self._addop(Cast(arg.args[0], arg.resolved_type)))
                        elif isinstance(arg, Operation) and arg.name == INT_TO_INT64_NAME and isinstance(arg.args[0], Constant):
                            args.append(self._addop(Operation(INT_TO_INT64_NAME, [arg.args[0]], arg.resolved_type)))
                        else:
                            assert 0, "not implemented so far"
                    res = self._addop(StructConstruction(res.name, args, res.resolved_type, res.sourcepos))
                return res
            if isinstance(parseval.resolved_type, types.Enum):
                if parseval.name in parseval.resolved_type.elements:
                    return EnumConstant(parseval.name, parseval.resolved_type)
            register_read = GlobalRead(parseval.name, parseval.resolved_type)
            self._addop(register_read)
            return register_read
        elif isinstance(parseval, parse.StructConstruction):
            assert parseval.fieldnames == list(parseval.resolved_type.names)
            args = self._get_args(parseval.fieldvalues)
            for index, fieldname in enumerate(parseval.fieldnames):
                arg = args[index]
                targettyp = parseval.resolved_type.internalfieldtyps[fieldname]
                if arg.resolved_type != targettyp:
                    if targettyp is types.MachineInt():
                        assert arg.resolved_type == types.Int()
                        castop = Operation(INT_TO_INT64_NAME, [arg], types.MachineInt())
                    elif targettyp is types.Int():
                        assert arg.resolved_type == types.MachineInt()
                        castop = Operation(INT64_TO_INT_NAME, [arg], targettyp)
                    elif isinstance(targettyp, types.Packed):
                        if targettyp.typ is not arg.resolved_type:
                            if targettyp.typ is types.Int():
                                assert arg.resolved_type == types.MachineInt()
                                arg = self._addop(Operation(INT64_TO_INT_NAME, [arg], targettyp.typ))
                            else:
                                assert targettyp.typ is types.GenericBitVector()
                                arg = self._addop(Cast(arg, targettyp.typ))
                        castop = PackPackedField(arg)
                    else:
                        castop = Cast(arg, targettyp)
                    args[index] = self._addop(castop)
            ssaop = StructConstruction(parseval.name, args, parseval.resolved_type)
            self._addop(ssaop)
            return ssaop
        elif isinstance(parseval, parse.FieldAccess):
            # this optimization is necessary, annoyingly enough
            if isinstance(parseval.obj, parse.StructConstruction):
                index = parseval.obj.fieldnames.index(parseval.element)
                return self._get_arg(parseval.obj.fieldvalues[index])
            arg = self._get_arg(parseval.obj)
            internalfieldtyp = arg.resolved_type.internalfieldtyps[parseval.element]
            ssaop = FieldAccess(parseval.element, [arg], internalfieldtyp)
            self._addop(ssaop)
            if isinstance(internalfieldtyp, types.Packed):
                ssaop = self._addop(UnpackPackedField(ssaop))
            return ssaop
        elif isinstance(parseval, parse.Cast):
            arg = self._get_arg(parseval.expr)
            ssaop = UnionCast(parseval.variant, [arg], parseval.resolved_type)
            return self._addop(ssaop)
        elif isinstance(parseval, parse.RefOf):
            arg = self._get_arg(parseval.expr)
            assert isinstance(arg, GlobalRead)
            assert arg.name in self.codegen.all_registers
            return self._addop(RefOf(arg.name, parseval.resolved_type))
        elif isinstance(parseval, parse.Number):
            return MachineIntConstant(parseval.number)
        elif isinstance(parseval, parse.BitVectorConstant):
            return SmallBitVectorConstant(r_uint(eval(parseval.constant)), parseval.resolved_type)
        elif isinstance(parseval, parse.String):
            return StringConstant(eval(parseval.string))
        else:
            assert isinstance(parseval, parse.Unit)
            return UnitConstant.UNIT

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
        if op.resolved_type is types.Unit():
            return UnitConstant.UNIT
        return op

    def _store(self, result, value):
        if result not in self.variable_map and result != 'return' or result == 'current_exception':
            self._addop(GlobalWrite(result, [value], value.resolved_type))
        else:
            self.variable_map[result] = value

def insert_struct_copies_for_arguments(graph, codegen):
    copy_needed = set()
    for arg in graph.args:
        if isinstance(arg.resolved_type, types.Struct) and not arg.resolved_type.tuplestruct:
            copy_needed.add(arg)
    if not copy_needed:
        return
    mutated_struct_types = compute_mutations_of_non_copied_structs(graph)
    copied_args = [arg for arg in graph.args
                   if arg in copy_needed and
                       arg.resolved_type in mutated_struct_types]
    if not copied_args:
        return
    ops = []
    replacements = {}
    for arg in copied_args:
        op = StructCopy(arg.resolved_type.name, arg, arg.resolved_type)
        ops.append(op)
        replacements[arg] = op
    graph.replace_ops(replacements)
    graph.startblock = Block(ops, Goto(graph.startblock))
    res = light_simplify(graph, codegen)
    if res:
        partial_allocation_removal(graph, codegen)

def compute_mutations_of_non_copied_structs(graph):
    # very rough over-approximation
    result = set()
    for block in graph.iterblocks():
        for op in block.operations:
            if not isinstance(op, FieldWrite):
                continue
            if isinstance(op.args[0], (StructCopy, Allocate)):
                continue
            result.add(op.args[0].resolved_type)
    return result


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
    if not isinstance(value, (StructConstruction, Constant)):
        return
    return value


INT_TO_INT64_NAME = "zz5izDzKz5i64"
INT64_TO_INT_NAME = "zz5i64zDzKz5i"

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

    def emit(self, cls, opname, args, resolved_type, sourcepos=None, varname_hint=None):
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
                continue
            #assert otherblock not in op.prevblocks
            for index, oldblock in enumerate(op.prevblocks):
                if oldblock is block:
                    op.prevblocks[index] = otherblock
            assert len(op.prevblocks) == len(set(op.prevblocks))

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

    def next_blocks(self):
        return self.next.next_blocks()

    def copy_operations(self, replacements, block_replacements=None, patch_phis=None):
        def replace(arg, is_phi=False):
            if isinstance(arg, Constant):
                return arg
            if is_phi and arg not in replacements:
                return None
            return replacements[arg]
        res = []
        for op in self.operations:
            if isinstance(op, NonSSAAssignment):
                continue
            elif isinstance(op, Phi):
                newop = Phi(
                    [block_replacements[block] for block in op.prevblocks],
                    [replace(arg, is_phi=True) for arg in op.prevvalues],
                    op.resolved_type)
                for index, (newarg, arg) in enumerate(zip(newop.prevvalues, op.prevvalues)):
                    if newarg is None:
                        patch_phis.append((newop, index, arg))
            else:
                newop = Operation(op.name, [replace(arg) for arg in op.args], op.resolved_type, op.sourcepos, op.varname_hint)
                newop.__class__ = op.__class__
            replacements[op] = newop
            res.append(newop)
        return res

    def _dot(self, dotgen, seen, print_varnames, codegen, backedges):
        if codegen is None:
            builtin_names = {}
        else:
            builtin_names = codegen.builtin_names
        if self in seen:
            return str(id(self))
        seen.add(self)
        res = []
        for index, op in enumerate(self.operations):
            if op is None:
                res.append('None')
                continue
            name = op._get_print_name(print_varnames) if op is not None else 'None'
            if isinstance(op, Operation):
                oprepr = "%s(%s) [%s]" % (
                    builtin_names.get(op.name, op.name),
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
            nextid = nextblock._dot(dotgen, seen, print_varnames, codegen, backedges)
            label = ''
            if len(nextblocks) > 1:
                label = str(bool(index))
            if (self, nextblock) in backedges:
                color = "blue"
            else:
                color = "black"
            dotgen.emit_edge(str(id(self)), nextid, label=label, color=color)
        return str(id(self))

    def split(self, index, keep_op):
        startindex = index
        if not keep_op:
            startindex += 1
        newblock = Block()
        newblock.operations = self.operations[startindex:]
        for op in newblock.operations:
            assert not isinstance(op, Phi)
        del self.operations[index:]
        newblock.next = self.next
        for furtherblock in self.next.next_blocks():
            furtherblock.replace_prev(self, newblock)
        self.next = Goto(newblock)
        return newblock

class Graph(object):
    def __init__(self, name, args, startblock, has_loop=False):
        self.name = name
        self.args = args
        self.startblock = startblock
        self.has_loop = has_loop

    def __repr__(self):
        return "<Graph %s %s>" % (self.name, self.args)

    def __getitem__(self, node): # compatibility with the networkx algos
        assert isinstance(node, Block)
        return node.next.next_blocks()

    def view(self, codegen=None, maxblocks=None):
        from rpython.translator.tool.make_dot import DotGen
        from dotviewer import graphclient
        import pytest
        import os
        dotgen = DotGen('G')
        print_varnames = self._dot(dotgen, codegen, maxblocks)
        if self.has_more_than_n_blocks(200) and maxblocks is None:
            p = pytest.ensuretemp("pyparser").join("temp.dot")
            p.write(dotgen.generate(target=None))
            p2 = p.new(ext=".plain")
            # twopi is a mess and the wrong tool, but it *will* show you really
            # huge graphs quickly and not crash
            os.system("twopi -Tplain %s > %s" % (p, p2))
            graphclient.display_dot_file(str(p2))
        else:
            GraphPage(dotgen.generate(target=None), print_varnames, self.args).display()

    def _dot(self, dotgen, codegen, maxblocks):
        name = "graph" + self.name
        dotgen.emit_node(
            name,
            shape="box",
            fillcolor="green",
            label="\\l".join([self.name, "[" + ", ".join([a.name for a in self.args]) + "]"])
        )
        seen = set()
        print_varnames = {}
        if self.has_loop:
            backedges = set(find_backedges(self))
        else:
            backedges = set()
        if maxblocks is not None:
            seen = set(self.iterblocks())
            blocks = list(self.iterblocks_breadth_first())[:maxblocks]
            for block in blocks:
                seen.remove(block)
        firstid = self.startblock._dot(dotgen, seen, print_varnames, codegen, backedges)
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

    def has_more_than_n_blocks(self, maxblocks):
        count = 0
        for _ in self.iterblocks():
            count += 1
            if count > maxblocks:
                return True
        return False

    def iteredges(self):
        todo = [self.startblock]
        seen = set()
        while todo:
            block = todo.pop()
            if block in seen:
                continue
            seen.add(block)
            for next in block.next.next_blocks():
                yield block, next
                if next not in seen:
                    todo.append(next)

    def __iter__(self):
        return self.iterblocks()

    def iterblockops(self):
        for block in self.iterblocks():
            for op in block.operations:
                yield op, block

    def iterblocks_breadth_first(self, start=None):
        from collections import deque
        if start is None:
            start = self.startblock
        todo = deque([start])
        seen = set()
        res = []
        while todo:
            block = todo.popleft()
            if block in seen:
                continue
            seen.add(block)
            todo.extend(block.next.next_blocks())
            res.append(block)
        return res

    def make_entrymap(self):
        todo = [self.startblock]
        seen = set()
        entry = defaultdict(list)
        while todo:
            block = todo.pop()
            seen.add(block)
            for next in block.next.next_blocks():
                entry[next].append(block)
                if next not in seen:
                    todo.append(next)
        entry[self.startblock] = []
        return entry

    def idoms_and_entrymap(self, startblock=None):
        from pydrofoil import graphalgorithms
        startblock = self.startblock
        entrymap = self.make_entrymap()
        return graphalgorithms.immediate_dominators(self, startblock, entrymap), entrymap

    def immediate_dominators(self):
        return self.idoms_and_entrymap()[0]

    def check(self):
        # minimal consistency check, will add things later
        idom, entrymap = self.idoms_and_entrymap()
        defined_vars_per_block = {} # block -> set of values
        # first compute vars defined directly in all blocks
        #all_phi_prevblocks_ids = {}
        for block, entry in entrymap.iteritems():
            defined_vars = defined_vars_per_block[block] = set()
            if block is self.startblock:
                defined_vars.update(self.args)
            for op in block:
                defined_vars.add(op)
                if not isinstance(op, Phi):
                    continue
                #pid = id(op.prevblocks)
                #assert pid not in all_phi_prevblocks_ids
                #all_phi_prevblocks_ids[pid] = op
                for prevblock in op.prevblocks:
                    assert prevblock in entrymap
                    assert prevblock in entry
                assert len({val.resolved_type for val in op.prevvalues}) == 1
        # check that all the used values are defined somewhere
        for block in entrymap:
            defined_vars = defined_vars_per_block[block]
            if block is not self.startblock:
                defined_vars.update(defined_vars_per_block[idom[block]])
        for block in entrymap:
            defined_vars = defined_vars_per_block[block]
            assert len(set(block.operations)) == len(block.operations)
            for op in block:
                if isinstance(op, Phi):
                    for prevvalue, prevblock in zip(op.prevvalues, op.prevblocks):
                        assert isinstance(prevvalue, Constant) or prevvalue in defined_vars_per_block[prevblock]
                else:
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
    def is_union_creation(self):
        return False

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

    def comparison_key(self):
        return self

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
        return "%s(%r, %r, %r, %r)" % (self.__class__.__name__, self.name, self.args, self.resolved_type, self.sourcepos)

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

    def is_union_creation(self):
        return isinstance(self.resolved_type, types.Union) and type(self) is Operation and self.name in self.resolved_type.variants


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

class StructCopy(Operation):
    can_have_side_effects = False

    def __init__(self, name, arg, resolved_type, sourcepos=None):
        Operation.__init__(self, name, [arg], resolved_type, sourcepos)

    def __repr__(self):
        return "StructCopy(%r, %r, %r, %r)" % (self.name, self.args[0], self.resolved_type, self.sourcepos)

class FieldAccess(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "%s(%r, %r, %r)" % (self.__class__.__name__, self.name, self.args, self.resolved_type)

class FieldWrite(Operation):
    def __init__(self, name, args, resolved_type=None, sourcepos=None, varname_hint=None):
        if resolved_type is None:
            resolved_type = types.Unit()
        Operation.__init__(self, name, args, resolved_type, sourcepos, varname_hint)

    def __repr__(self):
        return "%s(%r, %r)" % (self.__class__.__name__, self.name, self.args)

class UnionVariantCheck(Operation):
    can_have_side_effects = False

    def __repr__(self):
        return "UnionVariantCheck(%r, %r, %r)" % (self.name, self.args, self.resolved_type)

class UnionCast(Operation):
    can_have_side_effects = False
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

    def __init__(self, name, resolved_type, sourcepos=None):
        Operation.__init__(self, name, [], resolved_type, sourcepos)

    def __repr__(self):
        return "RefOf(%r, %r, %r)" % (self.name, self.resolved_type, self.sourcepos, )

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


class UnpackPackedField(Operation):
    can_have_side_effects = False

    def __init__(self, arg, sourcepos=None):
        assert isinstance(arg.resolved_type, types.Packed)
        Operation.__init__(self, "$unpack", [arg], arg.resolved_type.typ, sourcepos)

    def __repr__(self):
        return "UnpackPackedField(%s)" % self.args[0]


class PackPackedField(Operation):
    can_have_side_effects = False

    def __init__(self, arg, sourcepos=None):
        assert isinstance(arg.resolved_type, (types.Int, types.GenericBitVector, types.BigFixedBitVector))
        Operation.__init__(self, "$pack", [arg], types.Packed(arg.resolved_type), sourcepos)

    def __repr__(self):
        return "PackPackedField(%s)" % self.args[0]


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

    def comparison_key(self):
        return (MachineIntConstant, self.number, self.resolved_type)

    def __repr__(self):
        return "MachineIntConstant(%r)" % (self.number, )


class IntConstant(Constant):
    resolved_type = types.Int()
    def __init__(self, number):
        self.number = number

    def _repr(self, print_varnames):
        return repr(self)

    def comparison_key(self):
        return (IntConstant, self.number, self.resolved_type)

    def __repr__(self):
        return "IntConstant(%r)" % (self.number, )


class SmallBitVectorConstant(Constant):
    def __init__(self, value, resolved_type):
        if isinstance(value, int):
            value = r_uint(value)
        assert isinstance(value, r_uint)
        assert isinstance(resolved_type, types.SmallFixedBitVector)
        self.value = value
        self.resolved_type = resolved_type

    @staticmethod
    def from_ruint(size, val):
        return SmallBitVectorConstant(val, types.SmallFixedBitVector(size))

    def comparison_key(self):
        return (SmallBitVectorConstant, self.value, self.resolved_type)

    def _repr(self, print_varnames):
        return repr(self)

    def __repr__(self):
        size = self.resolved_type.width
        val = self.value
        if size % 4 == 0:
            value = hex(int(val))
        else:
            value = bin(int(val))
        return "SmallBitVectorConstant(%s, %s)" % (value, self.resolved_type)


class GenericBitVectorConstant(Constant):
    resolved_type = types.GenericBitVector()

    def __init__(self, value):
        assert isinstance(value, bitvector.BitVector)
        self.value = value

    def comparison_key(self):
        return (GenericBitVectorConstant, self._construction_expr(), self.resolved_type)

    def _repr(self, print_varnames):
        return repr(self)

    def _construction_expr(self):
        val = self.value.tolong()
        size = self.value.size()
        if size % 4 == 0:
            value = hex(int(val))
        else:
            value = bin(int(val))
        if isinstance(self.value, (bitvector.SparseBitVector, bitvector.SmallBitVector)):
            return "bitvector.from_ruint(%s, r_uint(%s))" % (size, self.value.val)
        return "bitvector.from_bigint(%s, rbigint.fromlong(%s))" % (size, value)

    def __repr__(self):
        return "GenericBitVectorConstant(%s)" % self._construction_expr()


class DefaultValue(Constant):

    def __init__(self, resolved_type):
        self.resolved_type = resolved_type

    def comparison_key(self):
        return (DefaultValue, self.resolved_type)

    def __repr__(self):
        return "DefaultValue(%r)" % (self.resolved_type, )


class EnumConstant(Constant):
    def __init__(self, variant, resolved_type):
        self.variant = variant
        self.resolved_type = resolved_type

    def comparison_key(self):
        return (EnumConstant, self.variant, self.resolved_type)

    def __repr__(self):
        return "EnumConstant(%r, %r)" % (self.variant, self.resolved_type)


class StringConstant(Constant):
    resolved_type = types.String()

    def __init__(self, string):
        self.string = string

    def comparison_key(self):
        return (StringConstant, self.string, self.resolved_type)

    def __repr__(self):
        return "StringConstant(%r)" % (self.string, )


class UnitConstant(Constant):
    resolved_type = types.Unit()
    def __repr__(self):
        return "UnitConstant.UNIT"

UnitConstant.UNIT = UnitConstant()

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
    def __init__(self, kind, sourcepos=None):
        self.kind = kind
        self.sourcepos = sourcepos

    def getargs(self):
        return [self.kind]

    def replace_ops(self, replacements):
        if self.kind in replacements:
            self.kind = replacements[self.kind]
            return True
        return False

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
    def __init__(self, booleanvalue, truetarget, falsetarget, sourcepos=None):
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

def print_graph_construction(graph, codegen=None):
    res = []
    blocks = list(graph.iterblocks())
    if codegen is not None:
        builtin_names = codegen.builtin_names
    else:
        builtin_names = {}

    bigtyps = []
    seen_bigtyps = {}
    def type_repr(typ):
        if isinstance(typ, (types.Union, types.Enum, types.Struct)):
            if typ.name not in seen_bigtyps:
                bigtyps.append("%s = %r" % (typ.name, typ))
                seen_bigtyps[typ.name] = typ
            return typ.name
        return repr(typ)

    blocknames = {block: "block%s" % i for i, block in enumerate(blocks)}
    print_varnames = {}
    for arg in graph.args:
        print_varnames[arg] = arg.name
        res.append("%s = Argument(%r, %s)" % (arg.name, arg.name, type_repr(arg.resolved_type)))
    for block, name in blocknames.iteritems():
        res.append("%s = Block()" % name)
    pending_updates = defaultdict(list)
    seen_ops = set()

    for block, blockname in blocknames.iteritems():
        for op in block.operations:
            name = op._get_print_name(print_varnames)
            if isinstance(op, Operation):
                args = ", ".join([a._repr(print_varnames) for a in op.args])
                res.append("%s = %s.emit(%s, %r, [%s], %s, %r, %r)"  % (name, blockname, op.__class__.__name__, builtin_names.get(op.name, op.name), args, type_repr(op.resolved_type), op.sourcepos, op.varname_hint))
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
                res.append("%s = %s.emit_phi([%s], [%s], %s)" % (name, blockname, blockargs, args, type_repr(op.resolved_type)))
            if pending_updates[op]:
                for prevname, index in pending_updates[op]:
                    res.append("%s.prevvalues[%s] = %s" % (prevname, index, name))
            seen_ops.add(op)
        res.append("%s.next = %s" % (blockname, block.next._repr(print_varnames, blocknames)))
    res.append("graph = Graph(%r, [%s], block0%s)" % (graph.name, ", ".join(arg.name for arg in graph.args), ", True" if graph.has_loop else ""))
    res = bigtyps + res
    return res


class GraphPage(BaseGraphPage):
    save_tmp_file = str(udir.join('graph.dot'))

    def compute(self, source, varnames, args):
        self.source = source
        self.links = {var: str(op.resolved_type) for op, var in varnames.items()}
        for arg in args:
            self.links[arg.name] = str(arg.resolved_type)


# some simple graph simplifications

class CantFold(Exception):
    pass

TIMINGS = defaultdict(float)
COUNTS = defaultdict(int)
STACK_START_TIMES = []

def print_stats():
    print "OPTIMIZATION STATISTICS"
    timings = TIMINGS.items()
    timings.sort(key=lambda element: element[1])
    timings.reverse()
    total = 0.0
    maxnamesize = 0
    for name, t in timings:
        total += t
        maxnamesize = max(maxnamesize, len(name))
    for name, t in timings:
        print name.rjust(maxnamesize), "time:", round(t, 2), "number of times called:", COUNTS[name], "time[ms]/call:", round(t / COUNTS[name] * 1000, 4), "percentage:", round(t / total * 100, 1)
        total += t
    print "TOTAL", round(total, 2)

DEBUG_REPEAT = False

def repeat(func):
    def repeated(graph, codegen, *args, **kwargs):
        t1_proper = time.time()
        STACK_START_TIMES.append(t1_proper)
        ever_changed = False
        for i in range(1000):
            if DEBUG_REPEAT and repeat.debug_list is not None:
                repeat.debug_list.append((func.func_name, "before", i, print_graph_construction(graph), ever_changed))
            changed = func(graph, codegen, *args, **kwargs)
            if DEBUG_REPEAT and repeat.debug_list is not None:
                repeat.debug_list.append((func.func_name, "after", i, print_graph_construction(graph), changed))
            assert isinstance(changed, (bool, str, type(None)))
            if not changed:
                break
            ever_changed = True
        else:
            codegen.print_debug_msg("LIMIT REACHED!", graph, func.func_name)
            added_debug_list = False
            if DEBUG_REPEAT:
                if repeat.debug_list is None:
                    repeat.debug_list = []
                    added_debug_list = True
                try:
                    repeat.debug_list.append((func.func_name, "debug start", 0, print_graph_construction(graph), ''))
                    changed = func(graph, codegen, *args, **kwargs)
                    repeat.debug_list.append((func.func_name, "debug end", 0, print_graph_construction(graph), ''))
                    print "CHANGES", changed
                    print "#" * 60
                    print "\n".join(repeat.debug_list[0][3])
                    print "#" * 60

                    import difflib, sys
                    prev = None
                    for curr in repeat.debug_list:
                        if prev is None:
                            prev = curr
                            continue
                        print "_" * 60
                        print prev[0], prev[1], prev[2], prev[4]
                        print curr[0], curr[1], curr[2], curr[4]
                        l_before = [line + "\n" for line in prev[3]]
                        l_after = [line + "\n" for line in curr[3]]
                        sys.stdout.writelines(difflib.unified_diff(l_before, l_after, fromfile='before', tofile='after'))
                        prev = curr
                finally:
                    if added_debug_list:
                        repeat.debug_list = None
        t2 = time.time()
        t1 = STACK_START_TIMES.pop()
        assert t2 - t1 >= 0
        TIMINGS[func.func_name] += t2 - t1
        COUNTS[func.func_name] += i + 1
        if STACK_START_TIMES: # parent optimization overcounts, so add t2 - t1_proper to start time
            STACK_START_TIMES[-1] += t2 - t1_proper
        if ever_changed:
            ever_changed = func.func_name
        return ever_changed
    return repeated
repeat.debug_list = None

def light_simplify(graph, codegen):
    # in particular, don't specialize
    codegen.print_debug_msg("simplifying ssa")
    res = _optimize(graph, codegen)
    if res:
        graph.check()
    return res


def optimize(graph, codegen):
    from pydrofoil.specialize import SpecializingOptimizer
    res = _optimize(graph, codegen)
    if graph.name not in codegen.inlinable_functions:
        for i in range(100):
            specialized = SpecializingOptimizer(graph, codegen).optimize()
            if specialized:
                res = _bare_optimize(graph, codegen) or res
            else:
                break
        res = _optimize(graph, codegen) or res
    if res:
        graph.check()
    return res

def _bare_optimize(graph, codegen):
    from pydrofoil.absinterp import optimize_with_range_info
    res = False
    res = propagate_equality(graph, codegen) or res
    res = join_blocks(graph, codegen) or res
    res = remove_dead(graph, codegen) or res
    res = simplify_phis(graph, codegen) or res
    res = sink_allocate(graph, codegen) or res
    res = inline(graph, codegen) or res
    res = remove_superfluous_union_checks(graph, codegen) or res
    res = localopt(graph, codegen, do_double_casts=False) or res
    res = remove_empty_blocks(graph, codegen) or res
    res = swap_not(graph, codegen) or res
    res = optimize_with_range_info(graph, codegen) or res
    res = cse_global_reads(graph, codegen) or res
    res = cse_field_reads(graph, codegen) or res
    res = remove_superfluous_union_checks(graph, codegen) or res
    res = localopt(graph, codegen, do_double_casts=True) or res
    res = remove_if_phi_constant(graph, codegen) or res
    res = remove_superfluous_enum_cases(graph, codegen) or res
    res = remove_useless_switch(graph, codegen) or res
    partial_allocation_removal(graph, codegen)
    return res

_optimize = repeat(_bare_optimize)

@repeat
def localopt(graph, codegen, do_double_casts=True):
    return LocalOptimizer(graph, codegen, do_double_casts).optimize()

@repeat
def remove_dead(graph, codegen):
    def can_remove_op(op):
        if not op.can_have_side_effects:
            return True
        if op.name == "@not":
            return True
        if op.name == "@eq":
            return True
        if op.is_union_creation():
            return True
        name = op.name.lstrip("@$")
        name = codegen.builtin_names.get(name, name)
        return type(op) is Operation and name in supportcode.purefunctions

    changed = False
    needed = set()
    # in theory we need a proper fix point but too annoying (Sail has very few
    # loops)
    blocks = list(graph.iterblocks())
    for block in blocks:
        for op in block.operations:
            args = op.getargs()[:]
            if isinstance(op, Phi) and op in args:
                args.remove(op)
            needed.update(args)
        needed.update(block.next.getargs())
    for block in blocks:
        operations = [op for op in block.operations if op in needed or not can_remove_op(op)]
        if len(operations) != len(block.operations):
            changed = True
            block.operations[:] = operations
    return changed

@repeat
def remove_empty_blocks(graph, codegen):
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
def join_blocks(graph, codegen):
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
def simplify_phis(graph, codegen):
    replace_phis = {}
    for block in graph.iterblocks():
        for index, op in enumerate(block.operations):
            if not isinstance(op, Phi):
                continue
            values = set(op.prevvalues)
            if len(values) == 1 or (len(values) == 2 and op in values):
                values.discard(op)
                value, = values
                replace_phis[op] = value
                # this is really inefficient, but I don't want to think
                del block.operations[index]
                graph.replace_ops(replace_phis)
                break # continue with the next block
    return False

@repeat
def remove_if_true_false(graph, codegen):
    changed = False
    for block in graph.iterblocks():
        cond = block.next
        if not isinstance(cond, ConditionalGoto) or type(cond.booleanvalue) is not BooleanConstant:
            continue
        if cond.booleanvalue.value:
            takenblock = cond.truetarget
        else:
            takenblock = cond.falsetarget
        block.next = Goto(takenblock)
        changed = True
    if changed:
        # need to remove Phi arguments
        _remove_unreachable_phi_prevvalues(graph)
    return changed

def _remove_unreachable_phi_prevvalues(graph):
    replace_phis = {}
    entrymap = graph.make_entrymap()
    for block, entry in entrymap.iteritems():
        block_changed = False
        for index, op in enumerate(block.operations):
            if not isinstance(op, Phi):
                continue
            prevblocks = []
            prevvalues = []
            for prevblock, prevvalue in zip(op.prevblocks, op.prevvalues):
                if prevblock in entry:
                    prevblocks.append(prevblock)
                    prevvalues.append(replace_phis.get(prevvalue, prevvalue))
            op.prevblocks = prevblocks
            op.prevvalues = prevvalues
            if len(prevblocks) == 1:
                replace_phis[op] = op.prevvalues[0]
                block.operations[index] = None
                block_changed = True
        if block_changed:
            block.operations = [op for op in block.operations if op]
    if replace_phis:
        graph.replace_ops(replace_phis)

@repeat
def remove_if_phi_constant(graph, codegen):
    from pydrofoil.emitfunction import count_uses
    uses = count_uses(graph)
    res = False
    for block in graph.iterblocks():
        ops = [op for op in block.operations if not isinstance(op, Comment)]
        if len(ops) != 1:
            continue
        op, = ops
        if not isinstance(op, Phi):
            continue
        if op.resolved_type is not types.Bool():
            continue
        if not isinstance(block.next, ConditionalGoto):
            continue
        if block.next.booleanvalue is not op:
            continue
        if uses[op] != 1:
            continue
        prevblocks = []
        prevvalues = []
        for prevblock, val in zip(op.prevblocks, op.prevvalues):
            if isinstance(val, BooleanConstant):
                if val.value:
                    target = block.next.truetarget
                else:
                    target = block.next.falsetarget
                prevblock.next.replace_next(block, target)
                res = True
            else:
                prevblocks.append(prevblock)
                prevvalues.append(val)
        if len(prevvalues) < len(op.prevvalues):
            op.prevvalues = prevvalues
            op.prevblocks = prevblocks
    if res:
        _remove_unreachable_phi_prevvalues(graph)
        simplify_phis(graph, codegen)
        join_blocks(graph, codegen)
    return res


@repeat
def convert_sail_assert_to_exception(graph, codegen):
    res = False
    for block in list(graph.iterblocks()):
        for index, op in enumerate(block.operations):
            if not isinstance(op, Operation):
                continue
            name = op.name
            name = codegen.builtin_names.get(name, name)
            if name != 'zsail_assert':
                continue
            newblock = block.split(index, keep_op=False)
            failblock = Block()
            failblock.next = Raise(op.args[1], None)
            if isinstance(op.args[1], StringConstant):
                assert_str = 'sail_assert'
                assert_str += ' ' + op.args[1].string
                block.operations.append(Comment(assert_str))
            block.next = ConditionalGoto(op.args[0], newblock, failblock, op.sourcepos)
            res = True
            # try with the next blocks, but if there are multiple asserts in
            # this one we need to repeat
            break
    return res

def duplicate_end_blocks(graph, codegen):
    assert not graph.has_loop
    # make sure that all end blocks have exactly one predecessor.
    # not used by default, but graph splitting needs it
    def should_duplicate(block):
        return len(block.next.next_blocks()) == 0 and len(entrymap[block]) > 1

    num_duplicated = 0
    num_ops_duplicated = 0
    entrymap = graph.make_entrymap()
    candidates = [block for block in entrymap if should_duplicate(block)]
    while candidates:
        block = candidates.pop()
        preds = entrymap[block]
        assert should_duplicate(block)
        del entrymap[block] # the block won't be reachable at all any more
        next = block.next
        for predblock in preds:
            num_duplicated += 1
            # copy operations of the end block, removing phis (they can be
            # removed because we will only have a single predecessor)
            ops = []
            replacements = {}
            for op in block.operations:
                if isinstance(op, Phi):
                    index = op.prevblocks.index(predblock)
                    value = op.prevvalues[index]
                    replacements[op] = value
                else:
                    assert isinstance(op, Operation)
                    newop = Operation(op.name, [replacements.get(arg, arg) for arg in op.args], op.resolved_type, op.sourcepos, op.varname_hint)
                    newop.__class__ = op.__class__
                    replacements[op] = newop
                    ops.append(newop)
                    num_ops_duplicated += 1
            if isinstance(predblock.next, Goto):
                # just put the operations in the previous block
                predblock.operations.extend(ops)
                newblock = predblock
                if 1 < len(entrymap[predblock]) < 8:
                    # the previous block needs duplication too
                    candidates.append(predblock)
            else:
                # need a new block, the previous block has several successors
                newblock = Block(ops)
                predblock.next.replace_next(block, newblock)
            if isinstance(next, Return):
                newblock.next = Return(replacements.get(next.value, next.value), next.sourcepos)
            elif isinstance(next, Raise):
                newblock.next = Raise(replacements.get(next.kind, next.kind), next.sourcepos)
            else:
                assert 0, "unreachable"
    if num_duplicated:
        graph.check()
    return num_duplicated


class defaultdict_with_key_arg(dict):
    def __init__(self, factory):
        self.factory = factory
    def __missing__(self, key):
        res = self[key] = self.factory(key)
        return res


def remove_superfluous_enum_cases(graph, codegen):
    if graph.has_loop:
        return

    def init_enum_set(value):
        typ = value.resolved_type
        if isinstance(value, EnumConstant):
            return {value.variant}
        else:
            return set(typ.elements)

    changed = False
    # maps blocks -> values -> sets of enum names
    possible_enum_values = defaultdict(lambda : defaultdict_with_key_arg(init_enum_set))
    entrymap = graph.make_entrymap()
    for block in topo_order(graph):
        values_in_block = possible_enum_values[block]
        if isinstance(block.next, ConditionalGoto):
            value = block.next.booleanvalue
            if (isinstance(value, Operation) and value.name == "@eq" and
                    isinstance(value.args[0].resolved_type, types.Enum)):
                arg0, arg1 = value.args
                if not isinstance(arg1, EnumConstant):
                    arg0, arg1 = arg1, arg0
                if isinstance(arg1, EnumConstant):
                    possible_values_arg0 = values_in_block[arg0]
                    possible_values_arg1 = values_in_block[arg1]
                    assert len(possible_values_arg1) == 1
                    if possible_values_arg0 == possible_values_arg1:
                        changed = True
                        block.next.booleanvalue = BooleanConstant.TRUE
                    else:
                        if len(entrymap[block.next.truetarget]) == 1:
                            possible_enum_values[block.next.truetarget][arg0] = possible_values_arg1
                        if len(entrymap[block.next.falsetarget]) == 1:
                            possible_enum_values[block.next.falsetarget][arg0] = possible_values_arg0 - possible_values_arg1
    if changed:
        remove_if_true_false(graph, codegen)
        remove_dead(graph, codegen)
        return True
    return False

def remove_superfluous_union_checks(graph, codegen):
    if graph.has_loop:
        return

    def init_variant_set(value):
        typ = value.resolved_type
        return frozenset(typ.variants)

    changed = False
    # maps blocks -> values -> sets of variant names
    possible_union_variants = defaultdict(lambda : defaultdict_with_key_arg(init_variant_set))
    entrymap = graph.make_entrymap()
    for block in topo_order(graph):
        values_in_block = possible_union_variants[block]
        if not isinstance(block.next, ConditionalGoto) or not isinstance(block.next.booleanvalue, UnionVariantCheck):
            for nextblock in block.next.next_blocks():
                if len(entrymap[nextblock]) == 1:
                    possible_union_variants[nextblock].update(values_in_block)
            continue
        cond = block.next.booleanvalue
        assert isinstance(cond, UnionVariantCheck)
        arg0, = cond.args
        possible_values_arg0 = values_in_block[arg0]
        single = frozenset([cond.name])
        if possible_values_arg0 == single:
            changed = True
            block.next.booleanvalue = BooleanConstant.FALSE
        else:
            if len(entrymap[block.next.truetarget]) == 1:
                values_in_block = possible_union_variants[block.next.truetarget]
                values_in_block[arg0] = possible_values_arg0 - single
            if len(entrymap[block.next.falsetarget]) == 1:
                values_in_block = possible_union_variants[block.next.falsetarget]
                values_in_block[arg0] = single
    if changed:
        remove_if_true_false(graph, codegen)
        remove_dead(graph, codegen)
        return True
    return False


def remove_useless_switch(graph, codegen):
    # if we have a switch where the two target blocks are the same we can
    # remove the if completely
    res = False
    for block in graph.iterblocks():
        if not isinstance(block.next, ConditionalGoto):
            continue
        if block.next.truetarget is block.next.falsetarget:
            for op in block.next.truetarget.operations:
                assert not isinstance(op, Phi)
            block.next = Goto(block.next.truetarget, block.next.sourcepos)
            res = True
    if res:
        remove_dead(graph, codegen)
    return res


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

class BaseOptimizer(object):
    def __init__(self, graph, codegen, do_double_casts=True):
        self.graph = graph
        self.codegen = codegen
        self.changed = False
        self.anticipated_casts = find_anticipated_casts(graph)
        self.entrymap = graph.make_entrymap()
        self.nextblocks = defaultdict(set)
        for block, entry in self.entrymap.iteritems():
            for prevblock in entry:
                self.nextblocks[prevblock].add(block)
        self.do_double_casts = do_double_casts
        self.current_block = self.graph.startblock
        self._dead_blocks = False
        self._need_dead_code_removal = False
        self.newoperations = None
        self.replacements = {}
        # cse attributes
        self.cse_op_available = {} # block -> block -> prev_op
        self.cse_op_available_in_block = None

    def __repr__(self):
        return "<%s %s>" % (self.__class__.__name__, self.graph)

    def view(self):
        self.graph.view(self.codegen)

    def optimize(self):
        self.replacements = {}
        for block in topo_order_best_attempt(self.graph):
            self.current_block = block
            self.optimize_block(block)
        if self.replacements:
            # XXX do them all in one go
            while 1:
                changed = self.graph.replace_ops(self.replacements)
                if not changed:
                    break
            self.replacements.clear()
            self.changed = True
        if self._dead_blocks:
            _remove_unreachable_phi_prevvalues(self.graph)
            self.changed = True
        if self._need_dead_code_removal:
            remove_dead(self.graph, self.codegen)
        return self.changed

    def optimize_block(self, block):
        # prepare CSE
        available_in_block = self._compute_available_in_block_from_predecessors(block)
        self.cse_op_available[block] = available_in_block
        self.cse_op_available_in_block = available_in_block

        self.newoperations = []
        for i, op in enumerate(block.operations):
            newop = self._optimize_op(block, i, op)
            if newop is REMOVE:
                self.changed = True
            elif newop is not None:
                assert op.resolved_type is newop.resolved_type
                self.replacements[op] = newop
        if isinstance(block.next, ConditionalGoto):
            cond = block.next
            condition = self._known_boolean_value(block.next.booleanvalue)
            if condition is not None:
                if condition.value:
                    takenblock = cond.truetarget
                else:
                    takenblock = cond.falsetarget
                block.next = Goto(takenblock)
                self._dead_blocks = True
        block.operations = self.newoperations
        self.newoperations = None
        self.cse_op_available_in_block = None

    def _compute_available_in_block_from_predecessors(self, block):
        available_in_block = {}
        prev_blocks = self.entrymap[block]
        if prev_blocks:
            if len(prev_blocks) == 1:
                prev_block, = prev_blocks
                nextblocks_of_prevblock = self.nextblocks[prev_block]
                available_in_block = self.cse_op_available[prev_blocks[0]]
                if len(nextblocks_of_prevblock) > 1:
                    available_in_block = available_in_block.copy()
            else:
                # intersection of what's available in the previous blocks
                prev_cse_dicts = []
                for prev_block in prev_blocks:
                    prev_cse_dict = self.cse_op_available.get(prev_block, None)
                    if not prev_cse_dict:
                        break # one of the available dicts is empty, no need to intersect
                    prev_cse_dicts.append(prev_cse_dict)
                else:
                    prev_cse_dicts.sort(key=len)
                    smallest_dict = prev_cse_dicts.pop(0)
                    for key, prev_op in smallest_dict.iteritems():
                        for prev_cse_dict in prev_cse_dicts:
                            if prev_cse_dict.get(key, None) is not prev_op:
                                break
                        else:
                            available_in_block[key] = prev_op
            for prevblock in prev_blocks:
                nextblocks_of_prevblock = self.nextblocks[prevblock]
                nextblocks_of_prevblock.discard(block)
                if not nextblocks_of_prevblock and prevblock in self.cse_op_available:
                    # don't keep all the cse info alive, it's way too huge
                    del self.cse_op_available[prevblock]
        return available_in_block

    def _known_boolean_value(self, op):
        op = self._get_op_replacement(op)
        if isinstance(op, BooleanConstant):
            return op

    def _optimize_op(self, block, index, op):
        # base implementation, do CSE
        key = None
        if isinstance(op, Phi):
            key = (Phi, self._cse_comparison_tuple(op.prevvalues), tuple(op.prevblocks), op.resolved_type)
        elif not self._cse_can_replace(op):
            if isinstance(op, FieldWrite) and self._cse_is_tuplestruct(op):
                assert not isinstance(op.args[0], StructConstruction)
                res = op.args[1]
                writekey = (FieldAccess, op.name, self._cse_comparison_tuple(op.args[:1]), res.resolved_type)
                self.cse_op_available_in_block[writekey] = self.replacements.get(res, res)
            if isinstance(op, StructConstruction) and self._cse_is_tuplestruct_typ(op.resolved_type):
                for fieldname, val in zip(op.resolved_type.names, op.args):
                    writekey = (FieldAccess, fieldname, (op, ), val.resolved_type)
                    self.cse_op_available_in_block[writekey] = self.replacements.get(val, val)
        else:
            key = (type(op), op.name, self._cse_comparison_tuple(op.args), op.resolved_type)
        if key is not None:
            if key in self.cse_op_available_in_block:
                block.operations[index] = None
                self._need_dead_code_removal = True
                return self.cse_op_available_in_block[key]
            else:
                self.cse_op_available_in_block[key] = op
        self.newoperations.append(op)

    # some cse helpers

    def _cse_is_tuplestruct_typ(self, typ):
        return isinstance(typ, types.Struct) and typ.tuplestruct

    def _cse_is_tuplestruct(self, op):
        return self._cse_is_tuplestruct_typ(op.args[0].resolved_type)

    def _cse_can_replace(self, op):
        if isinstance(op, Cast):
            return True
        if isinstance(op, UnionCast):
            return True
        if isinstance(op, UnionVariantCheck):
            return True
        if isinstance(op, FieldAccess) and self._cse_is_tuplestruct(op):
            return True
        if op.name == "@not":
            return True
        name = self.codegen.builtin_names.get(op.name, op.name)
        name = name.lstrip('@')
        return type(op) is Operation and name in supportcode.purefunctions

    def _cse_comparison_tuple(self, valuelist):
        return tuple(self.replacements.get(arg, arg).comparison_key() for arg in valuelist)

    # end cse helpers

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
        newop = Phi(prevblocks[:], prevvalues, resolved_type)
        self.newoperations.append(newop)
        return newop

    def _convert_to_machineint(self, arg):
        try:
            return self._extract_machineint(arg)
        except NoMatchException:
            # call int_to_int64
            return self.newop(INT_TO_INT64_NAME, [arg], types.MachineInt())

    def _make_int64_to_int(self, arg, sourcepos=None):
        return self.newop(INT64_TO_INT_NAME, [arg], types.Int(), sourcepos)

    def _make_int_to_int64(self, arg, sourcepos=None):
        return self.newop(INT_TO_INT64_NAME, [arg], types.MachineInt(), sourcepos)

    def _get_op_replacement(self, value):
        while value in self.replacements:
            value = self.replacements[value]
        return value

    def _args(self, op):
        return [self._get_op_replacement(value) for value in op.args]

    def _builtinname(self, name):
        return self.codegen.builtin_names.get(name, name)

    def _extract_smallfixedbitvector(self, arg):
        if isinstance(arg, GenericBitVectorConstant) and arg.value.size() <= 64:
            typ = types.SmallFixedBitVector(arg.value.size())
            return SmallBitVectorConstant(arg.value.touint(), typ), typ
        if isinstance(arg.resolved_type, types.SmallFixedBitVector):
            return arg, arg.resolved_type
        if not isinstance(arg, Cast):
            if self.newoperations is not None:
                # xxx, wrong complexity
                anticipated = self.anticipated_casts.get(self.current_block, set())
                casts = {typ for (op, typ) in anticipated if self.replacements.get(op, op) is arg}
                if not casts:
                    raise NoMatchException
                if len(casts) == 1:
                    typ, = casts
                    return self.newcast(arg, typ), typ
            raise NoMatchException
        expr = arg.args[0]
        typ = expr.resolved_type
        if not isinstance(typ, types.SmallFixedBitVector):
            assert typ is types.GenericBitVector() or isinstance(
                typ, types.BigFixedBitVector
            )
            raise NoMatchException
        return expr, typ

    def _extract_machineint(self, arg, want_constant=True, can_recurse=True):
        if arg.resolved_type is types.MachineInt():
            return arg
        if isinstance(arg, IntConstant):
            if not want_constant:
                raise NoMatchException
            if isinstance(arg.number, int):
                return MachineIntConstant(arg.number)
        if isinstance(arg, DefaultValue):
            return DefaultValue(types.MachineInt())
        if (
            isinstance(arg, Operation)
            and self._builtinname(arg.name) == "int64_to_int"
        ):
            return arg.args[0]
        if isinstance(arg, Cast):
            import pdb;pdb.set_trace()
        # check whether we have a cast as an available expression (ie "above" us)
        key = (Operation, INT_TO_INT64_NAME, self._cse_comparison_tuple([arg]), types.MachineInt())
        if self.cse_op_available_in_block and key in self.cse_op_available_in_block:
            return self.cse_op_available_in_block[key]
        if self.newoperations is not None:
            anticipated = self.anticipated_casts.get(self.current_block, set())
            if (arg, types.MachineInt()) in anticipated:
                return self._make_int_to_int64(arg)
        if isinstance(arg, Phi) and can_recurse:
            # XXX can do even better with loops
            prevvalues = []
            for prevvalue in arg.prevvalues:
                prevvalues.append(self._extract_machineint(
                    self._get_op_replacement(prevvalue),
                    want_constant=want_constant,
                    can_recurse=not self.graph.has_loop))
            newres = Phi(arg.prevblocks, prevvalues, types.MachineInt())
            self._need_dead_code_removal = True
            # this is quite delicate, need to insert the Phi into the right block
            if arg in self.current_block.operations:
                self.newoperations.insert(0, newres)
                return newres
            for prevblock in arg.prevblocks:
                if isinstance(prevblock.next, Goto):
                    homeblock = prevblock.next.target
                    if arg in homeblock.operations:
                        homeblock.operations.insert(0, newres)
                        return newres
        raise NoMatchException

    def _extract_number(self, arg):
        if isinstance(arg, MachineIntConstant):
            return arg
        num = self._extract_machineint(arg)
        if not isinstance(num, MachineIntConstant):
            raise NoMatchException
        return num

    def _must_be_non_negative(self, arg):
        return isinstance(arg, Operation) and arg.name in (
                "@unsigned_bv_wrapped_res", "@unsigned_bv", "@length_unwrapped_res", "@vec_length_unwrapped_res")

def is_pow_2(num):
    return num & (num - 1) == 0

def shift_amount(num):
    return bitvector.BigInteger._shift_amount(num)

class LocalOptimizer(BaseOptimizer):

    def _should_fit_machine_int(self, op):
        anticipated = self.anticipated_casts.get(self.current_block, set())
        return (op, types.MachineInt()) in anticipated

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
        return BaseOptimizer._optimize_op(self, block, index, op)

    def _optimize_Cast(self, op, block, index):
        arg, = self._args(op)
        if op.resolved_type is arg.resolved_type:
            block.operations[index] = None
            return arg
        if isinstance(op.resolved_type, types.SmallFixedBitVector):
            if isinstance(arg, UnpackPackedField):
                return self.newop("@packed_field_cast_smallfixedbitvector", [MachineIntConstant(op.resolved_type.width), arg.args[0]], op.resolved_type, op.sourcepos)
        if self.do_double_casts and isinstance(arg, Cast):
            arg2, = self._args(arg)
            if arg2.resolved_type is op.resolved_type:
                block.operations[index] = None
                return arg2
            return self.newcast(arg2, op.resolved_type, op.sourcepos, op.varname_hint)

    def _optimize_PackPackedField(self, op, block, index):
        arg, = self._args(op)
        if isinstance(arg, UnpackPackedField):
            return arg.args[0]
        if arg.resolved_type is types.GenericBitVector():
            arg, typ = self._extract_smallfixedbitvector(arg)
            return self.newop("@pack_smallfixedbitvector", [MachineIntConstant(typ.width), arg], op.resolved_type, op.sourcepos)
        elif op.args[0].resolved_type is types.Int():
            arg = self._extract_machineint(arg)
            return self.newop("@pack_machineint", [arg], op.resolved_type, op.sourcepos)

    def _optimize_UnpackPackedField(self, op, block, index):
        arg, = self._args(op)
        if not isinstance(op.args[0], FieldAccess):
            if type(arg) is Operation and arg.name == "@pack_smallfixedbitvector":
                return self.newcast(arg.args[1], op.resolved_type, op.sourcepos, op.varname_hint)
            if type(arg) is Operation and arg.name == "@pack_machineint":
                return self.newop(INT64_TO_INT_NAME, [arg.args[0]], types.Int(), arg.sourcepos)
            if isinstance(arg, PackPackedField):
                return arg.args[0]
            if not isinstance(arg, Phi):
                import pdb;pdb.set_trace()
            else:
                l = []
                for prevvalue, prevblock in zip(arg.prevvalues, arg.prevblocks):
                    unpack = UnpackPackedField(prevvalue)
                    prevblock.operations.append(unpack)
                    l.append(unpack)
                phi = self.newphi(
                    arg.prevblocks,
                    l,
                    arg.resolved_type.typ)
                self.newoperations.pop()
                self.newoperations.insert(0, phi)
                return phi


    def _optimize_Operation(self, op, block, index):
        if op.name in self.codegen.method_graphs_by_name and op.args[0].is_union_creation():
            variants = self.codegen.method_graphs_by_name[op.name]
            if op.args[0].name in variants:
                op.name = variants[op.args[0].name].name
        name = self._builtinname(op.name)
        if name.lstrip('@') in supportcode.all_unwraps:
            specs, unwrapped_name = supportcode.all_unwraps[name.lstrip('@')]
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
        name = name.lstrip("$@")
        meth = getattr(self, "optimize_%s" % name, None)
        if meth:
            try:
                newop = meth(op)
            except NoMatchException:
                pass
            else:
                if newop is not None:
                    return newop

        # try generic constant folding
        func = getattr(supportcode, name, None)
        if not func:
            return
        if op.resolved_type is types.Real():
            return # later
        args = self._args(op)
        if name not in supportcode.purefunctions:
            return
        if "undefined" in name:
            return
        if not all(isinstance(arg, Constant) for arg in args):
            return self._try_fold_phi(name, func, args, op.resolved_type, op)
        return self._try_fold(name, func, args, op.resolved_type, op)

    def _try_fold(self, name, func, args, resolved_type, op):
        runtimeargs = []
        for arg in args:
            if isinstance(arg, IntConstant):
                if not isinstance(arg.number, int):
                    return None # XXX can be improved
                runtimeargs.append(bitvector.Integer.fromint(arg.number))
            elif isinstance(arg, MachineIntConstant):
                runtimeargs.append(arg.number)
            elif isinstance(arg, SmallBitVectorConstant):
                runtimeargs.append(arg.value)
            elif isinstance(arg, GenericBitVectorConstant):
                runtimeargs.append(arg.value)
            elif arg.resolved_type is types.Real():
                return # later
            elif arg.resolved_type is types.Unit():
                runtimeargs.append(())
            elif arg.resolved_type is types.String():
                runtimeargs.append(arg.string)
            else:
                return None
        try:
            res = func("constfolding", *runtimeargs)
        except CantFold:
            return None # silent
        except (Exception, AssertionError) as e:
            print "generict const-folding failed", name, op, "with error", e, "arguments", args
            return None
        if resolved_type is types.MachineInt():
            assert isinstance(res, int)
            return MachineIntConstant(res)
        if resolved_type is types.Int():
            return IntConstant(int(res.tolong()))
        if isinstance(resolved_type, types.SmallFixedBitVector):
            assert isinstance(res, r_uint)
            return SmallBitVectorConstant.from_ruint(resolved_type.width, res)
        if resolved_type is types.Bool():
            assert isinstance(res, bool)
            return BooleanConstant.frombool(res)
        if resolved_type is types.String():
            assert isinstance(res, str)
            return StringConstant(res)
        if resolved_type is types.GenericBitVector():
            assert isinstance(res, bitvector.BitVector)
            return GenericBitVectorConstant(res)
        # XXX other types? import pdb;pdb.set_trace()

    def _try_fold_phi(self, name, func, args, resolved_type, op):
        phi_index = -1
        for index, arg in enumerate(args):
            if isinstance(arg, Constant):
                pass
            elif isinstance(arg, Phi):
                if phi_index != -1:
                    #if arg in self.current_block.operations and args[phi_index] in self.current_block.operations:
                    #    import pdb;pdb.set_trace()
                    return # only one phi possible
                phi_index = index
                if not all(isinstance(value, Constant) for value in arg.prevvalues):
                    return
            else:
                return
        phi = args[phi_index]
        results = []
        first_comparison_key = None
        all_same = True
        for value in phi.prevvalues:
            newargs = args[:]
            newargs[phi_index] = value
            res = self._try_fold(name, func, newargs, resolved_type, op)
            if res is None:
                return
            if not results:
                first_comparison_key = res.comparison_key()
            else:
                all_same = all_same and res.comparison_key() == first_comparison_key
            results.append(res)
        if len(results) == 1 or all_same:
            return results[0]
        newphi = Phi(phi.prevblocks[:], results, resolved_type)
        if phi in self.current_block.operations or phi in self.newoperations:
            self.newoperations.insert(0, newphi)
            return newphi
        else:
            # try to find correct block to insert
            # XXX this shows the need for phis to point to their "home" block
            correct_block = self._try_find_phi_home_block(phi)
            if correct_block:
                if len(correct_block.operations) < 50:
                    # weird heuristic, triggers some super strange restriction
                    # in the GC(!) if we add too many phis
                    correct_block.operations.insert(0, newphi)
                    return newphi
            return None

    def _try_find_phi_home_block(self, phi):
        for prevblock in phi.prevblocks:
            for correct_block in prevblock.next.next_blocks():
                if phi in correct_block.operations:
                    return correct_block

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
            seentyp = None
            for arg in op.prevvalues:
                if isinstance(arg, DefaultValue):
                    bvs.append(DefaultValue(None))
                else:
                    arg, typ = self._extract_smallfixedbitvector(self._get_op_replacement(arg))
                    bvs.append(arg)
                    if seentyp is None:
                        seentyp = typ
                    elif seentyp is not typ:
                        raise NoMatchException
            for arg in bvs:
                if isinstance(arg, DefaultValue):
                    arg.resolved_type = seentyp
            return self.newcast(
                self.newphi(
                    op.prevblocks,
                    bvs,
                    seentyp),
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
        if isinstance(op.resolved_type, types.Struct) and op.resolved_type.tuplestruct:
            if not all(isinstance(arg, (StructConstruction, DefaultValue)) for arg in op.prevvalues):
                return
            fields = []
            for index, name in enumerate(op.resolved_type.names):
                values = []
                fieldtyp = op.resolved_type.internalfieldtyps[name]
                for arg in op.prevvalues:
                    if isinstance(arg, DefaultValue):
                        values.append(DefaultValue(fieldtyp))
                    else:
                        values.append(arg.args[index])
                fields.append(self.newphi(
                    op.prevblocks,
                    values,
                    fieldtyp
                ))
            res = StructConstruction(op.resolved_type.name, fields, op.resolved_type)
            self.newoperations.append(res)
            return res
        if isinstance(op.resolved_type, types.Union):
            names = set()
            for arg in op.prevvalues:
                if type(arg) is not Operation:
                    return
                if len(arg.args) != 1:
                    return
                names.add(arg.name)
            if len(names) != 1:
                return
            variant, = names
            if variant not in op.resolved_type.variants:
                return
            self._need_dead_code_removal = True
            arg = self.newphi(op.prevblocks, [arg.args[0] for arg in op.prevvalues],
                              op.prevvalues[0].args[0].resolved_type)
            return self.newop(variant, [arg], op.resolved_type)

    def _optimize_NonSSAAssignment(self, op, block, index):
        return REMOVE

    def _optimize_UnionVariantCheck(self, op, block, index):
        arg, = self._args(op)
        if type(arg) is Operation:
            if arg.name == op.name:
                return BooleanConstant.FALSE
            if arg.is_union_creation():
                return BooleanConstant.TRUE
        if not isinstance(arg, Phi):
            return
        phi = arg
        if not all(value.is_union_creation() for value in phi.prevvalues):
            return

        results = []
        for value in phi.prevvalues:
            results.append(BooleanConstant.frombool(value.name != op.name))
        if len(set(results)) == 1:
            return results[0]
        newphi = Phi(phi.prevblocks[:], results, types.Bool())
        if phi in self.current_block.operations or phi in self.newoperations:
            self.newoperations.insert(0, newphi)
            return newphi
        correct_block = self._try_find_phi_home_block(phi)
        if correct_block:
            correct_block.operations.insert(0, newphi)
            return newphi
        return None

    def _optimize_UnionCast(self, op, block, index):
        arg0, = self._args(op)
        if arg0.is_union_creation() and arg0.name == op.name:
            assert len(arg0.args) == 1
            assert arg0.args[0].resolved_type == op.resolved_type
            return arg0.args[0]

    def _optimize_StructCopy(self, op, block, index):
        from pydrofoil.emitfunction import count_uses
        arg0, = self._args(op)
        if isinstance(arg0, UnionCast) and block.operations[index - 1] is arg0:
            # a unioncast just before the copy does not need copying again
            uses = count_uses(self.graph)
            if uses[arg0] == 1:
                return arg0
        if isinstance(arg0, Phi):
            if all(isinstance(arg, StructConstruction) for arg in arg0.prevvalues):
                uses = count_uses(self.graph)
                if op.resolved_type.tuplestruct or all(uses[arg] == 1 for arg in arg0.prevvalues):
                    return arg0

    def _optimize_StructConstruction(self, op, block, index):
        args = self._args(op)
        if op.resolved_type.tuplestruct and all(isinstance(arg, FieldAccess) for arg in args):
            fieldreadargs = {arg.args[0] for arg in args}
            if len(fieldreadargs) == 1:
                res, = fieldreadargs
                if res.resolved_type == op.resolved_type:
                    return res

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

    @symmetric
    def optimize_neq(self, op, arg0, arg1):
        return self.newop(
            "@not", [self.newop(
                "@eq",
                [arg0, arg1], op.resolved_type, op.sourcepos, op.varname_hint
            )],
            op.resolved_type
        )

    def optimize_int64_to_int(self, op):
        (arg0,) = self._args(op)
        if isinstance(arg0, MachineIntConstant):
            return IntConstant(arg0.number)
        if self.do_double_casts:
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
        if not isinstance(arg0, Operation):
            return
        if isinstance(arg0, UnpackPackedField):
            return self.newop(
                "@packed_field_int_to_int64",
                [arg0.args[0]],
                op.resolved_type,
                op.sourcepos,
                op.varname_hint)

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
        if arg0 is arg1:
            return BooleanConstant.FALSE
        try:
            arg1num = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            if arg1num.number == 0 and self._must_be_non_negative(arg0):
                return BooleanConstant.FALSE
        if arg0.resolved_type is not types.Int():
            try:
                arg0, arg1 = self._extract_number(arg0), self._extract_number(arg1)
            except NoMatchException:
                pass
            else:
                return BooleanConstant.frombool(arg0.number < arg1.number)
        else:
            try:
                arg0, arg1 = self._extract_machineint(arg0), self._extract_machineint(arg1)
            except NoMatchException:
                pass
            else:
                return self.newop("@lt", [arg0, arg1], op.resolved_type, op.sourcepos,
                                  op.varname_hint)
        return self._cmp_generic_optimization(op, arg0, arg1)

    def optimize_gt(self, op):
        arg0, arg1 = self._args(op)
        if arg0 is arg1:
            return BooleanConstant.FALSE
        if arg0.resolved_type is not types.Int():
            try:
                arg0, arg1 = self._extract_number(arg0), self._extract_number(arg1)
            except NoMatchException:
                pass
            else:
                return BooleanConstant.frombool(arg0.number > arg1.number)
        else:
            try:
                arg0, arg1 = self._extract_machineint(arg0), self._extract_machineint(arg1)
            except NoMatchException:
                pass
            else:
                return self.newop("@gt", [arg0, arg1], op.resolved_type, op.sourcepos,
                                  op.varname_hint)
        return self._cmp_generic_optimization(op, arg0, arg1)

    def _cmp_generic_optimization(self, op, arg0, arg1):
        assert arg0.resolved_type is arg1.resolved_type
        if arg0.resolved_type is not types.MachineInt():
            if (isinstance(arg0, Operation) and arg0.name == "@unsigned_bv_wrapped_res"
                    and isinstance(arg1, Operation) and arg1.name == "@unsigned_bv_wrapped_res"):
                newname = "@" + self._builtinname(op.name).lstrip("@") + "_unsigned64"
                return self.newop(newname, [arg0.args[0],
                                            arg1.args[0]],
                                  op.resolved_type,
                                  op.sourcepos,
                                  op.varname_hint)
        add_components, sub_components, constant, useful = self._add_sub_extract_components(arg0, arg1)
        if useful:
            if len(add_components) + len(sub_components) <= 1 and isinstance(constant, int):
                if sub_components:
                    assert not add_components
                    rhs, = sub_components
                    if rhs.resolved_type is types.MachineInt():
                        lhs = MachineIntConstant(constant)
                    else:
                        assert rhs.resolved_type is types.Int()
                        lhs = IntConstant(constant)
                elif add_components:
                    assert not sub_components
                    lhs, = add_components
                    if lhs.resolved_type is types.MachineInt():
                        rhs = MachineIntConstant(-constant)
                    else:
                        assert lhs.resolved_type is types.Int()
                        rhs = IntConstant(-constant)
                else:
                    lhs = MachineIntConstant(constant)
                    rhs = MachineIntConstant(0)
                assert rhs.resolved_type is lhs.resolved_type
                name = op.name
                if rhs.resolved_type is types.MachineInt() and not name.startswith("@"):
                    name = "@" + self._builtinname(name)
                return self.newop(
                    name,
                    [lhs, rhs],
                    op.resolved_type,
                    op.sourcepos,
                    op.varname_hint
                )

    def optimize_lteq(self, op):
        arg0, arg1 = self._args(op)
        if arg0 is arg1:
            return BooleanConstant.TRUE
        if arg0.resolved_type is not types.Int():
            try:
                arg0, arg1 = self._extract_number(arg0), self._extract_number(arg1)
            except NoMatchException:
                pass
            else:
                return BooleanConstant.frombool(arg0.number <= arg1.number)
        else:
            if (isinstance(arg0, Operation) and
                    arg0.name == "@add_unsigned_bv64_unsigned_bv64_wrapped_res" and
                    isinstance(arg1, Operation) and
                    arg1.name == "@add_unsigned_bv64_unsigned_bv64_wrapped_res"):
                return self.newop(
                    "@lteq_add4_unsigned_bv64",
                    arg0.args + arg1.args,
                    types.Bool(),
                    op.sourcepos,
                    op.varname_hint)
            try:
                arg0, arg1 = self._extract_machineint(arg0), self._extract_machineint(arg1)
            except NoMatchException:
                pass
            else:
                return self.newop("@lteq", [arg0, arg1], op.resolved_type, op.sourcepos,
                                  op.varname_hint)
        return self._cmp_generic_optimization(op, arg0, arg1)

    def optimize_gteq(self, op):
        arg0, arg1 = self._args(op)
        if arg0 is arg1:
            return BooleanConstant.TRUE
        if arg0.resolved_type is not types.Int():
            try:
                arg0, arg1 = self._extract_number(arg0), self._extract_number(arg1)
            except NoMatchException:
                pass
            else:
                return BooleanConstant.frombool(arg0.number >= arg1.number)
        else:
            try:
                arg0, arg1 = self._extract_machineint(arg0), self._extract_machineint(arg1)
            except NoMatchException:
                pass
            else:
                return self.newop("@gteq", [arg0, arg1], op.resolved_type, op.sourcepos,
                                  op.varname_hint)
        return self._cmp_generic_optimization(op, arg0, arg1)

    def optimize_vector_subrange_o_i_i(self, op):
        arg0, arg1, arg2 = self._args(op)

        try:
            arg1 = self._extract_number(arg1)
            arg2 = self._extract_number(arg2)
        except NoMatchException:
            pass
        else:
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
        add_components, sub_components, constant, useful = self._add_sub_extract_components(arg1, arg2)
        if not add_components and not sub_components and isinstance(constant, int):
            return self.newop(
                "@slice_o_i_i",
                [arg0, arg2, MachineIntConstant(constant + 1)],
                types.GenericBitVector(),
                op.sourcepos,
                op.varname_hint,
            )


    def optimize_vector_subrange_o_i_i_unwrapped_res(self, op):
        arg0, arg1, arg2 = self._args(op)
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        return self.newop(
             "@vector_subrange_fixed_bv_i_i",
             [arg0, arg1, arg2],
             op.resolved_type,
             op.sourcepos,
             op.varname_hint,
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
        if isinstance(arg0, Operation) and arg0.name == "@zeros_i":
            return self.newop("@ones_i", [arg0.args[0]], arg0.resolved_type, arg0.sourcepos)
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
        return self.newop(
            "@bitvector_concat_bv_gbv_wrapped_res",
            [arg0, MachineIntConstant(typ0.width), arg1],
            types.GenericBitVector(),
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_bitvector_concat_bv_gbv_wrapped_res(self, op):
        arg0, arg1, arg2 = self._args(op)
        if isinstance(arg2, Operation) and arg2.name == "@zeros_i":
            subarg0, = self._args(arg2)
            if not isinstance(subarg0, Constant):
                return self.newop(
                    "@bitvector_concat_bv_n_zeros_wrapped_res",
                    [arg0, arg1, subarg0],
                    types.GenericBitVector(),
                    op.sourcepos,
                    op.varname_hint,
                )
        arg2, typ2 = self._extract_smallfixedbitvector(arg2)
        reswidth = self._extract_machineint(arg1).number + typ2.width
        if reswidth > 64:
            return
        res = self.newcast(
            self.newop(
                "@bitvector_concat_bv_bv",
                [arg0, MachineIntConstant(typ2.width), arg2],
                types.SmallFixedBitVector(reswidth),
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type,
        )
        return res

    def optimize_vector_update_subrange_o_i_i_o(self, op):
        arg0, arg1, arg2, arg3 = self._args(op)
        assert op.resolved_type is types.GenericBitVector()
        arg3, typ3 = self._extract_smallfixedbitvector(arg3)

        # super specific for arm
        typ0 = None
        if (self.graph.has_loop and isinstance(arg0, Phi) and
                len(arg0.prevvalues) == 2 and op in arg0.prevvalues):
            index = 1 - arg0.prevvalues.index(op)
            init = arg0.prevvalues[index]
            try:
                _, typ0 = self._extract_smallfixedbitvector(init)
            except NoMatchException:
                pass
            else:
                arg0 = self.newcast(arg0, typ0)
        if typ0 is None:
            arg0, typ0 = self._extract_smallfixedbitvector(arg0)
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

    def optimize_vector_slice_o_i_i_unwrapped_res(self, op):
        arg0, arg1, arg2 = self._args(op)
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        return self.newop(
            "@slice_fixed_bv_i_i",
            [arg0, arg1, arg2],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
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
        if arg0.number > 64 or arg0.number < 1:
            return
        resconst = SmallBitVectorConstant(0, types.SmallFixedBitVector(arg0.number))
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
            if isinstance(arg0, Operation) and arg0.name == '@ones_i':
                arg0arg0, = self._args(arg0)
                return self.newop(
                    "@ones_zero_extended_unwrapped_res",
                    [arg0arg0, arg1],
                    op.resolved_type,
                    op.sourcepos,
                    op.varname_hint,
                )
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

    ADD_OPS = {"add_int", "@add_o_i_wrapped_res", "@add_i_i_wrapped_res", "@add_i_i_must_fit"}
    SUB_OPS = {"sub_int", "@sub_o_i_wrapped_res", "@sub_i_o_wrapped_res", "@sub_i_i_wrapped_res", "@sub_i_i_must_fit"}

    def _add_sub_opt_reduce_additions(self, components):
        while len(components) > 1:
            arg1, arg0 = components.pop(), components.pop()
            if arg0.resolved_type is types.MachineInt() and arg1.resolved_type is types.MachineInt():
                opname = "@add_i_i_wrapped_res"
            elif arg0.resolved_type is types.MachineInt() and arg1.resolved_type is types.Int():
                opname = "@add_o_i_wrapped_res"
                arg0, arg1 = arg1, arg0
            elif arg0.resolved_type is types.Int() and arg1.resolved_type is types.MachineInt():
                opname = "@add_o_i_wrapped_res"
            else:
                assert arg0.resolved_type is types.Int() and arg1.resolved_type is types.Int()
                name = "@add_int"
            newop = self.newop(opname, [arg0, arg1], types.Int())
            components.append(newop)

    def _add_sub_extract_components(self, addop, subopt=None):
        todo = [(addop, 1)]
        if subopt:
            todo.append((subopt, -1))
        add_components = []
        sub_components = []
        constant = None
        useful = 0
        while todo:
            val, polarity = todo.pop()
            if isinstance(val, (MachineIntConstant, IntConstant)):
                if constant is None:
                    constant = val.number * polarity
                else:
                    constant += val.number * polarity
                    useful += 1
            elif type(val) is Operation and (val.name in self.ADD_OPS or val.name in self.SUB_OPS):
                arg0, arg1 = self._args(val)
                todo.append((arg0, polarity))
                if val.name in self.SUB_OPS:
                    polarity = -polarity
                todo.append((arg1, polarity))
            else:
                if polarity == 1:
                    add_components.append(val)
                else:
                    sub_components.append(val)
            if len(add_components) + len(sub_components) > 50:
                # something is wrong, stop trying to do more
                # see test_inlinability_changes
                while todo:
                    val, polarity = todo.pop()
                    if polarity == 1:
                        add_components.append(val)
                    else:
                        sub_components.append(val)
        index = 0
        while index < len(add_components):
            val = add_components[index]
            if val in sub_components:
                sub_components.remove(val)
                del add_components[index]
                useful += 1
                continue
            index += 1
        return add_components, sub_components, int(constant) if constant is not None else None, useful

    def _general_add_sub_opt(self, op):
        name = self._builtinname(op.name)
        assert name in self.ADD_OPS or name in self.SUB_OPS
        add_components, sub_components, constant, useful = self._add_sub_extract_components(op)
        if not useful:
            return None
        if useful > 4:
            import pdb;pdb.set_trace()

        # now we need to reconstruct the result
        if constant:
            constant = int(constant)
            if isinstance(constant, int):
                add_components.append(MachineIntConstant(constant))
            else:
                add_components.append(IntConstant(constant))
        self._add_sub_opt_reduce_additions(add_components)
        self._add_sub_opt_reduce_additions(sub_components)
        if not add_components:
            res = MachineIntConstant(0)
        else:
            res, = add_components
        if sub_components:
            arg0 = res
            arg1, = sub_components
            if arg0.resolved_type is types.MachineInt() and arg1.resolved_type is types.MachineInt():
                opname = "@sub_i_i_wrapped_res"
            elif arg0.resolved_type is types.MachineInt() and arg1.resolved_type is types.Int():
                opname = "@sub_i_o_wrapped_res"
            elif arg0.resolved_type is types.Int() and arg1.resolved_type is types.MachineInt():
                opname = "@sub_o_i_wrapped_res"
            else:
                assert arg0.resolved_type is types.Int() and arg1.resolved_type is types.Int()
                name = "@sub_int"
            res = self.newop(opname, [arg0, arg1], types.Int())
        if res.resolved_type != op.resolved_type:
            if res.resolved_type is types.MachineInt():
                return self._make_int64_to_int(res)
            else:
                if res.name == "@add_i_i_wrapped_res":
                    self._need_dead_code_removal = True
                    return self.newop(
                        "@add_i_i_must_fit",
                        res.args[:],
                        op.resolved_type
                    )
                elif res.name == "@sub_i_i_wrapped_res":
                    self._need_dead_code_removal = True
                    return self.newop(
                        "@sub_i_i_must_fit",
                        res.args[:],
                        op.resolved_type
                    )
                return self._make_int_to_int64(res)
        return res

    def _extract_unsigned_bv64(self, value):
        if (isinstance(value, Operation) and
                value.name == "@unsigned_bv_wrapped_res" and
                isinstance(value.args[1], MachineIntConstant) and
                value.args[1].number == 64):
            return value.args[0]
        elif isinstance(value, IntConstant):
            if 0 <= value.number < 2 ** 64:
                return SmallBitVectorConstant(r_uint(value.number), types.SmallFixedBitVector(64))
        elif isinstance(value, MachineIntConstant):
            if value.number >= 0:
                return SmallBitVectorConstant(r_uint(value.number), types.SmallFixedBitVector(64))
        raise NoMatchException

    @symmetric
    def optimize_add_int(self, op, arg0, arg1):
        try:
            bvarg0 = self._extract_unsigned_bv64(arg0)
            bvarg1 = self._extract_unsigned_bv64(arg1)
        except NoMatchException:
            pass
        else:
            return self.newop("@add_unsigned_bv64_unsigned_bv64_wrapped_res",
                              [bvarg0, bvarg1],
                              op.resolved_type, op.sourcepos, op.varname_hint)

        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
        arg1 = self._extract_machineint(arg1)
        return self.newop(
            "@add_o_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_add_o_i_wrapped_res(self, op):
        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
        arg0, arg1 = self._args(op)
        try:
            bvarg0 = self._extract_unsigned_bv64(arg0)
            bvarg1 = self._extract_unsigned_bv64(arg1)
        except NoMatchException:
            pass
        else:
            return self.newop("@add_unsigned_bv64_unsigned_bv64_wrapped_res",
                              [bvarg0, bvarg1],
                              op.resolved_type, op.sourcepos, op.varname_hint)
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

    @symmetric
    def optimize_add_i_i_wrapped_res(self, op, arg0, arg1):
        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
        try:
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            if self._should_fit_machine_int(op):
                return self._make_int64_to_int(
                    self.newop("@add_i_i_must_fit", op.args, types.MachineInt(),
                               op.sourcepos, op.varname_hint)
                )
        else:
            if arg1.number == 0:
                return self._make_int64_to_int(arg0, op.sourcepos)

    @symmetric
    def optimize_add_i_i_must_fit(self, op, arg0, arg1):
        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
        assert arg0.resolved_type is types.MachineInt()
        arg1 = self._extract_number(arg1)
        if arg1.number == 0:
            return arg0

    def optimize_sub_int(self, op):
        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
        arg0, arg1 = self._args(op)
        try:
            arg1 = self._extract_machineint(arg1)
        except NoMatchException:
            pass
        else:
            return self.newop(
                "@sub_o_i_wrapped_res",
                [arg0, arg1],
                op.resolved_type,
                op.sourcepos,
                op.varname_hint,
            )
        arg0 = self._extract_machineint(arg0)
        return self.newop(
            "@sub_i_o_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint
        )

    def optimize_sub_o_i_wrapped_res(self, op):
        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
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

    def optimize_sub_i_o_wrapped_res(self, op):
        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
        arg0, arg1 = self._args(op)
        arg1 = self._extract_machineint(arg1)
        return self.newop(
            "@sub_i_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_sub_i_i_wrapped_res(self, op):
        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
        if self._should_fit_machine_int(op):
            return self._make_int64_to_int(
                self.newop("@sub_i_i_must_fit", op.args, types.MachineInt(),
                           op.sourcepos, op.varname_hint)
            )
        arg0, arg1 = self._args(op)
        try:
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            if arg1.number == 0:
                return self._make_int64_to_int(arg0, op.sourcepos)

    def optimize_sub_i_i_must_fit(self, op):
        res = self._general_add_sub_opt(op)
        if res is not None:
            return res
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        if arg1.number == 0:
            return arg0

    def optimize_neg_int(self, op):
        arg0, = self._args(op)
        arg0 = self._extract_machineint(arg0)
        return self.newop(
            "@sub_i_i_wrapped_res",
            [MachineIntConstant(0), arg0],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint
        )

    @symmetric
    def optimize_mult_int(self, op, arg0, arg1):
        arg1 = self._extract_machineint(arg1)
        return self.newop(
            "@mult_o_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_mult_o_i_wrapped_res(self, op):
        arg0, arg1 = self._args(op)
        try:
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            arg0 = self._extract_machineint(arg0)
        else:
            if arg1.number == 1:
                return arg0
            if arg1.number == 0:
                return IntConstant(0)
            if arg1.number & (arg1.number - 1) == 0:
                # power of two
                exponent = arg1.number.bit_length() - 1
                assert 1 << exponent == arg1.number
                return self.newop(
                    "@shl_int_o_i",
                    [arg0, MachineIntConstant(exponent)],
                    op.resolved_type,
                    op.sourcepos,
                    op.varname_hint,
                )
            if arg1.number < 0:
                return None
            if self._should_fit_machine_int(op):
                # if a * x fits into a machine int, and x > 1, then a also fits
                # into a machine int
                arg0 = self._make_int_to_int64(arg0)
            else:
                return None
        return self.newop(
            "@mult_i_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    @symmetric
    def optimize_mult_i_i_wrapped_res(self, op, arg0, arg1):
        try:
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            if arg1.number == 1:
                return self._make_int64_to_int(arg0)
            if arg1.number == 0:
                return IntConstant(0)
            if is_pow_2(arg1.number):
                # power of two
                exponent = shift_amount(arg1.number)
                assert 1 << exponent == arg1.number
                return self.newop(
                    "@shl_int_i_i_wrapped_res",
                    [arg0, MachineIntConstant(exponent)],
                    op.resolved_type,
                    op.sourcepos,
                    op.varname_hint,
                )
        if self._should_fit_machine_int(op):
            return self._make_int64_to_int(
                self.newop("@mult_i_i_must_fit", op.args, types.MachineInt(),
                           op.sourcepos, op.varname_hint)
            )

    @symmetric
    def optimize_mult_i_i_must_fit(self, op, arg0, arg1):
        try:
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            if arg1.number == 1:
                return arg0
            if arg1.number == 0:
                return MachineIntConstant(0)
            if is_pow_2(arg1.number):
                # power of two
                exponent = shift_amount(arg1.number)
                assert 1 << exponent == arg1.number
                return self.newop(
                    "@shl_int_i_i_must_fit",
                    [arg0, MachineIntConstant(exponent)],
                    op.resolved_type,
                    op.sourcepos,
                    op.varname_hint,
                )

    def optimize_ediv_int(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        if arg1.number == 1:
            return arg0
        try:
            arg0 = self._extract_number(arg0)
        except NoMatchException:
            pass
        else:
            if arg0.number >= 0 and arg1.number > 0:
                return IntConstant(arg0.number // arg1.number)
        if arg1.number > 1 and isinstance(arg1.number, int):
            arg0 = self._extract_machineint(arg0)
            return self._make_int64_to_int(
                self.newop(
                    "@ediv_int_i_ipos",
                    [arg0, MachineIntConstant(arg1.number)],
                    types.MachineInt(),
                    op.sourcepos,
                    op.varname_hint,
                )
            )

    def optimize_shl_int_o_i(self, op):
        arg0, arg1 = self._args(op)
        arg0 = self._extract_machineint(arg0)
        return self.newop(
            "@shl_int_i_i_wrapped_res",
            [arg0, arg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_shl_int_i_i_wrapped_res(self, op):
        if self._should_fit_machine_int(op):
            arg0, arg1 = self._args(op)
            return self._make_int64_to_int(self.newop(
                "@shl_int_i_i_must_fit",
                [arg0, arg1],
                types.MachineInt(),
                op.sourcepos,
                op.varname_hint,
            ))

    def optimize_pow2_i(self, op):
        if self._should_fit_machine_int(op):
            arg0, = self._args(op)
            return self._make_int64_to_int(self.newop(
                "@shl_int_i_i_must_fit",
                [MachineIntConstant(1), arg0],
                types.MachineInt(),
                op.sourcepos,
                op.varname_hint,
            ))

    def optimize_tdiv_int(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        if arg1.number == 1:
            return arg0
        try:
            arg0 = self._extract_number(arg0)
        except NoMatchException:
            pass
        else:
            if arg0.number >= 0 and arg1.number > 0:
                return IntConstant(arg0.number // arg1.number)
        if isinstance(arg0, Operation) and arg0.name == "@unsigned_bv_wrapped_res":
            if arg1.number >= 2 and is_pow_2(arg1.number):
                shift = shift_amount(arg1.number)
                return self._make_int64_to_int(
                    self.newop(
                        "@unsigned_bv64_rshift_int_result",
                        [self._get_op_replacement(arg0.args[0]), MachineIntConstant(shift)],
                        types.MachineInt()
                    )
                )
            #import pdb;pdb.set_trace()
        if arg1.number not in (0, -1) and isinstance(arg1.number, int):
            arg0 = self._extract_machineint(arg0)
            return self._make_int64_to_int(
                self.newop(
                    "@tdiv_int_i_i",
                    [arg0, MachineIntConstant(arg1.number)],
                    types.MachineInt(),
                    op.sourcepos,
                    op.varname_hint,
                )
            )

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

    def optimize_get_slice_int_i_o_i_unwrapped_res(self, op):
        arg0, arg1, arg2 = self._args(op)
        try:
            arg1 = self._extract_machineint(arg1)
        except NoMatchException:
            pass
        else:
            return self.newop(
                "@get_slice_int_i_i_i",
                [arg0, arg1, arg2],
                op.resolved_type,
                op.sourcepos,
                op.varname_hint,
            )
        # rather arm specific
        arg0 = self._extract_number(arg0)
        if arg0.number != 64:
            return
        arg2 = self._extract_number(arg2)
        if arg2.number != 0:
            return
        if not isinstance(arg1, Operation) or arg1.name != "@shl_int_i_i_wrapped_res":
            return
        lshift_arg0, lshift_arg1 = self._args(arg1)
        lshift_arg1 = self._extract_number(lshift_arg1)
        if lshift_arg1.number <= 0:
            return
        if not isinstance(lshift_arg0, Operation) or lshift_arg0.name != "@unsigned_bv64_rshift_int_result":
            return
        address, shift = self._args(lshift_arg0)
        shift = self._extract_number(shift)
        if shift.number != lshift_arg1.number or lshift_arg1.number > 32:
            return
        mask = ~((r_uint(1) << lshift_arg1.number) - 1)
        assert op.resolved_type is types.SmallFixedBitVector(64)
        return self.newop(
            "@and_vec_bv_bv",
            [address, SmallBitVectorConstant(mask, types.SmallFixedBitVector(64))],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
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

    def optimize_shift_bits_left(self, op):
        arg0, arg1 = self._args(op)
        intarg1 = self.newop(
            "@sail_unsigned",
            [arg1],
            types.Int())
        return self.newop(
            "@shiftl",
            [arg0, intarg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint)

    def optimize_shift_bits_right(self, op):
        arg0, arg1 = self._args(op)
        intarg1 = self.newop(
            "@sail_unsigned",
            [arg1],
            types.Int())
        return self.newop(
            "@shiftr",
            [arg0, intarg1],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint)

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
        if isinstance(op.args[0].resolved_type, types.Vec):
            res = self.newop(
                    "@vec_length_unwrapped_res",
                    [arg0],
                    types.MachineInt(),
                    op.sourcepos,
                    op.varname_hint,
            )
            return self._make_int64_to_int(res, op.sourcepos)
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
            SmallBitVectorConstant(0 * num.number, types.SmallFixedBitVector(num.number)),
            op.resolved_type,
            op.sourcepos,
            op.varname_hint,
        )

    def optimize_sail_truncate_o_i(self, op):
        arg0, arg1 = self._args(op)
        num = self._extract_number(arg1)
        try:
            arg0, typ = self._extract_smallfixedbitvector(arg0)
        except NoMatchException:
            if num.number > 64:
                return
            newop = self.newop(
                "@truncate_unwrapped_res",
                [arg0, num],
                types.SmallFixedBitVector(num.number),
                op.sourcepos,
                op.varname_hint
            )
        else:
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

    def optimize_truncate_unwrapped_res(self, op):
        arg0, arg1 = self._args(op)
        if not isinstance(arg0, Operation) or not arg0.name == '@bitvector_concat_bv_gbv_wrapped_res':
            return
        arg1 = self._extract_number(arg1)
        if arg1.number > 64:
            return
        subarg0, subarg1, subarg2 = self._args(arg0)
        return self.newcast(
            self.newop(
                "@bitvector_concat_bv_gbv_truncate_to",
                [subarg0, subarg1, subarg2, arg1],
                types.SmallFixedBitVector(arg1.number),
                arg0.sourcepos,
                arg0.varname_hint,
            ),
            op.resolved_type
        )

    def optimize_bitvector_concat_bv_gbv_truncate_to(self, op):
        # very cheriot-specific :`-)
        arg0, arg1, arg2, arg3 = self._args(op)
        if not isinstance(arg2, Operation) or not arg2.name == '@bitvector_concat_bv_n_zeros_wrapped_res':
            return
        subarg0, subarg1, subarg2 = self._args(arg2)
        return self.newop(
            "@bitvector_concat_bv_bv_n_zeros_truncate",
            [arg0, arg1, subarg0, subarg1, subarg2, arg3],
            op.resolved_type,
            op.sourcepos,
            op.varname_hint
        )

    @symmetric
    def optimize_eq_bool(self, op, arg0, arg1):
        if not isinstance(arg0, BooleanConstant):
            raise NoMatchException
        if arg0.value:
            return arg1
        else:
            return self.newop(
                "@not",
                [arg1],
                types.Bool(),
                op.sourcepos,
                op.varname_hint
            )

    @symmetric
    def optimize_eq(self, op, arg0, arg1):
        if arg0 is arg1:
            return BooleanConstant.TRUE
        if isinstance(arg0, MachineIntConstant) and isinstance(arg1, MachineIntConstant):
            return BooleanConstant.frombool(arg0.number == arg1.number)
        if isinstance(arg0, EnumConstant) and isinstance(arg1, EnumConstant):
            return BooleanConstant.frombool(arg0.variant == arg1.variant)
        if isinstance(arg0, Constant) and isinstance(arg1, Constant):
            import pdb;pdb.set_trace()
        if isinstance(arg1, MachineIntConstant) and arg1.number == 0 and isinstance(arg0, Operation) and arg0.name == '@signed_bv':
            arg0arg0, typ = self._extract_smallfixedbitvector(arg0.args[0])
            return self.newop(
                "@eq_bits_bv_bv", [arg0arg0, SmallBitVectorConstant(0x0, typ)],
                op.resolved_type,
                op.sourcepos,
                op.varname_hint)

    def optimize_not(self, op):
        arg0, = self._args(op)
        if isinstance(arg0, BooleanConstant):
            return BooleanConstant.frombool(not arg0.value)
        if isinstance(arg0, Operation) and arg0.name == '@not':
            return self._args(arg0)[0]
        if op.name != "@not": # standardize only, don't change all the time
            return self.newop(
                "@not",
                [arg0],
                types.Bool(),
                op.sourcepos,
                op.varname_hint
            )

    optimize_not_ = optimize_not

    def optimize_replicate_bits_o_i(self, op):
        arg0, arg1 = self._args(op)
        arg1 = self._extract_number(arg1)
        if arg1.number == 1:
            return arg0

        arg0, typ = self._extract_smallfixedbitvector(arg0)
        newwidth = typ.width * arg1.number
        if newwidth > 64:
            return
        return self.newcast(
            self.newop(
                "@replicate_bv_i_i", [arg0, MachineIntConstant(typ.width),
                                      arg1],
                types.SmallFixedBitVector(newwidth),
                op.sourcepos,
                op.varname_hint
            ),
            op.resolved_type
        )

    def optimize_zupdate_fbits(self, op):
        arg0, arg1, arg2 = self._args(op)
        if arg0.resolved_type.width == 1:
            assert arg1.number == 0
            return arg2

    def optimize_vector_update_o_i_o(self, op):
        arg0, arg1, arg2 = self._args(op)
        if arg0.resolved_type is not types.GenericBitVector():
            return
        assert arg2.resolved_type is types.SmallFixedBitVector(1)
        arg0, typ = self._extract_smallfixedbitvector(arg0)
        if isinstance(arg1, MachineIntConstant):
            if not 0 <= arg1.number < typ.width:
                return None # usually means unreachable
        return self.newcast(
            self.newop(
                '$zupdate_fbits',
                [arg0, arg1, arg2],
                typ,
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type
        )

    def optimize_platform_read_mem_o_o_o_i(self, op, isfetch=False):
        arg0, arg1, arg2, arg3 = self._args(op)
        arg2, typ = self._extract_smallfixedbitvector(arg2)
        arg3 = self._extract_number(arg3)
        if arg3.number not in (1, 2, 4, 8):
            return None
        if isinstance(arg1, MachineIntConstant):
            assert arg1.number == typ.width
        assert typ.width in (32, 64)
        return self.newcast(
            self.newop(
                "@fast_read_mem_i_bv_i_isfetch",
                [arg1, arg2, arg3, BooleanConstant.frombool(isfetch)],
                types.SmallFixedBitVector(arg3.number * 8),
                op.sourcepos,
                op.varname_hint,
            ),
            op.resolved_type
        )
    optimize_read_mem_o_o_o_i = optimize_platform_read_mem_o_o_o_i

    def optimize_read_mem_ifetch_o_o_o_i(self, op):
        return self.optimize_platform_read_mem_o_o_o_i(op, isfetch=True)

    def optimize_UINT64_C(self, op):
        arg0, = self._args(op)
        assert isinstance(arg0, MachineIntConstant)
        assert arg0.number == 0
        return GenericBitVectorConstant(bitvector.from_ruint(0, r_uint(0)))

    def optimize_monomorphize(self, op):
        arg0, = self._args(op)
        return arg0

    def optimize_branch_announce(self, op):
        return UnitConstant.UNIT

    def optimize_instr_announce(self, op):
        return UnitConstant.UNIT

    def optimize_packed_field_cast_smallfixedbitvector(self, op):
        arg0, arg1 = self._args(op)
        if not isinstance(arg1, FieldAccess):
            if arg1.name == "@pack_smallfixedbitvector":
                assert arg0.number == arg1.args[0].number
                return arg1.args[1]
            import pdb;pdb.set_trace()

    def optimize_packed_field_int_to_int64(self, op):
        arg0, = self._args(op)
        if not isinstance(arg0, FieldAccess) and isinstance(arg0, Operation):
            if arg0.name == "@pack_machineint":
                return arg0.args[0]

@repeat
def inline(graph, codegen):
    # don't add blocks to functions that are already really big and need to be
    # split later
    #if graph.name == "zhex_bits_2_forwards":
    #    import pdb;pdb.set_trace()
    really_huge_function = graph.has_more_than_n_blocks(1000)
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
                elif not really_huge_function and not subgraph.has_loop and subgraph is not graph:
                    # complicated case
                    _inline(graph, codegen, block, index, subgraph)
                    remove_empty_blocks(graph, codegen)
                    join_blocks(graph, codegen)
                    remove_double_exception_check(graph, codegen)
                    return True
            elif isinstance(op, Operation):
                codegen.inline_dependencies[op.name].add(graph)
            index += 1
    if changed:
        remove_double_exception_check(graph, codegen)
    return changed

def _inline(graph, codegen, block, index, subgraph, add_comment=True):
    # split current block
    op = block.operations[index]
    newblock = block.split(index, keep_op=False)
    if add_comment:
        block.operations.append(Comment("inlined %s" % subgraph.name))
    start_block, return_block = copy_blocks(subgraph, op)
    block.next = Goto(start_block)
    res, = return_block.operations
    assert return_block.next is None
    return_block.next = Goto(newblock)
    graph.replace_op(op, return_block.operations[0])
    _remove_unreachable_phi_prevvalues(graph)
    simplify_phis(graph, codegen)

def copy_ops(op, subgraph):
    assert isinstance(subgraph.startblock.next, Return)
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
    patch_phis = []
    for block in topo_order_best_attempt(graph):
        ops = block.copy_operations(replacements, blocks, patch_phis)
        newblock = blocks[block]
        newblock.operations = ops
        todo_next.append((block.next, newblock))

    for op, index, arg in patch_phis:
        op.prevvalues[index] = replacements[arg]

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
            newblock.next = Raise(replacements.get(next.kind, next.kind), next.sourcepos)
        else:
            assert 0, "unreachable"

    return blocks[graph.startblock], returnblock

def should_inline(graph, model_specific_should_inline=None):
    if model_specific_should_inline:
        res = model_specific_should_inline(graph.name)
        if res is not None:
            return res
    if graph.has_loop:
        return False
    blocks = list(graph.iterblocks())
    if any([isinstance(block.next, Return) and block.next.value is None for block in blocks]):
        return False
    for op, _ in graph.iterblockops():
        if isinstance(op, Operation) and op.name == graph.name:
            return False # no recursive inlining
    number_ops = len([op for block in blocks for op in block.operations])
    return len(blocks) <= 4 and number_ops < 25


def topo_order(graph):
    order = list(graph.iterblocks()) # dfs

    # do a (slightly bad) topological sort
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


def topo_order_best_attempt(graph):
    # supports loops too
    if not graph.has_loop:
        return topo_order(graph)

    order = list(graph.iterblocks()) # dfs

    incoming = defaultdict(set)
    for block in order:
        for nextblock in block.next.next_blocks():
            incoming[nextblock].add(block)
    no_incoming = [order[0]]
    incoming = dict(incoming)
    assert set(incoming).union({graph.startblock}) == set(order)
    result = []
    while 1:
        while no_incoming:
            assert set(incoming).union(result).union(no_incoming) == set(order)
            block = no_incoming.pop()
            assert block not in incoming
            assert block not in result
            result.append(block)
            for child in set(block.next.next_blocks()):
                if child in incoming:
                    incoming[child].discard(block)
                    if not incoming[child]:
                        no_incoming.append(child)
                        del incoming[child]
        if not incoming:
            break
        # we have a loop. just pick a block
        for block in order:
            if block in incoming:
                no_incoming.append(block)
                del incoming[block]
                break
    # check result
    assert set(result) == set(order)
    assert len(set(result)) == len(result)
    return result

@repeat
def remove_double_exception_check(graph, codegen):
    def is_exception_check(block, index):
        op = block.operations[index]
        if not isinstance(op, GlobalRead):
            return False
        if op.name != "have_exception":
            return False
        if not isinstance(block.next, ConditionalGoto):
            return False
        if block.next.booleanvalue is not op:
            return False
        return True
    def is_exceptional_return(block):
        if block.operations:
            return False
        if not isinstance(block.next, Return):
            return False
        return isinstance(block.next.value, DefaultValue)

    def find_next_op(block):
        while not block.operations:
            if not isinstance(block.next, Goto):
                return None, None
            block = block.next.target
        for i, op in enumerate(block.operations):
            if not isinstance(op, (Phi, Comment)):
                return block, i
        return None, None

    exception_checks = []
    for block in graph.iterblocks():
        if not block.operations:
            continue
        if not is_exception_check(block, -1):
            continue
        exception_checks.append(block)

    for block in exception_checks:
        nextblock, index = find_next_op(block.next.truetarget)
        if nextblock is None:
            continue
        if not is_exception_check(nextblock, index):
            continue
        if len(nextblock.operations) - 1 != index:
            continue
        exceptional_return = nextblock.next.truetarget
        if not is_exceptional_return(exceptional_return):
            continue
        block.next.truetarget = exceptional_return
        nextblock.next.booleanvalue = BooleanConstant.FALSE
        remove_if_true_false(graph, codegen)
        remove_empty_blocks(graph, codegen)
        join_blocks(graph, codegen)
        remove_dead(graph, codegen)
        return True
    for block in exception_checks:
        nextblock, index = find_next_op(block.next.falsetarget)
        if nextblock is None:
            continue
        if not is_exception_check(nextblock, index):
            continue
        if len(nextblock.operations) - 1 != index:
            continue
        if not isinstance(block.next.truetarget.next, Return):
            continue
        nextblock.next.booleanvalue = BooleanConstant.FALSE
        remove_if_true_false(graph, codegen)
        remove_empty_blocks(graph, codegen)
        join_blocks(graph, codegen)
        remove_dead(graph, codegen)
        return True
    return False

def find_anticipated_casts(graph):
    blocks = topo_order_best_attempt(graph)
    blocks.reverse()
    # set entries are tuples (value, targettype)
    anticipated_casts = {}

    for block in blocks:
        # go over the successors and intersect
        assert block not in anticipated_casts
        s = anticipated_casts[block] = set()
        # we ignore the raise blocks when intersecting - they are internal
        # errors and would lead to crashes. this can lead to cast errors in
        # situation where a later Raise would have ended the emulation anyway,
        # but that's fine
        next_blocks = [nextblock for nextblock in block.next.next_blocks()
                       if not isinstance(nextblock.next, Raise)]

        if next_blocks and all(next_block in anticipated_casts for next_block in next_blocks):
            s.update(anticipated_casts[next_blocks[0]])
            for next_block in next_blocks[1:]:
                s.intersection_update(anticipated_casts[next_block])
        # add casts happening *within* the block
        for op in block.operations:
            if isinstance(op, Cast) and isinstance(op.resolved_type, types.SmallFixedBitVector):
                s.add((op.args[0], op.resolved_type))
            if isinstance(op, Operation) and op.name == INT_TO_INT64_NAME:
                s.add((op.args[0], op.resolved_type))
    return anticipated_casts


@repeat
def cse_global_reads(graph, codegen):
    # very simple forward load-after-load pass
    def leaves_globals_alone(op):
        if not op.can_have_side_effects:
            return True
        if isinstance(op, Comment):
            return True
        if op.name == "@not":
            return True
        if op.name == "@eq":
            return True
        name = op.name.lstrip("@$")
        name = codegen.builtin_names.get(name, name)
        return type(op) is Operation and name in supportcode.purefunctions

    replacements = {}
    available = {} # block -> block -> prev_op

    entrymap = graph.make_entrymap()
    blocks = topo_order_best_attempt(graph)
    for block in blocks:
        available_in_block = {}
        prev_blocks = entrymap[block]
        if prev_blocks:
            if len(prev_blocks) == 1:
                available_in_block = available[prev_blocks[0]].copy()
            else:
                # intersection of what's available in the previous blocks
                for key, prev_op in available[prev_blocks[0]].iteritems():
                    if not all(available.get(prev_block, {}).get(key, None) == prev_op
                               for prev_block in prev_blocks):
                        continue
                    available_in_block[key] = prev_op
        available[block] = available_in_block
        for index, op in enumerate(block.operations):
            if isinstance(op, GlobalRead):
                key = (op.name, op.resolved_type)
            elif isinstance(op, GlobalWrite):
                key = (op.name, op.resolved_type)
                available_in_block[key] = op.args[0]
                continue
            elif not leaves_globals_alone(op):
                available_in_block.clear()
                continue
            else:
                continue
            if key in available_in_block:
                block.operations[index] = None
                replacements[op] = available_in_block[key]
            else:
                available_in_block[key] = op
    if replacements:
        for block in blocks:
            block.operations = [op for op in block.operations if op is not None]
        while 1:
            # XXX do them in one go somehow
            changed = graph.replace_ops(replacements)
            if not changed:
                break
        return True
    return False

@repeat
def sink_allocate(graph, codegen):
    changed = False
    for block in graph.iterblocks():
        newoperations = []
        alloc = None
        count = 0
        for op in block.operations:
            if isinstance(op, Allocate):
                count += 1
        if count != 1:
            continue
        for index, op in enumerate(block.operations):
            if (alloc is None and 
                    isinstance(op, Allocate) and
                    index + 1 < len(block.operations) and
                    op not in block.operations[index + 1].getargs()):
                alloc = op
                continue
            if alloc in op.getargs():
                newoperations.append(alloc)
                newoperations.extend(block.operations[index:])
                changed = True
                break
            newoperations.append(op)
        else:
            if alloc:
                newoperations.append(alloc)
        if changed:
            block.operations = newoperations
    return changed

@repeat
def partial_allocation_removal(graph, codegen):
    # local removal only so far
    def escape(value):
        if value not in virtuals_in_block:
            return value
        fields = virtuals_in_block.pop(value)
        fieldvalues = []
        typ = value.resolved_type
        if isinstance(value, StructConstruction) or not typ.tuplestruct:
            for name in typ.names:
                if name in fields:
                    fieldvalue = escape(fields[name])
                else:
                    fieldvalue = DefaultValue(typ.internalfieldtyps[name])
                fieldvalues.append(fieldvalue)
            op = StructConstruction(typ.name, fieldvalues, typ, value.sourcepos)
            newoperations.append(op)
        else:
            op = Allocate(typ, value.sourcepos)
            newoperations.append(op)
            for name in typ.names:
                if name in fields:
                    newoperations.append(FieldWrite(name, [op, escape(fields[name])]))
        replacements[value] = op
        return op
    def get_repr(value):
        while value in replacements:
            value = replacements[value]
        return value

    replacements = {}
    changes = False
    for block in graph.iterblocks():
        virtuals_in_block = {}
        newoperations = []
        for index, op in enumerate(block.operations):
            if isinstance(op, Allocate):
                virtuals_in_block[op] = {}
                continue
            if isinstance(op, StructConstruction):
                fields = {}
                for fieldname, value in zip(op.resolved_type.names, op.args):
                    fields[fieldname] = value
                virtuals_in_block[op] = fields
                continue
            if isinstance(op, StructCopy):
                obj = get_repr(op.args[0])
                if obj in virtuals_in_block:
                    fields = virtuals_in_block[obj].copy()
                    virtuals_in_block[op] = fields
                    continue
                # copy of a non-virtual struct. we could indiscriminantly turn
                # it into a StructConstruction, but that seems potentially
                # bloaty. Instead, check whether it's used in the next op of
                # the current block and only do that if yes.
                if index + 1 < len(block.operations) and op in block.operations[index + 1].getargs():
                    typ = op.resolved_type
                    fields = {}
                    for fieldname in typ.names:
                        fieldvalue = FieldAccess(fieldname, [op.args[0]], typ.internalfieldtyps[fieldname])
                        newoperations.append(fieldvalue)
                        fields[fieldname] = fieldvalue
                    virtuals_in_block[op] = fields
                    continue
            if isinstance(op, FieldWrite):
                obj = get_repr(op.args[0])
                if obj in virtuals_in_block:
                    virtuals_in_block[obj][op.name] = op.args[1]
                    continue
            if isinstance(op, FieldAccess):
                obj = get_repr(op.args[0])
                if obj in virtuals_in_block:
                    assert op.resolved_type is virtuals_in_block[obj][op.name].resolved_type
                    replacements[op] = virtuals_in_block[obj][op.name]
                    continue
            if isinstance(op, GlobalWrite) and op.name in codegen.all_registers:
                obj = get_repr(op.args[0])
                if obj in virtuals_in_block:
                    typ = op.args[0].resolved_type
                    fields = virtuals_in_block[obj]
                    target = GlobalRead(op.name, typ)
                    newoperations.append(target)
                    for name in typ.names:
                        if name in fields:
                            fieldvalue = escape(fields[name])
                        else:
                            fieldvalue = DefaultValue(typ.internalfieldtyps[name])
                        newoperations.append(FieldWrite(name, [target, fieldvalue]))
                    continue

            for arg in op.getargs():
                escape(arg)
            newoperations.append(op)
        if isinstance(block.next, Return):
            escape(block.next.value)
        else:
            while virtuals_in_block:
                value = next(virtuals_in_block.iterkeys())
                escape(value)

        changes = changes or len(newoperations) != len(block.operations)
        block.operations = newoperations
    if replacements:
        while 1:
            res = graph.replace_ops(replacements)
            if not res:
                break
    return changes


@repeat
def cse_field_reads(graph, codegen):
    # very simple forward load-after-load and load-after-store pass for struct fields
    def leaves_structs_alone(op):
        if not op.can_have_side_effects:
            return True
        if isinstance(op, Comment):
            return True
        if op.name == "@not":
            return True
        if op.name == "@eq":
            return True
        name = op.name.lstrip("@$")
        name = codegen.builtin_names.get(name, name)
        return type(op) is Operation and name in supportcode.purefunctions

    replacements = {}
    available = {} # block -> block -> prev_op

    entrymap = graph.make_entrymap()
    blocks = topo_order_best_attempt(graph)
    for block in blocks:
        available_in_block = {} # (type, fieldname) -> (source, result)
        prev_blocks = entrymap[block]
        if prev_blocks:
            if len(prev_blocks) == 1:
                available_in_block = available[prev_blocks[0]].copy()
            else:
                # intersection of what's available in the previous blocks
                for key, val in available[prev_blocks[0]].iteritems():
                    if not all(available.get(prev_block, {}).get(key, None) == val
                               for prev_block in prev_blocks):
                        continue
                    available_in_block[key] = val
        available[block] = available_in_block
        for index, op in enumerate(block.operations):
            if isinstance(op, FieldAccess):
                key = (op.args[0].resolved_type, op.name)
                if key in available_in_block:
                    source, res = available_in_block[key]
                    if source is op.args[0]:
                        replacements[op] = res
                        block.operations[index] = None
                        continue
                available_in_block[key] = (op.args[0], op)
            elif isinstance(op, FieldWrite):
                key = (op.args[0].resolved_type, op.name)
                available_in_block[key] = (op.args[0], op.args[1])
                continue
            elif isinstance(op, StructConstruction):
                for arg, typ, name in zip(op.args, op.resolved_type.typs, op.resolved_type.names):
                    available_in_block[op.resolved_type, name] = (op, arg)
            elif not leaves_structs_alone(op):
                available_in_block.clear()
                continue
            else:
                continue
    if replacements:
        for block in blocks:
            block.operations = [op for op in block.operations if op is not None]
        while 1:
            # XXX do them in one go somehow
            changed = graph.replace_ops(replacements)
            if not changed:
                break
        return True
    return False

# ____________________________________________________________
# dominator-tree based algorithms

def compute_dominators(G):
    return _compute_dominators(G)[0]

def _compute_dominators(G):
    preds = G.make_entrymap()
    start = G.startblock
    # initialize
    dominators = {}
    for node in preds:
        dominators[node] = set(preds)
    dominators[start] = {start}

    # fixpoint
    changed = True
    while changed:
        changed = False
        for node in preds:
            if node == start:
                continue
            dom = set(preds).intersection(*[dominators[x] for x in preds[node]])
            dom.add(node)
            if dom != dominators[node]:
                changed = True
                dominators[node] = dom
    return dominators, preds

def dominatees(G):
    dom, pred = _compute_dominators(G)
    res = defaultdict(set)
    for block, doms in dom.iteritems():
        for dominator_block in doms:
            res[dominator_block].add(block)
    return dict(res)

def find_backedges(G):
    # a backedge is an edge where the target node dominates the source node
    assert G.has_loop
    dom = compute_dominators(G)
    for source, target in G.iteredges():
        if target in dom[source]:
            yield source, target

def propagate_equality(graph, codegen):
    changed = False
    # maps blocks -> values -> [(intconst, prevblock)]
    int_constants_and_sources = defaultdict(lambda : defaultdict(list))

    entrymap = None
    dom = None
    for block in topo_order_best_attempt(graph):
        if not isinstance(block.next, ConditionalGoto):
            continue
        value = block.next.booleanvalue
        if (isinstance(value, Operation) and value.name == "@eq" and
                value.args[0].resolved_type is types.MachineInt()):
            intarg, intconst = value.args
            if not isinstance(intconst, MachineIntConstant):
                intarg, intconst = intconst, intarg
            if not isinstance(intconst, MachineIntConstant):
                continue
            targetblock = block.next.truetarget
            targetvalues = int_constants_and_sources[targetblock]
            targetvalues[intarg].append((intconst, block))
            if entrymap is None:
                entrymap = graph.make_entrymap()
            if len(targetvalues[intarg]) != len(entrymap[targetblock]):
                continue
            # try to see whether we use the int in the target block
            if dom is None:
                dom = dominatees(graph)
            ops = []
            for furtherblock in dom[targetblock]:
                for op in furtherblock.operations:
                    if intarg in op.getargs():
                        ops.append(op)
            if not ops:
                continue
            prevvalues, prevblocks = zip(*targetvalues[intarg])
            if len(prevvalues) == 1:
                newvalue = prevvalues[0]
            else:
                newvalue = Phi(list(prevblocks), list(prevvalues), types.MachineInt())
                targetblock.operations.insert(0, newvalue)
            d = {intarg: newvalue}
            for op in ops:
                res = op.replace_ops(d)
                assert res
            changed = True
    return changed
