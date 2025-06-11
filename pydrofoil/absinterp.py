import sys
from collections import defaultdict
import typing

from pydrofoil import ir, makecode, types

MININT = -sys.maxint - 1
MAXINT = sys.maxint


def int_c_div(x, y):
    r = x // y
    if x ^ y < 0 and x % y != 0:
        r += 1
    return r


class Range(object):
    def __init__(self, low=None, high=None):
        # both can be None
        self.low = low  # type: int | None
        self.high = high  # type: int | None
        if low is not None and high is not None:
            assert low <= high

    @staticmethod
    def fromconst(value):
        return Range(value, value)

    def is_bounded(self):
        return self.low is not None and self.high is not None

    def __repr__(self):
        return "Range(%r, %r)" % (self.low, self.high)

    def __eq__(self, other):
        return self.low == other.low and self.high == other.high

    def __ne__(self, other):
        return not self == other

    def contains(self, number):
        if self.low is not None and not self.low <= number:
            return False
        if self.high is not None and not number <= self.high:
            return False
        return True

    def contains_range(self, other):
        # type: (Range) -> bool
        if self.low is not None:
            if other.low is None:
                return False
            if other.low < self.low:
                return False
        if self.high is not None:
            if other.high is None:
                return False
            if other.high > self.high:
                return False
        return True

    def isconstant(self):
        return self.low is not None and self.low == self.high

    def fits_machineint(self):
        return self.is_bounded() and self.low >= MININT and self.high <= MAXINT

    def add(self, other):
        low = high = None
        if self.low is not None and other.low is not None:
            low = self.low + other.low
        if self.high is not None and other.high is not None:
            high = self.high + other.high
        return Range(low, high)

    def neg(self):
        low = high = None
        if self.low is not None:
            high = -self.low
        if self.high is not None:
            low = -self.high
        return Range(low, high)

    def sub(self, other):
        return self.add(other.neg())

    def mul(self, other):
        if self.is_bounded() and other.is_bounded():
            values = [
                self.low * other.low,
                self.high * other.low,
                self.low * other.high,
                self.high * other.high,
            ]
            return Range(min(values), max(values))
        if self.low is not None and other.low is not None:
            if self.low >= 0 and other.low >= 0:
                return Range(self.low * other.low, None)
        if self.high is not None and other.high is not None:
            if self.high < 0 and other.high < 0:
                return Range(self.high * other.high, None)
        return UNBOUNDED

    def tdiv(self, other):
        # very minimal for now
        if other.low is not None and other.low >= 1:
            if other.high is not None and self.is_bounded():
                values = [
                    int_c_div(self.low, other.low),
                    int_c_div(self.high, other.low),
                    int_c_div(self.low, other.high),
                    int_c_div(self.high, other.high),
                ]
                return Range(min(values), max(values))
            # division by positive number cannot change the sign
            if self.low is not None and self.low >= 0:
                return Range(0, self.high)
            if self.high is not None and self.high <= 0:
                return Range(self.low, 0)
        return UNBOUNDED

    def ediv(self, other):
        # very minimal for now
        if other.low is not None and other.low >= 1:
            # division by positive number cannot change the sign
            if self.low is not None and self.low >= 0:
                return Range(0, self.high)
        return UNBOUNDED

    def lshift(self, other):
        if (
            self.is_bounded()
            and other.is_bounded()
            and 0 <= other.low
            and other.high <= 64
        ):
            values = [
                self.low << other.low,
                self.high << other.low,
                self.low << other.high,
                self.high << other.high,
            ]
            return Range(min(values), max(values))
        if self.low is not None and self.low >= 0 and other.low is not None:
            if 0 <= other.low <= 64:
                return Range(self.low << other.low, None)
            return Range(self.low, None)
        return UNBOUNDED

    def rshift(self, other):
        if (
            self.is_bounded()
            and other.is_bounded()
            and 0 <= other.low
            and other.high <= sys.maxint
        ):
            values = [
                self.low >> other.low,
                self.high >> other.low,
                self.low >> other.high,
                self.high >> other.high,
            ]
            return Range(min(values), max(values))
        return UNBOUNDED

    def union(self, other):
        low = high = None
        if self.low is not None and other.low is not None:
            low = min(self.low, other.low)
        if self.high is not None and other.high is not None:
            high = max(self.high, other.high)
        return Range(low, high)

    @staticmethod
    def union_many(ranges):
        # type: (Iterable[Range]) -> Range
        ranges_iter = iter(ranges)
        try:
            res = next(ranges_iter)
        except StopIteration:
            raise ValueError("No ranges given")
        for range in ranges_iter:
            res = res.union(range)
        return res

    def le(self, other):
        if self.high is not None and other.low is not None:
            if self.high <= other.low:
                return TRUE
        if self.low is not None and other.high is not None:
            if other.high < self.low:
                return FALSE
        return BOOL

    def lt(self, other):
        if self.high is not None and other.low is not None:
            if self.high < other.low:
                return TRUE
        if self.low is not None and other.high is not None:
            if other.high <= self.low:
                return FALSE
        return BOOL

    def ge(self, other):
        if self.low is not None and other.high is not None:
            if self.low >= other.high:
                return TRUE
        if self.high is not None and other.low is not None:
            if other.low > self.high:
                return FALSE
        return BOOL

    def gt(self, other):
        if self.low is not None and other.high is not None:
            if self.low > other.high:
                return TRUE
        if self.high is not None and other.low is not None:
            if other.low >= self.high:
                return FALSE
        return BOOL

    def make_le(self, other):
        if other.high is not None:
            return self.make_le_const(other.high)
        return self

    def make_le_const(self, const):
        if self.high is None or const < self.high:
            return Range(self.low, const)
        return self

    def make_lt(self, other):
        if other.high is not None:
            return self.make_lt_const(other.high)
        return self

    def make_lt_const(self, const):
        return self.make_le_const(const - 1)

    def make_ge(self, other):
        if other.low is not None:
            return self.make_ge_const(other.low)
        return self

    def make_ge_const(self, const):
        if self.low is None or const > self.low:
            return Range(const, self.high)
        return self

    def make_gt(self, other):
        if other.low is not None:
            return self.make_gt_const(other.low)
        return self

    def make_gt_const(self, const):
        return self.make_ge_const(const + 1)


UNBOUNDED = Range(None, None)
MACHINEINT = Range(MININT, MAXINT)
BOOL = Range(0, 1)
TRUE = Range(1, 1)
FALSE = Range(0, 0)

RELEVANT_TYPES = (types.MachineInt(), types.Int(), types.Bool())
INT_TYPES = (types.MachineInt(), types.Int())


def analyze(graph, codegen, view=False):
    # type: (ir.Graph, makecode.Codegen, bool) -> dict[ir.Block, dict[ir.Value, Range]]
    absinterp = AbstractInterpreter(graph, codegen)
    res = absinterp.analyze()
    if view:
        absinterp.view()
    return res


class AbstractInterpreter(object):
    _view = False

    def __init__(self, graph, codegen):
        # type: (ir.Graph, makecode.Codegen) -> None
        self.graph = graph
        self.codegen = codegen
        self.values = {}  # type: dict[ir.Block, dict[ir.Value, Range]]

    def _builtinname(self, name):
        return self.codegen.builtin_names.get(name, name)

    def __repr__(self):
        return "<%s %s>" % (self.__class__.__name__, self.graph)

    def view(self):
        from rpython.translator.tool.make_dot import DotGen
        from dotviewer import graphclient
        import pytest

        dotgen = DotGen("G")
        print_varnames = self.graph._dot(dotgen, self.codegen, None)
        for block in self.graph.iterblocks():
            extrainfoid = "info" + str(id(block))
            if block not in self.values:
                dotgen.emit_node(
                    extrainfoid,
                    shape="box",
                    fillcolor="orange",
                    label="NOT REACHED",
                )
            else:
                current_values = self.values[block]
                res = []
                for op, r in current_values.iteritems():
                    if op in block.operations:
                        continue
                    if (
                        r == UNBOUNDED
                        or (op.resolved_type is types.Bool() and r == BOOL)
                        or (
                            op.resolved_type is types.MachineInt()
                            and r == MACHINEINT
                        )
                    ):
                        continue
                    res.append("%s: %r" % (op._repr(print_varnames), r))
                if res:
                    res.append("")
                for index, op in enumerate(block.operations):
                    if op not in current_values:
                        continue
                    r = current_values[op]
                    if (
                        r == UNBOUNDED
                        or (op.resolved_type is types.Bool() and r == BOOL)
                        or (
                            op.resolved_type is types.MachineInt()
                            and r == MACHINEINT
                        )
                    ):
                        continue
                    res.append("%s: %r" % (op._repr(print_varnames), r))
                if not res:
                    continue
                label = "\\l".join(res)
                dotgen.emit_node(
                    extrainfoid,
                    shape="box",
                    fillcolor="pink",
                    label=label,
                )
            dotgen.emit_edge(extrainfoid, str(id(block)))
        ir.GraphPage(
            dotgen.generate(target=None), print_varnames, self.graph.args
        ).display()

    def analyze(self):
        startblock_values = self._init_argument_bounds()
        self.values[self.graph.startblock] = startblock_values

        for block in ir.topo_order(self.graph):
            self.current_block = block
            if block not in self.values:
                # unreachable
                continue
            self.current_values = self.values[block]
            self.analyze_block(block)
            self.analyze_link(block)
        if self._view:
            import pdb

            pdb.set_trace()

        return self.values

    def _init_argument_bounds(self):
        startblock_values = {}
        for arg in self.graph.args:
            startblock_values[arg] = UNBOUNDED
        return startblock_values

    def analyze_link(self, block):
        if isinstance(block.next, ir.Goto):
            self._merge_values(self.current_values, block.next.target)
        elif isinstance(block.next, ir.ConditionalGoto):
            # first, check if one of the paths is dead
            cond = self._bounds(block.next.booleanvalue)
            if cond is not None and cond == TRUE:
                self._merge_values(self.current_values, block.next.truetarget)
                return
            elif cond is not None and cond == FALSE:
                self._merge_values(self.current_values, block.next.falsetarget)
                return
            truevalues, falsevalues = self.analyze_condition(
                block.next.booleanvalue
            )
            truevalues[block.next.booleanvalue] = TRUE
            falsevalues[block.next.booleanvalue] = FALSE
            self._merge_values(truevalues, block.next.truetarget)
            self._merge_values(falsevalues, block.next.falsetarget)
        elif isinstance(block.next, ir.Return):
            self._analyze_return(block.next)
        elif isinstance(block.next, (ir.Raise, ir.JustStop)):
            pass
        else:
            assert 0, "unreachable"

    def _analyze_return(self, next):
        pass

    def _merge_values(self, values, nextblock):
        if nextblock not in self.values:
            self.values[nextblock] = values.copy()
        else:
            nextblock_values = self.values[nextblock]
            for op, rop in values.iteritems():
                if op in nextblock_values:
                    nextblock_values[op] = rop.union(nextblock_values[op])
                else:
                    nextblock_values[op] = rop

    def analyze_block(self, block):
        for op in block.operations:
            meth = getattr(
                self, "analyze_" + op.__class__.__name__, self.analyze_default
            )
            res = meth(op)
            if op.resolved_type in RELEVANT_TYPES:
                assert res is not None
                self.current_values[op] = res
            else:
                assert res is None

    def analyze_default(self, op):
        if op.resolved_type is types.Bool():
            return BOOL
        if op.resolved_type is types.MachineInt():
            return MACHINEINT
        if op.resolved_type is types.Int():
            return UNBOUNDED
        return None

    def analyze_Operation(self, op):
        name = op.name.lstrip("@$")
        name = self._builtinname(name)
        meth = getattr(self, "analyze_" + name, self.analyze_default)
        return meth(op)

    def analyze_Phi(self, op):
        if op.resolved_type not in RELEVANT_TYPES:
            return
        res = None
        for prevblock, value in zip(op.prevblocks, op.prevvalues):
            b = self._bounds(value, must_exist=False, block=prevblock)
            if res is None:
                res = b
            elif b is not None:
                res = res.union(b)
        return res

    def analyze_RangeCheck(self, op):
        # type: (ir.RangeCheck) -> None
        oldbound, low, high, _ = self._argbounds(op)
        assert low is not None
        assert high is not None
        assert oldbound is not None
        newbound = oldbound.make_ge(low).make_le(high)
        self.current_values[op.args[0]] = newbound
        return None

    def _bounds(self, op, must_exist=True, block=None):
        if isinstance(op, ir.BooleanConstant):
            if op.value:
                return TRUE
            return FALSE
        if isinstance(op, (ir.MachineIntConstant, ir.IntConstant)):
            return Range.fromconst(op.number)
        if op.resolved_type not in RELEVANT_TYPES:
            return None
        if isinstance(op, ir.DefaultValue):
            return self.analyze_default(op)
        block_values = self.current_values
        if block is not None:
            block_values = self.values.get(block, None)
            if not block_values:
                return None
        if not must_exist:
            return block_values.get(op, None)
        return block_values[op]

    def _argbounds(self, op):
        if isinstance(op, ir.Operation):
            l = op.args
        elif isinstance(op, ir.Phi):
            l = op.prevvalues
        else:
            assert isinstance(op, list)
            l = op
        return [self._bounds(arg) for arg in l]

    def analyze_lteq(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.le(arg1)

    def analyze_gteq(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.ge(arg1)

    def analyze_lt(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.lt(arg1)

    def analyze_gt(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.gt(arg1)

    def analyze_add(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.add(arg1)

    analyze_add_int = analyze_add
    analyze_add_i_i_must_fit = analyze_add
    analyze_add_i_i_wrapped_res = analyze_add
    analyze_add_o_i_wrapped_res = analyze_add

    def analyze_sub(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.sub(arg1)

    analyze_sub_int = analyze_sub
    analyze_sub_i_i_must_fit = analyze_sub
    analyze_sub_i_i_wrapped_res = analyze_sub
    analyze_sub_o_i_wrapped_res = analyze_sub
    analyze_sub_i_o_wrapped_res = analyze_sub

    def analyze_int_to_int64(self, op):
        # this is a weird op, it raises if the argument doesn't fit in a
        # machine int. that means afterwards know we that the *argument*
        # has to fit (because otherwise int_to_int64 would have raised)
        res = self._bounds(op.args[0])
        low = res.low
        if low is None or low < MACHINEINT.low:
            low = MACHINEINT.low
        high = res.high
        if high is None or high > MACHINEINT.high:
            high = MACHINEINT.high
        res = self.current_values[op.args[0]] = Range(low, high)
        return res

    def analyze_int64_to_int(self, op):
        return self._bounds(op.args[0])

    def analyze_unsigned_bv(self, op):
        _, arg1 = self._argbounds(op)
        if not arg1.isconstant():
            return
        return Range(0, 2 ** arg1.low - 1)

    def analyze_unsigned_bv_wrapped_res(self, op):
        _, arg1 = self._argbounds(op)
        if not arg1.isconstant():
            return
        return Range(0, 2 ** arg1.low - 1)

    def analyze_signed_bv(self, op):
        _, arg1 = self._argbounds(op)
        if not arg1.isconstant():
            return
        exponent = arg1.low - 1
        return Range(-(2 ** exponent), 2 ** exponent - 1)

    def analyze_mult_int(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.mul(arg1)

    analyze_mult_i_i_wrapped_res = analyze_mult_int
    analyze_mult_i_i_must_fit = analyze_mult_int

    def analyze_tdiv_int(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.tdiv(arg1)

    analyze_tdiv_int_i_i = analyze_tdiv_int

    def analyze_ediv_int(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.ediv(arg1)

    analyze_ediv_int_i_ipos = analyze_ediv_int

    def analyze_lshift(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.lshift(arg1)

    analyze_shl_mach_int = analyze_lshift
    analyze_shl_int_o_i = analyze_lshift
    analyze_shl_int_i_i_wrapped_res = analyze_lshift
    analyze_shl_int_i_i_must_fit = analyze_lshift

    def analyze_pow2_i(self, op):
        (arg0,) = self._argbounds(op)
        return Range(1, 1).lshift(arg0)

    def analyze_rshift(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.rshift(arg1)

    analyze_shr_mach_int = analyze_rshift
    analyze_shr_int_o_i = analyze_rshift

    def analyze_assert_in_range(self, op):  # tests only for now
        arg0, arg1, arg2 = self._argbounds(op)
        assert arg1.isconstant() and arg2.isconstant()
        res = self.current_values[op.args[0]] = Range(arg1.low, arg2.high)
        return res

    def analyze_length_unwrapped_res(self, op):
        return Range(0, None)

    # conditions

    def analyze_condition(self, op):
        truevalues = self.current_values.copy()
        falsevalues = self.current_values.copy()
        if isinstance(op, ir.Operation):
            name = self._builtinname(op.name)
            name = name.lstrip("@")
            args = op.args
            if name == "gteq":
                args = [args[1], args[0]]
                name = "lteq"
            if name == "gt":
                args = [args[1], args[0]]
                name = "lt"

            if name == "lteq":
                arg0, arg1 = self._argbounds(args)
                truevalues[args[0]] = arg0.make_le(arg1)
                truevalues[args[1]] = arg1.make_ge(arg0)
                falsevalues[args[0]] = arg0.make_gt(arg1)
                falsevalues[args[1]] = arg1.make_lt(arg0)
            elif name == "lt":
                arg0, arg1 = self._argbounds(args)
                truevalues[args[0]] = arg0.make_lt(arg1)
                truevalues[args[1]] = arg1.make_gt(arg0)
                falsevalues[args[0]] = arg0.make_ge(arg1)
                falsevalues[args[1]] = arg1.make_le(arg0)
            elif (
                name in ("eq", "eq_int", "eq_int_o_i", "eq_int_i_i")
                and args[0].resolved_type in INT_TYPES
            ):
                arg0, arg1 = self._argbounds(args)
                if arg0.isconstant():
                    truevalues[args[1]] = arg0
                if arg1.isconstant():
                    truevalues[args[0]] = arg1
            else:
                if name != op.name and any(
                    arg.resolved_type in INT_TYPES for arg in op.args
                ):
                    self.codegen.print_debug_msg("UNKNOWN CONDITION", name, op)
        return truevalues, falsevalues


class IntOpOptimizer(ir.LocalOptimizer):
    def __init__(self, graph, codegen, absinterp, *args, **kwargs):
        ir.LocalOptimizer.__init__(self, graph, codegen, *args, **kwargs)
        self.absinterp = absinterp
        self.values = absinterp.values
        self.current_values = None
        self.idom = graph.immediate_dominators()

    def _should_fit_machine_int(self, op):
        if self.current_values:
            value = self.current_values.get(op, None)
            if value is not None and value.fits_machineint():
                return True
        return ir.LocalOptimizer._should_fit_machine_int(self, op)

    def optimize_block(self, block):
        if block not in self.values:  # dead
            self.current_values = None
            return
        self.current_values = self.values[block]
        return ir.LocalOptimizer.optimize_block(self, block)

    def _get_op_replacement(self, arg):
        # bit of a hack, but allows the optimizer to still find the analysis
        # results
        return arg

    def _known_boolean_value(self, op):
        value = self.current_values.get(op, None)
        if value is None:
            return None
        if value == TRUE:
            return ir.BooleanConstant.TRUE
        if value == FALSE:
            return ir.BooleanConstant.FALSE

    def _optimize_op(self, block, index, op):
        if op.resolved_type is types.Bool():
            res = self._known_boolean_value(op)
            if res is not None:
                return res
        elif op.resolved_type is types.Int():
            b = self.current_values.get(op, None)
            if b and b.isconstant():
                return ir.IntConstant(b.low)
        elif op.resolved_type is types.MachineInt():
            b = self.current_values.get(op, None)
            if b and b.isconstant():
                return ir.MachineIntConstant(b.low)
        return ir.LocalOptimizer._optimize_op(self, block, index, op)

    def _insert_int_to_int64_into_right_block(self, arg, targetblock):
        # carefully place the cast into the earliest block, following
        # the immediate domtree
        conversion = ir.Operation("zz5izDzKz5i64", [arg], types.MachineInt())
        while 1:
            if targetblock is self.graph.startblock:
                break
            prevblock = self.idom[targetblock]
            if (
                not self.values.get(prevblock, {})
                .get(arg, UNBOUNDED)
                .fits_machineint()
            ):
                break
            targetblock = prevblock
        self._need_dead_code_removal = True
        if targetblock is self.current_block:
            self.newoperations.append(conversion)
        else:
            targetblock.operations.append(conversion)
        return conversion

    def _extract_machineint(self, arg, *args, **kwargs):
        if arg.resolved_type is types.Int():
            value = self.current_values.get(arg, None)
            if value is not None and value.fits_machineint():
                return self._insert_int_to_int64_into_right_block(
                    arg, self.current_block
                )
        return ir.LocalOptimizer._extract_machineint(
            self, arg, *args, **kwargs
        )

    def _optimize_Phi(self, op, block, index):
        if op.resolved_type is types.Int():
            if all(isinstance(arg, ir.Constant) for arg in op.prevvalues):
                return
            machineints = []
            for prevblock, arg in zip(op.prevblocks, op.prevvalues):
                value = self.values.get(prevblock, {}).get(arg, None)
                if value is not None and value.fits_machineint():
                    arg = self._insert_int_to_int64_into_right_block(
                        arg, prevblock
                    )
                else:
                    return None
                machineints.append(arg)
            return self._make_int64_to_int(
                self.newphi(op.prevblocks, machineints, types.MachineInt())
            )
        return ir.LocalOptimizer._optimize_Phi(self, op, block, index)

    def optimize_tdiv_int(self, op):
        arg0, arg1 = self._args(op)
        arg0 = self._extract_machineint(arg0)
        if self.current_values:
            value = self.current_values.get(arg1, UNBOUNDED)
            if value.fits_machineint() and value.low >= 1:
                return self._make_int64_to_int(
                    self.newop(
                        "@tdiv_int_i_i",
                        [arg0, self._make_int_to_int64(arg1)],
                        types.MachineInt(),
                        op.sourcepos,
                        op.varname_hint,
                    )
                )


def optimize_with_range_info(graph, codegen):
    if graph.has_loop:
        return False
    if graph.has_more_than_n_blocks(1000):
        return False
    absinterp = AbstractInterpreter(graph, codegen)
    absinterp.analyze()
    opt = IntOpOptimizer(graph, codegen, absinterp)
    return opt.optimize()


def default_for_type(typ):
    # type: (types.Type) -> Range
    if typ is types.Bool():
        return BOOL
    elif typ is types.MachineInt():
        return MACHINEINT
    else:
        return UNBOUNDED


def apply_interprocedural_optimizations(codegen):
    # type: (makecode.Codegen) -> None
    location_manager = compute_all_ranges(codegen)
    changed_graphs = rewrite_global_ranges_into_checks(
        location_manager, codegen.all_graph_by_name
    )
    for graph in changed_graphs:
        ir.light_simplify(graph, codegen)


def compute_all_ranges(codegen):
    # type: (makecode.Codegen) -> LocationManager
    todo_set = set(codegen.all_graph_by_name.values())
    location_manager = LocationManager()
    # Initialize ranges with all functions
    for graph in todo_set:
        absinterp = InterproceduralAbstractInterpreter(
            graph, codegen, location_manager
        )
        absinterp.analyze()
    # run to fixpoint
    while todo_set:
        graph = todo_set.pop()
        absinterp = InterproceduralAbstractInterpreter(
            graph, codegen, location_manager
        )
        absinterp.analyze()
        for mod_location in location_manager.find_modified():
            todo_set.update(mod_location.readers)
    return location_manager


def rewrite_global_ranges_into_checks(location_manager, graphs):
    # type: (LocationManager, dict[str, ir.Graph]) -> list[ir.Graph]
    changed_graphs = []
    for graph in graphs.values():
        was_rewritten = _rewrite_graph(location_manager, graph, graphs)
        if was_rewritten:
            changed_graphs.append(graph)
    return changed_graphs


def _rewrite_graph(location_manager, graph, graphs):
    # type: (LocationManager, ir.Graph, dict[str, ir.Graph]) -> bool
    has_changed = False

    # Add checks for argument
    for argument in graph.args:
        if argument.resolved_type not in RELEVANT_TYPES:
            continue
        location = location_manager.get_location_for_argument(argument)

        block = graph.startblock
        assert not block.operations or not isinstance(
            block.operations[0], ir.Phi
        )
        has_changed = _make_check(
            location,
            argument,
            "Argument %s of function %s"
            % (repr(argument.name), repr(graph.name)),
            block,
            0,
            has_changed,
        )

    # Add checks based on operation
    for block in graph.iterblocks():
        # Iterate in reversed order to preserve indices when inserting
        for i, instruction in reversed(list(enumerate(block.operations))):
            if (
                type(instruction) is ir.Operation
                and instruction.name in graphs
            ):
                callee = graphs[instruction.name]
                location = location_manager.get_location_for_result(
                    callee, instruction.resolved_type
                )
                msg = "Result of function %s" % repr(instruction.name)
            elif type(instruction) is ir.FieldAccess:
                arg = instruction.args[0]
                struct_type = arg.resolved_type  # type: types.Struct
                field_name = instruction.name
                location = location_manager.get_location_for_field(
                    struct_type, field_name
                )
                msg = "Access to field %s of struct %s" % (
                    repr(field_name),
                    repr(struct_type.name),
                )
            elif type(instruction) is ir.UnionCast:
                arg = instruction.args[0]
                union_type = arg.resolved_type  # type: types.Union
                variant_name = instruction.name
                location = location_manager.get_location_for_union(
                    union_type, variant_name
                )
                msg = "Variant %s of union %s" % (
                    repr(variant_name),
                    repr(union_type.name),
                )
            else:
                continue
            has_changed = _make_check(
                location, instruction, msg, block, i + 1, has_changed
            )
    return has_changed


def _make_check(location, value, msg, block, index, has_changed_before):
    # type: (Location, ir.Value, str, ir.Block, int, bool) -> bool
    # TODO this is not a good way to access the bound
    bound = location._bound
    # TODO this is not precise enough for certain types like machine ints
    if not bound.is_bounded():
        return has_changed_before

    new_instruction = ir.RangeCheck(
        value,
        ir.IntConstant(bound.low),
        ir.IntConstant(bound.high),
        ir.StringConstant(msg),
    )
    block.operations.insert(index, new_instruction)
    return True


class LocationManager(object):
    def __init__(self):
        self._all_locations = []  # type: list[Location]
        self._argument_locations = {}  # type: dict[ir.Argument, Location]
        self._result_locations = {}  # type: dict[ir.Graph, Location]
        self._field_locations = (
            {}
        )  # type: dict[tuple[types.Struct, str], Location]
        self._union_locations = (
            {}
        )  # type: dict[tuple[types.Union, str], Location]

    def new_location(self, typ):
        # type: (types.Type) -> Location
        loc = Location(self, typ)
        self._all_locations.append(loc)
        return loc

    def find_modified(self):
        # type: () -> frozenset[Location]
        modified = set()
        for location in self._all_locations:
            if location._recompute():
                modified.add(location)
        return frozenset(modified)

    def get_location_for_argument(self, arg):
        # type: (ir.Argument) -> Location
        loc = self._argument_locations.get(arg)
        if loc is None:
            loc = self._argument_locations[arg] = self.new_location(
                arg.resolved_type
            )
        return loc

    def get_location_for_result(self, graph, typ):
        # type: (ir.Graph, types.Type) -> Location
        loc = self._result_locations.get(graph)
        if loc is None:
            loc = self._result_locations[graph] = self.new_location(typ)
        return loc

    def get_location_for_field(self, typ, field_name):
        # type: (types.Struct, str) -> Location
        key = (typ, field_name)
        loc = self._field_locations.get(key)
        if loc is None:
            loc = self._field_locations[key] = self.new_location(
                typ.fieldtyps[field_name]
            )
        return loc

    def get_location_for_union(self, typ, variant_name):
        # type: (types.Union, str) -> Location
        key = (typ, variant_name)
        loc = self._union_locations.get(key)
        if loc is None:
            loc = self._union_locations[key] = self.new_location(
                typ.variants[variant_name]
            )
        return loc


class Location(object):
    """
    A location is a point in the code where multiple sources for bounds come
    together (or are consumed by several consumers).

    Examples:
    - The arguments of a function are locations
    - The return value of a function
    - The values of a specific field of a struct type

    The write and read locations are keyed by a graph.
    TODO do we need more precision for the key?
    """

    def __init__(self, manager, typ):
        # type: (LocationManager, types.Type) -> None
        self._manager = manager
        self._typ = typ
        self._bound = default_for_type(typ)
        self._writes = (
            {}
        )  # type: dict[tuple[ir.Graph, typing.Hashable], Range]
        self.readers = set()  # type: set[ir.Graph]

    def write(self, new_bound, graph, graph_position=None):
        # type: (Range, ir.Graph, typing.Hashable) -> None
        """Give a new value for the bound from source graph."""
        default = default_for_type(self._typ)
        new_bound = new_bound.make_ge(default).make_le(default)
        self._writes[graph, graph_position] = new_bound
        assert self._bound.contains_range(new_bound)

    def read(self, graph):
        self.readers.add(graph)
        return self._bound

    def _recompute(self):
        # type: () -> bool
        if not self._writes:
            return False
        old = self._bound
        self._bound = Range.union_many(self._writes.values())
        assert old.contains_range(self._bound)
        return self._bound != old


class InterproceduralAbstractInterpreter(AbstractInterpreter):
    def __init__(self, graph, codegen, location_manager):
        # type: (ir.Graph, makecode.Codegen, LocationManager) -> None
        super(InterproceduralAbstractInterpreter, self).__init__(
            graph, codegen
        )
        self._location_manager = location_manager

    def analyze_Operation(self, op):
        # type: (ir.Operation) -> Range | None
        if op.is_union_creation():
            return self.analyze_UnionCreation(op)
        if op.name not in self.codegen.all_graph_by_name:
            return super(
                InterproceduralAbstractInterpreter, self
            ).analyze_Operation(op)
        func_graph = self.codegen.all_graph_by_name[op.name]
        arg_bounds = self._argbounds(op)
        # write argument bounds
        for func_arg, bound in zip(func_graph.args, arg_bounds):
            if func_arg.resolved_type not in RELEVANT_TYPES:
                continue
            arg_location = self._location_manager.get_location_for_argument(
                func_arg
            )
            arg_location.write(bound, self.graph, op)
        if op.resolved_type not in RELEVANT_TYPES:
            return None
        # read result bounds
        result_location = self._location_manager.get_location_for_result(
            func_graph, op.resolved_type
        )
        return result_location.read(self.graph)

    def analyze_FieldAccess(self, op):
        if op.resolved_type not in RELEVANT_TYPES:
            return None
        location = self._location_manager.get_location_for_field(
            op.args[0].resolved_type, op.name
        )
        return location.read(self.graph)

    def analyze_FieldWrite(self, op):
        # type: (ir.FieldWrite) -> None
        if op.args[1].resolved_type not in RELEVANT_TYPES:
            return None
        location = self._location_manager.get_location_for_field(
            op.args[0].resolved_type, op.name
        )
        new_bound = self._bounds(op.args[1])
        location.write(new_bound, self.graph, op)
        return None

    def analyze_StructConstruction(self, op):
        # type: (ir.StructConstruction) -> None
        struct_type = op.resolved_type  # type: types.Struct
        for field_value, field_name in zip(op.args, struct_type.names):
            field_type = struct_type.fieldtyps[field_name]
            if field_type not in RELEVANT_TYPES:
                continue
            location = self._location_manager.get_location_for_field(
                struct_type, field_name
            )
            new_bound = self._bounds(field_value)
            location.write(new_bound, self.graph, op)
        return None

    def analyze_UnionCast(self, op):
        # type: (ir.UnionCast) -> Range | None
        if op.resolved_type not in RELEVANT_TYPES:
            return None
        location = self._location_manager.get_location_for_union(
            op.args[0].resolved_type, op.name
        )
        return location.read(self.graph)

    def analyze_UnionCreation(self, op):
        # type: (ir.Operation) -> None
        if op.args[0].resolved_type not in RELEVANT_TYPES:
            return None
        location = self._location_manager.get_location_for_union(
            op.resolved_type, op.name
        )
        (bound,) = self._argbounds(op)
        location.write(bound, self.graph, op)

    def _init_argument_bounds(self):
        startblock_values = {}
        for arg in self.graph.args:
            if arg.resolved_type not in RELEVANT_TYPES:
                continue
            arg_location = self._location_manager.get_location_for_argument(
                arg
            )
            startblock_values[arg] = arg_location.read(self.graph)
        return startblock_values

    def _analyze_return(self, next):
        # type: (ir.Return) -> None
        if next.value.resolved_type not in RELEVANT_TYPES:
            return
        result_location = self._location_manager.get_location_for_result(
            self.graph, next.value.resolved_type
        )
        bound = self._bounds(next.value)
        assert bound is not None
        result_location.write(bound, self.graph, next)
