import sys
from collections import defaultdict

from pydrofoil import ir, types

MININT = -sys.maxint-1
MAXINT = sys.maxint


class Range(object):
    def __init__(self, low=None, high=None):
        # both can be None
        self.low = low
        self.high = high
        if low is not None and high is not None:
            assert low <= high

    @staticmethod
    def fromconst(value):
        return Range(value, value)

    def __repr__(self):
        return "Range(%r, %r)" % (self.low, self.high)

    def __eq__(self, other):
        return self.low == other.low and self.high == other.high

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash((self.low, other.low))

    def contains(self, number):
        if self.low is not None and not self.low <= number:
            return False
        if self.high is not None and not number <= self.high:
            return False
        return True

    def isconstant(self):
        return self.low is not None and self.low == self.high

    def fits_machineint(self):
        return (self.low is not None and self.high is not None and
                self.low >= MININT and self.high <= MAXINT)

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

    def union(self, other):
        low = high = None
        if self.low is not None and other.low is not None:
            low = min(self.low, other.low)
        if self.high is not None and other.high is not None:
            high = max(self.high, other.high)
        return Range(low, high)

    def le(self, other):
        if self.high is not None and other.low is not None:
            if self.high <= other.low:
                return TRUE
        if self.low is not None and other.high is not None:
            if other.high < self.low:
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

    def make_le_const(self, const):
        return Range(self.low, const)

    def make_ge_const(self, const):
        return Range(const, self.high)

UNBOUNDED = Range(None, None)
MACHINEINT = Range(MININT, MAXINT)
BOOL = Range(0, 1)
TRUE = Range(1, 1)
FALSE = Range(0, 0)


def analyze(graph, view=False):
    absinterp = AbstractInterpreter(graph)
    res = absinterp.analyze()
    if view:
        absinterp.view()
    return res

class AbstractInterpreter(object):
    def __init__(self, graph):
        self.graph = graph
        self.values = {} # block -> value -> Range

    def view(self):
        from rpython.translator.tool.make_dot import DotGen
        from dotviewer import graphclient
        import pytest
        dotgen = DotGen('G')
        print_varnames = self.graph._dot(dotgen)
        for block in self.graph.iterblocks():
            extrainfoid = "info" + str(id(block))
            if block not in self.values:
                dotgen.emit_node(
                    extrainfoid,
                    shape="box",
                    fillcolor="orange",
                    label="NOT REACHED"
                )
            else:
                current_values = self.values[block]
                res = []
                for op, r in current_values.iteritems():
                    if op in block.operations:
                        continue
                    if r == UNBOUNDED or (op.resolved_type is types.Bool() and r == BOOL) or (op.resolved_type is types.MachineInt() and r == MACHINEINT):
                        continue
                    res.append("%s: %r" % (op._repr(print_varnames), r))
                if res:
                    res.append("")
                for index, op in enumerate(block.operations):
                    if op not in current_values:
                        continue
                    r = current_values[op]
                    if r == UNBOUNDED or (op.resolved_type is types.Bool() and r == BOOL) or (op.resolved_type is types.MachineInt() and r == MACHINEINT):
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
        ir.GraphPage(dotgen.generate(target=None), print_varnames, self.graph.args).display()

    def analyze(self):
        startblock_values = {}
        for arg in self.graph.args:
            startblock_values[arg] = UNBOUNDED
        self.values[self.graph.startblock] = startblock_values

        for block in ir.topo_order(self.graph):
            self.current_block = block
            if block not in self.values:
                # unreachable
                continue
            self.current_values = self.values[block]
            self.analyze_block(block)
            self.analyze_link(block)
        return self.values

    def analyze_link(self, block):
        if isinstance(block.next, ir.Goto):
            self._merge_values(self.current_values, block.next.target)
        elif isinstance(block.next, ir.ConditionalGoto):
            # first, check if one of the paths is dead
            cond = self._bounds(block.next.booleanvalue)
            if cond == TRUE:
                import pdb;pdb.set_trace()
                xxx
            elif cond == FALSE:
                self._merge_values(self.current_values, block.next.falsetarget)
                return
            truevalues, falsevalues = self.analyze_condition(block.next.booleanvalue)
            self._merge_values(truevalues, block.next.truetarget)
            self._merge_values(falsevalues, block.next.falsetarget)
        elif isinstance(block.next, (ir.Return, ir.Raise)):
            pass
        else:
            assert 0, "unreachable"

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
            if op.resolved_type in (types.MachineInt(), types.Int(), types.Bool()):
                meth = getattr(self, "analyze_" + op.__class__.__name__, self.analyze_default)
                res = meth(op)
                assert res is not None
                self.current_values[op] = res

    def analyze_default(self, op):
        if op.resolved_type is types.Bool():
            return BOOL
        if op.resolved_type is types.MachineInt():
            return MACHINEINT
        return UNBOUNDED

    def analyze_Operation(self, op):
        name = op.name.lstrip("@$")
        meth = getattr(self, "analyze_" + name, self.analyze_default)
        return meth(op)

    def _bounds(self, op):
        if isinstance(op, ir.BooleanConstant):
            if op.value:
                return TRUE
            return FALSE
        if isinstance(op, (ir.MachineIntConstant, ir.IntConstant)):
            return Range.fromconst(op.number)
        if op.resolved_type not in (types.Int(), types.MachineInt(), types.Bool()):
            return None
        return self.current_values[op]

    def _argbounds(self, op):
        return [self._bounds(arg) for arg in op.args]

    def analyze_lteq(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.le(arg1)

    def analyze_gteq(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.ge(arg1)

    def analyze_add(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.add(arg1)
    analyze_add_i_i_must_fit = analyze_add
    analyze_add_i_i_wrapped_res = analyze_add
    analyze_add_o_i_wrapped_res = analyze_add

    def analyze_sub(self, op):
        arg0, arg1 = self._argbounds(op)
        return arg0.sub(arg1)
    analyze_sub_i_i_must_fit = analyze_sub
    analyze_sub_i_i_wrapped_res = analyze_sub

    def analyze_int_to_int64(self, op):
        return self._bounds(op.args[0])

    def analyze_unsigned_bv(self, op):
        _, arg1 = self._argbounds(op)
        if not arg1.isconstant():
            return
        return Range(0, 2**arg1.low - 1)

    def analyze_signed_bv(self, op):
        _, arg1 = self._argbounds(op)
        if not arg1.isconstant():
            return
        exponent = arg1.low - 1
        return Range(-(2 ** exponent), 2 ** exponent - 1)

    # conditions

    def analyze_condition(self, op):
        truevalues = self.current_values.copy()
        falsevalues = self.current_values.copy()
        if op.name == "@lteq":
            arg0, arg1 = self._argbounds(op)
            if arg0.isconstant():
                truevalues[op.args[1]] = arg1.make_ge_const(arg0.low)
            if arg1.isconstant():
                truevalues[op.args[0]] = arg0.make_le_const(arg1.low)
        else:
            print "UNKNOWN CONDITION", op
        return truevalues, falsevalues


class IntOpOptimizer(ir.LocalOptimizer):
    def __init__(self, graph, codegen, values, *args, **kwargs):
        ir.LocalOptimizer.__init__(self, graph, codegen, *args, **kwargs)
        self.values = values
        self.current_values = None

    def _should_fit_machine_int(self, op):
        if self.current_values:
            value = self.current_values.get(op, None)
            if value is not None and value.fits_machineint():
                return True
        return ir.LocalOptimizer._should_fit_machine_int(self, op)

    def optimize_block(self, block):
        if block not in self.values: # dead
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
        if value == TRUE:
            return ir.BooleanConstant.TRUE
        if value == FALSE:
            return ir.BooleanConstant.FALSE

    def _optimize_op(self, block, index, op):
        if op.resolved_type is types.Bool():
            res = self._known_boolean_value(op)
            if res is not None:
                return res
        return ir.LocalOptimizer._optimize_op(self, block, index, op)

    def _extract_machineint(self, arg, *args, **kwargs):
        if arg.resolved_type is types.Int():
            value = self.current_values.get(arg, None)
            if value is not None and value.fits_machineint():
                return self._make_int_to_int64(arg)
        return ir.LocalOptimizer._extract_machineint(self, arg, *args, **kwargs)

def optimize_with_range_info(graph, codegen):
    values = analyze(graph)
    opt = IntOpOptimizer(graph, codegen, values)
    return opt.optimize()
