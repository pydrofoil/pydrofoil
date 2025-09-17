import collections
from pydrofoil import absinterp, ir, types
from pydrofoil.test.test_ir import compare, check_optimize
from pydrofoil.test.util import MockCodegen


def test_rangecheck_constant():
    x = ir.Argument("x", types.Int())
    block_f = ir.Block()
    i1 = block_f.emit(
        ir.RangeCheck,
        "$rangecheck",
        [
            ir.IntConstant(7),
            ir.IntConstant(5),
            ir.IntConstant(15),
            ir.StringConstant("Argument 'x' of function 'f'"),
        ],
        types.Unit(),
        None,
        None,
    )
    res = block_f.emit(
        ir.Operation, "add_int", [x, ir.IntConstant(1)], types.Int()
    )
    block_f.next = ir.Return(res)
    graph_f = ir.Graph("f", [x], block_f)
    absinterp.optimize_with_range_info(graph_f, MockCodegen({"f": graph_f}))
    compare(
        graph_f,
        """
x = Argument('x', Int())
block0 = Block()
i1 = block0.emit(Operation, '@add_o_i_wrapped_res', [x, MachineIntConstant(1)], Int(), None, None)
block0.next = Return(i1, None)
graph = Graph('f', [x], block0)
""",
    )


def test_rangecheck_int64_to_int():
    zlen = ir.Argument("zlen", types.MachineInt())
    block0 = ir.Block()
    i2 = block0.emit(
        ir.Operation, "int64_to_int", [zlen], types.Int(), None, None
    )
    i3 = block0.emit(
        ir.RangeCheck,
        "$rangecheck",
        [
            i2,
            ir.IntConstant(8),
            ir.IntConstant(64),
            ir.StringConstant(
                "Argument 'zlen' of function 'zsigned_saturation'"
            ),
        ],
        types.Unit(),
        None,
        None,
    )
    block0.next = ir.Return(zlen, None)
    graph = ir.Graph("f", [zlen], block0)
    absinterp.optimize_with_range_info(graph, MockCodegen({"f": graph}))
    compare(
        graph,
        """
zlen = Argument('zlen', MachineInt())
block0 = Block()
i1 = block0.emit(Operation, 'int64_to_int', [zlen], Int(), None, None)
i2 = block0.emit(Operation, 'zz5izDzKz5i64', [i1], MachineInt(), None, None)
i3 = block0.emit(RangeCheck, '$rangecheck', [i2, IntConstant(8), IntConstant(64), StringConstant("Argument 'zlen' of function 'zsigned_saturation'")], Unit(), None, None)
block0.next = Return(zlen, None)
graph = Graph('f', [zlen], block0)""",
    )


def test_optimize_neg_int():
    zlen = ir.Argument("zlen", types.MachineInt())
    block0 = ir.Block()
    i1 = block0.emit(
        ir.Operation, "int64_to_int", [zlen], types.Int(), None, None
    )
    i2 = block0.emit(
        ir.RangeCheck,
        "$rangecheck",
        [
            zlen,
            ir.IntConstant(-64),
            ir.IntConstant(64),
            ir.StringConstant(
                "Argument 'zlen' of function 'zsigned_saturation'"
            ),
        ],
        types.Unit(),
        None,
        None,
    )
    i3 = block0.emit(ir.Operation, "neg_int", [i1], types.Int(), None, None)
    i4 = block0.emit(
        ir.Operation, "int_to_int64", [i3], types.MachineInt(), None, None
    )
    block0.next = ir.Return(i4, None)
    graph = ir.Graph("f", [zlen], block0)
    check_optimize(
        graph,
        """
zlen = Argument('zlen', MachineInt())
block0 = Block()
i1 = block0.emit(RangeCheck, '$rangecheck', [zlen, IntConstant(-64), IntConstant(64), StringConstant("Argument 'zlen' of function 'zsigned_saturation'")], Unit(), None, None)
i2 = block0.emit(Operation, '@sub_i_i_must_fit', [MachineIntConstant(0), zlen], MachineInt(), None, None)
block0.next = Return(i2, None)
graph = Graph('f', [zlen], block0)
""",
    )


def test_optimize_abs_int():
    zlen = ir.Argument("zlen", types.MachineInt())
    block0 = ir.Block()
    i1 = block0.emit(
        ir.Operation, "int64_to_int", [zlen], types.Int(), None, None
    )
    i2 = block0.emit(
        ir.RangeCheck,
        "$rangecheck",
        [
            zlen,
            ir.IntConstant(-64),
            ir.IntConstant(64),
            ir.StringConstant(
                "Argument 'zlen' of function 'zsigned_saturation'"
            ),
        ],
        types.Unit(),
        None,
        None,
    )
    i3 = block0.emit(ir.Operation, "abs_int", [i1], types.Int(), None, None)
    i4 = block0.emit(
        ir.Operation, "int_to_int64", [i3], types.MachineInt(), None, None
    )
    block0.next = ir.Return(i4, None)
    graph = ir.Graph("f", [zlen], block0)
    check_optimize(
        graph,
        """
zlen = Argument('zlen', MachineInt())
block0 = Block()
i1 = block0.emit(RangeCheck, '$rangecheck', [zlen, IntConstant(-64), IntConstant(64), StringConstant("Argument 'zlen' of function 'zsigned_saturation'")], Unit(), None, None)
i2 = block0.emit(Operation, '@abs_i_must_fit', [zlen], MachineInt(), None, None)
block0.next = Return(i2, None)
graph = Graph('f', [zlen], block0)
""",
    )


def test_optimize_max_int():
    arg_a = ir.Argument("arg_a", types.MachineInt())
    arg_b = ir.Argument("arg_b", types.MachineInt())
    block0 = ir.Block()
    i1 = block0.emit(
        ir.Operation, "int64_to_int", [arg_a], types.Int(), None, None
    )
    i2 = block0.emit(
        ir.Operation, "int64_to_int", [arg_b], types.Int(), None, None
    )
    i4 = block0.emit(
        ir.Operation, "max_int", [i1, i2], types.Int(), None, None
    )
    i5 = block0.emit(
        ir.Operation, "int_to_int64", [i4], types.MachineInt(), None, None
    )
    block0.next = ir.Return(i5, None)
    graph = ir.Graph("f", [arg_a, arg_b], block0)
    check_optimize(
        graph,
        """
arg_a = Argument('arg_a', MachineInt())
arg_b = Argument('arg_b', MachineInt())
block0 = Block()
i2 = block0.emit(Operation, '@max_i_i_must_fit', [arg_a, arg_b], MachineInt(), None, None)
block0.next = Return(i2, None)
graph = Graph('f', [arg_a, arg_b], block0)
""",
    )


def test_optimize_min_int():
    arg_a = ir.Argument("arg_a", types.MachineInt())
    arg_b = ir.Argument("arg_b", types.MachineInt())
    block0 = ir.Block()
    i1 = block0.emit(
        ir.Operation, "int64_to_int", [arg_a], types.Int(), None, None
    )
    i2 = block0.emit(
        ir.Operation, "int64_to_int", [arg_b], types.Int(), None, None
    )
    i4 = block0.emit(
        ir.Operation, "min_int", [i1, i2], types.Int(), None, None
    )
    i5 = block0.emit(
        ir.Operation, "int_to_int64", [i4], types.MachineInt(), None, None
    )
    block0.next = ir.Return(i5, None)
    graph = ir.Graph("f", [arg_a, arg_b], block0)
    check_optimize(
        graph,
        """
arg_a = Argument('arg_a', MachineInt())
arg_b = Argument('arg_b', MachineInt())
block0 = Block()
i2 = block0.emit(Operation, '@min_i_i_must_fit', [arg_a, arg_b], MachineInt(), None, None)
block0.next = Return(i2, None)
graph = Graph('f', [arg_a, arg_b], block0)
""",
    )
