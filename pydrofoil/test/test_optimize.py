import collections
from pydrofoil import absinterp, ir, types
from pydrofoil.test.test_ir import compare


class MockCodegen(object):
    builtin_names = {
        "zz5izDzKz5i64": "int_to_int64",
        "zz5i64zDzKz5i": "int64_to_int",
    }

    def __init__(self, graphs, entry_points=None):
        self.all_graph_by_name = graphs
        self.inlinable_functions = []
        self.inline_dependencies = collections.defaultdict(set)
        self.method_graphs_by_name = {}
        self.program_entrypoints = entry_points

    def get_effects(self, _):
        pass

    def print_debug_msg(self, _):
        pass


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
