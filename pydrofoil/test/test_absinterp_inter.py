import collections
from pydrofoil import types
from pydrofoil import ir
from pydrofoil.absinterp import (
    Range,
    Location,
    LocationManager,
    analyze,
    apply_interprocedural_optimizations,
    compute_all_ranges,
    rewrite_global_ranges_into_checks,
    MININT,
    MAXINT,
)
from pydrofoil.test.test_ir import compare
import pytest


def test_creation():
    m = LocationManager()
    typ = types.Int()
    l = m.new_location(typ, "")
    graph = object()
    assert not l.read(graph).is_bounded()
    assert graph in l.readers

    typ = types.MachineInt()
    l = m.new_location(typ, "")
    assert l.read(object()).is_bounded()


def test_location_write():
    m = LocationManager()
    typ = types.Int()
    l = m.new_location(typ, "")
    graph = object()
    range = Range(0, 100)
    l.write(new_bound=range, graph=graph)
    assert l._writes[graph, None] == range


def test_location_write_error_checking():
    m = LocationManager()
    typ = types.Int()
    l = m.new_location(typ, "")
    graph = object()
    range = Range(0, 100)
    l._bound = Range(0, 10)
    with pytest.raises(AssertionError):
        l.write(new_bound=range, graph=graph)


def test_location_write_range_too_large_for_type():
    m = LocationManager()
    typ = types.MachineInt()
    l = m.new_location(typ, "")
    graph = object()
    l.write(Range(1, None), object())
    m.find_modified()
    assert l._bound == Range(1, MAXINT)


def test_find_modified():
    m = LocationManager()
    typ = types.Int()
    l1 = m.new_location(typ, "")
    l2 = m.new_location(typ, "")
    l1.write(Range(0, 100), object())
    assert m.find_modified() == {l1}


def test_recompute_limit():
    m = LocationManager()
    typ = types.Int()
    loc = m.new_location(typ, "")
    graph_location = object()
    for i in range(200):
        loc.write(Range(0, 10000 - i), graph_location)
        if i < 100:
            mod = m.find_modified()
            assert mod == {loc}
        else:
            mod = m.find_modified()
            assert not mod
    assert loc._bound == Range(0, 10000 - 99)


def test_recompute_limit_many_graph_locations():
    m = LocationManager()
    typ = types.Int()
    loc = m.new_location(typ, "")
    for i in range(200):
        loc.write(Range(0, i + 1), object())  # writes from 200 locations
    mod = m.find_modified()
    assert mod == {loc}
    assert loc._bound == Range(0, 200)


def _get_graphs_interprocedural_range():
    # Graph that makes x+1
    # Graph that calls with 5 and 10 and one that call with 15
    # Result -> Range(6, 16)
    x = ir.Argument("x", types.Int())
    block_f = ir.Block()
    res = block_f.emit(
        ir.Operation, "add_int", [x, ir.IntConstant(1)], types.Int()
    )
    block_f.next = ir.Return(res)
    graph_f = ir.Graph("f", [x], block_f)

    block_c1 = ir.Block()
    block_c1.emit(ir.Operation, "f", [ir.IntConstant(5)], types.Int())
    block_c1.emit(ir.Operation, "f", [ir.IntConstant(10)], types.Int())
    block_c1.next = ir.Return(ir.UnitConstant.UNIT)
    graph_c1 = ir.Graph("c1", [], block_c1)

    block_c2 = ir.Block()
    block_c2.emit(ir.Operation, "f", [ir.IntConstant(15)], types.Int())
    block_c2.next = ir.Return(ir.UnitConstant.UNIT)
    graph_c2 = ir.Graph("c2", [], block_c2)

    return {"f": graph_f, "c1": graph_c1, "c2": graph_c2}


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


def test_interprocedural_range():
    graphs = _get_graphs_interprocedural_range()
    codegen = MockCodegen(graphs)
    locmanager = compute_all_ranges(codegen)
    loc = locmanager.get_location_for_result(graphs["f"], types.Int())
    assert loc._bound.is_bounded()
    assert loc._bound.low == 6
    assert loc._bound.high == 16


def _get_example_struct_ranges():
    s = ir.Argument(
        "s", types.Struct("S", ("x", "y"), (types.Int(), types.Int()))
    )
    t = ir.Argument(
        "t", types.Struct("T", ("x", "y"), (types.Int(), types.Int()))
    )
    u = ir.Argument(
        "u", types.Struct("U", ("x", "y"), (types.Int(), types.Int()))
    )

    block_f = ir.Block()

    block_f.emit(ir.Operation, "g", [s, t], types.Unit())
    a2 = block_f.emit(ir.FieldAccess, "x", [s], types.Int())
    block_f.next = ir.Return(a2)
    graph_f = ir.Graph("f", [s, t], block_f)

    block_g = ir.Block()
    block_g.emit(ir.FieldWrite, "x", [s, ir.IntConstant(5)], types.Unit())
    block_g.emit(ir.FieldWrite, "x", [s, ir.IntConstant(7)], types.Unit())
    block_g.emit(
        ir.StructConstruction,
        "S",
        [ir.IntConstant(9), ir.IntConstant(100)],
        s.resolved_type,
    )
    block_g.next = ir.Return(ir.UnitConstant.UNIT)
    graph_g = ir.Graph("g", [s, t, u], block_g)

    return {"f": graph_f, "g": graph_g}


def test_struct_ranges():
    graphs = _get_example_struct_ranges()

    codegen = MockCodegen(graphs)
    locmanager = compute_all_ranges(codegen)
    loc = locmanager.get_location_for_result(graphs["f"], types.Int())
    assert loc._bound.is_bounded()
    assert loc._bound.low == 5
    assert loc._bound.high == 9
    s_loc = locmanager.get_location_for_field(
        types.Struct("S", ("x", "y"), (types.Int(), types.Int())), "y"
    )
    assert s_loc._bound.is_bounded()
    assert s_loc._bound.low == 100
    assert s_loc._bound.high == 100


def _get_example_union_ranges():
    u = types.Union("myunion", ("first", "second"), (types.Int(), types.Int()))

    block_f = ir.Block()

    res = block_f.emit(ir.Operation, "g", [], u)
    a2 = block_f.emit(ir.UnionCast, "first", [res], types.Int())
    block_f.next = ir.Return(a2)
    graph_f = ir.Graph("f", [], block_f)

    block_g = ir.Block()
    block_g.emit(ir.Operation, "first", [ir.IntConstant(5)], u)
    ret = block_g.emit(ir.Operation, "first", [ir.IntConstant(10)], u)
    block_g.next = ir.Return(ret)
    graph_g = ir.Graph("g", [], block_g)

    return {"f": graph_f, "g": graph_g}


def test_union_ranges():
    u = types.Union("myunion", ("first", "second"), (types.Int(), types.Int()))
    graphs = _get_example_union_ranges()

    codegen = MockCodegen(graphs)
    locmanager = compute_all_ranges(codegen)
    loc = locmanager.get_location_for_result(graphs["f"], types.Int())
    assert loc._bound.is_bounded()
    assert loc._bound.low == 5
    assert loc._bound.high == 10
    u_loc = locmanager.get_location_for_union(u, "first")
    assert u_loc._bound.is_bounded()
    assert u_loc._bound.low == 5
    assert u_loc._bound.high == 10


def test_rewrite():
    graphs = _get_graphs_interprocedural_range()
    codegen = MockCodegen(graphs)
    locmanager = compute_all_ranges(codegen)
    rewrite_global_ranges_into_checks(locmanager, graphs)
    compare(
        graphs["f"],
        """
x = Argument('x', Int())
block0 = Block()
i1 = block0.emit(RangeCheck, '$rangecheck', [x, IntConstant(5), IntConstant(15), StringConstant("Argument 'x' of function 'f'")], Unit(), None, None)
i2 = block0.emit(Operation, 'add_int', [x, IntConstant(1)], Int(), None, None)
block0.next = Return(i2, None)
graph = Graph('f', [x], block0)""",
    )
    compare(
        graphs["c2"],
        """
block0 = Block()
i0 = block0.emit(Operation, 'f', [IntConstant(15)], Int(), None, None)
i1 = block0.emit(RangeCheck, '$rangecheck', [i0, IntConstant(6), IntConstant(16), StringConstant("Result of function 'f'")], Unit(), None, None)
block0.next = Return(UnitConstant.UNIT, None)
graph = Graph('c2', [], block0)""",
    )
    compare(
        graphs["c1"],
        """
block0 = Block()
i0 = block0.emit(Operation, 'f', [IntConstant(5)], Int(), None, None)
i1 = block0.emit(RangeCheck, '$rangecheck', [i0, IntConstant(6), IntConstant(16), StringConstant("Result of function 'f'")], Unit(), None, None)
i2 = block0.emit(Operation, 'f', [IntConstant(10)], Int(), None, None)
i3 = block0.emit(RangeCheck, '$rangecheck', [i2, IntConstant(6), IntConstant(16), StringConstant("Result of function 'f'")], Unit(), None, None)
block0.next = Return(UnitConstant.UNIT, None)
graph = Graph('c1', [], block0)""",
    )


def _get_example_struct_ranges_2():
    s = ir.Argument(
        "s", types.Struct("S", ("x", "y"), (types.Int(), types.Int()))
    )
    t = ir.Argument(
        "t", types.Struct("T", ("x", "y"), (types.Int(), types.Int()))
    )
    u = ir.Argument(
        "u", types.Struct("U", ("x", "y"), (types.Int(), types.Int()))
    )

    block_f = ir.Block()

    o1 = block_f.emit(
        ir.StructConstruction,
        "S",
        [ir.IntConstant(10), ir.IntConstant(20)],
        s.resolved_type,
    )
    o2 = block_f.emit(
        ir.StructConstruction,
        "T",
        [ir.IntConstant(30), ir.IntConstant(40)],
        t.resolved_type,
    )
    o3 = block_f.emit(
        ir.StructConstruction,
        "U",
        [ir.IntConstant(50), ir.IntConstant(60)],
        u.resolved_type,
    )
    o4 = block_f.emit(ir.Operation, "g", [o1, o2, o3], u.resolved_type)
    o5 = block_f.emit(ir.FieldAccess, "x", [o4], types.Int())
    block_f.next = ir.Return(o5)
    graph_f = ir.Graph("f", [], block_f)

    block_g = ir.Block()
    o1 = block_g.emit(ir.FieldAccess, "x", [s], types.Int())
    block_g.emit(ir.FieldWrite, "y", [t, o1], types.Unit())
    o2 = block_g.emit(ir.FieldAccess, "y", [t], types.Int())
    block_g.emit(ir.FieldWrite, "x", [u, o2], types.Unit())
    block_g.next = ir.Return(u)
    graph_g = ir.Graph("g", [s, t, u], block_g)

    return {"f": graph_f, "g": graph_g}


def test_rewrite_structs():
    graphs = _get_example_struct_ranges_2()
    codegen = MockCodegen(graphs)
    locmanager = compute_all_ranges(codegen)
    rewrite_global_ranges_into_checks(locmanager, graphs)
    compare(
        graphs["f"],
        """
S = Struct('S', ('x', 'y'), (Int(), Int()))
T = Struct('T', ('x', 'y'), (Int(), Int()))
U = Struct('U', ('x', 'y'), (Int(), Int()))
block0 = Block()
i0 = block0.emit(StructConstruction, 'S', [IntConstant(10), IntConstant(20)], S, None, None)
i1 = block0.emit(StructConstruction, 'T', [IntConstant(30), IntConstant(40)], T, None, None)
i2 = block0.emit(StructConstruction, 'U', [IntConstant(50), IntConstant(60)], U, None, None)
i3 = block0.emit(Operation, 'g', [i0, i1, i2], U, None, None)
i4 = block0.emit(FieldAccess, 'x', [i3], Int(), None, None)
i5 = block0.emit(RangeCheck, '$rangecheck', [i4, IntConstant(10), IntConstant(50), StringConstant("Access to field 'x' of struct 'U'")], Unit(), None, None)
block0.next = Return(i4, None)
graph = Graph('f', [], block0)""",
    )
    compare(
        graphs["g"],
        """
S = Struct('S', ('x', 'y'), (Int(), Int()))
T = Struct('T', ('x', 'y'), (Int(), Int()))
U = Struct('U', ('x', 'y'), (Int(), Int()))
s = Argument('s', S)
t = Argument('t', T)
u = Argument('u', U)
block0 = Block()
i3 = block0.emit(FieldAccess, 'x', [s], Int(), None, None)
i4 = block0.emit(RangeCheck, '$rangecheck', [i3, IntConstant(10), IntConstant(10), StringConstant("Access to field 'x' of struct 'S'")], Unit(), None, None)
i5 = block0.emit(FieldWrite, 'y', [t, i3], Unit(), None, None)
i6 = block0.emit(FieldAccess, 'y', [t], Int(), None, None)
i7 = block0.emit(RangeCheck, '$rangecheck', [i6, IntConstant(10), IntConstant(40), StringConstant("Access to field 'y' of struct 'T'")], Unit(), None, None)
i8 = block0.emit(FieldWrite, 'x', [u, i6], Unit(), None, None)
block0.next = Return(u, None)
graph = Graph('g', [s, t, u], block0)""",
    )


def test_rewrite_union():
    graphs = _get_example_union_ranges()
    codegen = MockCodegen(graphs)
    locmanager = compute_all_ranges(codegen)
    changed_graphs = rewrite_global_ranges_into_checks(locmanager, graphs)
    assert set(changed_graphs) == {graphs["f"]}
    compare(
        graphs["f"],
        """
myunion = Union('myunion', ('first', 'second'), (Int(), Int()))
block0 = Block()
i0 = block0.emit(Operation, 'g', [], myunion, None, None)
i1 = block0.emit(UnionCast, 'first', [i0], Int(), None, None)
i2 = block0.emit(RangeCheck, '$rangecheck', [i1, IntConstant(5), IntConstant(10), StringConstant("Variant 'first' of union 'myunion'")], Unit(), None, None)
block0.next = Return(i1, None)
graph = Graph('f', [], block0)""",
    )
    compare(
        graphs["g"],
        """
myunion = Union('myunion', ('first', 'second'), (Int(), Int()))
block0 = Block()
i0 = block0.emit(Operation, 'first', [IntConstant(5)], myunion, None, None)
i1 = block0.emit(Operation, 'first', [IntConstant(10)], myunion, None, None)
block0.next = Return(i1, None)
graph = Graph('g', [], block0)""",
    )


def test_local_with_range_check():
    x = ir.Argument("x", types.Int())
    block0 = ir.Block()
    i1 = block0.emit(
        ir.RangeCheck,
        "$rangecheck",
        [
            x,
            ir.IntConstant(5),
            ir.IntConstant(15),
            ir.StringConstant("Argument 'x' of function 'f'"),
        ],
        types.Unit(),
        None,
        None,
    )
    i2 = block0.emit(
        ir.Operation,
        "add_int",
        [x, ir.IntConstant(1)],
        types.Int(),
        None,
        None,
    )
    block0.next = ir.Return(i2, None)
    graph = ir.Graph("f", [x], block0)
    graphs = {"f": graph}

    codegen = MockCodegen(graphs)
    values = analyze(graph, codegen)
    assert values[block0][i2] == Range(6, 16)
    assert values[block0][x] == Range(5, 15)


def test_apply_interprocedural_optimizations():
    graphs = _get_graphs_interprocedural_range()
    codegen = MockCodegen(graphs)
    apply_interprocedural_optimizations(codegen)
    compare(
        graphs["f"],
        """
x = Argument('x', Int())
block0 = Block()
i1 = block0.emit(RangeCheck, '$rangecheck', [x, IntConstant(5), IntConstant(15), StringConstant("Argument 'x' of function 'f'")], Unit(), None, None)
i2 = block0.emit(Operation, 'zz5izDzKz5i64', [x], MachineInt(), None, None)
i3 = block0.emit(Operation, '@add_i_i_must_fit', [i2, MachineIntConstant(1)], MachineInt(), None, None)
i4 = block0.emit(Operation, 'zz5i64zDzKz5i', [i3], Int(), None, None)
block0.next = Return(i4, None)
graph = Graph('f', [x], block0)
""",
    )


def test_entry_point_args():
    graphs = _get_graphs_interprocedural_range()
    codegen = MockCodegen(graphs, ["f"])
    locmanager = compute_all_ranges(codegen)
    loc = locmanager.get_location_for_result(graphs["f"], types.Int())
    assert not loc._bound.is_bounded()
