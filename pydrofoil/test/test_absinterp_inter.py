from pydrofoil import types
from pydrofoil import ir
from pydrofoil.absinterp import (
    Range,
    Location,
    LocationManager,
    compute_all_ranges,
)
import pytest


def test_creation():
    m = LocationManager()
    typ = types.Int()
    l = m.new_location(typ)
    graph = object()
    assert not l.read(graph).is_bounded()
    assert graph in l.readers

    typ = types.MachineInt()
    l = m.new_location(typ)
    assert l.read(object()).is_bounded()


def test_location_write():
    m = LocationManager()
    typ = types.Int()
    l = m.new_location(typ)
    graph = object()
    range = Range(0, 100)
    l.write(new_bound=range, graph=graph)
    assert l._writes[graph, None] == range


def test_location_write_error_checking():
    m = LocationManager()
    typ = types.Int()
    l = m.new_location(typ)
    graph = object()
    range = Range(0, 100)
    l._bound = Range(0, 10)
    with pytest.raises(AssertionError):
        l.write(new_bound=range, graph=graph)


def test_find_modified():
    m = LocationManager()
    typ = types.Int()
    l1 = m.new_location(typ)
    l2 = m.new_location(typ)
    l1.write(Range(0, 100), object())
    assert m.find_modified() == {l1}


def _get_graphs_interprocedural_range():
    # Graph that makes x+1
    # Graph that calls with 5 and 10 and one that call with 15
    # Result -> Range(6, 16)
    x = ir.Argument("x", types.Int())
    block_f = ir.Block()
    res = block_f.emit(
        ir.Operation, "$add", [x, ir.IntConstant(1)], types.Int()
    )
    block_f.next = ir.Return(res)
    graph_f = ir.Graph("f", [x], block_f)

    block_c1 = ir.Block()
    block_c1.emit(ir.Operation, "f", [ir.IntConstant(5)], types.Int())
    block_c1.emit(ir.Operation, "f", [ir.IntConstant(10)], types.Int())
    block_c1.next = ir.Return(ir.UnitConstant.UNIT)
    graph_c1 = ir.Graph("c1", [x], block_c1)

    block_c2 = ir.Block()
    block_c2.emit(ir.Operation, "f", [ir.IntConstant(15)], types.Int())
    block_c2.next = ir.Return(ir.UnitConstant.UNIT)
    graph_c2 = ir.Graph("c2", [x], block_c2)

    return {"f": graph_f, "c1": graph_c1, "c2": graph_c2}


class MockCodegen(object):
    def __init__(self, graphs):
        self.all_graph_by_name = graphs
        self.builtin_names = {}


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
