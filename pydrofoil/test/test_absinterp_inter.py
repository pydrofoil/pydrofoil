from pydrofoil import types
from pydrofoil import ir
from pydrofoil.absinterp import Range, Location, LocationManager
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
    assert l._writes[graph] == range


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
    x = ir.Argument('x', types.Int())
    block_f = ir.Block()
    res = block_f.emit(ir.Operation, "$add", [x, ir.IntConstant(1)], types.Int())
    block_f.next = ir.Return(res)
    graph_f = ir.Graph("f", [x], block_f)

    block_c1 = ir.Block()
    block_c1.emit(ir.Operation, "f", [ir.IntConstant(5)], types.Int())
    block_c1.emit(ir.Operation, "f", [ir.IntConstant(10)], types.Int())
    graph_c1 = ir.Graph("c1", [x], block_c1)

    block_c2 = ir.Block()
    block_c2.emit(ir.Operation, "f", [ir.IntConstant(15)], types.Int())
    graph_c2 = ir.Graph("c2", [x], block_c2)

    return {"f": graph_f, "c1": graph_c1, "c2": graph_c2}


def test_interprocedural_range():
    graphs = _get_graphs_interprocedural_range()

