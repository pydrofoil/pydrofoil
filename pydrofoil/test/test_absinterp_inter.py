from pydrofoil import types
from pydrofoil.ir import Graph
from pydrofoil.absinterp import Range, Location, LocationManager
import pytest


def test_creation():
    m = LocationManager()
    typ = types.Int()
    l = m.new_location(typ)
    graph = object()
    assert not l.read(graph).is_bounded()
    assert graph in l._readers

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


def _get_graphs_XXX():
    # TODO graph that makes x+1
    # TODO graph that calls with 5 and one that call with 10
    # TODO result -> Range(6, 11)
    return
