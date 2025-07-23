from pydrofoil import bitvector, ir, types
from pydrofoil.z3backend import z3backend
from hypothesis import given, strategies, assume, example, settings
import z3
import pytest

from rpython.rlib.rarithmetic import r_uint
from rpython.rlib.rbigint import rbigint

## copied from test_supportcode.py ##

def _make_small_bitvector(data):
    width = data.draw(strategies.integers(1, 64))
    value = data.draw(strategies.integers(0, 2**width-1))
    return ir.SmallBitVectorConstant.from_ruint(width, r_uint(value))


def _make_small_bitvector_2(data):
    width = data.draw(strategies.integers(2, 64))
    value = data.draw(strategies.integers(0, 2**width-1))
    return ir.SmallBitVectorConstant.from_ruint(width, r_uint(value))

def _make_generic_bitvector(data):
    width = data.draw(strategies.integers(65, 1000))
    value = data.draw(strategies.integers(0, 2**width-1))
    return ir.GenericBitVectorConstant(rbigint.fromlong(value))

small_bitvectors = strategies.builds(
    _make_small_bitvector,
    strategies.data())

small_bitvectors_w_ge_2 = strategies.builds(
    _make_small_bitvector_2,
    strategies.data())

generic_bitvectors = strategies.builds(
    _make_generic_bitvector,
    strategies.data())

#####################################

def _first_interpreter():
    return z3backend.Interpreter(DummyGraph.Dummy, [], z3backend.SharedState(), {})

interpreter = strategies.builds(
    _first_interpreter)

#####################################

class DummyGraph():

    def __init__(self):
        self.has_loop = False
        self.args = []
    
DummyGraph.Dummy = DummyGraph()

#####################################

@settings(deadline=1000)
@given(interpreter, small_bitvectors)
def test_signed_bv(interp, bv_con):

    w_width = z3backend.ConstantInt(bv_con.resolved_type.width)

    w_bv_abs = z3backend.Z3Value(z3.BitVec("bitvec", w_width.value))
    w_bv_con = interp.convert(bv_con)

    res_abs = interp._signed_bv(w_bv_abs, w_width)
    res_con = interp._signed_bv(w_bv_con, w_width)

    assert isinstance(res_con, z3backend.ConstantInt)
    assert isinstance(res_abs, z3backend.Z3Value)

    # res can be negative
    # we must interpret bv_cons bits as signed bv
    if 2**(w_width.value-1) & bv_con.value != 0:
        bv_con_val = -(2**(w_width.value-1) - int(bv_con.value & ~(2**(w_width.value-1)))) 
    else:
        bv_con_val = int(bv_con.value)

    assert res_con.value == bv_con_val

    solver = z3.Solver()
    solver.add(w_bv_abs.toz3() == res_con.toz3())

    solvable = solver.check(z3.Not(res_con.toz3() == res_abs.toz3()))

    assert solvable == z3.unsat