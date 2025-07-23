from pydrofoil import bitvector, ir, types
from pydrofoil.z3backend import z3backend, z3btypes
from hypothesis import given, strategies, assume, example, settings
import z3

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

def _make_2_small_bitvectors_w_le_64(data):
    width0 = data.draw(strategies.integers(1, 63))
    value0 = data.draw(strategies.integers(1, 2**width0-1))
    width1 = data.draw(strategies.integers(1, 64-width0))
    value1 = data.draw(strategies.integers(0, 2**width1-1))
    return ir.SmallBitVectorConstant.from_ruint(width0, r_uint(value0)), ir.SmallBitVectorConstant.from_ruint(width1, r_uint(value1))

small_bitvectors = strategies.builds(
    _make_small_bitvector,
    strategies.data())

small_bitvectors_w_ge_2 = strategies.builds(
    _make_small_bitvector_2,
    strategies.data())

small_bitvector_2tuple_w_le_64 = strategies.builds(
    _make_2_small_bitvectors_w_le_64,
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
    w_width = z3btypes.ConstantInt(bv_con.resolved_type.width)

    w_bv_abs = z3btypes.Z3Value(z3.BitVec("bitvec", w_width.value))
    w_bv_con = interp.convert(bv_con)

    # res can be negative
    # we must interpret bv_cons bits as signed bv
    if 2**(w_width.value-1) & bv_con.value != 0:
        bv_con_val = -(2**(w_width.value-1) - int(bv_con.value & ~(2**(w_width.value-1)))) 
    else:
        bv_con_val = int(bv_con.value)


    res_abs = interp._signed_bv(w_bv_abs, w_width)
    res_con = interp._signed_bv(w_bv_con, w_width)


    assert isinstance(res_con, z3btypes.ConstantInt)
    assert isinstance(res_abs, z3btypes.Z3Value)

    assert res_con.value == bv_con_val

    solver = z3.Solver()
    solver.add(w_bv_abs.toz3() == res_con.toz3())
    solvable = solver.check(z3.Not(res_con.toz3() == res_abs.toz3()))
    assert solvable == z3.unsat

@settings(deadline=1000)
@given(interpreter, small_bitvector_2tuple_w_le_64)
def test_bitvector_concat_bv_bv(interp, bv_tuple):
    bv0, bv1 = bv_tuple

    assert bv0.resolved_type.width + bv1.resolved_type.width <= 64

    l_shift_width = z3btypes.ConstantInt(bv1.resolved_type.width)

    w_con_bv0 = z3btypes.ConstantSmallBitVector(bv0.value, bv0.resolved_type.width)
    w_con_bv1 = z3btypes.ConstantSmallBitVector(bv1.value, bv1.resolved_type.width)

    w_abs_bv0 = z3btypes.Z3Value(z3.BitVec("abs_bv0", bv0.resolved_type.width))
    w_abs_bv1 = z3btypes.Z3Value(z3.BitVec("abs_bv1", bv1.resolved_type.width))

    res_val = (bv0.value << bv1.resolved_type.width) + bv1.value


    res_con_con = interp._bitvector_concat_bv_bv(w_con_bv0, w_con_bv1, l_shift_width)
    res_con_abs = interp._bitvector_concat_bv_bv(w_con_bv0, w_abs_bv1, l_shift_width)
    res_abs_con = interp._bitvector_concat_bv_bv(w_abs_bv0, w_con_bv1, l_shift_width)
    res_abs_abs = interp._bitvector_concat_bv_bv(w_abs_bv0, w_abs_bv1, l_shift_width)


    assert isinstance(res_con_con, z3btypes.ConstantSmallBitVector)
    assert isinstance(res_con_abs, z3btypes.Z3Value)
    assert isinstance(res_abs_con, z3btypes.Z3Value)
    assert isinstance(res_abs_abs, z3btypes.Z3Value)

    assert res_con_con.value == res_val

    solver = z3.Solver()
    solver.add(w_abs_bv1.toz3() == bv1.value)
    solvable = solver.check(z3.Not(res_con_abs.toz3() == res_val))
    assert solvable == z3.unsat

    solver = z3.Solver()
    solver.add(w_abs_bv0.toz3() == bv0.value)
    solvable = solver.check(z3.Not(res_abs_con.toz3() == res_val))
    assert solvable == z3.unsat

    solver = z3.Solver()
    solver.add(w_abs_bv1.toz3() == bv1.value)
    solver.add(w_abs_bv0.toz3() == bv0.value)
    solvable = solver.check(z3.Not(res_abs_abs.toz3() == res_val))
    assert solvable == z3.unsat