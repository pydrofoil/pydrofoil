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

def _make_2_small_bitvectors_same_width(data):
    width = data.draw(strategies.integers(1, 64))
    value0 = data.draw(strategies.integers(0, 2**width-1))
    value1 = data.draw(strategies.integers(0, 2**width-1))
    return ir.SmallBitVectorConstant.from_ruint(width, r_uint(value0)), ir.SmallBitVectorConstant.from_ruint(width, r_uint(value1))

small_bitvectors = strategies.builds(
    _make_small_bitvector,
    strategies.data())

small_bitvectors_w_ge_2 = strategies.builds(
    _make_small_bitvector_2,
    strategies.data())

small_bitvector_2tuple_w_le_64 = strategies.builds(
    _make_2_small_bitvectors_w_le_64,
    strategies.data())

small_bitvectors_2tuple_same_width = strategies.builds(
    _make_2_small_bitvectors_same_width,
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
    solver.add(w_bv_abs.toz3() == z3.Int2BV(res_con.toz3(), w_width.value))
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

@settings(deadline=1000)
@given(interpreter, small_bitvectors_2tuple_same_width)
def test_eq_anything_bv(interp, bv_tuple):
    bv0, bv1 = bv_tuple
    
    w_con_bv0 = z3btypes.ConstantSmallBitVector(bv0.value, bv0.resolved_type.width)
    w_con_bv1 = z3btypes.ConstantSmallBitVector(bv1.value, bv1.resolved_type.width)

    w_abs_bv0 = z3btypes.Z3Value(z3.BitVec("abs_bv0", bv0.resolved_type.width))
    w_abs_bv1 = z3btypes.Z3Value(z3.BitVec("abs_bv1", bv1.resolved_type.width))

    equal = bv0.value == bv1.value

    #res_con_con = interp._eq_anything(w_con_bv0, w_con_bv1) # 2 non z3  values not implemented yet
    res_con_abs = interp._eq_anything(w_con_bv0, w_abs_bv1)
    res_abs_con = interp._eq_anything(w_abs_bv0, w_con_bv1)
    res_abs_abs = interp._eq_anything(w_abs_bv0, w_abs_bv1)

    #assert isinstance(res_con_con, z3btypes.ConstantSmallBitVector)
    assert isinstance(res_con_abs, z3btypes.Z3Value)
    assert isinstance(res_abs_con, z3btypes.Z3Value)
    assert isinstance(res_abs_abs, z3btypes.Z3Value)

    solver = z3.Solver()
    solver.add(w_abs_bv1.toz3() == bv1.value)
    solvable = solver.check(z3.Not(res_con_abs.toz3() == equal))
    assert solvable == z3.unsat

    solver = z3.Solver()
    solver.add(w_abs_bv0.toz3() == bv0.value)
    solvable = solver.check(z3.Not(res_abs_con.toz3() == equal))
    assert solvable == z3.unsat

    solver = z3.Solver()
    solver.add(w_abs_bv1.toz3() == bv1.value)
    solver.add(w_abs_bv0.toz3() == bv0.value)
    solvable = solver.check(z3.Not(res_abs_abs.toz3() == equal))
    assert solvable == z3.unsat


@settings(deadline=1000)
@given(interpreter, strategies.integers(0,1), strategies.integers(0,1),  small_bitvectors_2tuple_same_width)
def test_eq_anything_union(interp, variant0, variant1, bv_tuple):
    bv0, bv1 = bv_tuple

    test_union = types.Union("test",  ("A", "B"), (types.SmallFixedBitVector(64), types.Bool()))
    z3typ = interp.sharedstate.get_z3_union_type(test_union)

    if variant0 == 0:
        w_union0 = z3btypes.UnionConstant("A", z3btypes.ConstantSmallBitVector(bv0.value, 64), test_union, z3typ)
    else:
        w_union0 = z3btypes.UnionConstant("B", z3btypes.BooleanConstant(bv0.value % 2 == 0), test_union, z3typ)

    if variant1 == 0:
        w_union1 = z3btypes.UnionConstant("A", z3btypes.ConstantSmallBitVector(bv1.value, 64), test_union, z3typ)
    else:
        w_union1 = z3btypes.UnionConstant("B", z3btypes.BooleanConstant(bv1.value % 2 == 0), test_union, z3typ)

    equal = (variant0 == variant1) and ((variant0 == 0 and bv0.value == bv1.value) or (variant0 == 1 and bv0.value % 2 == bv1.value % 2))
    
    w_res = interp._eq_anything(w_union0, w_union1)

    assert isinstance(w_res,z3btypes.BooleanConstant)
    assert w_res.value == equal

@given(interpreter)
def test_allocate(interp):
    test_struct = types.Struct("test",  ("a", "b"), (types.SmallFixedBitVector(64), types.Unit()))

    struct_instance = interp._allocate(test_struct)

    assert isinstance(struct_instance, z3btypes.StructConstant)

    assert isinstance(struct_instance.vals_w[0], z3btypes.Z3Value)
    assert isinstance(struct_instance.vals_w[1], z3btypes.UnitConstant)

@given(interpreter)
def test_struct_construction(interp):
    test_struct = types.Struct("test",  ("a", "b"), (types.SmallFixedBitVector(64), types.Unit()))

    args = [z3btypes.ConstantSmallBitVector(1337, 64), z3btypes.UnitConstant(interp.sharedstate._z3_unit)]
    struct_instance = interp._struct_construction(args, test_struct)

    assert isinstance(struct_instance, z3btypes.StructConstant)

    assert isinstance(struct_instance.vals_w[0], z3btypes.ConstantSmallBitVector)
    assert struct_instance.vals_w[0].value == 1337

    assert isinstance(struct_instance.vals_w[1], z3btypes.UnitConstant)

@given(interpreter)
def test_struct_copy(interp):
    test_struct = types.Struct("test",  ("a", "b"), (types.SmallFixedBitVector(64), types.Unit()))

    args = [z3btypes.ConstantSmallBitVector(1234567, 64), z3btypes.UnitConstant(interp.sharedstate._z3_unit)]
    struct_instance = z3btypes.StructConstant(args, test_struct, interp.sharedstate.get_z3_struct_type(test_struct))

    copied_struct_instance = interp._struct_copy(struct_instance)

    assert struct_instance != copied_struct_instance

    assert isinstance(copied_struct_instance, z3btypes.StructConstant)

    assert isinstance(copied_struct_instance.vals_w[0], z3btypes.ConstantSmallBitVector)
    assert struct_instance.vals_w[0].value == 1234567

    assert isinstance(copied_struct_instance.vals_w[1], z3btypes.UnitConstant)

@given(interpreter, strategies.integers(0,1), small_bitvectors)
def test_field_access(interp, const, bv):
    test_struct = types.Struct("test",  ("a", "b", "c"), (types.SmallFixedBitVector(bv.resolved_type.width), types.Unit(), types.Bool()))

    if const:
        args = [z3btypes.ConstantSmallBitVector(bv.value, bv.resolved_type.width), z3btypes.UnitConstant(interp.sharedstate._z3_unit), z3btypes.BooleanConstant(True)]
        struct_instance = z3btypes.StructConstant(args, test_struct, interp.sharedstate.get_z3_struct_type(test_struct))
    else:
        z3type = interp.sharedstate.get_z3_struct_type(test_struct)
        struct_instance = z3btypes.Z3Value(interp.sharedstate.get_abstract_const_of_ztype(z3type, "test"))

    field_a = interp._field_access("a", struct_instance, test_struct)
    field_b = interp._field_access("b", struct_instance, test_struct)
    field_c = interp._field_access("c", struct_instance, test_struct)

    if const: 
        assert isinstance(field_a, z3btypes.ConstantSmallBitVector)
        assert field_a.value == bv.value
        assert field_a.width == bv.resolved_type.width

        assert isinstance(field_b, z3btypes.UnitConstant)

        assert isinstance(field_c, z3btypes.BooleanConstant)
        assert field_c.value == True
    else:
        assert isinstance(field_a, z3btypes.Z3Value)
        assert field_a.toz3().sort().size() == bv.resolved_type.width

        # TODO: make _field_access("a", Z3Value, ...) return UnitConstant if 'a' is Unit
        assert isinstance(field_b, z3btypes.Z3Value) 

        assert isinstance(field_c, z3btypes.Z3BoolValue)

@given(interpreter, small_bitvectors)
def test_field_write(interp, bv):
    test_struct = types.Struct("test",  ("a", "b", "c"), (types.SmallFixedBitVector(bv.resolved_type.width), types.Unit(), types.Bool()))

    z3type = interp.sharedstate.get_z3_struct_type(test_struct)
    struct_instance = z3btypes.Z3Value(interp.sharedstate.get_abstract_const_of_ztype(z3type, "test"))

    new_a = z3btypes.ConstantSmallBitVector(bv.value, bv.resolved_type.width)
    new_b = z3btypes.UnitConstant(interp.sharedstate._z3_unit)
    new_c = z3btypes.BooleanConstant(bv.value % 7 == 0)

    struct_new_field_a = interp._field_write(struct_instance, test_struct, "a", new_a)
    struct_new_field_b = interp._field_write(struct_instance, test_struct, "b", new_b)
    struct_new_field_c = interp._field_write(struct_instance, test_struct, "c", new_c)

    assert struct_new_field_a is not struct_instance
    assert struct_new_field_b is not struct_instance
    assert struct_new_field_c is not struct_instance


    struct_na_a = interp._field_access("a", struct_new_field_a, test_struct)
    struct_na_b = interp._field_access("b", struct_new_field_a, test_struct)
    struct_na_c = interp._field_access("c", struct_new_field_a, test_struct)

    assert isinstance(struct_na_a, z3btypes.ConstantSmallBitVector)
    assert struct_na_a.value == bv.value
    assert isinstance(struct_na_b, z3btypes.Z3Value) 
    assert isinstance(struct_na_c, z3btypes.Z3BoolValue)


    struct_nb_a = interp._field_access("a", struct_new_field_b, test_struct)
    struct_nb_b = interp._field_access("b", struct_new_field_b, test_struct)
    struct_nb_c = interp._field_access("c", struct_new_field_b, test_struct)

    assert isinstance(struct_nb_a, z3btypes.Z3Value)
    assert isinstance(struct_nb_b, z3btypes.UnitConstant) 
    assert isinstance(struct_nb_c, z3btypes.Z3BoolValue)


    struct_nc_a = interp._field_access("a", struct_new_field_c, test_struct)
    struct_nc_b = interp._field_access("b", struct_new_field_c, test_struct)
    struct_nc_c = interp._field_access("c", struct_new_field_c, test_struct)

    assert isinstance(struct_nc_a, z3btypes.Z3Value)
    assert isinstance(struct_nc_b, z3btypes.Z3Value) 
    assert isinstance(struct_nc_c, z3btypes.BooleanConstant)
    assert struct_nc_c.value == bool(bv.value % 7 == 0)
