import pytest
from pydrofoil import bitvector, ir, types
from rpython.rlib.rbigint import rbigint

from pydrofoil.absinterp import AbstractInterpreter, Range
from pydrofoil.test.util import MockCodegen


def _run_op(op_name, *arg_definitions):
    # type: (str, tuple[types.Type, Range | None]) -> Range | None
    codegen = MockCodegen({})
    interp = AbstractInterpreter(codegen=codegen, graph=None)
    args = [
        ir.Argument("arg_%s" % i, typ)
        for i, (typ, _) in enumerate(arg_definitions)
    ]
    op = ir.Operation("@" + op_name, args, types.GenericBitVector())
    interp.current_values = {
        arg: r for arg, (_, r) in zip(args, arg_definitions)
    }
    new_range = interp.analyze_Operation(op)
    return new_range


def test_zeros_i():
    new_range = _run_op("zeros_i", (types.MachineInt(), Range(-1, 100)))
    assert new_range == Range(0, 100)


def test_add_bits():
    new_range = _run_op(
        "add_bits",
        (types.GenericBitVector(), Range(0, 70)),
        (types.GenericBitVector(), Range(50, 100)),
    )
    assert new_range == Range(50, 70)


def test_add_bits_int():
    new_range = _run_op(
        "add_bits_int",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, None)),
    )
    assert new_range == Range(0, 100)


def test_sign_extend_o_i():
    new_range = _run_op(
        "sign_extend_o_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.MachineInt(), Range(-42, 23)),
    )
    assert new_range == Range(0, 23)


def test_zero_extend_o_i():
    new_range = _run_op(
        "zero_extend_o_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.MachineInt(), Range(-42, 23)),
    )
    assert new_range == Range(0, 23)


def test_length_unwrapped_res():
    new_range = _run_op(
        "length_unwrapped_res",
        (types.GenericBitVector(), Range(0, 100)),
    )
    assert new_range == Range(0, 100)


def test_not_bits():
    new_range = _run_op(
        "not_bits",
        (types.GenericBitVector(), Range(0, 100)),
    )
    assert new_range == Range(0, 100)


def test_sail_unsigned_byte():
    new_range = _run_op(
        "sail_unsigned",
        (types.GenericBitVector(), Range(0, 8)),
    )
    assert new_range == Range(0, 255)


def test_sail_unsigned_with_low():
    new_range = _run_op(
        "sail_unsigned",
        (types.GenericBitVector(), Range(3, 10)),
    )
    assert new_range == Range(0, 1023)


def test_sail_signed_byte():
    new_range = _run_op(
        "sail_signed",
        (types.GenericBitVector(), Range(0, 8)),
    )
    assert new_range == Range(-128, 127)


def test_sail_signed_with_low():
    new_range = _run_op(
        "sail_signed",
        (types.GenericBitVector(), Range(3, 10)),
    )
    assert new_range == Range(-512, 511)


def test_get_slice_int_i_o_i():
    new_range = _run_op(
        "get_slice_int_i_o_i",
        (types.Int(), Range(-10, 42)),
        (types.Int(), Range(None, None)),
        (types.Int(), Range(None, None)),
    )
    assert new_range == Range(0, 42)


def test_vector_subrange_o_i_i():
    new_range = _run_op(
        "vector_subrange_o_i_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(0, 20)),
        (types.Int(), Range(0, 20)),
    )
    assert new_range == Range(0, 21)

    new_range = _run_op(
        "vector_subrange_o_i_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, 20)),
        (types.Int(), Range(3, None)),
    )
    assert new_range == Range(0, 18)

    new_range = _run_op(
        "vector_subrange_o_i_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, None)),
        (types.Int(), Range(None, None)),
    )
    assert new_range == Range(0, 100)


def test_slice_o_i_i():
    new_range = _run_op(
        "slice_o_i_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, None)),
        (types.Int(), Range(0, 20)),
    )
    assert new_range == Range(0, 20)

    new_range = _run_op(
        "slice_o_i_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, None)),
        (types.Int(), Range(None, None)),
    )
    assert new_range == Range(0, 100)


def test_sub_bits():
    new_range = _run_op(
        "sub_bits",
        (types.GenericBitVector(), Range(0, 100)),
        (types.GenericBitVector(), Range(20, 150)),
    )
    assert new_range == Range(20, 100)


def test_shiftr_o_i():
    new_range = _run_op(
        "shiftr_o_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, None)),
    )
    assert new_range == Range(0, 100)


def test_shiftl_o_i():
    new_range = _run_op(
        "shiftl_o_i",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, None)),
    )
    assert new_range == Range(0, 100)


def test_or_bits():
    new_range = _run_op(
        "or_bits",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, None)),
    )
    assert new_range == Range(0, 100)


def test_read_mem_exclusive_o_o_o_i():
    new_range = _run_op(
        "read_mem_exclusive_o_o_o_i",
        (types.Struct("x", (), ()), None),
        (types.Int(), Range(None, None)),
        (types.GenericBitVector(), Range(0, None)),
        (types.Int(), Range(4, 8)),
    )
    assert new_range == Range(32, 64)


def test_vector_update_subrange_o_i_i_o():
    new_range = _run_op(
        "vector_update_subrange_o_i_i_o",
        (types.GenericBitVector(), Range(0, 100)),
        (types.Int(), Range(None, None)),
        (types.Int(), Range(None, None)),
        (types.GenericBitVector(), Range(0, 100)),
    )
    assert new_range == Range(0, 100)


def test_eq_bits():
    new_range = _run_op(
        "eq_bits",
        (types.GenericBitVector(), Range(0, 100)),
        (types.GenericBitVector(), Range(0, 100)),
    )
    assert new_range == Range(0, 1)


def test_bitvector_concat_bv_gbv_wrapped_res():
    new_range = _run_op(
        "bitvector_concat_bv_gbv_wrapped_res",
        (types.Int(), Range(None, None)),
        (types.Int(), Range(4, None)),
        (types.GenericBitVector(), Range(0, 100)),
    )
    assert new_range == Range(4, None)

    new_range = _run_op(
        "bitvector_concat_bv_gbv_wrapped_res",
        (types.Int(), Range(None, None)),
        (types.Int(), Range(4, 200)),
        (types.GenericBitVector(), Range(0, 100)),
    )
    assert new_range == Range(4, 300)


def test_bitvector_concat_bv_n_zeros_wrapped_res():
    new_range = _run_op(
        "bitvector_concat_bv_n_zeros_wrapped_res",
        (types.Int(), Range(None, None)),
        (types.Int(), Range(4, 8)),
        (types.Int(), Range(10, 20)),
    )
    assert new_range == Range(14, 28)


def test_xor_bits():
    new_range = _run_op(
        "xor_bits",
        (types.GenericBitVector(), Range(0, 100)),
        (types.GenericBitVector(), Range(20, 200)),
    )
    assert new_range == Range(0, 100)


def test_and_bits():
    new_range = _run_op(
        "and_bits",
        (types.GenericBitVector(), Range(0, 100)),
        (types.GenericBitVector(), Range(20, 200)),
    )
    assert new_range == Range(0, 100)


def test_undefined_bitvector_i():
    new_range = _run_op(
        "undefined_bitvector_i",
        (types.Int(), Range(-1, 100)),
    )
    assert new_range == Range(0, 100)


# TODO replicate_bits_o_i
