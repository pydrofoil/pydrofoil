from pydrofoil.test import supportcode
from pydrofoil import bitvector

from rpython.rlib.rbigint import rbigint

def test_fast_signed():
    assert supportcode.fast_signed(0b0, 1) == 0
    assert supportcode.fast_signed(0b1, 1) == -1
    assert supportcode.fast_signed(0b0, 2) == 0
    assert supportcode.fast_signed(0b1, 2) == 1
    assert supportcode.fast_signed(0b10, 2) == -2
    assert supportcode.fast_signed(0b11, 2) == -1

def test_sign_extend():
    assert supportcode.sign_extend(bitvector.GenericBitVector(1, rbigint.fromint(0b0)), rbigint.fromint(2)).rval.toint() == 0
    assert supportcode.sign_extend(bitvector.GenericBitVector(1, rbigint.fromint(0b1)), rbigint.fromint(2)).rval.toint() == 0b11
    assert supportcode.sign_extend(bitvector.GenericBitVector(2, rbigint.fromint(0b00)), rbigint.fromint(4)).rval.toint() == 0
    assert supportcode.sign_extend(bitvector.GenericBitVector(2, rbigint.fromint(0b01)), rbigint.fromint(4)).rval.toint() == 1
    assert supportcode.sign_extend(bitvector.GenericBitVector(2, rbigint.fromint(0b10)), rbigint.fromint(4)).rval.toint() == 0b1110
    assert supportcode.sign_extend(bitvector.GenericBitVector(2, rbigint.fromint(0b11)), rbigint.fromint(4)).rval.toint() == 0b1111

def test_get_slice_int():
    assert supportcode.get_slice_int(rbigint.fromint(8), rbigint.fromint(0b011010010000), rbigint.fromint(4)).rval.toint() == 0b01101001
