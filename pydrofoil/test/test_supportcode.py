from pydrofoil.test import supportcode
from pydrofoil import bitvector

from rpython.rlib.rbigint import rbigint

def gbv(size, val):
    return bitvector.GenericBitVector(size, rbigint.fromint(val))

def test_fast_signed():
    assert supportcode.fast_signed(0b0, 1) == 0
    assert supportcode.fast_signed(0b1, 1) == -1
    assert supportcode.fast_signed(0b0, 2) == 0
    assert supportcode.fast_signed(0b1, 2) == 1
    assert supportcode.fast_signed(0b10, 2) == -2
    assert supportcode.fast_signed(0b11, 2) == -1

def test_signed():
    assert supportcode.sail_signed(gbv(1, 0b0)).toint() == 0
    assert supportcode.sail_signed(gbv(1, 0b1)).toint() == -1
    assert supportcode.sail_signed(gbv(2, 0b0)).toint() == 0
    assert supportcode.sail_signed(gbv(2, 0b1)).toint() == 1
    assert supportcode.sail_signed(gbv(2, 0b10)).toint() == -2
    assert supportcode.sail_signed(gbv(2, 0b11)).toint() == -1

def test_sign_extend():
    assert supportcode.sign_extend(gbv(1, 0b0), rbigint.fromint(2)).toint() == 0
    assert supportcode.sign_extend(gbv(1, 0b1), rbigint.fromint(2)).toint() == 0b11
    assert supportcode.sign_extend(gbv(2, 0b00), rbigint.fromint(4)).toint() == 0
    assert supportcode.sign_extend(gbv(2, 0b01), rbigint.fromint(4)).toint() == 1
    assert supportcode.sign_extend(gbv(2, 0b10), rbigint.fromint(4)).toint() == 0b1110
    assert supportcode.sign_extend(gbv(2, 0b11), rbigint.fromint(4)).toint() == 0b1111

def test_get_slice_int():
    assert supportcode.get_slice_int(rbigint.fromint(8), rbigint.fromint(0b011010010000), rbigint.fromint(4)).toint() == 0b01101001

def test_vector_update():
    x = bitvector.GenericBitVector(6, rbigint.fromint(1))
    res = x.update_bit(2, 1)
    assert res.size == 6
    assert res.toint() == 0b101

    x = bitvector.GenericBitVector(6, rbigint.fromint(1))
    res = x.update_bit(0, 1)
    assert res.size == 6
    assert res.toint() == 0b1

    x = bitvector.GenericBitVector(6, rbigint.fromint(0b11))
    res = x.update_bit(2, 0)
    assert res.size == 6
    assert res.toint() == 0b011

    x = bitvector.GenericBitVector(6, rbigint.fromint(0b111))
    res = x.update_bit(1, 0)
    assert res.size == 6
    assert res.toint() == 0b101

def test_vector_subrange():
    x = bitvector.GenericBitVector(6, rbigint.fromint(0b111))
    r = x.subrange(3, 2)
    assert r.size == 2
    assert r.toint() == 1
