from pydrofoil.test import supportcode
from pydrofoil import bitvector

from rpython.rlib.rarithmetic import r_uint, intmask
from rpython.rlib.rbigint import rbigint

def gbv(size, val):
    return bitvector.GenericBitVector(size, rbigint.fromlong(val))

def bv(size, val):
    return bitvector.from_ruint(size, r_uint(val))

def test_fast_signed():
    assert supportcode.fast_signed(0b0, 1) == 0
    assert supportcode.fast_signed(0b1, 1) == -1
    assert supportcode.fast_signed(0b0, 2) == 0
    assert supportcode.fast_signed(0b1, 2) == 1
    assert supportcode.fast_signed(0b10, 2) == -2
    assert supportcode.fast_signed(0b11, 2) == -1

def test_signed():
    for c in gbv, bv:
        assert supportcode.sail_signed(c(1, 0b0)).toint() == 0
        assert supportcode.sail_signed(c(1, 0b1)).toint() == -1
        assert supportcode.sail_signed(c(2, 0b0)).toint() == 0
        assert supportcode.sail_signed(c(2, 0b1)).toint() == 1
        assert supportcode.sail_signed(c(2, 0b10)).toint() == -2
        assert supportcode.sail_signed(c(2, 0b11)).toint() == -1
        assert supportcode.sail_signed(c(64, 0xffffffffffffffff)).toint() == -1
        assert supportcode.sail_signed(c(64, 0x1)).toint() == 1

def test_sign_extend():
    for c in gbv, bv:
        assert supportcode.sign_extend(c(1, 0b0), rbigint.fromint(2)).toint() == 0
        assert supportcode.sign_extend(c(1, 0b1), rbigint.fromint(2)).toint() == 0b11
        assert supportcode.sign_extend(c(2, 0b00), rbigint.fromint(4)).toint() == 0
        assert supportcode.sign_extend(c(2, 0b01), rbigint.fromint(4)).toint() == 1
        assert supportcode.sign_extend(c(2, 0b10), rbigint.fromint(4)).toint() == 0b1110
        assert supportcode.sign_extend(c(2, 0b11), rbigint.fromint(4)).toint() == 0b1111

def test_unsigned():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        assert x.unsigned().tolong() == 0b10001101
        x = c(64, 0b10001101)
        assert x.unsigned().tolong() == 0b10001101
        x = c(64, r_uint(-1))
        assert x.unsigned().tolong() == (1<<64)-1

def test_unsigned():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        assert x.unsigned().tolong() == 0b10001101
        x = c(64, 0b10001101)
        assert x.unsigned().tolong() == 0b10001101
        x = c(64, r_uint(-1))
        assert x.unsigned().tolong() == (1<<64)-1

def test_get_slice_int():
    assert supportcode.get_slice_int(rbigint.fromint(8), rbigint.fromint(0b011010010000), rbigint.fromint(4)).toint() == 0b01101001

def test_vector_update():
    for c in gbv, bv:
        x = c(6, 1)
        res = x.update_bit(2, 1)
        assert res.size == 6
        assert res.toint() == 0b101

        x = c(6, 1)
        res = x.update_bit(0, 1)
        assert res.size == 6
        assert res.toint() == 0b1

        x = c(6, 0b11)
        res = x.update_bit(2, 0)
        assert res.size == 6
        assert res.toint() == 0b011

        x = c(6, 0b111)
        res = x.update_bit(1, 0)
        assert res.size == 6
        assert res.toint() == 0b101

def test_vector_subrange():
    x = bitvector.GenericBitVector(6, rbigint.fromint(0b111))
    r = x.subrange(3, 2)
    assert r.size == 2
    assert r.toint() == 1
    x = bv(6, 0b111)
    r = x.subrange(3, 2)
    assert r.size == 2
    assert r.toint() == 1

def test_vector_update_subrange():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        x = x.update_subrange(5, 2, bv(4, 0b1010))
        assert x.toint() == 0b10101001

def test_vector_shift():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        res = x.lshift(5)
        assert res.size == 8
        assert res.toint() == 0b10100000

        x = c(8, 0b10001101)
        res = x.rshift(5)
        assert res.size == 8
        assert res.toint() == 0b00000100

def test_vector_shift_bits():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        res = x.lshift_bits(c(8, 5))
        assert res.size == 8
        assert res.toint() == 0b10100000

        x = c(8, 0b10001101)
        res = x.rshift_bits(c(16, 5))
        assert res.size == 8
        assert res.toint() == 0b00000100

def test_bitvector_touint():
    for size in [6, 6000]:
        assert bv(size, 0b11).touint() == r_uint(0b11)

def test_add_int():
    assert bv(6, 0b11).add_int(rbigint.fromint(0b111111111)).touint() == (0b11 + 0b111111111) & 0b111111
    assert bv(6000, 0b11).add_int(rbigint.fromint(0b111111111)).touint() == 0b11 + 0b111111111

def test_bv_bitwise():
    for c in gbv, bv:
        i1 = c(8, 0b11110000)
        i2 = c(8, 0b11001100)
        res = i1.and_(i2)
        assert res.toint() == 0b11110000 & 0b11001100
        res = i1.or_(i2)
        assert res.toint() == 0b11110000 | 0b11001100
        res = i1.xor(i2)
        assert res.toint() == 0b11110000 ^ 0b11001100
        res = i1.invert()
        assert res.toint() == 0b00001111
