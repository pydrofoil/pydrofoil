import pytest

from pydrofoil import supportcode
from pydrofoil import bitvector
from pydrofoil.bitvector import int_fromint, int_frombigint

from rpython.rlib.rarithmetic import r_uint, intmask
from rpython.rlib.rbigint import rbigint

def gbv(size, val):
    return bitvector.GenericBitVector(size, rbigint.fromlong(val))

def bv(size, val):
    return bitvector.from_ruint(size, r_uint(val))

def si(val):
    return int_fromint(val)

def bi(val):
    return int_frombigint(rbigint.fromlong(val))

machine = "dummy"

def test_fast_signed():
    assert supportcode.fast_signed(machine, 0b0, 1) == 0
    assert supportcode.fast_signed(machine, 0b1, 1) == -1
    assert supportcode.fast_signed(machine, 0b0, 2) == 0
    assert supportcode.fast_signed(machine, 0b1, 2) == 1
    assert supportcode.fast_signed(machine, 0b10, 2) == -2
    assert supportcode.fast_signed(machine, 0b11, 2) == -1

def test_signed():
    def check(size, val):
        return bitvector.int_tolong(supportcode.sail_signed(machine, c(size, val)))
    for c in gbv, bv:
        assert check(1, 0) == 0
        assert check(1, 0b1) == -1
        assert check(2, 0b0) == 0
        assert check(2, 0b1) == 1
        assert check(2, 0b10) == -2
        assert check(2, 0b11) == -1
        assert check(64, 0xffffffffffffffff) == -1
        assert check(64, 0x1) == 1

def test_sign_extend():
    for c in gbv, bv:
        assert supportcode.sign_extend(machine, c(1, 0b0), int_fromint(2)).toint() == 0
        assert supportcode.sign_extend(machine, c(1, 0b1), int_fromint(2)).toint() == 0b11
        assert supportcode.sign_extend(machine, c(2, 0b00), int_fromint(4)).toint() == 0
        assert supportcode.sign_extend(machine, c(2, 0b01), int_fromint(4)).toint() == 1
        assert supportcode.sign_extend(machine, c(2, 0b10), int_fromint(4)).toint() == 0b1110
        assert supportcode.sign_extend(machine, c(2, 0b11), int_fromint(4)).toint() == 0b1111

        assert supportcode.sign_extend(machine, c(2, 0b00), int_fromint(100)).tobigint().tolong() == 0
        assert supportcode.sign_extend(machine, c(2, 0b01), int_fromint(100)).tobigint().tolong() == 1
        assert supportcode.sign_extend(machine, c(2, 0b10), int_fromint(100)).tobigint().tolong() == 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110
        assert supportcode.sign_extend(machine, c(2, 0b11), int_fromint(100)).tobigint().tolong() == 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111


def test_unsigned():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        assert bitvector.int_tolong(x.unsigned()) == 0b10001101
        x = c(64, 0b10001101)
        assert bitvector.int_tolong(x.unsigned()) == 0b10001101
        x = c(64, r_uint(-1))
        assert bitvector.int_tolong(x.unsigned()) == (1<<64)-1

def test_get_slice_int():
    for c in si, bi:
        assert supportcode.get_slice_int(machine, int_fromint(8), c(0b011010010000), int_fromint(4)).tolong() == 0b01101001
        assert supportcode.get_slice_int(machine, int_fromint(8), c(-1), int_fromint(4)).tolong() == 0b11111111
        assert supportcode.get_slice_int(machine, int_fromint(64), c(-1), int_fromint(5)).tolong() == 0xffffffffffffffff
        assert supportcode.get_slice_int(machine, int_fromint(100), c(-1), int_fromint(11)).tolong() == 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
        assert supportcode.get_slice_int(machine, int_fromint(8), c(-1), int_fromint(1000)).tolong() == 0b11111111
        assert supportcode.get_slice_int(machine, int_fromint(64), c(-1), int_fromint(1000)).tolong() == 0xffffffffffffffff
        assert supportcode.get_slice_int(machine, int_fromint(100), c(-1), int_fromint(1000)).tolong() == 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111


def test_vector_access():
    for c in gbv, bv:
        x = c(6, 0b101100)
        for i in range(6):
            assert x.read_bit(i) == [0, 0, 1, 1, 0, 1][i]

def test_vector_update():
    for c in gbv, bv:
        x = c(6, 1)
        res = x.update_bit(2, 1)
        assert res.size() == 6
        assert res.toint() == 0b101

        x = c(6, 1)
        res = x.update_bit(0, 1)
        assert res.size() == 6
        assert res.toint() == 0b1

        x = c(6, 0b11)
        res = x.update_bit(2, 0)
        assert res.size() == 6
        assert res.toint() == 0b011

        x = c(6, 0b111)
        res = x.update_bit(1, 0)
        assert res.size() == 6
        assert res.toint() == 0b101

def test_vector_subrange():
    for c in gbv, bv:
        x = c(6, 0b111)
        r = x.subrange(3, 2)
        assert r.size() == 2
        assert r.toint() == 1
        assert isinstance(r, bitvector.SmallBitVector)

    # regression bug
    b = gbv(128, 0x36000000000000001200L)
    x = b.subrange(63, 0)
    assert x.touint() == 0x1200

    b = gbv(128, 0x36000000000000001200L)
    x = b.subrange(66, 0)
    assert x.tolong() == 0x1200
    assert isinstance(x, bitvector.GenericBitVector)

def test_vector_update_subrange():
    for c1 in gbv, bv:
        for c2 in gbv, bv:
            x = c1(8, 0b10001101)
            x = x.update_subrange(5, 2, c2(4, 0b1010))
            assert x.toint() == 0b10101001
            x = c1(64, 0b10001101)
            y = c2(64, 0b1101001010010)
            x = x.update_subrange(63, 0, y)
            assert x.eq(y)

def test_vector_shift():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        res = x.lshift(5)
        assert res.size() == 8
        assert res.toint() == 0b10100000

        x = c(8, 0b10001101)
        res = x.rshift(5)
        assert res.size() == 8
        assert res.toint() == 0b00000100

        x = c(8, 0b10001101)
        res = x.lshift(65)
        assert res.size() == 8
        assert res.toint() == 0

        x = c(8, 0b10001101)
        res = x.rshift(65)
        assert res.size() == 8
        assert res.toint() == 0

def test_vector_shift_bits():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        res = x.lshift_bits(c(8, 5))
        assert res.size() == 8
        assert res.toint() == 0b10100000

        x = c(8, 0b10001101)
        res = x.rshift_bits(c(16, 5))
        assert res.size() == 8
        assert res.toint() == 0b00000100

        x = c(8, 0b10001101)
        res = x.lshift_bits(c(8, 65))
        assert res.size() == 8
        assert res.toint() == 0

        x = c(8, 0b10001101)
        res = x.rshift_bits(c(16, 65))
        assert res.size() == 8
        assert res.toint() == 0

def test_bitvector_touint():
    for size in [6, 6000]:
        assert bv(size, 0b11).touint() == r_uint(0b11)

def test_add_int():
    for c in bi, si:
        assert bv(6, 0b11).add_int(c(0b111111111)).touint() == (0b11 + 0b111111111) & 0b111111
        assert gbv(6000, 0b11).add_int(c(0b111111111)).touint() == 0b11 + 0b111111111

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

def test_eq_int():
    for c1 in bi, si:
        for c2 in bi, si:
            assert bitvector.int_eq(c1(-12331), c2(-12331))
            assert not bitvector.int_eq(c1(-12331), c2(12331))

def test_op_int():
    for c1 in bi, si:
        for c2 in bi, si:
            for v1 in [-10, 223, 12311, 0, 1, 2**63-1]:
                a = c1(v1)
                for v2 in [-10, 223, 12311, 0, 1, 2**63-1, -2**45]:
                    b = c2(v2)
                    assert bitvector.int_tolong(bitvector.int_add(a, b)) == v1 + v2
                    assert bitvector.int_tolong(bitvector.int_sub(a, b)) == v1 - v2
                    assert bitvector.int_tolong(bitvector.int_mul(a, b)) == v1 * v2
                    if v2:
                        assert bitvector.int_tolong(bitvector.int_tdiv(c1(abs(v1)), c2(abs(v2)))) == abs(v1) // abs(v2)
                        assert bitvector.int_tolong(bitvector.int_tmod(c1(abs(v1)), c2(abs(v2)))) == abs(v1) % abs(v2)
                        # (a/b) * b + a%b == a
                        assert bitvector.int_eq(bitvector.int_add(bitvector.int_mul(bitvector.int_tdiv(a, b), b), bitvector.int_tmod(a, b)), a)

                    assert bitvector.int_eq(a, b) == (v1 == v2)
                    assert bitvector.int_lt(a, b) == (v1 < v2)
                    assert bitvector.int_gt(a, b) == (v1 > v2)
                    assert bitvector.int_le(a, b) == (v1 <= v2)
                    assert bitvector.int_ge(a, b) == (v1 >= v2)
                with pytest.raises(ZeroDivisionError):
                    bitvector.int_tdiv(c1(v1), c2(0))
                with pytest.raises(ZeroDivisionError):
                    bitvector.int_tmod(c1(v1), c2(0))

def test_op_int_div_mod():
    for c1 in bi, si:
        for c2 in bi, si:
            # round towards zero
            assert bitvector.int_tolong(bitvector.int_tdiv(c1(1), c2(2))) == 0
            assert bitvector.int_tolong(bitvector.int_tdiv(c1(-1), c2(2))) == 0
            assert bitvector.int_tolong(bitvector.int_tdiv(c1(1), c2(-2))) == 0
            assert bitvector.int_tolong(bitvector.int_tdiv(c1(-1), c2(-2))) == 0

            # mod signs
            assert bitvector.int_tolong(bitvector.int_tmod(c1(5), c2(3))) == 2
            assert bitvector.int_tolong(bitvector.int_tmod(c1(5), c2(-3))) == 2
            assert bitvector.int_tolong(bitvector.int_tmod(c1(-5), c2(3))) == -2
            assert bitvector.int_tolong(bitvector.int_tmod(c1(-5), c2(-3))) == -2

            # ovf correctly
            assert bitvector.int_tolong(bitvector.int_tdiv(c1(-2**63), c2(-1))) == 2 ** 63
            assert bitvector.int_tolong(bitvector.int_tmod(c1(-2**63), c2(-1))) == 0


def test_op_gv_int():
    for c1 in gbv, bv:
        for c2 in bi, si:
            assert c1(16, 4).add_int(c2(9)).touint() == 13
            assert c1(16, 4).sub_int(c2(9)).touint() == r_uint((-5) & 0xffff)


def test_string_of_bits():
    for c in gbv, bv:
        assert c(32, 0x1245ab).string_of_bits() == "0x001245AB"
        assert c(64, 0x1245ab).string_of_bits() == "0x00000000001245AB"
        assert c(3, 0b1).string_of_bits() == "0b001"
        assert c(9, 0b1101).string_of_bits() == "0b000001101"

def test_int_fromstr():
    for s in ['0', '-1', '12315', '1' * 100, '-' + '2' * 200]:
        assert bitvector.int_tolong(bitvector.int_fromstr(s)) == int(s)
