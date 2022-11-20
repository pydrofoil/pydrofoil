import pytest

from pydrofoil import supportcode
from pydrofoil import bitvector
from pydrofoil.bitvector import int_fromint, int_frombigint

from rpython.rlib.rarithmetic import r_uint, intmask
from rpython.rlib.rbigint import rbigint

def gbv(size, val):
    return (size, -1, rbigint.fromlong(val))

def bv(size, val):
    return (size, r_uint(val), None)

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
    def check(size, val, targetsize, res):
        assert bitvector.bv_tolong(supportcode.sign_extend(machine, c(size, val), int_fromint(targetsize))) == res
    for c in gbv, bv:
        check(1, 0b0, 2, 0)
        check(1, 0b1, 2, 0b11)
        check(2, 0b00, 4, 0)
        check(2, 0b01, 4, 1)
        check(2, 0b10, 4, 0b1110)
        check(2, 0b11, 4, 0b1111)

        check(2, 0b00, 100, 0)
        check(2, 0b01, 100, 1)
        check(2, 0b10, 100, 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110)
        check(2, 0b11, 100, 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111)


def test_unsigned():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        assert bitvector.int_tolong(bitvector.bv_unsigned(x)) == 0b10001101
        x = c(64, 0b10001101)
        assert bitvector.int_tolong(bitvector.bv_unsigned(x)) == 0b10001101
        x = c(64, r_uint(-1))
        assert bitvector.int_tolong(bitvector.bv_unsigned(x)) == (1<<64)-1

def test_get_slice_int():
    for c in si, bi:
        for lenvalue, bvvalue, startvalue, res in [
                (8, 0b011010010000, 4, 0b01101001),
                (8, -1, 4, 0b11111111),
                (64, -1, 5, 0xffffffffffffffff),
                (100, -1, 11, 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111),
                (8, -1, 1000, 0b11111111),
                (64, -1, 1000, 0xffffffffffffffff),
                (100, -1, 1000, 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111),
        ]:
            assert bitvector.bv_tolong(supportcode.get_slice_int(machine, int_fromint(lenvalue), c(bvvalue), int_fromint(startvalue))) == res


def test_vector_access():
    for c in gbv, bv:
        x = c(6, 0b101100)
        for i in range(6):
            assert bitvector.bv_read_bit(x, i) == [0, 0, 1, 1, 0, 1][i]

def test_vector_update():
    for c in gbv, bv:
        x = c(6, 1)
        res = bitvector.bv_update_bit(x, 2, 1)
        assert bitvector.bv_size(res) == 6
        assert bitvector.bv_toint(res) == 0b101

        x = c(6, 1)
        res = bitvector.bv_update_bit(x, 0, 1)
        assert bitvector.bv_size(res) == 6
        assert bitvector.bv_toint(res) == 0b1

        x = c(6, 0b11)
        res = bitvector.bv_update_bit(x, 2, 0)
        assert bitvector.bv_size(res) == 6
        assert bitvector.bv_toint(res) == 0b011

        x = c(6, 0b111)
        res = bitvector.bv_update_bit(x, 1, 0)
        assert bitvector.bv_size(res) == 6
        assert bitvector.bv_toint(res) == 0b101

def test_vector_subrange():
    for c in gbv, bv:
        x = c(6, 0b111)
        res = bitvector.bv_subrange(x, 3, 2)
        assert bitvector.bv_size(res) == 2
        assert bitvector.bv_toint(res) == 1
        assert res[2] is None

    # regression bug
    b = gbv(128, 0x36000000000000001200L)
    x = bitvector.bv_subrange(b, 63, 0)
    assert bitvector.bv_touint(x) == 0x1200

    b = gbv(128, 0x36000000000000001200L)
    x = bitvector.bv_subrange(b, 66, 0)
    assert bitvector.bv_touint(x) == 0x1200
    assert x[2] is not None

def test_vector_update_subrange():
    for c1 in gbv, bv:
        for c2 in gbv, bv:
            x = c1(8, 0b10001101)
            x = bitvector.bv_update_subrange(x, 5, 2, c2(4, 0b1010))
            assert bitvector.bv_toint(x) == 0b10101001
            x = c1(64, 0b10001101)
            y = c2(64, 0b1101001010010)
            x = bitvector.bv_update_subrange(x, 63, 0, y)
            assert bitvector.bv_eq(x, y)

def test_vector_shift():
    for c in gbv, bv:
        for val, shift, lres, rres in [
                (0b10001101, 5, 0b10100000, 0b00000100),
                (0b10001101, 65, 0, 0),
        ]:
            x = c(8, val)
            res = bitvector.bv_lshift(x, shift)
            assert bitvector.bv_size(res) == 8
            assert bitvector.bv_toint(res) == lres

            res = bitvector.bv_rshift(x, shift)
            assert bitvector.bv_size(res) == 8
            assert bitvector.bv_toint(res) == rres

            res = bitvector.bv_lshift_bits(x, c(12, shift))
            assert bitvector.bv_size(res) == 8
            assert bitvector.bv_toint(res) == lres

            res = bitvector.bv_rshift_bits(x, c(12, shift))
            assert bitvector.bv_size(res) == 8
            assert bitvector.bv_toint(res) == rres

def test_bitvector_touint():
    for size in [6, 6000]:
        assert bitvector.bv_touint(bv(size, 0b11)) == r_uint(0b11)

def test_add_int():
    for c in bi, si:
        assert bitvector.bv_touint(bitvector.bv_add_int(bv(6, 0b11), c(0b111111111))) == (0b11 + 0b111111111) & 0b111111
        assert bitvector.bv_touint(bitvector.bv_add_int(gbv(6000, 0b11), c(0b111111111))) == 0b11 + 0b111111111

def test_bv_bitwise():
    for c in gbv, bv:
        i1 = c(8, 0b11110000)
        i2 = c(8, 0b11001100)
        res = bitvector.bv_and(i1, i2)
        assert bitvector.bv_toint(res) == 0b11110000 & 0b11001100
        res = bitvector.bv_or(i1, i2)
        assert bitvector.bv_toint(res) == 0b11110000 | 0b11001100
        res = bitvector.bv_xor(i1, i2)
        assert bitvector.bv_toint(res) == 0b11110000 ^ 0b11001100
        res = bitvector.bv_invert(i1)
        assert bitvector.bv_toint(res) == 0b00001111

        i1 = c(8, 0b11110101)
        i2 = c(4,     0b1100)
        res = bitvector.bv_and(i1, i2)
        assert bitvector.bv_toint(res) == 0b11110101 & 0b1100
        res = bitvector.bv_or(i1, i2)
        assert bitvector.bv_toint(res) == 0b11110101 | 0b1100
        res = bitvector.bv_xor(i1, i2)
        assert bitvector.bv_toint(res) == 0b11110101 ^ 0b1100
        res = bitvector.bv_invert(i1)
        assert bitvector.bv_toint(res) == 0b1010

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
            assert bitvector.bv_toint(bitvector.bv_add_int(c1(16, 4), c2(9))) == 13
            assert bitvector.bv_toint(bitvector.bv_sub_int(c1(16, 4), c2(9))) == r_uint((-5) & 0xffff)


def test_string_of_bits():
    for c in gbv, bv:
        assert bitvector.bv_string_of_bits(c(32, 0x1245ab)) == "0x001245AB"
        assert bitvector.bv_string_of_bits(c(64, 0x1245ab)) == "0x00000000001245AB"
        assert bitvector.bv_string_of_bits(c(3, 0b1)) == "0b001"
        assert bitvector.bv_string_of_bits(c(9, 0b1101)) == "0b000001101"

def test_int_fromstr():
    for s in ['0', '-1', '12315', '1' * 100, '-' + '2' * 200]:
        assert bitvector.int_tolong(bitvector.int_fromstr(s)) == int(s)
