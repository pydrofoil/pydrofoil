import pytest
import math

from pydrofoil import supportcode
from pydrofoil import bitvector
from pydrofoil.bitvector import Integer, SmallInteger, BigInteger, MININT, SparseBitVector
from pydrofoil.real import *
from hypothesis import given, strategies, assume, example, settings
from fractions import Fraction

from rpython.rlib.rarithmetic import r_uint, intmask, r_ulonglong
from rpython.rlib.rbigint import rbigint


def make_int(data):
    if data.draw(strategies.booleans()):
        # big ints
        return BigInteger(rbigint.fromlong(data.draw(strategies.integers())))
    else:
        # small ints
        return SmallInteger(data.draw(ints))

ints = strategies.integers(-sys.maxint-1, sys.maxint)
wrapped_ints = strategies.builds(
        make_int,
        strategies.data())

def _make_small_bitvector(data, width=-1):
    if width == -1:
        width = data.draw(strategies.integers(1, 64))
    value = data.draw(strategies.integers(0, 2**width-1))
    return bitvector.SmallBitVector(width, r_uint(value))

def _make_sparse_bitvector(data, width=-1):
    if width == -1:
        width = data.draw(strategies.integers(65, 1000))
    value = data.draw(strategies.integers(0, 2**64-1))
    return bitvector.SparseBitVector(width, r_uint(value))

def _make_generic_bitvector(data, width=-1):
    if width == -1:
        width = data.draw(strategies.integers(65, 1000))
    value = data.draw(strategies.integers(0, 2**width-1))
    return bitvector.GenericBitVector(width, rbigint.fromlong(value))

def make_bitvector(data, width=-1):
    if width > 0:
        if width <= 64:
            kind = 0
        else:
            kind = data.draw(strategies.integers(1, 2))
    else:
        kind = data.draw(strategies.integers(0, 2))
    if kind == 0:
        return _make_small_bitvector(data, width)
    else:
        if kind == 1:
            return _make_sparse_bitvector(data, width)
        else:
            return _make_generic_bitvector(data, width)

bitvectors = strategies.builds(
    make_bitvector,
    strategies.data())

def make_two_bitvectors(data):
    kind = data.draw(strategies.integers(0, 4))
    if kind == 0:
        v1 = _make_small_bitvector(data)
        v2 = _make_small_bitvector(data, v1.size())
    else:
        width = data.draw(strategies.integers(65, 1000))
        if kind == 1:
            v1 = _make_sparse_bitvector(data)
            v2 = _make_sparse_bitvector(data, v1.size())
        elif kind == 2 or kind == 4:
            v1 = _make_sparse_bitvector(data)
            v2 = _make_generic_bitvector(data, v1.size())
            if kind == 4:
                v2, v1 = v1, v2
        else:
            v1 = _make_generic_bitvector(data)
            v2 = _make_generic_bitvector(data, v1.size())
    return v1, v2


two_bitvectors = strategies.builds(
    make_two_bitvectors,
    strategies.data())


def gbv(size, val):
    return bitvector.GenericBitVector(size, rbigint.fromlong(val))

def bv(size, val):
    return bitvector.from_ruint(size, r_uint(val))

def si(val):
    return bitvector.SmallInteger(val)

def bi(val):
    return bitvector.BigInteger(rbigint.fromlong(val))

machine = "dummy"

def test_signed_bv():
    assert supportcode.signed_bv(machine, 0b0, 1) == 0
    assert supportcode.signed_bv(machine, 0b1, 1) == -1
    assert supportcode.signed_bv(machine, 0b0, 2) == 0
    assert supportcode.signed_bv(machine, 0b1, 2) == 1
    assert supportcode.signed_bv(machine, 0b10, 2) == -2
    assert supportcode.signed_bv(machine, 0b11, 2) == -1

def test_signed():
    for c in gbv, bv:
        assert supportcode.sail_signed(machine, c(1, 0b0)).toint() == 0
        assert supportcode.sail_signed(machine, c(1, 0b1)).toint() == -1
        assert supportcode.sail_signed(machine, c(2, 0b0)).toint() == 0
        assert supportcode.sail_signed(machine, c(2, 0b1)).toint() == 1
        assert supportcode.sail_signed(machine, c(2, 0b10)).toint() == -2
        assert supportcode.sail_signed(machine, c(2, 0b11)).toint() == -1
        assert supportcode.sail_signed(machine, c(64, 0xffffffffffffffff)).toint() == -1
        assert supportcode.sail_signed(machine, c(64, 0x1)).toint() == 1

def test_sign_extend():
    for c in gbv, bv:
        assert supportcode.sign_extend(machine, c(1, 0b0), Integer.fromint(2)).toint() == 0
        assert supportcode.sign_extend(machine, c(1, 0b1), Integer.fromint(2)).toint() == 0b11
        assert supportcode.sign_extend(machine, c(2, 0b00), Integer.fromint(4)).toint() == 0
        assert supportcode.sign_extend(machine, c(2, 0b01), Integer.fromint(4)).toint() == 1
        assert supportcode.sign_extend(machine, c(2, 0b10), Integer.fromint(4)).toint() == 0b1110
        assert supportcode.sign_extend(machine, c(2, 0b11), Integer.fromint(4)).toint() == 0b1111

        assert supportcode.sign_extend(machine, c(2, 0b00), Integer.fromint(100)).tobigint().tolong() == 0
        assert isinstance(supportcode.sign_extend(machine, bv(2, 0b00), Integer.fromint(100)), SparseBitVector) #test if it returns SparseBitVector
        assert supportcode.sign_extend(machine, c(2, 0b01), Integer.fromint(100)).tobigint().tolong() == 1
        assert supportcode.sign_extend(machine, c(2, 0b10), Integer.fromint(100)).tobigint().tolong() == 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110
        assert supportcode.sign_extend(machine, c(2, 0b11), Integer.fromint(100)).tobigint().tolong() == 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111

def test_zero_extend():
    for c in gbv, bv:
        assert supportcode.zero_extend(machine, c(1, 0b0), Integer.fromint(2)).size() == 2
        assert supportcode.zero_extend(machine, c(2, 0b00), Integer.fromint(100)).size() == 100
        assert supportcode.zero_extend(machine, c(1, 0b0), Integer.fromint(2)).toint() == 0
        assert supportcode.zero_extend(machine, c(1, 0b1), Integer.fromint(2)).toint() == 0b01
        assert supportcode.zero_extend(machine, c(2, 0b00), Integer.fromint(4)).toint() == 0
        assert supportcode.zero_extend(machine, c(2, 0b01), Integer.fromint(4)).toint() == 1
        assert supportcode.zero_extend(machine, c(2, 0b10), Integer.fromint(4)).toint() == 0b0010
        assert supportcode.zero_extend(machine, c(2, 0b11), Integer.fromint(4)).toint() == 0b0011

        assert supportcode.zero_extend(machine, c(2, 0b00), Integer.fromint(100)).tobigint().tolong() == 0
        assert supportcode.zero_extend(machine, c(2, 0b01), Integer.fromint(100)).tobigint().tolong() == 1
        assert supportcode.zero_extend(machine, c(2, 0b10), Integer.fromint(100)).tobigint().tolong() == 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010
        assert supportcode.zero_extend(machine, c(2, 0b11), Integer.fromint(100)).tobigint().tolong() == 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011


def test_unsigned():
    for c in gbv, bv:
        x = c(8, 0b10001101)
        assert x.unsigned().tolong() == 0b10001101
        x = c(64, 0b10001101)
        assert x.unsigned().tolong() == 0b10001101
        x = c(64, r_uint(-1))
        assert x.unsigned().tolong() == (1<<64)-1

def test_get_slice_int():
    for c in si, bi:
        assert supportcode.get_slice_int(machine, Integer.fromint(8), c(0b011010010000), Integer.fromint(4)).tolong() == 0b01101001
        assert supportcode.get_slice_int(machine, Integer.fromint(8), c(-1), Integer.fromint(4)).tolong() == 0b11111111
        assert supportcode.get_slice_int(machine, Integer.fromint(64), c(-1), Integer.fromint(5)).tolong() == 0xffffffffffffffff
        assert supportcode.get_slice_int(machine, Integer.fromint(100), c(-1), Integer.fromint(11)).tolong() == 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
        assert supportcode.get_slice_int(machine, Integer.fromint(8), c(-1), Integer.fromint(1000)).tolong() == 0b11111111
        assert supportcode.get_slice_int(machine, Integer.fromint(64), c(-1), Integer.fromint(1000)).tolong() == 0xffffffffffffffff
        assert supportcode.get_slice_int(machine, Integer.fromint(100), c(-1), Integer.fromint(1000)).tolong() == 0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111

@given(wrapped_ints, strategies.integers(0, 100), strategies.integers(1, 100), strategies.data())
def test_set_slice_int(i, start, length, data):
    value = data.draw(strategies.integers(0, 2**length - 1))
    bv = bitvector.from_bigint(length, rbigint.fromlong(value))
    i2 = i.set_slice_int(length, start, bv)
    assert i2.slice(length, start).eq(bv)
    if start:
        assert i2.slice(start, 0).eq(i.slice(start, 0))
        assert i2.slice(100, start + length).eq(i.slice(100, start + length))

@given(strategies.integers(1, 1000), strategies.integers(0, sys.maxint), wrapped_ints)
def test_hypothesis_get_slice_int(length, start, i):
    res = supportcode.get_slice_int_i_o_i(machine, length, i, start)
    assert res.size() == length
    assert res.tobigint().tolong() == (i.tolong() >> start) % (2 ** length)

@given(strategies.integers(1, 64), strategies.integers(0, sys.maxint), ints)
def test_hypothesis_get_slice_int_i_i_i(length, start, i):
    res = supportcode.get_slice_int_i_i_i(machine, length, i, start)
    assert res == (i >> start) % (2 ** length)

@given(strategies.integers(1, 64), strategies.integers(0, sys.maxint), wrapped_ints)
def test_hypothesis_get_slice_int_unwrapped_res(length, start, i):
    res = supportcode.get_slice_int_i_o_i_unwrapped_res(machine, length,
            i, start)
    assert res == (i.tolong() >> start) % (2 ** length)

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

@given(strategies.data())
def test_hypothesis_vector_subrange(data):
    bitwidth = data.draw(strategies.integers(1, 10000))
    lower = data.draw(strategies.integers(0, bitwidth-1))
    upper = data.draw(strategies.integers(lower, bitwidth-1))
    value = data.draw(strategies.integers(0, 2**bitwidth - 1))
    as_bit_string = bin(value)[2:]
    assert len(as_bit_string) <= bitwidth
    as_bit_string = as_bit_string.rjust(bitwidth, '0')[::-1]
    correct_res = as_bit_string[lower:upper+1] # sail is inclusive
    correct_res_as_int = int(correct_res[::-1], 2)

    # now do the sail computation
    bv = bitvector.from_bigint(bitwidth, rbigint.fromlong(value))
    bvres = bv.subrange(upper, lower)
    assert bvres.tobigint().tolong() == correct_res_as_int

@settings(deadline=1000)
@given(strategies.data())
def test_hypothesis_sign_extend(data):
    bitwidth = data.draw(strategies.integers(1, 10000))
    target_bitwidth = bitwidth + data.draw(strategies.integers(1, 100))
    value = data.draw(strategies.integers(0, 2**bitwidth - 1))
    bv = bitvector.from_bigint(bitwidth, rbigint.fromlong(value))
    res = bv.sign_extend(target_bitwidth)
    assert bv.signed().tobigint().tolong() == res.signed().tobigint().tolong()

@given(strategies.data())
def test_hypothesis_sign_extend_ruint(data):
    bitwidth = data.draw(strategies.integers(1, 63))
    targetwidth = data.draw(strategies.integers(bitwidth, 64))
    value = data.draw(strategies.integers(-2**(bitwidth-1), 2**(bitwidth-1)-1))
    bv = supportcode._mask(bitwidth, r_uint(value))
    res = supportcode.sign_extend_bv_i_i(machine, bv, bitwidth, targetwidth)
    assert res == supportcode._mask(targetwidth, r_uint(value))

@given(strategies.data())
def test_hypothesis_vector_subrange_unwrapped_res(data):
    if data.draw(strategies.booleans()):
        bitwidth = data.draw(strategies.integers(65, 10000))
    else:
        bitwidth = data.draw(strategies.integers(1, 64))
    lower = data.draw(strategies.integers(0, bitwidth-1))
    upper = data.draw(strategies.integers(lower, min(bitwidth-1, lower + 63)))
    assert 1 <= upper - lower + 1 <= 64
    assert 0 <= lower <= upper < bitwidth
    value = data.draw(strategies.integers(0, 2**bitwidth - 1))
    as_bit_string = bin(value)[2:]
    assert len(as_bit_string) <= bitwidth
    as_bit_string = as_bit_string.rjust(bitwidth, '0')[::-1]
    correct_res = as_bit_string[lower:upper+1] # sail is inclusive
    correct_res_as_int = int(correct_res[::-1], 2)

    # now do the sail computation
    bv = bitvector.from_bigint(bitwidth, rbigint.fromlong(value))
    bvres = bv.subrange_unwrapped_res(upper, lower)
    assert bvres == correct_res_as_int

@given(strategies.data())
def Xtest_hypothesis_subrange_unwrapped_res(data):
    bitwidth = data.draw(strategies.integers(1, 10000))
    start = data.draw(strategies.integers(0, 2 * bitwidth))
    value = data.draw(strategies.integers(0, 2**bitwidth - 1))
    rb = rbigint.fromlong(value)
    bv = bitvector.from_bigint(bitwidth, rb)
    res = bv.subrange_unwrapped_res(start + 63, start)
    assert res == rb.rshift(start).and_(rbigint.fromlong(2**64-1)).tolong()

@given(strategies.integers(), strategies.integers(0, 100))
@example(-9223372036854775935L, 1)
@example(-9223372036854775809L, 63)
def test_hypothesis_extract_ruint(value, shift):
    rval = rbigint.fromlong(value)
    assert bitvector.rbigint_extract_ruint(rval, shift) == r_uint(value >> shift)

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

def test_sparse_vector_update_subrange():
    for c in SparseBitVector, gbv:
        x = c(100, 0b10001101)
        x = x.update_subrange(5, 2, bv(4, 0b1010))
        assert x.toint() == 0b10101001
        x = c(100, 0b10001101)
        y = c(100, 0b1101001010010)
        x = x.update_subrange(99, 0, y)
        assert x.eq(y)
        x = SparseBitVector(65, 0b10001101)
        y = c(65, 0b1101001010010)
        x = x.update_subrange(64, 0, y)
        assert x.eq(y)
    x = SparseBitVector(1000, 0b10001101)
    y = gbv(1000, 0b1101001010010)
    x = x.update_subrange(999, 0, y)
    assert isinstance(x, bitvector.GenericBitVector)

@given(bitvectors, strategies.data())
def test_vector_update_subrange_hypothesis(bv, data):
    width = bv.size()
    value = bv.tolong()
    lower = data.draw(strategies.integers(0, width-1))
    upper = data.draw(strategies.integers(lower, width-1))
    subwidth = upper - lower + 1
    subvalue = r_uint(data.draw(strategies.integers(0, 2 ** min(subwidth, 64) - 1)))
    replace_bv = make_bitvector(data, subwidth)

    res = bv.update_subrange(upper, lower, replace_bv)
    # check: the read of the same range must return replace_bv
    assert replace_bv.eq(res.subrange(upper, lower))
    # the other bits must be unchanged
    if lower:
        assert res.subrange(lower - 1, 0).eq(bv.subrange(lower - 1, 0))
    if upper < width - 1:
        assert res.subrange(width - 1, upper + 1).eq(bv.subrange(width - 1, upper + 1))

@given(strategies.data())
def test_sparse_vector_update_subrange_hypothesis(data):
    width = data.draw(strategies.integers(65, 256))
    value = r_uint(data.draw(strategies.integers(0, 2**64 - 1)))
    lower = data.draw(strategies.integers(0, width-1))
    upper = data.draw(strategies.integers(lower, width-1))
    subwidth = upper - lower + 1
    subvalue = r_uint(data.draw(strategies.integers(0, 2 ** min(subwidth, 64) - 1)))
    replace_bv = bitvector.from_ruint(subwidth, subvalue)

    # two checks: check that the generic is the same as sparse
    sbv = SparseBitVector(width, value)
    sres = sbv.update_subrange(upper, lower, replace_bv)
    sres2 = sbv._to_generic().update_subrange(upper, lower, replace_bv)
    assert sres.eq(sres2)
    # second check: the read of the same range must return replace_bv
    assert replace_bv.eq(sres.subrange(upper, lower))


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


def test_arith_shiftr():
    for c in bv, gbv:
        x = c(8, 0b10001101)
        res = x.arith_rshift(2)
        assert res.size() == 8
        assert res.toint() == 0b11100011

        res = x.arith_rshift(8)
        assert res.size() == 8
        assert res.toint() == 0b11111111

        x = c(8, 0b00101101)
        res = x.arith_rshift(3)
        assert res.size() == 8
        assert res.toint() == 0b101

@given(bitvectors, strategies.data())
def test_arith_shiftr_hypothesis(bv, data):
    value = bv.tolong()
    size = bv.size()
    shift = data.draw(strategies.integers(0, size+10))
    res = bv.arith_rshift(shift)
    # compare against signed, then integer shift
    intres = bv.signed().tobigint().tolong() >> shift
    assert res.tobigint().tolong() == intres & ((1 << size) - 1)

def test_bitvector_touint():
    for size in [6, 6000]:
        assert bv(size, 0b11).touint() == r_uint(0b11)

def test_add_int():
    for c in bi, si:
        assert bv(6, 0b11).add_int(c(0b111111111)).touint() == (0b11 + 0b111111111) & 0b111111
        assert gbv(6000, 0b11).add_int(c(0b111111111)).touint() == 0b11 + 0b111111111

def test_add_bits_int_bv_i():
    assert supportcode.add_bits_int_bv_i(None, r_uint(0b11), 6, 0b111111111) == (0b11 + 0b111111111) & 0b111111
    assert supportcode.add_bits_int_bv_i(None, r_uint(0b11), 6, -0b111111111) == (0b11 - 0b111111111) & 0b111111
    assert supportcode.add_bits_int_bv_i(None, r_uint(0b1011), 6, -2 ** 63) == (0b1011 - 2**63) & 0b111111

@given(strategies.data())
def test_hypothesis_add_bits_int(data):
    if not data.draw(strategies.booleans()):
        bitwidth = data.draw(strategies.integers(1, 64))
    else:
        bitwidth = data.draw(strategies.integers(65, 10000))
    value = data.draw(strategies.integers(0, 2**bitwidth - 1))
    bvvalue = bitvector.from_bigint(bitwidth, rbigint.fromlong(value))
    rhs = data.draw(ints)
    irhs = Integer.frombigint(rbigint.fromlong(rhs))
    bvres = bvvalue.add_int(irhs)
    assert bvres.tolong() == (value + rhs) % (2 ** bitwidth)
    bvres = bvvalue.sub_int(irhs)
    assert bvres.tolong() == (value - rhs) % (2 ** bitwidth)

@given(strategies.data())
def test_hypothesis_add_bits_int_bv_i(data):
    bitwidth = data.draw(strategies.integers(1, 64))
    value = r_uint(data.draw(strategies.integers(0, 2**bitwidth - 1)))
    rhs = data.draw(ints)
    res = supportcode.add_bits_int_bv_i(None, value, bitwidth, rhs)
    assert res == supportcode._mask(bitwidth, value + r_uint(rhs))
    res = supportcode.sub_bits_int_bv_i(None, value, bitwidth, rhs)
    assert res == supportcode._mask(bitwidth, value - r_uint(rhs))

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

def test_add_bv():
    for c in gbv, bv:
        assert supportcode.add_bits(None, c(6, 0b11), c(6, 0b111)).touint() == (0b11 + 0b111) & 0b111111
        assert supportcode.add_bits(None, c(6, 0b10000), c(6, 0b10001)).touint() == (0b10000 + 0b10001) & 0b111111
        assert supportcode.add_bits(None, c(6, 0b100000), c(6, 0b100001)).touint() == (0b100000 + 0b100001) & 0b111111

def test_sub_bv():
    for c in gbv, bv:
        assert supportcode.sub_bits(None, c(6, 0b111), c(6, 0b11)).touint() == (0b111 - 0b11) & 0b111111
        assert supportcode.sub_bits(None, c(6, 0b10000), c(6, 0b10001)).touint() == (0b10000 - 0b10001) & 0b111111
        assert supportcode.sub_bits(None, c(6, 0b100000), c(6, 0b100001)).touint() == (0b100000 - 0b100001) & 0b111111


def test_eq_int():
    for c1 in bi, si:
        for c2 in bi, si:
            assert c1(-12331).eq(c2(-12331))
            assert not c1(-12331).eq(c2(12331))

def test_op_int():
    for c1 in bi, si:
        for c2 in bi, si:
            for v1 in [-10, 223, 12311, 0, 1, 2**63-1]:
                a = c1(v1)
                for v2 in [-10, 223, 12311, 0, 1, 8, 2**63-1, -2**45]:
                    b = c2(v2)
                    assert a.add(b).tolong() == v1 + v2
                    assert a.sub(b).tolong() == v1 - v2
                    assert a.mul(b).tolong() == v1 * v2
                    if v2:
                        assert c1(abs(v1)).tdiv(c2(abs(v2))).tolong() == abs(v1) // abs(v2)
                        assert c1(abs(v1)).tmod(c2(abs(v2))).tolong() == abs(v1) % abs(v2)
                        # (a/b) * b + a%b == a
                        assert a.tdiv(b).mul(b).add(a.tmod(b)).eq(a)

                    assert a.eq(b) == (v1 == v2)
                    assert a.lt(b) == (v1 < v2)
                    assert a.gt(b) == (v1 > v2)
                    assert a.le(b) == (v1 <= v2)
                    assert a.ge(b) == (v1 >= v2)
                with pytest.raises(ZeroDivisionError):
                    c1(v1).tdiv(c2(0))
                with pytest.raises(ZeroDivisionError):
                    c1(v1).tmod(c2(0))

@given(wrapped_ints, wrapped_ints)
def test_op_int_hypothesis(a, b):
    v1 = a.tobigint().tolong()
    v2 = b.tobigint().tolong()
    assert a.add(b).tolong() == v1 + v2
    assert a.sub(b).tolong() == v1 - v2
    assert a.mul(b).tolong() == v1 * v2
    if v2:
        assert a.abs().tdiv(b.abs()).tolong() == abs(v1) // abs(v2)
        assert a.abs().tmod(b.abs()).tolong() == abs(v1) % abs(v2)
        # (a/b) * b + a%b == a
        assert a.tdiv(b).mul(b).add(a.tmod(b)).eq(a)

    assert a.eq(b) == (v1 == v2)
    assert a.lt(b) == (v1 < v2)
    assert a.gt(b) == (v1 > v2)
    assert a.le(b) == (v1 <= v2)
    assert a.ge(b) == (v1 >= v2)
    with pytest.raises(ZeroDivisionError):
        a.tdiv(si(0))
    with pytest.raises(ZeroDivisionError):
        a.tdiv(si(0))
    with pytest.raises(ZeroDivisionError):
        a.tmod(bi(0))
    with pytest.raises(ZeroDivisionError):
        a.tmod(bi(0))

@given(wrapped_ints, ints)
def test_int_add_sub_hypothesis(a, b):
    v1 = a.tobigint().tolong()
    v2 = b
    assert a.int_add(b).tolong() == v1 + v2
    assert a.int_sub(b).tolong() == v1 - v2

def test_op_int_div_mod():
    for c1 in bi, si:
        for c2 in bi, si:
            # round towards zero
            assert c1(1).tdiv(c2(2)).tolong() == 0
            assert c1(-1).tdiv(c2(2)).tolong() == 0
            assert c1(1).tdiv(c2(-2)).tolong() == 0
            assert c1(-1).tdiv(c2(-2)).tolong() == 0

            # mod signs
            assert c1(5).tmod(c2(3)).tolong() == 2
            assert c1(5).tmod(c2(-3)).tolong() == 2
            assert c1(-5).tmod(c2(3)).tolong() == -2
            assert c1(-5).tmod(c2(-3)).tolong() == -2

            # ovf correctly
            assert c1(-2**63).tdiv(c2(-1)).tolong() == 2 ** 63
            assert c1(-2**63).tmod(c2(-1)).tolong() == 0

def test_shift_amount():
    for i in range(63):
        assert BigInteger._shift_amount(2 ** i) == i

def test_mul_optimized(monkeypatch):
    monkeypatch.setattr(rbigint, "mul", None)
    monkeypatch.setattr(rbigint, "int_mul", None)
    res = bi(3 ** 100).mul(si(16))
    assert res.tolong() == 3 ** 100 * 16
    res = si(1024).mul(bi(-5 ** 60))
    assert res.tolong() == -5 ** 60 * 1024


def test_op_gv_int():
    for c1 in gbv, bv:
        for c2 in bi, si:
            assert c1(16, 4).add_int(c2(9)).touint() == 13
            assert c1(16, 4).sub_int(c2(9)).touint() == r_uint((-5) & 0xffff)

def test_int_shift():
    for c in bi, si:
        assert c(0b1010001).rshift(2).tobigint().tolong() == 0b10100
        assert c(-0b1010001).rshift(3).tobigint().tolong() == -0b1011
        assert c(0b1010001).lshift(2).tobigint().tolong() == 0b101000100
        assert c(-0b1010001).lshift(3).tobigint().tolong() == -0b1010001000

def test_replicate_bits():
    for c1 in gbv, bv:
        res = c1(3, 0b011).replicate(10)
        assert res.size() == 3 * 10
        assert res.touint() == 0b011011011011011011011011011011
        res = c1(8, 0xe7).replicate(15)
        assert res.size() == 8*15
        assert res.tobigint().tolong() == 0xe7e7e7e7e7e7e7e7e7e7e7e7e7e7e7

def test_truncate():
    for c1 in gbv, bv:
        res = c1(10, 0b1011010100).truncate(2)
        assert res.size() == 2
        assert res.touint() == 0b00
        res = c1(10, 0b1011010100).truncate(6)
        assert res.size() == 6
        assert res.touint() == 0b010100

@given(bitvectors, strategies.data())
def test_hypothesis_truncate(bv, data):
    bitwidth = bv.size()
    if not data.draw(strategies.booleans()):
        truncatewidth = data.draw(strategies.integers(1, min(64, bitwidth)))
    else:
        truncatewidth = data.draw(strategies.integers(1, bitwidth))
    value = data.draw(strategies.integers(0, 2**bitwidth - 1))
    as_bit_string = bin(value)[2:]
    bv = bitvector.from_bigint(bitwidth, rbigint.fromlong(value))
    res = bv.truncate(truncatewidth)
    assert bin(bv.tolong())[2:].rjust(bitwidth, '0')[-truncatewidth:] == bin(res.tolong())[2:].rjust(truncatewidth, '0')


def test_string_of_bits():
    for c in gbv, bv:
        assert c(32, 0x1245ab).string_of_bits() == "0x001245AB"
        assert c(64, 0x1245ab).string_of_bits() == "0x00000000001245AB"
        assert c(3, 0b1).string_of_bits() == "0b001"
        assert c(9, 0b1101).string_of_bits() == "0b000001101"


def test_append():
    for c1 in gbv, bv:
        for c2 in gbv, bv:
            assert c1(16, 0xa9e3).append(c2(16, 0x04fb)).toint() == 0xa9e304fb

def test_abs_int():
    for c in si, bi:
        for value in [-2**63, -6, 10, 2**63-1]:
            assert c(value).abs().tobigint().tolong() == abs(value)

def test_rshift_int():
   for c in bi, si:
       assert c(0b1010001).rshift(2).tobigint().tolong() == 0b10100
       assert c(-0b1010001).rshift(3).tobigint().tolong() == -11

def test_emod_ediv_int():
   for c1 in bi, si:
        for c2 in bi, si:
            assert c1(123875).emod(si(13)).toint() == 123875 % 13
            assert c1(123875).ediv(c2(13)).toint() == 123875 // 13
            assert c1(MININT).ediv(c2(2)).toint() == -2**62
            assert c1(MININT).ediv(c2(-2)).toint() == 2**62
            assert c1(MININT).ediv(c2(MININT)).toint() == 1
            assert c1(5).ediv(c2(MININT)).toint() == 0
            assert c1(-5).ediv(c2(MININT)).toint() == 1
            assert c1(MININT + 1).ediv(c2(sys.maxint)).toint() == -1
            assert c1(MININT).ediv(c2(MININT)).toint() == 1
            assert c1(7).ediv(c2(5)).toint() == 1
            assert c1(7).ediv(c2(-5)).toint() == -1
            assert c1(-7).ediv(c2(-5)).toint() == 2
            assert c1(-7).ediv(c2(5)).toint() == -2
            assert c1(12).ediv(c2(3)).toint() == 4
            assert c1(12).ediv(c2(-3)).toint() == -4
            assert c1(-12).ediv(c2(3)).toint() == -4
            assert c1(-12).ediv(c2(-3)).toint() == 4
            assert c1(MININT).emod(c2(2)).toint() == 0
            assert c1(MININT).emod(c2(- 2)).toint() == 0
            assert c1(MININT).emod(c2(- 2 ** 63)).toint() == 0
            assert c1(sys.maxint).emod(c2(sys.maxint)).toint() == 0
            assert c1(7).emod(c2(5)).toint() == 2
            assert c1(7).emod(c2(-5)).toint() == 2
            assert c1(-7).emod(c2(5)).toint() == 3
            assert c1(-7).emod(c2(-5)).toint() == 3
            assert c1(12).emod(c2(3)).toint() == 0
            assert c1(12).emod(c2(-3)).toint() == 0
            assert c1(-12).emod(c2(3)).toint() == 0
            assert c1(-12).emod(c2(-3)).toint() == 0


   assert bi(0xfffffe00411e0e90L).emod(si(64)).toint() == 16
   assert bi(98765432109876543210).ediv(bi(12345678901234567890)).toint() == 8
   assert bi(98765432109876543210).emod(bi(12345678901234567890)).toint() == 900000000090
   assert bi(12345678901234567890).ediv(bi(-10000000000000000000)).toint() == -1
   assert bi(12345678901234567890).emod(bi(-10000000000000000000)).toint() == 2345678901234567890
   assert bi(-12345678901234567890).ediv(bi(-10000000000000000000)).toint() == 2
   assert bi(-12345678901234567890).ediv(bi(10000000000000000000)).toint() == -2
   assert bi(-12345678901234567890).emod(bi(10000000000000000000)).toint() == 7654321098765432110
   assert bi(-12345678901234567890).emod(bi(-10000000000000000000)).toint() == 7654321098765432110

def test_pow2():
    for i in range(1000):
        assert supportcode.pow2_i(None, i).tobigint().tolong() == 2 ** i
    # check that small results use small ints
    for i in range(63):
        assert supportcode.pow2_i(None, i).val == 2 ** i

# softfloat

class DummyMachine(object): pass


def test_softfloat_f16add():
    machine = DummyMachine()
    supportcode.softfloat_f16add(machine, 0, 0b0011110000000000, 0b0011100000000000)
    assert machine._reg_zfloat_result == 0b0011111000000000

def test_softfloat_f16div():
    machine = DummyMachine()
    supportcode.softfloat_f16div(machine, 0, 0b0011110000000000, 0b0011100000000000)
    assert machine._reg_zfloat_result == 0b0100000000000000

def test_softfloat_f16eq():
    machine = DummyMachine()
    supportcode.softfloat_f16eq(machine, 0b0011100000000000, 0b0011100000000000)
    assert machine._reg_zfloat_result == 1

def test_softfloat_f16le():
    machine = DummyMachine()
    supportcode.softfloat_f16le(machine, 0b0011100000000000, 0b0011100000000000)
    assert machine._reg_zfloat_result == 1

def test_softfloat_f16lt():
    machine = DummyMachine()
    supportcode.softfloat_f16lt(machine, 0b0011100000000000, 0b0011100000000000)
    assert machine._reg_zfloat_result == 0

def test_softfloat_f16mul():
    machine = DummyMachine()
    supportcode.softfloat_f16mul(machine, 0, 0b0011110000000000, 0b0011100000000000)
    assert machine._reg_zfloat_result == 0b0011100000000000

def test_softfloat_f16muladd():
    machine = DummyMachine()
    supportcode.softfloat_f16muladd(machine, 0, 0b0011110000000000, 0b0011100000000000, 0b0011110000000000)
    assert machine._reg_zfloat_result == 0b0011111000000000

def test_softfloat_f16sqrt():
    machine = DummyMachine()
    supportcode.softfloat_f16sqrt(machine, 0, 0b0100010000000000)
    assert machine._reg_zfloat_result == 0b0100000000000000

def test_softfloat_f16sub():
    machine = DummyMachine()
    supportcode.softfloat_f16sub(machine, 0, 0b0011110000000000, 0b0011100000000000)
    assert machine._reg_zfloat_result == 0b0011100000000000

def test_softfloat_f32add():
    machine = DummyMachine()
    supportcode.softfloat_f32add(machine, 0, 0b00111111000000000000000000000000, 0b00111111100000000000000000000000)
    assert machine._reg_zfloat_result == 0b00111111110000000000000000000000

def test_softfloat_f32div():
    machine = DummyMachine()
    supportcode.softfloat_f32div(machine, 0, 0b00111111100000000000000000000000, 0b01000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b00111111000000000000000000000000

def test_softfloat_f32eq():
    machine = DummyMachine()
    supportcode.softfloat_f32eq(machine, 0b00111111000000000000000000000000, 0b00111111000000000000000000000000)
    assert machine._reg_zfloat_result == 1

def test_softfloat_f32le():
    machine = DummyMachine()
    supportcode.softfloat_f32le(machine, 0b00111111000000000000000000000000, 0b00111111000000000000000000000000)
    assert machine._reg_zfloat_result == 1

def test_softfloat_f32lt():
    machine = DummyMachine()
    supportcode.softfloat_f32lt(machine, 0b00111111000000000000000000000000, 0b00111111000000000000000000000000)
    assert machine._reg_zfloat_result == 0

def test_softfloat_f32mul():
    machine = DummyMachine()
    supportcode.softfloat_f32mul(machine, 0, 0b00111111100000000000000000000000, 0b01000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b01000000000000000000000000000000

def test_softfloat_f32muladd():
    machine = DummyMachine()
    supportcode.softfloat_f32muladd(machine, 0, 0b00111111100000000000000000000000, 0b00111111000000000000000000000000, 0b00111111100000000000000000000000)
    assert machine._reg_zfloat_result == 0b00111111110000000000000000000000

def test_softfloat_f32sqrt():
    machine = DummyMachine()
    supportcode.softfloat_f32sqrt(machine, 0, 0b01000000100000000000000000000000)
    assert machine._reg_zfloat_result == 0b01000000000000000000000000000000

def test_softfloat_f32sub():
    machine = DummyMachine()
    supportcode.softfloat_f32sub(machine, 0, 0b01000000000000000000000000000000, 0b00111111100000000000000000000000)
    assert machine._reg_zfloat_result == 0b00111111100000000000000000000000

def test_softfloat_f64add():
    machine = DummyMachine()
    supportcode.softfloat_f64add(machine, 0, 0b0011111111110000000000000000000000000000000000000000000000000000, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0011111111111000000000000000000000000000000000000000000000000000

def test_softfloat_f64div():
    machine = DummyMachine()
    supportcode.softfloat_f64div(machine, 0, 0b0011111111110000000000000000000000000000000000000000000000000000, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0100000000000000000000000000000000000000000000000000000000000000

def test_softfloat_f64eq():
    machine = DummyMachine()
    supportcode.softfloat_f64eq(machine, 0b0011111111100000000000000000000000000000000000000000000000000000, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 1

def test_softfloat_f64le():
    machine = DummyMachine()
    supportcode.softfloat_f64le(machine, 0b0011111111100000000000000000000000000000000000000000000000000000, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 1

def test_softfloat_f64lt():
    machine = DummyMachine()
    supportcode.softfloat_f64lt(machine, 0b0011111111100000000000000000000000000000000000000000000000000000, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0

def test_softfloat_f64mul():
    machine = DummyMachine()
    supportcode.softfloat_f64mul(machine, 0, 0b0011111111110000000000000000000000000000000000000000000000000000, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0011111111100000000000000000000000000000000000000000000000000000

def test_softfloat_f64muladd():
    machine = DummyMachine()
    supportcode.softfloat_f64muladd(machine, 0, 0b0011111111110000000000000000000000000000000000000000000000000000, 0b0011111111100000000000000000000000000000000000000000000000000000, 0b0011111111110000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0011111111111000000000000000000000000000000000000000000000000000

def test_softfloat_f64sqrt():
    machine = DummyMachine()
    supportcode.softfloat_f64sqrt(machine, 0, 0b0100000000010000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0100000000000000000000000000000000000000000000000000000000000000

def test_softfloat_f64sub():
    machine = DummyMachine()
    supportcode.softfloat_f64sub(machine, 0, 0b0011111111110000000000000000000000000000000000000000000000000000, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0011111111100000000000000000000000000000000000000000000000000000

def test_softfloat_f16tof32():
    machine = DummyMachine()
    supportcode.softfloat_f16tof32(machine, 0, 0b0011100000000000)
    assert machine._reg_zfloat_result == 0b00111111000000000000000000000000

def test_softfloat_f32tof16():
    machine = DummyMachine()
    supportcode.softfloat_f32tof16(machine, 0, 0b00111111000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0011100000000000

def test_softfloat_f16tof64():
    machine = DummyMachine()
    supportcode.softfloat_f16tof64(machine, 0, 0b0011100000000000)
    assert machine._reg_zfloat_result == 0b0011111111100000000000000000000000000000000000000000000000000000

def test_softfloat_f64tof16():
    machine = DummyMachine()
    supportcode.softfloat_f64tof16(machine, 0, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0011100000000000

def test_softfloat_f32tof64():
    machine = DummyMachine()
    supportcode.softfloat_f32tof64(machine, 0, 0b00111111000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0011111111100000000000000000000000000000000000000000000000000000

def test_softfloat_f64tof32():
    machine = DummyMachine()
    supportcode.softfloat_f64tof32(machine, 0, 0b0011111111100000000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b00111111000000000000000000000000

def test_softfloat_f16toi32():
    machine = DummyMachine()
    supportcode.softfloat_f16toi32(machine, 0, 0b1100010100000000)
    assert machine._reg_zfloat_result == 0b11111111111111111111111111111011

def test_softfloat_f16toi64():
    machine = DummyMachine()
    supportcode.softfloat_f16toi64(machine, 0, 0b1100010100000000)
    assert machine._reg_zfloat_result == 0b1111111111111111111111111111111111111111111111111111111111111011

def test_softfloat_f16toui32():
    machine = DummyMachine()
    supportcode.softfloat_f16toui32(machine, 0, 0b0100010100000000)
    assert machine._reg_zfloat_result == 0b00000000000000000000000000000101

def test_softfloat_f16toui64():
    machine = DummyMachine()
    supportcode.softfloat_f16toui64(machine, 0, 0b0100010100000000)
    assert machine._reg_zfloat_result == 0b0000000000000000000000000000000000000000000000000000000000000101

def test_softfloat_f32toi32():
    machine = DummyMachine()
    supportcode.softfloat_f32toi32(machine, 0, 0b11000000101000000000000000000000)
    assert machine._reg_zfloat_result == 0b11111111111111111111111111111011

def test_softfloat_f32toi64():
    machine = DummyMachine()
    supportcode.softfloat_f32toi64(machine, 0, 0b11000000101000000000000000000000)
    assert machine._reg_zfloat_result == 0b1111111111111111111111111111111111111111111111111111111111111011

def test_softfloat_f32toui32():
    machine = DummyMachine()
    supportcode.softfloat_f32toui32(machine, 0, 0b01000000101000000000000000000000)
    assert machine._reg_zfloat_result == 0b00000000000000000000000000000101

def test_softfloat_f32toui64():
    machine = DummyMachine()
    supportcode.softfloat_f32toui64(machine, 0, 0b01000000101000000000000000000000)
    assert machine._reg_zfloat_result == 0b0000000000000000000000000000000000000000000000000000000000000101

def test_softfloat_f64toi32():
    machine = DummyMachine()
    supportcode.softfloat_f64toi32(machine, 0, r_ulonglong(0b1100000000010100000000000000000000000000000000000000000000000000))
    assert machine._reg_zfloat_result == 0b11111111111111111111111111111011

def test_softfloat_f64toi64():
    machine = DummyMachine()
    supportcode.softfloat_f64toi64(machine, 0, r_ulonglong(0b1100000000010100000000000000000000000000000000000000000000000000))
    assert machine._reg_zfloat_result == 0b1111111111111111111111111111111111111111111111111111111111111011

def test_softfloat_f64toui32():
    machine = DummyMachine()
    supportcode.softfloat_f64toui32(machine, 0, 0b0100000000010100000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b00000000000000000000000000000101

def test_softfloat_f64toui64():
    machine = DummyMachine()
    supportcode.softfloat_f64toui64(machine, 0, 0b0100000000010100000000000000000000000000000000000000000000000000)
    assert machine._reg_zfloat_result == 0b0000000000000000000000000000000000000000000000000000000000000101

def test_softfloat_i32tof16():
    machine = DummyMachine()
    supportcode.softfloat_i32tof16(machine, 0, 0b11111111111111111111111111111011)
    assert machine._reg_zfloat_result == 0b1100010100000000

def test_softfloat_i32tof32():
    machine = DummyMachine()
    supportcode.softfloat_i32tof32(machine, 0, 0b11111111111111111111111111111011)
    assert machine._reg_zfloat_result == 0b11000000101000000000000000000000

def test_softfloat_i32tof64():
    machine = DummyMachine()
    supportcode.softfloat_i32tof64(machine, 0, 0b11111111111111111111111111111011)
    assert machine._reg_zfloat_result == 0b1100000000010100000000000000000000000000000000000000000000000000

def test_softfloat_i64tof16():
    machine = DummyMachine()
    supportcode.softfloat_i64tof16(machine, 0, r_ulonglong(0b1111111111111111111111111111111111111111111111111111111111111011))
    assert machine._reg_zfloat_result == 0b1100010100000000

def test_softfloat_i64tof32():
    machine = DummyMachine()
    supportcode.softfloat_i64tof32(machine, 0, r_ulonglong(0b1111111111111111111111111111111111111111111111111111111111111011))
    assert machine._reg_zfloat_result == 0b11000000101000000000000000000000

def test_softfloat_i64tof64():
    machine = DummyMachine()
    supportcode.softfloat_i64tof64(machine, 0, r_ulonglong(0b1111111111111111111111111111111111111111111111111111111111111011))
    assert machine._reg_zfloat_result == 0b1100000000010100000000000000000000000000000000000000000000000000

def test_softfloat_ui32tof16():
    machine = DummyMachine()
    supportcode.softfloat_ui32tof16(machine, 0, 0b00000000000000000000000000000101)
    assert machine._reg_zfloat_result == 0b0100010100000000

def test_softfloat_ui32tof32():
    machine = DummyMachine()
    supportcode.softfloat_ui32tof32(machine, 0, 0b00000000000000000000000000000101)
    assert machine._reg_zfloat_result == 0b01000000101000000000000000000000

def test_softfloat_ui32tof64():
    machine = DummyMachine()
    supportcode.softfloat_ui32tof64(machine, 0, 0b00000000000000000000000000000101)
    assert machine._reg_zfloat_result == 0b0100000000010100000000000000000000000000000000000000000000000000

def test_softfloat_ui64tof16():
    machine = DummyMachine()
    supportcode.softfloat_ui64tof16(machine, 0, 0b0000000000000000000000000000000000000000000000000000000000000101)
    assert machine._reg_zfloat_result == 0b0100010100000000

def test_softfloat_ui64tof32():
    machine = DummyMachine()
    supportcode.softfloat_ui64tof32(machine, 0, 0b0000000000000000000000000000000000000000000000000000000000000101)
    assert machine._reg_zfloat_result == 0b01000000101000000000000000000000

def test_softfloat_ui64tof64():
    machine = DummyMachine()
    supportcode.softfloat_ui64tof64(machine, 0, 0b0000000000000000000000000000000000000000000000000000000000000101)
    assert machine._reg_zfloat_result == 0b0100000000010100000000000000000000000000000000000000000000000000

# tests for real type
# Test for add
def test_add_real():
    x = Real.fromint(5)
    y = Real.fromint(7)
    res = x.add(y)
    assert res.toint() == 12
    x = Real.fromint(3, 4)
    y = Real.fromint(5, 4)
    res = x.add(y)
    assert res.toint() == 2
    x = Real.fromint(1, 2)
    y = Real.fromint(1, 2)
    res = x.add(y)
    assert res.toint() == 1
    x = Real.fromint(4, 2)
    y = Real.fromint(9, 3)
    res = x.add(y)
    assert res.toint() == 5
    x = Real.fromint(-4, 2)
    y = Real.fromint(9, -3)
    res = x.add(y)
    assert res.toint() == -5
    x = Real.fromint(-4, -2)
    y = Real.fromint(-9, 3)
    res = x.add(y)
    assert res.toint() == -1
    # Test for denominator equal to 0
    # x = Real.fromint(3, 0)
    # y = Real.fromint(2, 5)
    # res = x.add(y)
    # assert res.toint() == 1

# Test for sub
def test_sub_real():
    x = Real.fromint(16)
    y = Real.fromint(6)
    res = x.sub(y)
    assert res.toint() == 10
    x = Real.fromint(-10)
    y = Real.fromint(6)
    res = x.sub(y)
    assert res.toint() == -16
    x = Real.fromint(-10)
    y = Real.fromint(-6)
    res = x.sub(y)
    assert res.toint() == -4
    x = Real.fromint(-4, 2)
    y = Real.fromint(9, -3)
    res = x.sub(y)
    assert res.toint() == 1
    x = Real.fromint(-4, 2)
    y = Real.fromint(9, 3)
    res = x.sub(y)
    assert res.toint() == -5

# Test for mul
def test_mul_real():
    x = Real.fromint(10)
    y = Real.fromint(6)
    res = x.mul(y)
    assert res.toint() == 60
    x = Real.fromint(-10)
    y = Real.fromint(6)
    res = x.mul(y)
    assert res.toint() == -60
    x = Real.fromint(-10)
    y = Real.fromint(-6)
    res = x.mul(y)
    assert res.toint() == 60
    x = Real.fromint(4, 2)
    y = Real.fromint(9, 3)
    res = x.mul(y)
    assert res.toint() == 6
    x = Real.fromint(5, 2)
    y = Real.fromint(2, 5)
    res = x.mul(y)
    assert res.toint() == 1
    x = Real.fromint(-5, 2)
    y = Real.fromint(2, 5)
    res = x.mul(y)
    assert res.toint() == -1
    x = Real.fromint(-5, 2)
    y = Real.fromint(2, -5)
    res = x.mul(y)
    assert res.toint() == 1

# Test for div
def test_div_real():
    x = Real.fromint(10)
    y = Real.fromint(2)
    res = x.div(y)
    assert res.toint() == 5
    x = Real.fromint(-10)
    y = Real.fromint(2)
    res = x.div(y)
    assert res.toint() == -5
    x = Real.fromint(1, 5)
    y = Real.fromint(1, 25)
    res = x.div(y)
    assert res.toint() == 5
    x = Real.fromint(1, -5)
    y = Real.fromint(1, 25)
    res = x.div(y)
    assert res.toint() == -5
    x = Real.fromint(-1, 5)
    y = Real.fromint(1, -25)
    res = x.div(y)
    assert res.toint() == 5
    x = Real.fromint(-4, -2)
    assert x.num.toint() == 2
    assert x.den.toint() == 1
    x = Real.fromint(-4, 2)
    assert x.num.toint() == -2
    assert x.den.toint() == 1
    x = Real.fromint(4, -2)
    assert x.num.toint() == -2
    assert x.den.toint() == 1

# Test for neg
def test_neg_real():
    x = Real.fromint(10)
    res = x.neg()
    assert res.toint() == -10
    x = Real.fromint(-10)
    res = x.neg()
    assert res.toint() == 10
    x = Real.fromint(4, 2)
    res = x.neg()
    assert res.toint() == -2
    x = Real.fromint(-4, 2)
    res = x.neg()
    assert res.toint() == 2
    x = Real.fromint(4, -2)
    res = x.neg()
    assert res.toint() == 2

# Test for abs
def test_abs_real():
    x = Real.fromint(10)
    res = x.abs()
    assert res.toint() == 10
    x = Real.fromint(-10)
    res = x.abs()
    assert res.toint() == 10
    x = Real.fromint(4, 2)
    res = x.abs()
    assert res.toint() == 2
    x = Real.fromint(-4, 2)
    res = x.abs()
    assert res.toint() == 2
    x = Real.fromint(4, -2)
    res = x.abs()
    assert res.toint() == 2

# Test for eq
def test_eq_real():
    x = Real.fromint(10)
    y = Real.fromint(10)
    res = x.eq(y)
    assert res == True
    x = Real.fromint(10)
    y = Real.fromint(-3)
    res = x.eq(y)
    assert res == False
    x = Real.fromint(2, 7)
    y = Real.fromint(2, 7)
    res = x.eq(y)
    assert res == True
    x = Real.fromint(2, 9)
    y = Real.fromint(2, 7)
    res = x.eq(y)
    assert res == False

# Test for lt
def test_lt_real():
    x = Real.fromint(10)
    y = Real.fromint(11)
    res1 = x.lt(y)
    res2 = y.lt(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(-10)
    y = Real.fromint(2)
    res1 = x.lt(y)
    res2 = y.lt(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(10)
    y = Real.fromint(10)
    res = x.lt(y)
    assert res == False
    x = Real.fromint(1, 3)
    y = Real.fromint(5, 2)
    res = x.lt(y)
    assert res == True
    x = Real.fromint(1, 3)
    y = Real.fromint(1, 3)
    res = x.lt(y)
    assert res == False
    x = Real.fromint(-1, 3)
    y = Real.fromint(1, 6)
    res = x.lt(y)
    assert res == True
    x = Real.fromint(1, -3)
    y = Real.fromint(1, -6)
    res = x.lt(y)
    assert res == True

# Test for gt
def test_gt_real():
    x = Real.fromint(10)
    y = Real.fromint(8)
    res1 = x.gt(y)
    res2 = y.gt(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(10)
    y = Real.fromint(-11)
    res1 = x.gt(y)
    res2 = y.gt(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(2, 7)
    y = Real.fromint(2, 9)
    res1 = x.gt(y)
    res2 = y.gt(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(-1, 3)
    y = Real.fromint(1, 6)
    res1 = x.gt(y)
    res2 = y.gt(x)
    assert res1 == False
    assert res2 == True
    x = Real.fromint(1, -3)
    y = Real.fromint(1, -6)
    res = x.gt(y)
    assert res == False

# Test for le
def test_le_real():
    x = Real.fromint(10)
    y = Real.fromint(10)
    res = x.le(y)
    assert res == True
    x = Real.fromint(10)
    y = Real.fromint(8)
    res1 = x.le(y)
    res2 = y.le(x)
    assert res1 == False
    assert res2 == True
    x = Real.fromint(10)
    y = Real.fromint(-11)
    res1 = x.le(y)
    res2 = y.le(x)
    assert res1 == False
    assert res2 == True
    x = Real.fromint(2, 7)
    y = Real.fromint(2, 9)
    res1 = x.le(y)
    res2 = y.le(x)
    assert res1 == False
    assert res2 == True
    x = Real.fromint(-1, 3)
    y = Real.fromint(1, 6)
    res1 = x.le(y)
    res2 = y.le(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(1, -3)
    y = Real.fromint(1, -6)
    res = x.le(y)
    assert res == True
    x = Real.fromint(1, -3)
    y = Real.fromint(-1, 3)
    res = x.le(y)
    assert res == True

# Test for ge
def test_ge_real():
    x = Real.fromint(10)
    y = Real.fromint(10)
    res = x.ge(y)
    assert res == True
    x = Real.fromint(10)
    y = Real.fromint(8)
    res1 = x.ge(y)
    res2 = y.ge(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(10)
    y = Real.fromint(-11)
    res1 = x.ge(y)
    res2 = y.ge(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(2, 7)
    y = Real.fromint(2, 9)
    res1 = x.ge(y)
    res2 = y.ge(x)
    assert res1 == True
    assert res2 == False
    x = Real.fromint(-1, 3)
    y = Real.fromint(1, 6)
    res1 = x.ge(y)
    res2 = y.ge(x)
    assert res1 == False
    assert res2 == True
    x = Real.fromint(1, -3)
    y = Real.fromint(1, -6)
    res = x.ge(y)
    assert res == False
    x = Real.fromint(1, -3)
    y = Real.fromint(-1, 3)
    res = x.ge(y)
    assert res == True

# Test for basic corner cases
def test_corner_real():
    x = Real.fromint(2**63-1)
    assert x.den.str() == "1"
    assert x.num.str() == str(2**63-1)
    x = Real.fromint(-2**63)
    assert x.toint() == -2**63
    x = Real.fromint(-2**63)
    y = Real.fromint(1)
    res = x.add(y)
    assert res.toint() == -2**63+1
    x = Real.fromint(1, -2**63)
    assert x.num.str() == str(-1)
    assert x.den.str() == str(2**63)
    x = Real.fromint(1, 2**63-1)
    assert x.num.str() == "1"
    assert x.den.str() == str(2**63-1)
    x = Real.fromint(2**63-1, 2**63-1)
    assert x.toint() == 1
    x = Real.fromint(-2**63, -2**63)
    assert x.toint() == 1
    x = Real.fromint(2**63-1, -2**63)
    assert x.num.str() == str(-(2**63-1))
    assert x.den.str() == str(2**63)
    x = Real.fromint(-2**63, 2**63-1)
    assert x.num.str() == str(-2**63)
    assert x.den.str() == str(2**63-1)
    x = Real.fromint(-2**63)
    y = Real.fromint(-2**10)
    res = x.add(y)
    assert res.num.str() == str(-2**63-2**10)
    assert res.den.str() == str(1)
    x = Real.fromint(2**63-1)
    y = Real.fromint(3)
    res = x.add(y)
    assert res.num.str() == str(2**63+2)
    assert res.den.str() == str(1)

def test_fromstr_real():
    x = Real.fromstr("12")
    assert x.den.tolong() == 1
    assert x.num.tolong() == 12

def test_sqrt_real():
    x = Real.fromstr("4")
    res = x.sqrt()
    assert res.num.tolong() == 2
    assert res.den.tolong() == 1
    x = Real.fromstr("26")
    res = x.sqrt()
    assert res.den.tolong() == 13440582586105723640064737480160
    assert res.num.tolong() == 68533792880608460985460475212801
    x = Real.fromstr("0")
    res = x.sqrt()
    assert res.num.tolong() == 0
    assert res.den.tolong() == 1
    x = Real.fromstr("1")
    res = x.sqrt()
    assert res.num.tolong() == 1
    assert res.den.tolong() == 1


def rr_den_pos(num, den):
    num = rbigint.fromlong(num)
    den = rbigint.fromlong(den)
    return Real(num, den, False)

def test_pow_real():
    x = Real.fromint(1, 5)
    res = x.pow(0)
    assert res.num.toint() == 1
    assert res.den.toint() == 1
    x = rr_den_pos(1997831095010467864672715021484102, 3236962239656889)
    res = x.pow(157)
    assert res.num.tolong() == 190409951913019359038317205622379457602035828161843624841207699640927333775046592117576433413376876105733603132434130232503683347785849318708509006432638953486459208060845830210831558599521266976597040288338545867344941559448210334962626849683138394215452361342483721896244695900342376820803404194896623578448721624401505793922858830089779388353229122375093315200327346176160201718081720922073765801503425541320651826634918043017133821123183693597845974507140550679408598425919072817502440705107563048772735794355949110660987620452824340776421141373378290388817722475777148149975006672300034940593562448675468527495896721557991715834489874636851054079281397033594218236496485700225830148375518405292368299266009779917697829068198692096000628965707869321183885417286230992305081062530810866126143930416846043662822682676265086593516620362109350087692151401171574058530429406860774077169678007037105575066100122224458321910152117944402331106583508534456254328581000038776850549037516306343853937763154535726419506592565250043512735506500050261473531397610769914398937629531939801849672473635189016987431448735983440291380473040048197144019936119057341031918984486870504545050237287974159943109902318579139573274087239158619821430962845884982613093737307323878091650016619308103208329051403017616292867427190150854611336696189675504308156673508645105181281534412711098521536335431300694163571611622508279641087680718962608046173975982960763365829378072699378641778714190817639937109358325321390501277552874635888901134603602189317283813110095294463428256170489469014615855156113040491798719415902149707071886660965416331005536296213055293194324606271255372690723430086511418166517112555757502202943421083825056523256193875236868131174984183525966873195540423765385513537781389750320784087424269992287016787675035568680805164909381373540508162634656613331790628358843988423467684724221226370341755451140190650781392496569578390881482246137743560727961120731986954334551195036809498851891499076178759525544347615692909093530014144601840102691015315169454460358563561301836839948762170182154177820560799228353437527328887865228305164982877950354698743822854076828223264157126244593770905192754873629164102000824458166916255482474653728766584423935436416665805589318534422094319896764912922891833539002715876662525027414796574568793844818057873912316649506326200489784545284231310640311258092576397121085874623483705221538967981926375857588113488064860838693989619646910717850643725125121151234511228165467105756138172053457546627173533402454314427348881592924832613424836721378626746053259587650488905814047739578955554695190014861757531195585001381395177155962377973636592899925717133673364683892637460352899677059394634219468963753575873664804765393235790882252616112308232444860780269091312300714438345143185170047348769027612481660663086538261726430502662395476908993715884211257866079156686243943175661299906030620025565620307377497265614217590773929914349479073535628553786049948004222888033286872604240323620881874001858192397525515375033096723570220950963746360502322678972754702551350841260269564403529679481818049357095857577062718147264051178345559973013611595399542327251244339857400927908447217906468708735571398954364678012999940266806891496476698708680508763560788258191054422672424829577101528077350460987995283796127345586232872348026585327705119426167260906765363432483507311318583716014273159306874704208102292570789326518795588220950969393809356453658489749373250557552793974847344630507447675300224283881898448032208475834951974207816067748495800862805749758479452665073073752074093203171173647866537953578871912720053270564531412228847987973308723256009261963987757440489290836501484070922113537049266434700522488231367414903099627460332351165673486972622704133190312924635158945144528021166776465675177478477033832562308925055120304997687890399163253132001730170107718281112510035708801649669645292211763408389267000376007761925250203108215212103518733189179015050338309991434427035536843348866615402560771870192281519878418938465048851057800568710574851328316280359702405178729302310881503358523301282670768976929342234219755958251763163623019122054132586638636055406646489634749338893327349077769886809892948821987235170145851885728851836626227988340402437205450072047914494298390487209025687453319119517297422542231932617241772961034263051083941093827549112012830097767776861469860823431336653616381002324991088816484641564510478930156189810585298867775911888958837287778813463079052280097983414742675627089050251859351421557719614944181797856661305825845675150845525997176719912149567334085843289445778263408335744217060071779081954294980610542192840054769433871220932564149414702861477491108227104599349559153034972238340329231037305318962059908485157939430601857863362639690950321251652038851290606630911836583621377615188689341218152625038339018868626843846701526168656950409293804227910392545916376960555237496816629944195699706390319737311331640473976149436676091791677052875736540960938891648580742748218248088950832621657039938672448151609227744465296003314690599111225878734167290173489785600107683712190915766399968575750144
    assert res.den.tolong() == 152605935647679226282756190536636722669030930172767429260321713188655918063291372275949200913016469230881861936703267926892858191458666863236706148079968034303895171583534914159543857359589737180559339571339024633993101292297056083370608964594151791160554700812317461700468494874387520259364884336717586817778868394969465624697599648081857317122403102600721538641626163500190856568740415042847729062808976305298778819845783956670623356512378943285147657051165807324310741194576085942198601527892840213183790696348482655206168963355811560025082160505184110371696390624220005143785589654253497186816424880382583974181896693796771489424351793841770369303040204386469621500846258204487691049699829361937627175912264554944061791381666300044781732730751581825809003317286906774184845677020999700170418521310117798552782595025178116845856610447237341949406468521935351149232417276311757882172794671430098193798720976426930292527069917377994943054079172955248496471620627384146039114277553316420411898571728140514292645828750708028744876224446369411230868911890279944097845355858026893487929614329997659931762053654664862635020403815047127361278339525656399780842537282910548581007949535930754506407338788657741580953742155958283616108899207670258999952786492547280717908819145621372483197929855444767007288504579156624502324541571430514293204141107551108524249139085703904546174763838774659306760589080680752392716409190922535467519266207238159929509950267336791220517552975604697469453990196616594989092187988315421274118513323516422290303534101018693976123356270438385190370166384215870643122537135721541190703525629992429757758543711003399749182492092530329093962986465222895621542205981860941339743836893566694051422789063773150827779357821843524199955673573901121976427626673677852336319783284562438046308325164627990165473060582075767921495521043270500857512488056907397699831057657336723350597095074559442033991631963260738967102173706731010860031600250844534707322198534068002659601304943428683479507006764170029792019208835245080192898531303668306040449949556192399033456250780662678186777626097370254236651078644165664192559131037070113809176626408872070305666367546775016246021122268904569928324039173898484742373125824909799788656911845746229468127290683128367592262078509794696336528838202883291443449142660392362587336174811218403556760305442842323206883
    frac = Fraction(1997831095010467864672715021484102, 3236962239656889)
    frac2 = frac ** 157
    assert frac2.numerator == 190409951913019359038317205622379457602035828161843624841207699640927333775046592117576433413376876105733603132434130232503683347785849318708509006432638953486459208060845830210831558599521266976597040288338545867344941559448210334962626849683138394215452361342483721896244695900342376820803404194896623578448721624401505793922858830089779388353229122375093315200327346176160201718081720922073765801503425541320651826634918043017133821123183693597845974507140550679408598425919072817502440705107563048772735794355949110660987620452824340776421141373378290388817722475777148149975006672300034940593562448675468527495896721557991715834489874636851054079281397033594218236496485700225830148375518405292368299266009779917697829068198692096000628965707869321183885417286230992305081062530810866126143930416846043662822682676265086593516620362109350087692151401171574058530429406860774077169678007037105575066100122224458321910152117944402331106583508534456254328581000038776850549037516306343853937763154535726419506592565250043512735506500050261473531397610769914398937629531939801849672473635189016987431448735983440291380473040048197144019936119057341031918984486870504545050237287974159943109902318579139573274087239158619821430962845884982613093737307323878091650016619308103208329051403017616292867427190150854611336696189675504308156673508645105181281534412711098521536335431300694163571611622508279641087680718962608046173975982960763365829378072699378641778714190817639937109358325321390501277552874635888901134603602189317283813110095294463428256170489469014615855156113040491798719415902149707071886660965416331005536296213055293194324606271255372690723430086511418166517112555757502202943421083825056523256193875236868131174984183525966873195540423765385513537781389750320784087424269992287016787675035568680805164909381373540508162634656613331790628358843988423467684724221226370341755451140190650781392496569578390881482246137743560727961120731986954334551195036809498851891499076178759525544347615692909093530014144601840102691015315169454460358563561301836839948762170182154177820560799228353437527328887865228305164982877950354698743822854076828223264157126244593770905192754873629164102000824458166916255482474653728766584423935436416665805589318534422094319896764912922891833539002715876662525027414796574568793844818057873912316649506326200489784545284231310640311258092576397121085874623483705221538967981926375857588113488064860838693989619646910717850643725125121151234511228165467105756138172053457546627173533402454314427348881592924832613424836721378626746053259587650488905814047739578955554695190014861757531195585001381395177155962377973636592899925717133673364683892637460352899677059394634219468963753575873664804765393235790882252616112308232444860780269091312300714438345143185170047348769027612481660663086538261726430502662395476908993715884211257866079156686243943175661299906030620025565620307377497265614217590773929914349479073535628553786049948004222888033286872604240323620881874001858192397525515375033096723570220950963746360502322678972754702551350841260269564403529679481818049357095857577062718147264051178345559973013611595399542327251244339857400927908447217906468708735571398954364678012999940266806891496476698708680508763560788258191054422672424829577101528077350460987995283796127345586232872348026585327705119426167260906765363432483507311318583716014273159306874704208102292570789326518795588220950969393809356453658489749373250557552793974847344630507447675300224283881898448032208475834951974207816067748495800862805749758479452665073073752074093203171173647866537953578871912720053270564531412228847987973308723256009261963987757440489290836501484070922113537049266434700522488231367414903099627460332351165673486972622704133190312924635158945144528021166776465675177478477033832562308925055120304997687890399163253132001730170107718281112510035708801649669645292211763408389267000376007761925250203108215212103518733189179015050338309991434427035536843348866615402560771870192281519878418938465048851057800568710574851328316280359702405178729302310881503358523301282670768976929342234219755958251763163623019122054132586638636055406646489634749338893327349077769886809892948821987235170145851885728851836626227988340402437205450072047914494298390487209025687453319119517297422542231932617241772961034263051083941093827549112012830097767776861469860823431336653616381002324991088816484641564510478930156189810585298867775911888958837287778813463079052280097983414742675627089050251859351421557719614944181797856661305825845675150845525997176719912149567334085843289445778263408335744217060071779081954294980610542192840054769433871220932564149414702861477491108227104599349559153034972238340329231037305318962059908485157939430601857863362639690950321251652038851290606630911836583621377615188689341218152625038339018868626843846701526168656950409293804227910392545916376960555237496816629944195699706390319737311331640473976149436676091791677052875736540960938891648580742748218248088950832621657039938672448151609227744465296003314690599111225878734167290173489785600107683712190915766399968575750144
    assert frac2.denominator == 152605935647679226282756190536636722669030930172767429260321713188655918063291372275949200913016469230881861936703267926892858191458666863236706148079968034303895171583534914159543857359589737180559339571339024633993101292297056083370608964594151791160554700812317461700468494874387520259364884336717586817778868394969465624697599648081857317122403102600721538641626163500190856568740415042847729062808976305298778819845783956670623356512378943285147657051165807324310741194576085942198601527892840213183790696348482655206168963355811560025082160505184110371696390624220005143785589654253497186816424880382583974181896693796771489424351793841770369303040204386469621500846258204487691049699829361937627175912264554944061791381666300044781732730751581825809003317286906774184845677020999700170418521310117798552782595025178116845856610447237341949406468521935351149232417276311757882172794671430098193798720976426930292527069917377994943054079172955248496471620627384146039114277553316420411898571728140514292645828750708028744876224446369411230868911890279944097845355858026893487929614329997659931762053654664862635020403815047127361278339525656399780842537282910548581007949535930754506407338788657741580953742155958283616108899207670258999952786492547280717908819145621372483197929855444767007288504579156624502324541571430514293204141107551108524249139085703904546174763838774659306760589080680752392716409190922535467519266207238159929509950267336791220517552975604697469453990196616594989092187988315421274118513323516422290303534101018693976123356270438385190370166384215870643122537135721541190703525629992429757758543711003399749182492092530329093962986465222895621542205981860941339743836893566694051422789063773150827779357821843524199955673573901121976427626673677852336319783284562438046308325164627990165473060582075767921495521043270500857512488056907397699831057657336723350597095074559442033991631963260738967102173706731010860031600250844534707322198534068002659601304943428683479507006764170029792019208835245080192898531303668306040449949556192399033456250780662678186777626097370254236651078644165664192559131037070113809176626408872070305666367546775016246021122268904569928324039173898484742373125824909799788656911845746229468127290683128367592262078509794696336528838202883291443449142660392362587336174811218403556760305442842323206883

@given(strategies.integers(), strategies.integers(min_value = 1))
def test_real_neg_hypothesis(num, den):
    r = rr_den_pos(num, den)
    r_2 = r.neg()
    assert r.den.eq(r_2.den)
    assert r.num.neg().eq(r_2.num)

@given(strategies.integers(), strategies.integers(min_value = 1))
def test_real_abs_hypothesis(num, den):
    r = rr_den_pos(num, den)
    r_2 = r.abs()
    assert r.den.eq(r_2.den)
    assert r.num.abs().eq(r_2.num)


@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers(), strategies.integers(min_value = 1))
def test_real_add_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    res = r1.add(r2)
    frac = Fraction(num1, den1) + Fraction(num2, den2)
    assert res.num.tolong() == frac.numerator
    assert res.den.tolong() == frac.denominator

@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers(), strategies.integers(min_value = 1))
def test_real_sub_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    res = r1.sub(r2)
    frac = Fraction(num1, den1) - Fraction(num2, den2)
    assert res.num.tolong() == frac.numerator
    assert res.den.tolong() == frac.denominator

@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers(), strategies.integers(min_value = 1))
def test_real_mul_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    res = r1.mul(r2)
    frac = Fraction(num1, den1) * Fraction(num2, den2)
    assert res.num.tolong() == frac.numerator
    assert res.den.tolong() == frac.denominator

@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers().filter(lambda n: n != 0), strategies.integers(min_value = 1))
def test_real_div_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    res = r1.div(r2)
    frac = Fraction(num1, den1) / Fraction(num2, den2)
    assert res.num.tolong() == frac.numerator
    assert res.den.tolong() == frac.denominator

@given(strategies.integers(), strategies.integers(min_value = 1))
def test_real_ceil_hypothesis(num, den):
    r = rr_den_pos(num, den)
    res = r.ceil()
    frac = Fraction(num, den)
    if num % den == 0:
        assert res.tolong() == frac.numerator
    else:
        if num > 0:
            assert res.tolong() == frac.numerator // frac.denominator + 1
        else:
            assert res.tolong() == -((-frac.numerator) // frac.denominator)

@given(strategies.integers(), strategies.integers(min_value = 1))
def test_real_floor_hypothesis(num, den):
    r = rr_den_pos(num, den)
    res = r.floor()
    frac = Fraction(num, den)
    if num % den == 0:
        assert res.tolong() == frac.numerator
    else:
        if num > 0:
            assert res.tolong() == frac.numerator // frac.denominator
        else:
            assert res.tolong() == -((-frac.numerator) // frac.denominator + 1)

@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers(), strategies.integers(min_value = 1))
def test_real_eq_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    frac1 = Fraction(num1, den1)
    frac2 = Fraction(num2, den2)
    assert r1.eq(r2) == (frac1.numerator == frac2.numerator and frac1.denominator == frac2.denominator)

@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers(), strategies.integers(min_value = 1))
def test_real_lt_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    frac1 = Fraction(num1, den1)
    frac2 = Fraction(num2, den2)
    assert r1.lt(r2) == (frac1 - frac2 < 0)

@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers(), strategies.integers(min_value = 1))
def test_real_gt_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    frac1 = Fraction(num1, den1)
    frac2 = Fraction(num2, den2)
    assert r1.gt(r2) == (frac1 - frac2 > 0)

@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers(), strategies.integers(min_value = 1))
def test_real_le_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    frac1 = Fraction(num1, den1)
    frac2 = Fraction(num2, den2)
    assert r1.le(r2) == (frac1 - frac2 <= 0)

@given(strategies.integers(), strategies.integers(min_value = 1), strategies.integers(), strategies.integers(min_value = 1))
def test_real_ge_hypothesis(num1, den1, num2, den2):
    r1 = rr_den_pos(num1, den1)
    r2 = rr_den_pos(num2, den2)
    frac1 = Fraction(num1, den1)
    frac2 = Fraction(num2, den2)
    assert r1.ge(r2) == (frac1 - frac2 >= 0)

@given(strategies.integers().filter(lambda n: n != 0), strategies.integers(min_value = 1), strategies.integers(min_value = -50, max_value = 50))
def test_real_pow_hypothesis(num, den, n):
    r = rr_den_pos(num, den)
    res = r.pow(n)
    frac = Fraction(num, den)
    frac_pow = frac ** n
    assert res.num.tolong() == frac_pow.numerator
    assert res.den.tolong() == frac_pow.denominator

@given(strategies.integers(), strategies.integers(min_value = 0, max_value = 100), strategies.integers(min_value = 0))
def test_real_fromstr_2_hypothesis(integer, zeros, fractional):
    num_str = str(integer) + "." + "0"*zeros + str(fractional)
    r = Real.fromstr(num_str)
    frac = Fraction(num_str)
    assert r.num.tolong() == frac.numerator
    assert r.den.tolong() == frac.denominator

@settings(deadline=1000)
@given(strategies.floats(allow_nan = False, allow_infinity = False, min_value = 0, max_value = float(2**63-1)))
def test_real_sqrt_hypothesis(a):
    from rpython.rlib.rfloat import float_as_rbigint_ratio
    num, den = float_as_rbigint_ratio(a)
    x = Real(num, den).sqrt()
    assert math.sqrt(a) == x.num.truediv(x.den)
    num, den = float_as_rbigint_ratio(math.sqrt(a))
    assert max(len(x.num.str()), len(x.den.str())) >= max(len(num.str()), len(den.str()))

# memory

class FakeMachine(object):
    def __init__(self):
        self.g = supportcode.Globals()
        self._pydrofoil_enum_read_ifetch_value = 1

def test_read_write_mem():
    m = FakeMachine()
    for i in range(100):
        supportcode.write_mem(m, r_uint(i), r_uint((i * i) & 0xff))
    for i in range(100):
        supportcode.write_mem(m, r_uint(i + 0x80000000), r_uint((-i * i) & 0xff))
    for i in range(100):
        assert supportcode.read_mem(m, r_uint(i)) == r_uint((i * i) & 0xff)
    for i in range(100):
        assert supportcode.read_mem(m, r_uint(i + 0x80000000)) == r_uint((-i * i) & 0xff)

def test_platform_read_write_mem():
    m = FakeMachine()
    # here some of the arguments are BitVector/Integer instances
    read_kind = "read" # they are ignored for now, so use dummy strings
    write_kind = "write"
    for i in range(100):
        supportcode.platform_write_mem(
            m,
            write_kind,
            64,
            bitvector.from_ruint(64, r_uint(i)),
            Integer.fromint(1),
            bitvector.from_ruint(8, r_uint((i * i) & 0xff)))
    for i in range(100):
        supportcode.platform_write_mem(
            m,
            write_kind,
            64,
            bitvector.from_ruint(64, r_uint(i + 0x80000000)),
            Integer.fromint(1),
            bitvector.from_ruint(8, r_uint((-i * i) & 0xff)))
    for i in range(100):
        res = supportcode.platform_read_mem(
            m,
            read_kind,
            64,
            bitvector.from_ruint(64, r_uint(i)),
            Integer.fromint(1))
        assert res.touint() == r_uint((i * i) & 0xff)
        assert res.size() == 8
    for i in range(100):
        res = supportcode.platform_read_mem(
            m,
            read_kind,
            64,
            bitvector.from_ruint(64, r_uint(i + 0x80000000)),
            Integer.fromint(1))
        assert res.touint() == r_uint((-i * i) & 0xff)
        assert res.size() == 8

def test_platform_read_mem_large():
    m = FakeMachine()
    read_kind = "read"
    write_kind = "write"
    for i in range(100):
        supportcode.platform_write_mem(
            m,
            write_kind,
            64,
            bitvector.from_ruint(64, r_uint(i)),
            Integer.fromint(1),
            bitvector.from_ruint(8, r_uint((i * i) & 0xff)))
    res = supportcode.platform_read_mem(
        m,
        read_kind,
        64,
        bitvector.from_ruint(64, r_uint(0)),
        Integer.fromint(8))
    assert res.touint() == r_uint(0x3124191009040100L)
    assert res.size() == 64
    res = supportcode.platform_read_mem(
        m,
        read_kind,
        64,
        bitvector.from_ruint(64, r_uint(0)),
        Integer.fromint(16))
    assert res.tobigint().tolong() == 0xe1c4a990796451403124191009040100L
    assert res.size() == 128

def test_platform_write_mem_large():
    m = FakeMachine()
    read_kind = "read"
    write_kind = "write"
    supportcode.platform_write_mem(
        m,
        write_kind,
        64,
        bitvector.from_ruint(64, r_uint(0)),
        Integer.fromint(16),
        bitvector.from_bigint(128, rbigint.fromlong(0xe1c4a990796451403124191009040100L))
    )
    res = supportcode.platform_read_mem(
        m,
        read_kind,
        64,
        bitvector.from_ruint(64, r_uint(0)),
        Integer.fromint(8))
    assert res.touint() == r_uint(0x3124191009040100L)
    assert res.size() == 64
    res = supportcode.platform_read_mem(
        m,
        read_kind,
        64,
        bitvector.from_ruint(64, r_uint(0)),
        Integer.fromint(16))
    assert res.tobigint().tolong() == 0xe1c4a990796451403124191009040100L
    assert res.size() == 128

#section for test file for sparse bitvectors


def test_sparse_add_int():
    v = SparseBitVector(100, r_uint(0b111))
    res = v.add_int(Integer.fromint(0b1))
    assert res.touint() == 0b1000

def test_sparse_read_bit():
    v = SparseBitVector(100, r_uint(0b10101))
    assert v.read_bit(4) == True
    assert v.read_bit(3) == False
    assert v.read_bit(2) == True
    assert v.read_bit(1) == False
    assert v.read_bit(0) == True
    assert v.read_bit(65) == False
    assert v.read_bit(99) == False
    with pytest.raises(AssertionError):
        v.read_bit(100) 

def test_sparse_vector_shift():
    v = SparseBitVector(100, 0b10001101)

    res = v.rshift(5)
    assert res.size() == 100
    assert res.toint() == 0b00000100

    res = v.rshift(100)
    assert res.size() == 100
    assert res.toint() == 0
    
    res = v.rshift(65)
    assert res.size() == 100
    assert res.toint() == 0

def test_sparse_arith_shiftr():
    v = SparseBitVector(100, 0b00101101)
    res = v.arith_rshift(3)
    assert res.size() == 100
    assert res.toint() == 0b101

    v = SparseBitVector(100, 0b1000100)
    res = v.arith_rshift(6)
    assert res.size() == 100
    assert res.toint() == 0b1

def test_sparse_vector_shift_bits():
    v = SparseBitVector(100, 0b10001101)
    res = v.rshift_bits(SparseBitVector(100, 5))
    assert res.size() == 100
    assert res.toint() == 0b00000100

    v = SparseBitVector(100, 0b10001101)
    res = v.rshift_bits(SparseBitVector(100, 65))
    assert res.size() == 100
    assert res.toint() == 0

def test_sparse_bv_bitwise():
    v1 = SparseBitVector(100, 0b11110000)
    v2 = SparseBitVector(100, 0b11001100)
    res = v1.and_(v2)
    assert res.toint() == 0b11110000 & 0b11001100
    res = v1.or_(v2)
    assert res.toint() == 0b11110000 | 0b11001100
    res = v1.xor(v2)
    assert res.toint() == 0b11110000 ^ 0b11001100

def test_sparse_zero_extend():
    # XXX Should I test it with support code?
    v = SparseBitVector(65, 0b0)
    res = v.zero_extend(100)
    assert res.size() == 100
    assert res.toint() == 0

    v = SparseBitVector(100, 0b00)
    res = v.zero_extend(100)
    assert res.size() == 100
    assert res.toint() == 0

    v = SparseBitVector(65, 0b1)
    res = v.zero_extend(100)
    assert res.size() == 100
    assert res.toint() == 0b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001

    v = SparseBitVector(65, 0b11)
    res = v.zero_extend(100)
    assert res.size() == 100
    assert res.toint() == 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011

def test_sparse_sign_extend():
    # XXX Should I test it with support code?
    v = SparseBitVector(65, 0b0)
    res = v.sign_extend(100)
    assert res.size() == 100
    assert res.toint() == 0

    v = SparseBitVector(100, 0b00)
    res = v.sign_extend(100)
    assert res.size() == 100
    assert res.toint() == 0

    v = SparseBitVector(65, 0b1)
    res = v.sign_extend(100)
    assert res.size() == 100
    assert res.toint() == 0b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001

    v = SparseBitVector(65, 0b11)
    res = v.sign_extend(100)
    assert res.size() == 100
    assert res.toint() == 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011


def test_sparse_vector_subrange():
    # XXX Regression bug and sail implementation
    v = SparseBitVector(100, 0b111)
    r = v.subrange(3, 2)
    assert r.size() == 2
    assert r.toint() == 1
    assert isinstance(r, bitvector.SmallBitVector)

    # BUG Doesnt work on 64 width
    # v = SparseBitVector(65, 0b111)
    # r = v.subrange(63, 0)
    # assert r.size() == 64
    # assert r.toint() == 0b111
    # assert isinstance(r, bitvector.SmallBitVector)

    # v = SparseBitVector(100, 0b101010101)
    # r = v.subrange(65, 2)
    # assert r.size() == 64
    # assert r.toint() == 0b101010
    # assert isinstance(r, bitvector.SmallBitVector)

    v = SparseBitVector(100, 0b101010101)
    r = v.subrange(5, 0)
    assert r.size() == 6
    assert r.toint() == 0b10101
    assert isinstance(r, bitvector.SmallBitVector)

    v = SparseBitVector(100, 0b101010101)
    r = v.subrange(65, 0)
    assert r.size() == 66
    assert r.toint() == 0b101010101
    assert isinstance(r, bitvector.SparseBitVector)

    v = SparseBitVector(100, 0b101010101)
    r = v.subrange(65, 3)
    assert r.size() == 63
    assert r.toint() == 0b101010
    assert isinstance(r, bitvector.SmallBitVector)

    v = SparseBitVector(100, 0b101010101)
    r = v.subrange(65, 1)
    assert r.size() == 65
    assert r.toint() == 0b10101010
    assert isinstance(r, bitvector.SparseBitVector)

    v = SparseBitVector(100, 0b101010101)
    r = v.subrange(99, 0)
    assert r.size() == 100
    assert r.toint() == 0b101010101
    assert isinstance(r, bitvector.SparseBitVector)

def test_sparse_vector_update():
    v = SparseBitVector(100, 1)
    res = v.update_bit(2, 1)
    assert res.size() == 100
    assert res.toint() == 0b101
    
    v = SparseBitVector(65, r_uint(1))
    res = v.update_bit(1, 0)
    assert res.size() == 65
    assert res.toint() == 0b1

    v = SparseBitVector(65, r_uint(2))
    res = v.update_bit(0, 0)
    assert res.size() == 65
    assert res.toint() == 0b10

    v = SparseBitVector(65, r_uint(0))
    res = v.update_bit(1, 1)
    assert res.size() == 65
    assert res.tolong() == 0b10

    v = SparseBitVector(100, 1)
    res = v.update_bit(0, 1)
    assert res.size() == 100
    assert res.toint() == 0b1

    v = SparseBitVector(100, 0b11)
    res = v.update_bit(2, 0)
    assert res.size() == 100
    assert res.toint() == 0b011

    v = SparseBitVector(100, 0b111)
    res = v.update_bit(1, 0)
    assert res.size() == 100
    assert res.toint() == 0b101

    v = SparseBitVector(100, 0b111)
    res = v.update_bit(65, 0)
    assert res.size() == 100
    assert res.toint() == 0b111
    assert isinstance(res, bitvector.GenericBitVector)

def test_sparse_signed():
    # XXX Machine?
    v = SparseBitVector(65, 0b0)
    assert v.signed().toint() == 0 
    assert isinstance(v.signed(), SmallInteger)

def test_sparse_unsigned():
    v = SparseBitVector(100, 0b10001101)
    assert v.unsigned().tolong() == 0b10001101

    v = SparseBitVector(100, r_uint(-1))
    assert v.unsigned().tolong() == (1<<64)-1

def test_sparse_truncate():
    res = SparseBitVector(100, 0b1011010100).truncate(2)
    assert isinstance(res, bitvector.SmallBitVector)
    assert res.size() == 2
    assert res.touint() == 0b00
    res = SparseBitVector(100, 0b1011010100).truncate(6)
    assert res.size() == 6
    assert res.touint() == 0b010100
    res = SparseBitVector(100, 0b1011010100).truncate(100)
    assert isinstance(res, bitvector.SparseBitVector)
    assert res.touint() == 0b1011010100

def test_sparse_eq():
    assert SparseBitVector(100, -12331).eq(SparseBitVector(100, -12331))
    assert not SparseBitVector(100, -12331).eq(SparseBitVector(100, 12331))
    assert SparseBitVector(100, 0b10111).eq(bitvector.GenericBitVector(100, rbigint.fromlong(0b10111)))

def test_sparse_lshift():
    v = SparseBitVector(100, 0b10001101)
    res = v.lshift(5)
    assert res.size() == 100
    assert res.toint() == 0b1000110100000
    assert isinstance(res, SparseBitVector)

    v = SparseBitVector(65, 1)
    res = v.lshift(64)
    assert res.size() == 65
    assert res.tolong() == 1 << 64
    assert isinstance(res, bitvector.GenericBitVector)
    
    v = SparseBitVector(100, 0b0010000000000000000000000000000000000000000000000000000000000000)
    res = v.lshift(1)
    assert res.size() == 100
    assert res.toint() == 0b00100000000000000000000000000000000000000000000000000000000000000


    v = SparseBitVector(100, r_uint(1) << 63)
    res = v.lshift(1)
    assert res.size() == 100
    assert isinstance(res, bitvector.GenericBitVector)
    
def test_sparse_check_carry():
    v = SparseBitVector(100, r_uint(0xffffffffffffffff))
    assert v.check_carry(r_uint(0b1)) == 1
    v = SparseBitVector(100, r_uint(0xfffffffffffffffe))
    assert v.check_carry(r_uint(0b1)) == 0
    v = SparseBitVector(100, r_uint(0xfffffffffffffffe))
    assert v.check_carry(r_uint(0b10)) == 1
    v = SparseBitVector(100, r_uint(0xffffffffffffffee))
    assert v.check_carry(r_uint(0xffffffff)) == 1
    v = SparseBitVector(100, r_uint(0xffffffffffffffee))
    assert v.check_carry(r_uint(0x1)) == 0
    v = SparseBitVector(100, r_uint(0x0))
    assert v.check_carry(r_uint(0x1)) == 0


def test_sparse_add_int():
    for c in bi, si:
        assert SparseBitVector(6000, 0b11).add_int(c(0b111111111)).touint() == 0b11 + 0b111111111
        assert SparseBitVector(6000, r_uint(0xfffffffffffffffe)).add_int(c(0b1)).tolong() == 0xfffffffffffffffe + 1
        assert isinstance (SparseBitVector(100, r_uint(0xffffffffffffffff)).add_int(c(0b1)), bitvector.GenericBitVector)
        assert isinstance (SparseBitVector(100, r_uint(0xfffffffffffffffee)).add_int(c(0xfff)), bitvector.GenericBitVector)

def test_sparse_add_bits():
    for c in SparseBitVector, gbv:
        assert SparseBitVector(100, 0b11).add_bits(c(100, 0b111111111)).touint() == 0b11 + 0b111111111
        assert SparseBitVector(100, r_uint(0xfffffffffffffffe)).add_bits(SparseBitVector(100, 0b1)).tolong() == 0xfffffffffffffffe + 1
    assert isinstance(SparseBitVector(65, r_uint(0xffffffffffffffff)).add_bits(SparseBitVector(65,0b1)), bitvector.GenericBitVector)
    v1 = bitvector.SparseBitVector(65, r_uint(0xffffffffffff0001L))
    v2 = bitvector.GenericBitVector(65, [r_uint(0xffff), r_uint(0)])
    res = v1.add_bits(v2)
    assert res.tolong() == (v1.tolong() + v2.tolong()) % (2 ** 65)

def test_sparse_sub_bits():
    for c in gbv, SparseBitVector:
        assert (SparseBitVector(100, r_uint(0b0)).sub_bits(c(100, r_uint(0b1))), bitvector.GenericBitVector)
        assert SparseBitVector(100, r_uint(0b0)).sub_bits(c(100, 0b1)).tolong() == -1 % (2 ** 100)
        assert SparseBitVector(100, r_uint(0xffffffffffffffff)).sub_bits(c(100, 0b1)).tolong() == 0xffffffffffffffff - 1

def test_sparse_sub_int():
    for c in bi, si:
        assert SparseBitVector(100, 0b0).sub_int(c(0b1)).tolong() == -1 % (2 ** 100)
        assert SparseBitVector(6000, r_uint(0xffffffffffffffff)).sub_int(c(0b1)).tolong() == 0xffffffffffffffff -1 
        assert SparseBitVector(68, 4).sub_int(c(9)).tolong() == -5 % (2 ** 68)
        assert SparseBitVector(100, r_uint(18446744073709486081)).sub_int(c(-65535)).tolong() == 18446744073709551616
        assert SparseBitVector(68, 0b0).sub_int(c(0b1)).tolong() == -1 % (2 **68)
    assert isinstance(SparseBitVector(6000, 0b11).sub_int(si(0b11)), SparseBitVector)
    assert isinstance(SparseBitVector(6000, r_uint(0xffffffffffffffff)).sub_int(bi(0b1)), bitvector.GenericBitVector)

        
@given(strategies.data())
def test_sparse_hypothesis_sub_int(data):
    value1 = data.draw(strategies.integers(0, 2**64 - 1))
    value2 = data.draw(strategies.integers(MININT, sys.maxint))
    ans = value1 - value2
    for c in bi, si:
        assert SparseBitVector(100, r_uint(value1)).sub_int(c(value2)).tolong() == ans % (2 ** 100)

@given(two_bitvectors)
def test_hypothesis_sub_bits(values):
    v1, v2 = values
    value1 = v1.tolong()
    value2 = v2.tolong()
    ans = value1 - value2
    res = v1.sub_bits(v2)
    assert res.tolong() == ans % (2 ** v1.size())

@given(two_bitvectors)
def test_hypothesis_add_bits(values):
    v1, v2 = values
    value1 = v1.tolong()
    value2 = v2.tolong()
    ans = value1 + value2
    res = v1.add_bits(v2)
    assert res.tolong() == ans % (2 ** v1.size())


@given(strategies.data())
def test_sparse_hypothesis_add_int(data):
    value1 = data.draw(strategies.integers(0, 2**64 - 1))
    value2 = data.draw(strategies.integers(MININT, sys.maxint))
    ans = value1 + value2
    for c in bi, si:
        if ans >= 0:
            assert SparseBitVector(100, r_uint(value1)).add_int(c(value2)).tolong() == ans 
        assert SparseBitVector(100, r_uint(value1)).add_int(c(value2)).tolong() == ans % (2 ** 100)

@given(strategies.data())
def test_sparse_hypothesis_truncate(data):
    bitwidth = data.draw(strategies.integers(65, 10000))
    truncatewidth = data.draw(strategies.integers(1, bitwidth))
    value = data.draw(strategies.integers(0, 2**64 - 1))
    as_bit_string = bin(value)[2:]
    bv = SparseBitVector(bitwidth, r_uint(value))
    res = bv.truncate(truncatewidth)
    assert bin(bv.tolong())[2:].rjust(bitwidth, '0')[-truncatewidth:] == bin(res.tolong())[2:].rjust(truncatewidth, '0')

@given(strategies.data())
def test_sparse_hypothesis_vector_subrange(data):
    bitwidth = data.draw(strategies.integers(65, 10000))
    # TODO m- n + 1 = 64 wont work
    lower = data.draw(strategies.integers(0, 62))
    upper = data.draw(strategies.integers(lower, 62))
    value = data.draw(strategies.integers(0, 2**63 - 1))
    as_bit_string = bin(value)[2:]
    assert len(as_bit_string) <= bitwidth
    as_bit_string = as_bit_string.rjust(bitwidth, '0')[::-1]
    correct_res = as_bit_string[lower:upper+1] # sail is inclusive
    correct_res_as_int = int(correct_res[::-1], 2)

    # now do the sail computation
    v = SparseBitVector(bitwidth, value)
    vres = v.subrange(upper, lower)
    assert vres.tobigint().tolong() == correct_res_as_int

@settings(deadline=1000)
@given(strategies.data())
def test_sparse_hypothesis_sign_extend(data):
    bitwidth = data.draw(strategies.integers(65, 10000))
    target_bitwidth = bitwidth + data.draw(strategies.integers(1, 100))
    value = data.draw(strategies.integers(0, 2**64 - 1))
    bv = SparseBitVector(bitwidth, r_uint(value))
    res = bv.sign_extend(target_bitwidth)
    print bitwidth, target_bitwidth, value, bv, res, bv.signed().tobigint(), res.signed().tobigint()
    assert bv.signed().tobigint().tolong() == res.signed().tobigint().tolong()

@settings(deadline=1000)
@given(strategies.data())
def test_sparse_hypothesis_zero_extend(data):
    bitwidth = data.draw(strategies.integers(65, 10000))
    target_bitwidth = bitwidth + data.draw(strategies.integers(1, 100))
    value = data.draw(strategies.integers(0, 2**64 - 1))
    bv = SparseBitVector(bitwidth, r_uint(value))
    res = bv.zero_extend(target_bitwidth)
    print bitwidth, target_bitwidth, value, bv, res, bv.signed().tobigint(), res.signed().tobigint()
    assert bv.signed().tobigint().tolong() == res.signed().tobigint().tolong()

@given(strategies.data())
@settings(deadline = None)
def test_sparse_hypothesis_replicate(data):
    bitwidth = data.draw(strategies.integers(65, 10000))
    repeats = data.draw(strategies.integers(1, 10))
    value = data.draw(strategies.integers(0, 2 **64 - 1))
    bv = SparseBitVector(bitwidth, r_uint(value))
    res = bv.replicate(repeats)
    ans_as_int = bin(value)
    formatted_value = str(ans_as_int)[2:]
    leading_zero = (str(0)* (bitwidth - len(formatted_value)) + formatted_value)
    assert len(leading_zero) == bitwidth
    ans = str(leading_zero) * repeats
    assert res.tolong() == int(ans, 2) 


@given(two_bitvectors)
def test_hypothesis_eq(values):
    v1, v2 = values
    assert v1.eq(v1)
    assert v2.eq(v2)
    assert v1.eq(v2) == (v1.tolong() == v2.tolong())
    if isinstance(v1, SparseBitVector):
        assert v1._to_generic().eq(v1)
        assert v1.eq(v1._to_generic())

@given(bitvectors, strategies.data())
def test_hypothesis_update_bit(v, data):
    bitwidth = v.size()
    value = v.tobigint().tolong()
    pos = data.draw(strategies.integers(0, bitwidth - 1))
    bit = data.draw(strategies.integers(0, 1))
    formatted_value = str(bin(value))[2:]
    value = formatted_value.rjust(bitwidth, '0')[::-1]
    res = v.update_bit(pos, bit)
    for readpos in range(bitwidth):
        if pos == readpos:
            assert res.read_bit(readpos) == bit
        else:
            assert v.read_bit(readpos) == res.read_bit(readpos)

@given(bitvectors)
def test_hypothesis_read_bit(v):
    bitwidth = v.size()
    value = v.tobigint().tolong()
    value_as_str = str(bin(value))
    formatted_value = value_as_str[2:].rjust(bitwidth, '0')[::-1]
    for pos in range(bitwidth):
        assert v.read_bit(pos) == int(formatted_value[pos])

@given(two_bitvectors)
def test_hypothesis_op(values):
    v1, v2 = values
    value1 = v1.tolong()
    value2 = v2.tolong()
    assert v1.xor(v2).tolong() == (value1 ^ value2)
    assert v1.or_(v2).tolong() == (value1 | value2)
    assert v1.and_(v2).tolong() == (value1 & value2)


@given(bitvectors)
def test_hypothesis_invert(v):
    res = v.invert()
    assert res.size() == v.size()
    for pos in range(v.size()):
        assert res.read_bit(pos) != v.read_bit(pos)

@given(strategies.data())
def test_sparse_hypothesis_unsigned(data):
    bitwidth = data.draw(strategies.integers(65,10000))
    value = data.draw(strategies.integers(0, 2**64- 1))
    v = SparseBitVector(bitwidth, r_uint(value))
    value_as_str = str(bin(value))
    formatted_value = value_as_str[2:]
    filled = formatted_value.rjust(bitwidth, '0')
    assert v.unsigned().tolong() == int(filled, 2)

@given(strategies.data())
def test_sparse_hypothesis_signed(data):
    bitwidth = data.draw(strategies.integers(65,10000))
    value = data.draw(strategies.integers(-(2**63), (2**63)- 1))
    v = SparseBitVector(bitwidth, r_uint(value))
    # it could never be negative when interpret as signed
    assert v.signed().tolong() >= 0
    assert v.signed().tolong() == r_uint(value)


@given(strategies.data())
def test_sparse_hypothesis_lshift(data):
    bitwidth = data.draw(strategies.integers(65,10000))
    value = data.draw(strategies.integers(0, 2**64- 1))
    v = SparseBitVector(bitwidth, r_uint(value))
    shift = data.draw(strategies.integers(0, bitwidth))
    res = v.lshift(shift).tolong()
    mask = ''
    assert res == (value << shift) & ((1 << bitwidth) - 1) 

@given(strategies.data())
def test_sparse_hypothesis_lshift_bits(data):
    bitwidth = data.draw(strategies.integers(65,10000))
    value1 = data.draw(strategies.integers(0, 2**64- 1))
    value2 = data.draw(strategies.integers(0, bitwidth))
    v1 = SparseBitVector(bitwidth, r_uint(value1))
    v2 = SparseBitVector(bitwidth, r_uint(value2))
    res = v1.lshift_bits(v2).tolong()
    mask = ''
    assert res == (value1 << value2) & ((1 << bitwidth) - 1) 

@given(bitvectors, strategies.data())
def test_hypothesis_rshift(v, data):
    bitwidth = v.size()
    value = v.tolong()
    shift = data.draw(strategies.integers(0, bitwidth + 5))
    res = v.rshift(shift).tolong()
    assert res == (value >> shift)

@given(bitvectors, strategies.data())
def test_hypothesis_lshift(v, data):
    bitwidth = v.size()
    value = v.tolong()
    shift = data.draw(strategies.integers(0, bitwidth + 5))
    res = v.lshift(shift).tolong()
    assert res == (value << shift) % (2 ** bitwidth)

@given(strategies.data())
def test_sparse_hypothesis_rshift_bits(data):
    bitwidth = data.draw(strategies.integers(65,10000))
    value1 = data.draw(strategies.integers(0, 2**64- 1))
    value2 = data.draw(strategies.integers(0, bitwidth))
    v1 = SparseBitVector(bitwidth, r_uint(value1))
    v2 = SparseBitVector(bitwidth, r_uint(value2))
    res = v1.rshift_bits(v2).tolong()
    mask = ''
    assert res == (value1 >> value2) 

@given(strategies.data())
def test_sparse_arith_shiftr_hypothesis(data):
    size = data.draw(strategies.integers(65, 5000))
    value = data.draw(strategies.integers(0, 2**size-1))
    v = bitvector.SparseBitVector(size, r_uint(value))
    shift = data.draw(strategies.integers(0, size+10))
    res = v.arith_rshift(shift)
    intres = v.signed().tobigint().tolong() >> shift
    assert res.tobigint().tolong() == intres & ((1 << size) - 1)

# new generic bitvector infrastructure

@given(strategies.integers(0))
def test_array_from_to_rbigint_roundtrip(value):
    rval = rbigint.fromlong(value)
    data = bitvector.array_from_rbigint(rval.bit_length(), rval)
    rval2 = bitvector.rbigint_from_array(data)
    assert rval.eq(rval2)

@given(strategies.data())
def test_array_from_to_rbigint_roundtrip_size(data):
    bitwidth = data.draw(strategies.integers(65, 1000))
    extra_bits = data.draw(strategies.integers(1, 1000))
    value = data.draw(strategies.integers(0, 2**(bitwidth + extra_bits)))
    rval = rbigint.fromlong(value)
    data = bitvector.array_from_rbigint(bitwidth, rval)
    rval2 = bitvector.rbigint_from_array(data)
    assert rval2.tolong() == value & ((1 << bitwidth) - 1)

