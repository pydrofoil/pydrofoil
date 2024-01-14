import os
import pytest
import sys

from pydrofoil import supportcode
from pydrofoil import bitvector
from pydrofoil.bitvector import Integer, SmallInteger, BigInteger, MININT, SparseBitVector
from pydrofoil.bitvector import GenericBitVector, SmallBitVector
from hypothesis import given, strategies, assume, example, settings

from rpython.rlib.rarithmetic import r_uint, intmask
from rpython.rlib.rbigint import rbigint

MAXINT = sys.maxint
MININT = -sys.maxint - 1

def makelong_long_sequences(data, ndigits):
    """ From CPython:
    Get quasi-random long consisting of ndigits digits (in base BASE).
    quasi == the most-significant digit will not be 0, and the number
    is constructed to contain long strings of 0 and 1 bits.  These are
    more likely than random bits to provoke digit-boundary errors.
    The sign of the number is also random.
    """
    SHIFT = 64
    nbits_hi = ndigits * SHIFT
    nbits_lo = nbits_hi - SHIFT + 1
    answer = 0L
    nbits = 0
    r = data.draw(strategies.integers(0, SHIFT * 2 - 1)) | 1  # force 1 bits to start
    while nbits < nbits_lo:
        bits = (r >> 1) + 1
        bits = min(bits, nbits_hi - nbits)
        assert 1 <= bits <= SHIFT
        nbits = nbits + bits
        answer = answer << bits
        if r & 1:
            answer = answer | ((1 << bits) - 1)
        r = data.draw(strategies.integers(0, SHIFT * 2 - 1))
    assert nbits_lo <= nbits <= nbits_hi
    if data.draw(strategies.booleans()):
        answer = -answer
    return answer

def make_int(data):
    kind = data.draw(strategies.integers(0, 3))
    if kind == 0:
        return SmallInteger(data.draw(ints))
    elif kind == 1:
        return SmallInteger(intmask(r_uint(makelong_long_sequences(data, 1))))
    elif kind == 2:
        # big ints
        return bi(data.draw(strategies.integers()))
    else:
        ndigits = data.draw(strategies.integers(1, 20))
        return bi(makelong_long_sequences(data, ndigits))

ints = strategies.integers(-sys.maxint-1, sys.maxint)
wrapped_ints = strategies.builds(
        make_int,
        strategies.data())
uints = strategies.builds(
        r_uint, ints)

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
    return bitvector.from_bigint(width, rbigint.fromlong(value))

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
    return bitvector.from_bigint(width, rbigint.fromlong(value))

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

two_bitvectors = strategies.builds(
    make_two_bitvectors,
    strategies.data())

def gbv(size, val):
    return bitvector.GenericBitVector.from_bigint(size, rbigint.fromlong(val))

def bv(size, val):
    return bitvector.from_ruint(size, r_uint(val))

def sbv(size, val):
    return SparseBitVector(size, r_uint(val))

def si(val):
    return bitvector.SmallInteger(val)

def bi(val):
    return bitvector.BigInteger(*bitvector.array_and_sign_from_rbigint(rbigint.fromlong(val)))

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

def test_extend_same_width():
    for c in gbv, bv:
        x = c(8, 0b011100)
        assert x.sign_extend(8) is x
        assert x.zero_extend(8) is x
    x = sbv(100, 0b011100)
    assert x.sign_extend(100) is x
    assert x.zero_extend(100) is x

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
def test_hypothesis_set_slice_int(i, start, length, data):
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
    assert res.tolong() == (i.tolong() >> start) % (2 ** length)

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


@given(bitvectors)
def test_hypothesis_size_as_int(bv):
    assert bv.size_as_int().tolong() == bv.size()

@given(bitvectors)
def test_hypothesis_check_size_and_return(bv):
    assert bv.check_size_and_return(bv.size()) is bv
    with pytest.raises(ValueError):
        bv.check_size_and_return(bv.size() + 1)
    with pytest.raises(ValueError):
        bv.check_size_and_return(bv.size() - 1)

def test_toint_overflow():
    with pytest.raises(OverflowError):
        bv(64, r_uint(-1)).toint()

@settings(deadline=1000)
@given(strategies.data())
def test_hypothesis_sign_extend(data):
    bitwidth = data.draw(strategies.integers(1, 1000))
    target_bitwidth = bitwidth + data.draw(strategies.integers(0, 100))
    value = data.draw(strategies.integers(0, 2**bitwidth - 1))
    bv = bitvector.from_bigint(bitwidth, rbigint.fromlong(value))
    res = bv.sign_extend(target_bitwidth)
    assert bv.signed().tobigint().tolong() == res.signed().tobigint().tolong()

@given(strategies.data())
def test_hypothesis_sign_extend_ruint(data):
    bitwidth = data.draw(strategies.integers(1, 64))
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

def test_sparse_sub_range_unwrapped_res_bug():
    v = sbv(128, 2164260864)
    res = supportcode.vector_subrange_o_i_i_unwrapped_res(machine, v, 127, 64)
    assert res == 0
    #vector_subrange_o_i_i_unwrapped_res <SparseBitVector 128 2164260864> 127 64 -> 2164260864

@given(strategies.integers(), strategies.integers(0, 100))
@example(-9223372036854775935L, 1)
@example(-9223372036854775809L, 63)
def test_hypothesis_extract_ruint(value, shift):
    rval = rbigint.fromlong(value)
    assert bitvector.rbigint_extract_ruint(rval, shift) == r_uint(value >> shift)

def test_vector_update_subrange():
    for c1 in gbv, bv:
        for c2 in bv,:
            x = c1(8, 0b10001101)
            x = x.update_subrange(5, 2, c2(4, 0b1010))
            assert x.toint() == 0b10101001
            x = c1(64, 0b10001101)
            y = c2(64, 0b1101001010010)
            x = x.update_subrange(63, 0, y)
            assert x.tolong() == y.tolong()

def test_big_update_subrange():
    # word indexes                    4               3               2               1               0
    # word boundaries <       .       <       .       <       .       <       .       <       .       <
    v1 = gbv(5 * 64, 0x0102030405060708090a0b0c0e0f1112131415160102030405060708090a0b0c0e0f111213141516)
    # other word indexes                             2               1               0
    # other word boundaries                          <       .       <       .       <
    v2 = gbv(132,                                  0xaabacadaeafbabbcfafbfcfdfeffbfcbf)
    exp =           '0x0102030405060708090A0B0C0E0F11AABACADAEAFBABBCFAFBFCFDFEFFBFCBFC0E0F111213141516'
    res = v1.update_subrange(68 + 132 - 1, 68, v2)
    assert res.string_of_bits() == exp

    # word indexes                    4               3               2               1               0
    # word boundaries <       .       <       .       <       .       <       .       <       .       <
    v1 = gbv(5 * 64, 0x0102030405060708090a0b0c0e0f1112131415160102030405060708090a0b0c0e0f111213141516)
    # other word indexes                             2               1               0
    # other word boundaries                          <       .       <       .       <
    v2 = gbv(128,                                   0xabacadaeafbabbcfafbfcfdfeffbfcbf)
    exp =           '0x0102030405060708090A0B0C0E0F111ABACADAEAFBABBCFAFBFCFDFEFFBFCBFC0E0F111213141516'
    #                0x0102030405060708090a0b0c0e0f1112bacadaeafbabbcfafbfcfdfeffbfcbfc0e0f111213141516  resdata after loop
    res = v1.update_subrange(68 + 128 - 1, 68, v2)
    assert res.string_of_bits() == exp

    # word indexes                    4               3               2               1               0
    # word boundaries <       .       <       .       <       .       <       .       <       .       <
    v1 = gbv(5 * 64, 0x0102030405060708090a0b0c0e0f1112131415160102030405060708090a0b0c0e0f111213141516)
    # other word indexes                              2               1               0
    # other word boundaries                           <       .       <       .       <
    v2 = gbv(140,                                 0x999abacadaeafbabbcfafbfcfdfeffbfcbf)
    exp =           '0x0102030405060708090A0B0C0E0F1999ABACADAEAFBABBCFAFBFCFDFEFFBFCBF0E0F111213141516'
    #                0x0102030405060708090a0b0c0e0f1112bacadaeafbabbcfafbfcfdfeffbfcbfc0e0f111213141516  resdata after loop
    res = v1.update_subrange(64 + 140 - 1, 64, v2)
    assert res.string_of_bits() == exp

    # word indexes                    4               3               2               1               0
    # word boundaries <       .       <       .       <       .       <       .       <       .       <
    v1 = gbv(5 * 64, 0x0102030405060708090a0b0c0e0f1112131415160102030405060708090a0b0c0e0f111213141516)
    # other word indexes                              2               1               0
    # other word boundaries                           <       .       <       .       <
    v2 = gbv(128,                                    0xabacadaeafbabbcfafbfcfdfeffbfcbf)
    exp =           '0x0102030405060708090A0B0C0E0F1112ABACADAEAFBABBCFAFBFCFDFEFFBFCBF0E0F111213141516'
    #                0x0102030405060708090a0b0c0e0f1112bacadaeafbabbcfafbfcfdfeffbfcbfc0e0f111213141516  resdata after loop
    res = v1.update_subrange(64 + 128 - 1, 64, v2)
    assert res.string_of_bits() == exp

def test_sparse_vector_update_subrange():
    for c in sbv, gbv:
        x = c(100, 0b10001101)
        x = x.update_subrange(5, 2, bv(4, 0b1010))
        assert x.toint() == 0b10101001
        x = c(100, 0b10001101)
        y = c(100, 0b1101001010010)
        x = x.update_subrange(99, 0, y)
        assert x.eq(y)
        x = SparseBitVector(65, r_uint(0b10001101))
        y = c(65, 0b1101001010010)
        x = x.update_subrange(64, 0, y)
        assert x.eq(y)
    x = SparseBitVector(1000, r_uint(0b10001101))
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
def test_vector_update_subrange_hypothesis_unboxed(data):
    width = data.draw(strategies.integers(1, 64))
    value = data.draw(strategies.integers(0, 2**width-1))
    lower = data.draw(strategies.integers(0, width-1))
    upper = data.draw(strategies.integers(lower, width-1))
    subwidth = upper - lower + 1
    assert 1 <= subwidth <= width <= 64
    subvalue = supportcode.r_uint(data.draw(strategies.integers(0, 2 ** subwidth - 1)))

    res = supportcode.vector_update_subrange_fixed_bv_i_i_bv(machine, r_uint(value), upper, lower, subvalue)
    # check: the read of the same range must return replace_bv
    assert subvalue == supportcode.vector_subrange_fixed_bv_i_i(machine, res, upper, lower)
    # the other bits must be unchanged
    if lower:
        assert supportcode.vector_subrange_fixed_bv_i_i(machine, res, lower - 1, 0) == supportcode.vector_subrange_fixed_bv_i_i(machine, value, lower - 1, 0)
    if upper < width - 1:
        assert supportcode.vector_subrange_fixed_bv_i_i(machine, res, width - 1, upper + 1) == supportcode.vector_subrange_fixed_bv_i_i(machine, value, width - 1, upper + 1)

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

@given(bitvectors)
def test_hypothesis_unpack_pack(bv):
    tup = bv.pack()
    bv2 = bitvector.BitVector.unpack(*tup)
    assert bv2.eq(bv)

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

        with pytest.raises(ValueError):
            x.lshift(-1)
        with pytest.raises(ValueError):
            x.rshift(-1)

    x = bv(8, 0b10001101)
    res = x.lshift(10)
    assert res.size() == 8
    assert res.toint() == 0

    x = bv(8, 0b10001101)
    res = x.rshift(10)
    assert res.size() == 8
    assert res.toint() == 0


    x = gbv(65, 0b10001101)
    res = x.lshift(100)
    assert res.size() == 65
    assert res.toint() == 0
    x = gbv(65, 0b10001101)
    res = x.rshift(100)
    assert res.size() == 65
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

    x = bv(8, 0b10001101)
    res = x.lshift_bits(c(8, 65))
    assert res.size() == 8
    assert res.toint() == 0

    x = gbv(65, 0b10001101)
    res = x.lshift_bits(c(8, 100))
    assert res.size() == 65
    assert res.toint() == 0


def test_arith_shiftr():
    x = bv(8, 0b10001101)
    res = x.arith_rshift(2)
    assert res.size() == 8
    assert res.toint() == 0b11100011

    res = x.arith_rshift(8)
    assert res.size() == 8
    assert res.toint() == 0b11111111

    res = x.arith_rshift(10)
    assert res.size() == 8
    assert res.toint() == 0b11111111

    x = bv(8, 0b00101101)
    res = x.arith_rshift(3)
    assert res.size() == 8
    assert res.toint() == 0b101

    with pytest.raises(ValueError):
        x.arith_rshift(-1)

    x = gbv(100, 0xfffffffffffffffffffffff8d)
    res = x.arith_rshift(4)
    assert res.size() == 100
    assert res.tolong() == 0xffffffffffffffffffffffff8

    res = x.arith_rshift(8)
    assert res.size() == 100
    assert res.tolong() == 0xfffffffffffffffffffffffff

    res = x.arith_rshift(110)
    assert res.size() == 100
    assert res.tolong() == 0xfffffffffffffffffffffffff

    x = gbv(100, 0b00101101)
    res = x.arith_rshift(3)
    assert res.size() == 100
    assert res.tolong() == 0b101

    with pytest.raises(ValueError):
        x.arith_rshift(-1)

def test_arith_shiftr_bug():
    x = gbv(64, 18446744073709551616)
    x.arith_rshift(2)


@given(bitvectors, strategies.data())
def test_arith_shiftr_hypothesis(bv, data):
    value = bv.tolong()
    size = bv.size()
    shift = data.draw(strategies.integers(0, size+10))
    res = bv.arith_rshift(shift)
    # compare against signed, then integer shift
    intres = bv.signed().tobigint().tolong() >> shift
    assert res.tobigint().tolong() == intres & ((1 << size) - 1)

def test_shiftr_bv_i():
    assert supportcode.arith_shiftr_bv_i(machine, 0b10001101, 8, 2) == 0b11100011
    assert supportcode.arith_shiftr_bv_i(machine, 0b10001101, 8, 8) == 0b11111111
    assert supportcode.arith_shiftr_bv_i(machine, 0b00101101, 8, 3) == 0b101
    assert supportcode.shiftr_bv_i(machine, 0b10001101, 8, 2) == 0b100011
    assert supportcode.shiftr_bv_i(machine, 0b10001101, 8, 8) == 0b0
    assert supportcode.shiftr_bv_i(machine, 0b00101101, 8, 3) == 0b101

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

@given(bitvectors, wrapped_ints)
def test_hypothesis_add_bits_int(bvvalue, irhs):
    value = bvvalue.tolong()
    rhs = irhs.tolong()
    bvres = bvvalue.add_int(irhs)
    bitwidth = bvvalue.size()
    assert irhs.tolong() == rhs

    assert bvres.tolong() == (value + rhs) % (2 ** bitwidth)
    assert irhs.tolong() == rhs
    bvres = bvvalue.sub_int(irhs)
    assert irhs.tolong() == rhs
    assert bvres.tolong() == (value - rhs) % (2 ** bitwidth)
    assert irhs.tolong() == rhs

@given(strategies.data())
def test_hypothesis_add_bits_int_bv_i(data):
    bitwidth = data.draw(strategies.integers(1, 64))
    value = r_uint(data.draw(strategies.integers(0, 2**bitwidth - 1)))
    rhs = data.draw(ints)
    res = supportcode.add_bits_int_bv_i(None, value, bitwidth, rhs)
    assert res == supportcode._mask(bitwidth, value + r_uint(rhs))
    res = supportcode.sub_bits_int_bv_i(None, value, bitwidth, rhs)
    assert res == supportcode._mask(bitwidth, value - r_uint(rhs))

@given(two_bitvectors)
def test_hypothesis_add_bits_sub_bits(values):
    v1, v2 = values
    value1 = v1.tolong()
    value2 = v2.tolong()
    ans = value1 + value2
    res = v1.add_bits(v2)
    assert res.tolong() == ans % (2 ** v1.size())
    ans = value1 - value2
    res = v1.sub_bits(v2)
    assert res.tolong() == ans % (2 ** v1.size())

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
            assert c1(sys.maxint).eq(c2(sys.maxint))
            assert c1(-sys.maxint-1).eq(c2(-sys.maxint-1))

def test_op_int():
    for c1 in bi, si:
        for c2 in bi, si:
            for v1 in [-10, 223, 12311, 0, 1, 2**63-1, MININT]:
                a = c1(v1)
                assert a.neg().tolong() == -v1
                for v2 in [-10, 223, 12311, 0, 1, 8, 2**63-1, -2**45, MININT]:
                    v2 = int(v2)
                    b = c2(v2)
                    assert a.add(b).tolong() == v1 + v2
                    assert a.sub(b).tolong() == v1 - v2
                    assert a.mul(b).tolong() == v1 * v2
                    if v2 and v1 != MININT and v2 != MININT:
                        assert c1(abs(v1)).tdiv(c2(abs(v2))).tolong() == abs(v1) // abs(v2)
                        assert c1(abs(v1)).tmod(c2(abs(v2))).tolong() == abs(v1) % abs(v2)
                        # (a/b) * b + a%b == a
                        assert a.tdiv(b).mul(b).add(a.tmod(b)).eq(a)
                    assert a.int_add(v2).tolong() == v1 + v2
                    assert a.int_sub(v2).tolong() == v1 - v2

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
    v1 = a.tolong()
    v2 = b.tolong()
    aaddb = a.add(b)
    assert aaddb.tolong() == b.add(a).tolong() == v1 + v2
    assert a.sub(b).tolong() == v1 - v2
    assert a.mul(b).tolong() == b.mul(a).tolong() == v1 * v2
    if v2:
        assert a.abs().tdiv(b.abs()).tolong() == abs(v1) // abs(v2)
        assert a.abs().tmod(b.abs()).tolong() == abs(v1) % abs(v2)
        # (a/b) * b + a%b == a
        assert a.tdiv(b).mul(b).add(a.tmod(b)).eq(a)

    assert a.eq(a)
    assert b.eq(b)
    if v1 and v2:
        assert not b.eq(aaddb)
    assert a.eq(b) == (v1 == v2) == b.eq(a)
    if isinstance(b, SmallInteger):
        assert a.int_eq(b.val) == (v1 == v2)
        if v1 and v2:
            assert not aaddb.int_eq(b.val)
    if isinstance(a, SmallInteger):
        assert b.int_eq(a.val) == (v1 == v2)
    assert a.lt(b) == (v1 < v2)
    assert a.lt(a.int_add(1))
    if v1 > 0:
        assert a.lt(a.lshift(64))
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
    assert a.neg().tolong() == -v1

def test_int_eq_bug():
    a = bitvector.BigInteger([r_uint(1), r_uint(1)], 1)
    assert not a.int_eq(1)

@given(wrapped_ints, ints)
def test_int_add_sub_mul_hypothesis(a, b):
    v1 = a.tobigint().tolong()
    v2 = b
    assert a.int_add(b).tolong() == v1 + v2
    assert a.int_sub(b).tolong() == v1 - v2
    assert a.int_mul(b).tolong() == v1 * v2

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

def test_tdiv_int_i_i():
    # check rounding towards 0
    assert supportcode.tdiv_int_i_i(machine, 7, 2) == 3
    assert supportcode.tdiv_int_i_i(machine, -7, 2) == -3
    assert supportcode.tdiv_int_i_i(machine, 7, -2) == -3
    assert supportcode.tdiv_int_i_i(machine, -7, -2) == 3


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
    for c2 in bi, si:
        assert bv(16, 4).add_int(c2(9)).touint() == 13
        assert bv(16, 4).sub_int(c2(9)).touint() == r_uint((-5) & 0xffff)

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
    for c1 in bv,:
        for c2 in bv,:
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
           with pytest.raises(ZeroDivisionError):
               c1(123).emod(c2(0))
           with pytest.raises(ZeroDivisionError):
               c1(123).ediv(c2(0))
           assert c1(123875).emod(c2(13)).toint() == 123875 % 13
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

def test_ediv_int_i_ipos():
    assert supportcode.ediv_int_i_ipos(None, 123875, 13) == 123875 // 13
    assert supportcode.ediv_int_i_ipos(None, MININT, 2) == -2**62
    assert supportcode.ediv_int_i_ipos(None, MININT + 1, sys.maxint) == -1
    assert supportcode.ediv_int_i_ipos(None, 7, 5) == 1
    assert supportcode.ediv_int_i_ipos(None, -7, 5) == -2
    assert supportcode.ediv_int_i_ipos(None, 12, 3) == 4
    assert supportcode.ediv_int_i_ipos(None, -12, 3) == -4

def test_pow2():
    for i in range(1000):
        assert supportcode.pow2_i(None, i).tobigint().tolong() == 2 ** i
    # check that small results use small ints
    for i in range(63):
        assert supportcode.pow2_i(None, i).val == 2 ** i


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
    v = sbv(100, 0b10001101)

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
    v = sbv(100, 0b00101101)
    res = v.arith_rshift(3)
    assert res.size() == 100
    assert res.toint() == 0b101

    v = sbv(100, 0b1000100)
    res = v.arith_rshift(6)
    assert res.size() == 100
    assert res.toint() == 0b1

    v = sbv(100, 0b1000100)
    res = v.arith_rshift(200)
    assert res.size() == 100
    assert res.toint() == 0b0

def test_sparse_vector_shift_bits():
    v = sbv(100, 0b10001101)
    res = v.rshift_bits(sbv(100, 5))
    assert res.size() == 100
    assert res.toint() == 0b00000100

    v = sbv(100, 0b10001101)
    res = v.rshift_bits(sbv(100, 65))
    assert res.size() == 100
    assert res.toint() == 0

def test_sparse_bv_bitwise():
    v1 = sbv(100, 0b11110000)
    v2 = sbv(100, 0b11001100)
    res = v1.and_(v2)
    assert res.toint() == 0b11110000 & 0b11001100
    res = v1.or_(v2)
    assert res.toint() == 0b11110000 | 0b11001100
    res = v1.xor(v2)
    assert res.toint() == 0b11110000 ^ 0b11001100

def test_sparse_zero_extend():
    v = sbv(65, 0b0)
    res = v.zero_extend(100)
    assert res.size() == 100
    assert res.toint() == 0

    v = sbv(100, 0b00)
    res = v.zero_extend(100)
    assert res.size() == 100
    assert res.toint() == 0

    v = sbv(65, 0b1)
    res = v.zero_extend(100)
    assert res.size() == 100
    assert res.toint() == 0b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001

    v = sbv(65, 0b11)
    res = v.zero_extend(100)
    assert res.size() == 100
    assert res.toint() == 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011

def test_sparse_sign_extend():
    v = sbv(65, 0b0)
    res = v.sign_extend(100)
    assert res.size() == 100
    assert res.toint() == 0

    v = sbv(100, 0b00)
    res = v.sign_extend(100)
    assert res.size() == 100
    assert res.toint() == 0

    v = sbv(65, 0b1)
    res = v.sign_extend(100)
    assert res.size() == 100
    assert res.toint() == 0b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001

    v = sbv(65, 0b11)
    res = v.sign_extend(100)
    assert res.size() == 100
    assert res.toint() == 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011


def test_sparse_vector_subrange():
    v = sbv(100, 0b111)
    r = v.subrange(3, 2)
    assert r.size() == 2
    assert r.toint() == 1
    assert isinstance(r, bitvector.SmallBitVector)

    v = sbv(65, 0b111)
    r = v.subrange(63, 0)
    assert r.size() == 64
    assert r.toint() == 0b111
    assert isinstance(r, bitvector.SmallBitVector)

    v = sbv(100, 0b101010101)
    r = v.subrange(65, 2)
    assert r.size() == 64
    assert r.toint() == 0b1010101
    assert isinstance(r, bitvector.SmallBitVector)

    v = sbv(100, 0b101010101)
    r = v.subrange(5, 0)
    assert r.size() == 6
    assert r.toint() == 0b10101
    assert isinstance(r, bitvector.SmallBitVector)

    v = sbv(100, 0b101010101)
    r = v.subrange(65, 0)
    assert r.size() == 66
    assert r.toint() == 0b101010101
    assert isinstance(r, bitvector.SparseBitVector)

    v = sbv(100, 0b101010101)
    r = v.subrange(65, 3)
    assert r.size() == 63
    assert r.toint() == 0b101010
    assert isinstance(r, bitvector.SmallBitVector)

    v = sbv(100, 0b101010101)
    r = v.subrange(65, 1)
    assert r.size() == 65
    assert r.toint() == 0b10101010
    assert isinstance(r, bitvector.SparseBitVector)

    v = sbv(100, 0b101010101)
    r = v.subrange(99, 0)
    assert r.size() == 100
    assert r.toint() == 0b101010101
    assert isinstance(r, bitvector.SparseBitVector)

def test_sparse_vector_update():
    v = sbv(100, 1)
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

    v = sbv(100, 1)
    res = v.update_bit(0, 1)
    assert res.size() == 100
    assert res.toint() == 0b1

    v = sbv(100, 0b11)
    res = v.update_bit(2, 0)
    assert res.size() == 100
    assert res.toint() == 0b011

    v = sbv(100, 0b111)
    res = v.update_bit(1, 0)
    assert res.size() == 100
    assert res.toint() == 0b101

    v = sbv(100, 0b111)
    res = v.update_bit(65, 0)
    assert res.size() == 100
    assert res.toint() == 0b111
    assert isinstance(res, bitvector.GenericBitVector)

def test_sparse_signed():
    v = sbv(65, 0b0)
    assert v.signed().toint() == 0
    assert isinstance(v.signed(), SmallInteger)

def test_sparse_unsigned():
    v = sbv(100, 0b10001101)
    assert v.unsigned().tolong() == 0b10001101

    v = SparseBitVector(100, r_uint(-1))
    assert v.unsigned().tolong() == (1<<64)-1

def test_sparse_truncate():
    res = sbv(100, 0b1011010100).truncate(2)
    assert isinstance(res, bitvector.SmallBitVector)
    assert res.size() == 2
    assert res.touint() == 0b00
    res = sbv(100, 0b1011010100).truncate(6)
    assert res.size() == 6
    assert res.touint() == 0b010100
    res = sbv(100, 0b1011010100).truncate(100)
    assert isinstance(res, bitvector.SparseBitVector)
    assert res.touint() == 0b1011010100

def test_sparse_eq():
    assert sbv(100, -12331).eq(sbv(100, -12331))
    assert not sbv(100, -12331).eq(sbv(100, 12331))
    assert sbv(100, 0b10111).eq(gbv(100, 0b10111))

def test_sparse_lshift():
    v = sbv(100, 0b10001101)
    res = v.lshift(5)
    assert res.size() == 100
    assert res.toint() == 0b1000110100000
    assert isinstance(res, SparseBitVector)

    v = sbv(65, 1)
    res = v.lshift(64)
    assert res.size() == 65
    assert res.tolong() == 1 << 64
    assert isinstance(res, bitvector.GenericBitVector)

    v = sbv(100, 0b0010000000000000000000000000000000000000000000000000000000000000)
    res = v.lshift(1)
    assert res.size() == 100
    assert res.toint() == 0b00100000000000000000000000000000000000000000000000000000000000000


    v = sbv(100, r_uint(1) << 63)
    res = v.lshift(1)
    assert res.size() == 100
    assert isinstance(res, bitvector.GenericBitVector)

def test_sparse_add_int():
    for c in bi, si:
        assert sbv(6000, 0b11).add_int(c(0b111111111)).touint() == 0b11 + 0b111111111
        assert sbv(6000, r_uint(0xfffffffffffffffe)).add_int(c(0b1)).tolong() == 0xfffffffffffffffe + 1
        assert isinstance (sbv(100, r_uint(0xffffffffffffffff)).add_int(c(0b1)), bitvector.GenericBitVector)
        assert isinstance (sbv(100, r_uint(0xfffffffffffffffee)).add_int(c(0xfff)), bitvector.GenericBitVector)

def test_sparse_add_bits():
    for c in sbv, gbv:
        assert sbv(100, 0b11).add_bits(c(100, 0b111111111)).touint() == 0b11 + 0b111111111
        assert sbv(100, r_uint(0xfffffffffffffffe)).add_bits(sbv(100, 0b1)).tolong() == 0xfffffffffffffffe + 1
    assert isinstance(sbv(65, r_uint(0xffffffffffffffff)).add_bits(sbv(65,0b1)), bitvector.GenericBitVector)
    v1 = sbv(65, r_uint(0xffffffffffff0001L))
    v2 = bitvector.GenericBitVector(65, [r_uint(0xffff), r_uint(0)])
    res = v1.add_bits(v2)
    assert res.tolong() == (v1.tolong() + v2.tolong()) % (2 ** 65)

def test_sparse_sub_bits():
    for c in gbv, sbv:
        assert (sbv(100, r_uint(0b0)).sub_bits(c(100, r_uint(0b1))), bitvector.GenericBitVector)
        assert sbv(100, r_uint(0b0)).sub_bits(c(100, 0b1)).tolong() == -1 % (2 ** 100)
        assert sbv(100, r_uint(0xffffffffffffffff)).sub_bits(c(100, 0b1)).tolong() == 0xffffffffffffffff - 1

def test_sparse_sub_int():
    for c in bi, si:
        assert sbv(100, 0b0).sub_int(c(0b1)).tolong() == -1 % (2 ** 100)
        assert sbv(6000, r_uint(0xffffffffffffffff)).sub_int(c(0b1)).tolong() == 0xffffffffffffffff -1
        assert sbv(68, 4).sub_int(c(9)).tolong() == -5 % (2 ** 68)
        assert sbv(100, r_uint(18446744073709486081)).sub_int(c(-65535)).tolong() == 18446744073709551616
        assert sbv(68, 0b0).sub_int(c(0b1)).tolong() == -1 % (2 **68)
    assert isinstance(sbv(6000, 0b11).sub_int(si(0b11)), SparseBitVector)
    assert isinstance(sbv(6000, r_uint(0xffffffffffffffff)).sub_int(bi(0b1)), bitvector.GenericBitVector)


@given(strategies.data())
def test_sparse_hypothesis_sub_int(data):
    value1 = data.draw(strategies.integers(0, 2**64 - 1))
    value2 = data.draw(strategies.integers(MININT, sys.maxint))
    ans = value1 - value2
    for c in bi, si:
        assert sbv(100, r_uint(value1)).sub_int(c(value2)).tolong() == ans % (2 ** 100)

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
            assert sbv(100, r_uint(value1)).add_int(c(value2)).tolong() == ans
        assert sbv(100, r_uint(value1)).add_int(c(value2)).tolong() == ans % (2 ** 100)

@given(bitvectors, wrapped_ints)
def test_hypothesis_add_int(bv, i):
    res = bv.add_int(i)
    assert res.tolong() == (bv.tolong() + i.tolong()) % (2 ** bv.size())

@given(bitvectors, wrapped_ints)
def test_hypothesis_sub_int(bv, i):
    res = bv.sub_int(i)
    assert res.tolong() == (bv.tolong() - i.tolong()) % (2 ** bv.size())

@given(strategies.data())
def test_sparse_hypothesis_truncate(data):
    bitwidth = data.draw(strategies.integers(65, 10000))
    truncatewidth = data.draw(strategies.integers(1, bitwidth))
    value = data.draw(strategies.integers(0, 2**64 - 1))
    as_bit_string = bin(value)[2:]
    bv = sbv(bitwidth, r_uint(value))
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
    v = sbv(bitwidth, value)
    vres = v.subrange(upper, lower)
    assert vres.tobigint().tolong() == correct_res_as_int

@settings(deadline=1000)
@given(strategies.data())
def test_sparse_hypothesis_sign_extend(data):
    bitwidth = data.draw(strategies.integers(65, 10000))
    target_bitwidth = bitwidth + data.draw(strategies.integers(0, 100))
    value = data.draw(strategies.integers(0, 2**64 - 1))
    bv = SparseBitVector(bitwidth, r_uint(value))
    res = bv.sign_extend(target_bitwidth)
    assert bv.signed().tobigint().tolong() == res.signed().tobigint().tolong()

@settings(deadline=1000)
@given(strategies.data())
def test_sparse_hypothesis_zero_extend(data):
    bitwidth = data.draw(strategies.integers(65, 10000))
    target_bitwidth = bitwidth + data.draw(strategies.integers(0, 100))
    value = data.draw(strategies.integers(0, 2**64 - 1))
    bv = SparseBitVector(bitwidth, r_uint(value))
    res = bv.zero_extend(target_bitwidth)
    assert bv.signed().tobigint().tolong() == res.signed().tobigint().tolong()

@settings(deadline=1000)
@given(bitvectors, strategies.data())
def test_hypothesis_zero_extend(bv, data):
    bitwidth = bv.size()
    extra_width = data.draw(strategies.integers(0, 100))
    target_bitwidth = bitwidth + extra_width
    res = bv.zero_extend(target_bitwidth)
    assert res.truncate(bitwidth).eq(bv)
    if extra_width:
        assert res.rshift(bitwidth).truncate(extra_width).eq(bitvector.from_ruint(extra_width, r_uint(0)))
    assert bv.unsigned().eq(res.unsigned())

@given(bitvectors, strategies.data())
@settings(deadline = None)
def test_hypothesis_replicate(bv, data):
    bitwidth = bv.size()
    assume(bitwidth < 500)
    repeats = data.draw(strategies.integers(1, 100))
    res = bv.replicate(repeats)
    ans_as_int = bin(bv.tolong())
    formatted_value = str(ans_as_int)[2:]
    leading_zero = (str(0) * (bitwidth - len(formatted_value)) + formatted_value)
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
    # it can never be negative when interpreted as signed
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
    intres = v.signed().tolong() >> shift
    assert res.tobigint().tolong() == intres & ((1 << size) - 1)

@given(strategies.data())
def test_lshift_rshift_equivalent_to_mask(data):
    numbits = data.draw(strategies.integers(1, 20))
    value = data.draw(strategies.integers(0, 2**64))
    address = r_uint(value)
    machine = None
    proper_result = supportcode.get_slice_int_i_o_i_unwrapped_res(
        machine,
        64,
        supportcode.shl_int_i_i_wrapped_res(
            machine,
            supportcode.unsigned_bv64_rshift_int_result(machine, address, numbits),
            numbits,
        ),
        0,
    )
    mask = ~((r_uint(1) << numbits) - 1)
    fast_result = address & mask
    assert proper_result == fast_result

@given(bitvectors, bitvectors)
def test_append_hypothesis(a, b):
    la = a.tolong()
    lb = b.tolong()
    res = a.append(b)
    lres = res.tolong()
    assert lres == (la << b.size()) | lb

@given(bitvectors, uints)
def test_append_64_hypothesis(a, b):
    la = a.tolong()
    lb = int(b)
    res = a.append_64(b)
    lres = res.tolong()
    assert lres == (la << 64) | lb

@given(strategies.data())
def test_hypothesis_bitvector_touint(data):
    width = data.draw(strategies.integers(1, 64))
    value = data.draw(strategies.integers(0, 2**width-1))
    v = bv(width, value)
    assert v.touint() == v.touint(width) == value
    with pytest.raises(AssertionError):
        v.touint(width + 1)

@given(strategies.data())
def test_hypothesis_sparse_bitvector_touint(data):
    width = data.draw(strategies.integers(65, 1000))
    value = data.draw(strategies.integers(0, 2**64-1))
    v = sbv(width, value)
    assert v.touint() == v.touint(width) == value
    with pytest.raises(AssertionError):
        v.touint(width + 1)

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

@given(strategies.integers())
def test_array_and_sign_from_to_rbigint_roundtrip(value):
    rval = rbigint.fromlong(value)
    data, sign = bitvector.array_and_sign_from_rbigint(rval)
    rval2 = bitvector.rbigint_from_array_and_sign(data, sign)
    assert rval.eq(rval2)

@given(ints)
def test_data_and_sign_from_int(value):
    data, sign = bitvector._data_and_sign_from_int(value)
    assert bitvector.rbigint_from_array_and_sign(data, sign).tolong() == value

# more hypothesis tests for ints

@given(wrapped_ints, strategies.data())
def test_hypothesis_int_lshift(i, data):
    value = i.tolong()
    bitwidth = i.tolong().bit_length()
    shift = data.draw(strategies.integers(0, bitwidth + 100))
    res = i.lshift(shift).tolong()
    assert res == (value << shift)

@given(wrapped_ints, strategies.data())
def test_hypothesis_int_rshift(i, data):
    value = i.tolong()
    bitwidth = i.tolong().bit_length()
    shift = data.draw(strategies.integers(0, bitwidth + 100))
    res = i.rshift(shift).tolong()
    assert res == (value >> shift)

@given(wrapped_ints, strategies.data())
def test_hypothesis_int_lshift_multiple_of_64(i, data):
    value = i.tolong()
    bitwidth = i.tolong().bit_length()
    shift = data.draw(strategies.integers(0, bitwidth + 100)) // 64 * 64
    res = i.lshift(shift).tolong()
    assert res == (value << shift)

@given(wrapped_ints, strategies.data())
def test_hypothesis_int_rshift_multiple_of_64(i, data):
    value = i.tolong()
    bitwidth = i.tolong().bit_length()
    shift = data.draw(strategies.integers(0, bitwidth + 100)) // 64 * 64
    res = i.rshift(shift).tolong()
    assert res == (value >> shift)

@given(wrapped_ints)
def test_hypothesis_int_unpack_pack(i):
    tup = i.pack()
    i2 = bitvector.Integer.unpack(*tup)
    assert i2.eq(i)

@given(ints)
@example(MAXINT)
@example(MININT)
def test_hypothesis_int_toint(i):
    si = Integer.fromint(i)
    assert si.toint() == i
    data, sign = bitvector._data_and_sign_from_int(i)
    bi = bitvector.BigInteger(data, sign)
    assert bi.toint() == i

@given(strategies.integers())
def test_hypothesis_int_toint_error(i):
    data, sign = bitvector._data_and_sign_from_int(i)
    bi = bitvector.BigInteger(data, sign)
    assume(i != 0)
    if i > 0:
        bi = Integer.fromlong(i + MAXINT)
    elif i < 0:
        bi = Integer.fromlong(MININT + i)
    with pytest.raises(ValueError):
        bi.toint()

@given(strategies.integers())
def test_hypothesis_fromstr(i):
    assert Integer.fromstr(str(i).strip('L')).tolong() == i

@given(strategies.integers())
def test_hypothesis_fromlong(i):
    assert Integer.fromlong(i).tolong() == i

@given(strategies.integers())
def test_hypothesis_int_str(i):
    assert Integer.fromlong(i).str() == str(i)
    assert Integer.fromlong(i).hex() == hex(i)

@given(uints)
def test_hypothesis_int_from_ruint_to_uint_roundtrips(ui):
    assert Integer.from_ruint(ui).touint() == ui

def test_efficient_append(monkeypatch):
    tobigint = GenericBitVector.tobigint
    def tolong(res):
        return tobigint(res).tolong()
    monkeypatch.setattr(SmallBitVector, 'tobigint', None)
    monkeypatch.setattr(GenericBitVector, 'tobigint', None)
    monkeypatch.setattr(SparseBitVector, 'tobigint', None)
    v1 = bv(64, 0xa9e3)
    v2 = bv(16, 0x04fb)
    res = v1.append(v2)
    assert isinstance(res, SparseBitVector)
    assert res.toint() == 0xa9e304fb

    v1 = bv(64, 0xa9e3)
    v2 = bv(56, 0x04fb)
    res = v1.append(v2)
    assert isinstance(res, GenericBitVector)
    assert tolong(res) == (0xa9e3 << 56) | 0x04fb

    v1 = sbv(128, 0xa9e3)
    v2 = sbv(128, 0x04fb)
    res = v1.append(v2)
    assert isinstance(res, GenericBitVector)
    assert tolong(res) == (0xa9e3 << 128) | 0x04fb

    v1 = sbv(128, 0xa9e3)
    v2 = GenericBitVector(128, [r_uint(0), r_uint(0x04fb)])
    res = v1.append(v2)
    assert isinstance(res, GenericBitVector)
    assert tolong(res) == (0xa9e3 << 128) | (0x04fb << 64)

def test_efficient_append64(monkeypatch):
    tobigint = GenericBitVector.tobigint
    def tolong(res):
        return tobigint(res).tolong()
    monkeypatch.setattr(SmallBitVector, 'tobigint', None)
    monkeypatch.setattr(GenericBitVector, 'tobigint', None)
    monkeypatch.setattr(SparseBitVector, 'tobigint', None)

    v1 = bv(64, 0x0)
    res = v1.append_64(r_uint(0x04fb))
    assert isinstance(res, SparseBitVector)
    assert res.val == 0x04fb

    v1 = bv(32, 0xa9e3)
    res = v1.append_64(r_uint(0x04fb))
    assert isinstance(res, GenericBitVector)
    assert tolong(res) == (0xa9e3 << 64) | 0x04fb
    assert res.size() == 64 + 32

    v1 = sbv(128, 0xa9e3)
    res = v1.append_64(r_uint(0x04fb))
    assert tolong(res) == (0xa9e3 << 64) | 0x04fb
    assert res.size() == 64 + 128

    v1 = sbv(128, 0x0)
    res = v1.append_64(r_uint(0x04fb))
    assert isinstance(res, SparseBitVector)
    assert res.val == 0x04fb
    assert res.size() == 64 + 128

    v1 = GenericBitVector(128, [r_uint(0), r_uint(0xa9e3)])
    res = v1.append_64(r_uint(0x04fb))
    assert res.data == [r_uint(0x04fb), r_uint(0), r_uint(0xa9e3)]
