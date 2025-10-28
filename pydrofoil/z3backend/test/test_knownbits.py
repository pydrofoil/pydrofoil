# paritally adapted from https://pypy.org/posts/2024/08/toy-knownbits.html

import pytest
from hypothesis import given, strategies
from pydrofoil.z3backend.knownbits import KnownBits

###

constant_knownbits = strategies.builds(
    lambda value: (KnownBits.from_constant(value), value),
    strategies.integers()
)

def build_knownbits_from_ints(value, unknowns):
    ones = value & ~unknowns
    return KnownBits(ones, unknowns), value


def _get_random_range(data):
    a = data.draw(strategies.integers(0, 64))
    b = data.draw(strategies.integers(a, 64))
    return b, a
    
random_knownbits = strategies.builds(
    lambda value, unknowns: build_knownbits_from_ints(value, unknowns),
    strategies.integers(),
    strategies.integers()
)

random_range = strategies.builds(
    _get_random_range,
    strategies.data())

###

def test_init_well_formed():
    KnownBits(0, -1)
    KnownBits(0b0111, 0b1000)
    KnownBits(0b1, 0b0)
    KnownBits(0b101110111, 0b010000000)

def test_init_illegal():
    with pytest.raises(BaseException):
        KnownBits(0b1, -1)
    
    with pytest.raises(BaseException):
        KnownBits(0b11111, 10000)

def test_contains():
    kb = KnownBits(0b0111, 0b1000)

    assert kb.contains(0b1111)
    assert kb.contains(0b0111)
    assert not kb.contains(0b11111)
    assert not kb.contains(0b10000)
    assert not kb.contains(0b100000000000000000111)

def test_is_constant():
    assert KnownBits(0b1010101, 0).is_constant()
    assert KnownBits(16384, 0).is_constant()
    assert KnownBits(2**64-1, 0).is_constant()

    assert not KnownBits(0b1010100, 1).is_constant()
    assert not KnownBits(16384, 1).is_constant()

def test_knowns():
    # -0b111111111 = -512 + 1 => -511
    assert KnownBits(0b0111, 0b1000).knowns() == -9 # in 8 bit 11110111 = -8 -1 = -9
    assert KnownBits(0b10000, 0b1111).knowns() == -16 # in 8 bit 11110000 = -8 -4 -2 -1 -1 = -16
    assert KnownBits(0b1001, 0b01100110).knowns() == -103 # in 8 bit 10011001 = -64 -32 -4 -2 -1 = -103
    assert KnownBits(0x324985, 0x0).knowns() == -1

def test_zeros():
    assert KnownBits(0b0011, 0b1000).zeros() == -12 # zeros are 0100
    # -0b1100 & -0b0111 = -0100 = -12
    assert KnownBits(0b10000, 0b1100).zeros() == -29 # zeros are 00011, 
    # -0b01111 & -0b00011 = -0b00011 = -29
    assert KnownBits(0b1010100111, 0b0100011000).zeros() == -960 # zeros are 0001000000
    # -0b0101011000 & -0b1011100111 = -0b0001000000 = -1024 + 64 = -960
   
def test_str():
    assert str(KnownBits(0b0111, 0b1000)) == "?111"
    assert str(KnownBits(0b10000, 0b1111)) == "1????"
    assert str(KnownBits(0b1001, 0b01100110)) == "??01??1"

def test_extract():
    assert KnownBits.extract(0b0011111000, 8, 3) == 0b011111
    assert KnownBits.extract(0b01100110, 6, 1) == 0b110011
    assert KnownBits.extract(0b111001100111, 6, 3) == 0b1100

def test_is_range_known():
    assert not KnownBits(0b0, 0b1).is_range_known(0,0)
    #
    assert KnownBits(0b0111, 0b1000).is_range_known(2,0)
    assert not KnownBits(0b0111, 0b1000).is_range_known(3,3)
    #
    assert KnownBits(0b10000, 0b1111).is_range_known(165,4)
    assert not KnownBits(0b10000, 0b1111).is_range_known(3,0)
    #
    assert KnownBits(0b1001, 0b01100110).is_range_known(0,0)
    assert KnownBits(0b1001, 0b01100110).is_range_known(4,3)
    assert not KnownBits(0b1001, 0b01100110).is_range_known(2,1)

def test_get_known_range_int():
    assert KnownBits(0b0111, 0b1000).get_known_range_int(2,0) == 0b111
    with pytest.raises(AssertionError):
        assert KnownBits(0b0111, 0b1000).get_known_range_int(3,0)

    assert KnownBits(0b10000, 0b1111).get_known_range_int(165,4) == 1
    with pytest.raises(AssertionError):
        KnownBits(0b10000, 0b1111).get_known_range_int(3,0)

    assert KnownBits(0b1001, 0b01100110).get_known_range_int(0,0) == 1
    assert KnownBits(0b1001, 0b01100110).get_known_range_int(4,3) == 1
    with pytest.raises(AssertionError):
        KnownBits(0b1001, 0b01100110).get_known_range_int(2,1)

def test_abstract_invert():
    kb0 = KnownBits(0b0111, 0b1000)
    inv_kb0 = kb0.abstract_invert()

    assert str(inv_kb0) == "...1?000"
    assert inv_kb0.abstract_invert().ones == kb0.ones
    assert inv_kb0.unknowns == kb0.unknowns

    kb0 = KnownBits(0b1010100111, 0b0100011000)
    inv_kb0 = kb0.abstract_invert()

    assert str(inv_kb0) == "...10?010??000"
    assert inv_kb0.abstract_invert().ones == kb0.ones
    assert inv_kb0.unknowns == kb0.unknowns

def test_abstract_and():
    kb0 = KnownBits(0b01100111, 0b00011000)
    kb1 = KnownBits(0b01010111, 0b00101000)

    kb_and = kb0.abstract_and(kb1)

    assert str(kb_and) == "1???111"

## hypothesis tests ##

@given(constant_knownbits)
def test_constant_contains(kb_c):
    knownbits, constant = kb_c
    # dont need to call _check_well_formed as thats done on init
    assert knownbits.contains(constant)

@given(random_knownbits)
def test_random_contains(kb_c):
    knownbits, constant = kb_c
    assert knownbits.contains(constant) 

@given(constant_knownbits)
def test_constant_is_constant(kb_c):
    knownbits, _ = kb_c
    # dont need to call _check_well_formed as thats done on init
    assert knownbits.is_constant()

@given(constant_knownbits, constant_knownbits)
def test_constant_know_same(kb_c0, kb_c1):
    knownbits0, constant0 = kb_c0
    knownbits1, constant1 = kb_c1
    same = constant0 == constant1
    assert same == knownbits0.know_same(knownbits1)

@given(random_knownbits, random_knownbits)
def test_random_know_same(kb_c0, kb_c1):
    knownbits0, _ = kb_c0
    knownbits1, _ = kb_c1
    same = (knownbits0.ones == knownbits1.ones) & (knownbits0.unknowns == knownbits1.unknowns)
    assert same == knownbits0.know_same(knownbits1)

@given(random_knownbits)
def test_random_simple_invert(kb_c):
    knownbits, value = kb_c
    inv_knownbits = knownbits.abstract_invert()
    inv_value = ~value
    
    assert inv_knownbits.contains(inv_value)

@given(random_knownbits)
def test_random_str_invert(kb_c):
    knownbits, _ = kb_c
    inv_knownbits = knownbits.abstract_invert()

    if str(knownbits).startswith("...1"):
        assert not str(inv_knownbits).startswith("...")
    elif str(knownbits).startswith("...?"):
        assert str(inv_knownbits).startswith("...?")
    else:
        # all preceeding digits are 1
        assert str(inv_knownbits).startswith("...1")

@given(random_knownbits, random_knownbits)
def test_random_and_contains(kb_c0, kb_c1):
    knownbits0, constant0 = kb_c0
    knownbits1, constant1 = kb_c1

    constant_and = constant0 & constant1
    knownbits_and = knownbits0.abstract_and(knownbits1)

    assert knownbits_and.contains(constant_and)

@given(random_knownbits, random_range)
def test_random_is_range_known_str(kb_c, rand_range):
    knownbits, _ = kb_c
    start, stop = rand_range
    
    is_known = knownbits.is_range_known(start, stop)
    str_knownbits = str(knownbits)


    #if "?" in str(knownbits): import pdb; pdb.set_trace()

    # string indexing like with a bv read from right

    if str_knownbits.startswith("...?"):
        prefix = "?"
        cutoff = 4
    elif str_knownbits.startswith("...1"):
        prefix = "1"
        cutoff = 4
    else:
        prefix = "0"
        cutoff = 0

    str_knownbits = (prefix * (cutoff + start - len(str_knownbits) + 1)) + str_knownbits[cutoff:]

    unknown_in_range = "?" in str_knownbits[::-1][stop:start + 1]

    if is_known:
        assert not unknown_in_range
    else:
        assert unknown_in_range
