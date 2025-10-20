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
    
random_knownbits = strategies.builds(
    lambda value, unknowns: build_knownbits_from_ints(value, unknowns),
    strategies.integers(),
    strategies.integers()
)

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