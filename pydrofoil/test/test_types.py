from pydrofoil import types

def test_unique():
    assert types.FixedBitVector(6).width == 6
    assert types.FixedBitVector(6) is types.FixedBitVector(6)
