from pydrofoil import types

def test_unique():
    assert types.SmallFixedBitVector(6).width == 6
    assert types.SmallFixedBitVector(6) is types.SmallFixedBitVector(6)
