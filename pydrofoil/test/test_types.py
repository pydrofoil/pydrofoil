from pydrofoil import types

def test_unique():
    assert types.SmallFixedBitVector(6).width == 6
    assert types.SmallFixedBitVector(6) is types.SmallFixedBitVector(6)

def test_sail_repr():
    assert types.SmallFixedBitVector(6).sail_repr() == "bits(6)"
    assert types.BigFixedBitVector(100).sail_repr() == "bits(100)"
