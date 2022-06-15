from pydrofoil import types

def test_unique():
    assert types.BitVector(6).width == 6
    assert types.BitVector(6) is types.BitVector(6)
