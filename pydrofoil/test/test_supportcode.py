from pydrofoil.test import supportcode

def test_fast_signed():
    assert supportcode.fast_signed(0b0, 1) == 0
    assert supportcode.fast_signed(0b1, 1) == -1
    assert supportcode.fast_signed(0b0, 2) == 0
    assert supportcode.fast_signed(0b1, 2) == 1
    assert supportcode.fast_signed(0b10, 2) == -2
    assert supportcode.fast_signed(0b11, 2) == -1

