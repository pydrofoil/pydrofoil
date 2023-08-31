import pytest
from pydrofoil import supportcode
from pydrofoil import mangle
from hypothesis import given, strategies, assume
import string

def test_encode_mangle():
    assert mangle.mangle("option(TLB_Entry)") == "zoptionz8TLB_Entryz9"
    assert mangle.mangle(" ") == "zz0"
    assert mangle.mangle("(") == "zz8"
    assert mangle.mangle(")") == "zz9"
    assert mangle.mangle("*") == "zzA"
    assert mangle.mangle("+") == "zzB"
    assert mangle.mangle(".") == "zzE"
    assert mangle.mangle("/") == "zzF"
    assert mangle.mangle(":") == "zzG"
    assert mangle.mangle("?") == "zzL"
    assert mangle.mangle("@") == "zzM"
    assert mangle.mangle("[") == "zzN"
    assert mangle.mangle("\\") == "zzO"
    assert mangle.mangle("`") == "zzS"
    assert mangle.mangle("{") == "zzT"
    assert mangle.mangle("~") == "zzW"
    assert mangle.mangle("z") == "zzz"
    assert mangle.mangle("_") == "z_"
    assert mangle.mangle("a") == "za"
    assert mangle.mangle("A") == "zA"
    assert mangle.mangle("Z") == "zZ"
    assert mangle.mangle("1") == "z1"
    assert mangle.mangle("9") == "z9"
    assert mangle.mangle("%i64->%i") == "zz5i64zDzKz5i"

def test_decode_mangle():
    assert mangle.demangle("zz0") == " "
    assert mangle.demangle("zz1") == "!"
    assert mangle.demangle("zz8") == "("
    assert mangle.demangle("zz9") == ")"
    assert mangle.demangle("zzA") == "*"
    assert mangle.demangle("zzB") == "+"
    assert mangle.demangle("zzE") == "."
    assert mangle.demangle("zzF") == "/"
    assert mangle.demangle("zzG") == ":"
    assert mangle.demangle("zzL") == "?"
    assert mangle.demangle("zzM") == "@"
    assert mangle.demangle("zzN") == "["
    assert mangle.demangle("zzO") == "\\"
    assert mangle.demangle("zzR") == "_"
    assert mangle.demangle("zzS") == "`"
    assert mangle.demangle("zzT") == "{"
    assert mangle.demangle("zzW") == "~"
    assert mangle.demangle("zzz") == "z"
    assert mangle.demangle("z_")  == "_"
    assert mangle.demangle("za")  == "a"
    assert mangle.demangle("zA")  == "A"
    assert mangle.demangle("zZ")  == "Z"
    assert mangle.demangle("z1")  == "1"
    assert mangle.demangle("z9")  == "9"
    assert mangle.demangle("zy")  == "y"
    assert mangle.demangle("zz5i64zDzKz5i") == "%i64->%i"
    assert mangle.demangle("zoptionzIRTLB_EntryzK") == "option<RTLB_Entry>"

# hypothesis tests
@given(strategies.text(alphabet=string.ascii_letters, min_size=1))
def test_something(x):
    asciistring = x.encode('ascii')
    for char in asciistring:
        assert 0 <= ord(char) < 128
    assert mangle.demangle(mangle.mangle(asciistring)) == asciistring