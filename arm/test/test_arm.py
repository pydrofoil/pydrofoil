import pytest
import os
from os.path import dirname
from pydrofoil import bitvector


toplevel = dirname(dirname(dirname(__file__)))
armir = os.path.join(toplevel, "arm/armv9.ir")

# parsing

def xtest_parse_full_arm():
    from pydrofoil.parse import parser, lexer, LexingError, ParsingError
    with open(armir, "rb") as f:
        s = f.read()
    try:
        res = parser.parse(lexer.lex(s))
    except (LexingError, ParsingError) as e:
        print e.getsourcepos()
        print s[e.getsourcepos().idx:e.getsourcepos().idx+20]
        raise

@pytest.fixture(scope='session')
def armmain():
    from arm.targetarm import make_code
    return make_code()

def test_stuff(armmain):
    from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
    from arm import supportcodearm
    machine = armmain.mod.Machine()
    armmain("exe -b 0x80000000,arm/bootloader.bin -b 0x81000000,arm/sail.dtb -b 0x82080000,arm/Image -C cpu.cpu0.RVBAR=0x80000000 -C cpu.has_tlb=0x0  -l 100 -v 0b11".split())
