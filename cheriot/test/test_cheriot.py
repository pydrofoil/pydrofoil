import pytest
import os
from os.path import dirname


toplevel = dirname(dirname(dirname(__file__)))
cheriotir = os.path.join(toplevel, "cheriot/cheriot_model_rv32.ir")
elfdir = os.path.join(toplevel, "cheriot/input")
elfs = """
hello_world
"""

elfs = [os.path.join(elfdir, fn) for fn in elfs.split()]


# parsing

def test_parse_full_cheriot():
    from pydrofoil.parse import parser, lexer, LexingError, ParsingError
    with open(cheriotir, "rb") as f:
        s = f.read()
    try:
        res = parser.parse(lexer.lex(s))
    except (LexingError, ParsingError) as e:
        print e.getsourcepos()
        print s[e.getsourcepos().idx:e.getsourcepos().idx+20]
        raise


# running

@pytest.fixture(scope='session')
def cheriotmain():
    from cheriot.targetcheriot import make_code
    return make_code()

@pytest.mark.parametrize("elf", elfs)
def test_full_cheriot(cheriotmain, elf):
    cheriotmain(['executable', elf, "--verbose"])

