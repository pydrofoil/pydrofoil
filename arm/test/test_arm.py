import pytest
import os
from os.path import dirname


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

def test_instantiate(armmain):
    armmain.mod.Machine()
