from pydrofoil.makecode import *

import os

cir = os.path.join(os.path.dirname(__file__), "c.ir")
outpy = os.path.join(os.path.dirname(__file__), "out.py")

def test_enum():
    res = parse_and_make_code("""
enum zjump {
  zJDONT,
  zJGT,
  zJEQ,
  zJGE,
  zJLT,
  zJNE,
  zJLE,
  zJMP
}
""")
    assert """\
class Registers(object): pass
r = Registers()
class Enum_zjump(object):
    zJDONT = 0
    zJGT = 1
    zJEQ = 2
    zJGE = 3
    zJLT = 4
    zJNE = 5
    zJLE = 6
    zJMP = 7
""" in res

def test_union():
    res = parse_and_make_code("""
union zinstr {
  zAINST: %bv16,
  zCINST: (%bv1, (%bool, %bool, %bool), %bool)
}
""")
    assert """\
class Union_zinstr(object):
    pass
class Union_zinstr_zAINST(Union_zinstr):
    def __init__(self, a):
        self.a = a # NamedType('%bv16')
class Union_zinstr_zCINST(Union_zinstr):
    def __init__(self, a0, a1, a2):
        self.a0 = a0 # NamedType('%bv1')
        self.a1 = a1 # TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
        self.a2 = a2 # NamedType('%bool')
""" in res

def test_full():
    import py
    with open(cir, "rb") as f:
        s = f.read()
    res = parse_and_make_code(s)
    with open(outpy, "w") as f:
        f.write(res)
    d = {}
    res = py.code.Source(res)
    exec res.compile() in d
    d['func_zmain'](())
