from rpysail.makecode import *

import os

cir = os.path.join(os.path.dirname(__file__), "c.ir")

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
    assert res == """\
class Registers(object): pass
r = Registers()
class Enum_zjump(object):
    0 = zJDONT
    1 = zJGT
    2 = zJEQ
    3 = zJGE
    4 = zJLT
    5 = zJNE
    6 = zJLE
    7 = zJMP"""

def test_union():
    res = parse_and_make_code("""
union zinstr {
  zAINST: %bv16,
  zCINST: (%bv1, (%bool, %bool, %bool), %bool)
}
""")
    assert res == """\
class Registers(object): pass
r = Registers()
class Union_instr(object):
    pass
class Union_instr_AINST(Union_instr):
    def __init__(self, a):
        self.a = a # NamedType('%bv16')
class Union_instr_CINST(Union_instr):
    def __init__(self, a0, a1, a2):
        self.a0 = a0 # NamedType('%bv1')
        self.a1 = a1 # TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
        self.a2 = a2 # NamedType('%bool')\
"""

def test_full():

    with open(cir, "rb") as f:
        s = f.read()
    res = parse_and_make_code(s)
    print res
