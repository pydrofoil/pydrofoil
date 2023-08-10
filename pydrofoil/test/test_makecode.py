import pytest
from pydrofoil.makecode import *

from rpython.rlib import rarithmetic

import os

thisdir = os.path.dirname(__file__)
cir = os.path.join(thisdir, "nand2tetris/generated/nand2tetris.jib")
excir = os.path.join(thisdir, "exc/exc.ir")
outpy = os.path.join(thisdir, "nand2tetris/generated/nand_rpython.py")

addrom = os.path.join(os.path.dirname(os.path.dirname(__file__)), "test", "nand2tetris", "input", "Add.hack.bin")
sumrom = os.path.join(os.path.dirname(os.path.dirname(__file__)), "test", "nand2tetris", "input", "sum.hack.bin")

def test_enum():
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
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
""", support_code)
    assert "class Enum_zjump" in res
    assert """\
    zJDONT = 0
    zJGT = 1
    zJEQ = 2
    zJGE = 3
    zJLT = 4
    zJNE = 5
    zJLE = 6
    zJMP = 7
""" in res

def test_full_nand():
    import py
    from pydrofoil.test.nand2tetris import supportcodenand
    from rpython.translator.interactive import Translation
    with open(cir, "rb") as f:
        s = f.read()
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    res = parse_and_make_code(s, support_code)
    with open(outpy, "w") as f:
        f.write(res)

    # bit of a hack
    from pydrofoil.test.nand2tetris.generated import nand_rpython as out
    supportcodenand.load_rom(addrom)
    zmymain = out.func_zmymain
    machine = out.Machine()
    zmymain(machine, rarithmetic.r_uint(10), True)
    assert machine._reg_zD == 5
    assert machine._reg_zA == 0
    assert machine._reg_zPC == 11
    supportcodenand.load_rom(sumrom)
    zmymain(out.Machine(), rarithmetic.r_uint(2000), True)
    assert supportcodenand.my_read_mem(machine, 17) == 5050

    def main():
        supportcodenand.load_rom(addrom)
        zmymain(out.Machine(), 10, False)
    t = Translation(main, [])
    t.rtype() # check that it's rpython

