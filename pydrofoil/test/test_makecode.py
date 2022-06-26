import pytest
from pydrofoil.makecode import *

import os

cir = os.path.join(os.path.dirname(__file__), "c.ir")
mipsir = os.path.join(os.path.dirname(__file__), "mips.ir")
riscvir = os.path.join(os.path.dirname(__file__), "riscv_model_RV64.ir")
outpy = os.path.join(os.path.dirname(__file__), "out.py")
outmipspy = os.path.join(os.path.dirname(__file__), "outmips.py")
outriscvpy = os.path.join(os.path.dirname(__file__), "outriscv.py")

elfs = """
rv64ui-p-addi.elf rv64um-v-mul.elf rv64um-v-mulhu.elf rv64um-p-div.elf
rv64um-p-rem.elf rv64ua-v-amoadd_w.elf
"""

elfs = [os.path.join(os.path.dirname(__file__), fn) for fn in
        elfs.split()]


addrom = os.path.join(os.path.dirname(os.path.dirname(__file__)), "..", "nand2tetris", "input", "Add.hack.bin")
sumrom = os.path.join(os.path.dirname(os.path.dirname(__file__)), "..", "nand2tetris", "input", "sum.hack.bin")

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
    assert "class Union_zinstr(object):" in res
    assert "class Union_zinstr_zAINST(Union_zinstr):" in res
    assert "class Union_zinstr_zCINST(Union_zinstr):" in res

def test_full_nand():
    import py
    from pydrofoil.test import supportcode
    from rpython.translator.interactive import Translation
    with open(cir, "rb") as f:
        s = f.read()
    res = parse_and_make_code(s, "supportcode")
    with open(outpy, "w") as f:
        f.write(res)

    # bit of a hack
    from pydrofoil.test import out
    supportcode.load_rom(addrom)
    zmymain = out.func_zmymain
    zmymain(10, True)
    assert out.r.zD == 5
    assert out.r.zA == 0
    assert out.r.zPC == 11
    supportcode.load_rom(sumrom)
    zmymain(2000, True)
    assert supportcode.my_read_mem(17) == 5050

    def main():
        supportcode.load_rom(addrom)
        zmymain(10, False)
    t = Translation(main, [])
    t.rtype() # check that it's rpython

@pytest.mark.xfail
def test_full_mips():
    import py
    with open(mipsir, "rb") as f:
        s = f.read()
    res = parse_and_make_code(s, "supportcode")
    with open(outmipspy, "w") as f:
        f.write(res)
    d = {}
    res = py.code.Source(res)
    exec res.compile() in d

@pytest.fixture(scope='session')
def riscvmain():
    with open(riscvir, "rb") as f:
        s = f.read()
    res = parse_and_make_code(s, "supportcoderiscv")
    with open(outriscvpy, "w") as f:
        f.write(res)
    from pydrofoil.test import outriscv, supportcoderiscv
    supportcoderiscv.g.config_print_instr = False
    supportcoderiscv.g.config_print_reg = False
    supportcoderiscv.g.config_print_mem_access = False
    supportcoderiscv.g.config_print_platform = False
    return supportcoderiscv.get_main()

@pytest.mark.parametrize("elf", elfs)
def test_full_riscv(riscvmain, elf):
    riscvmain(['executable', elf])
