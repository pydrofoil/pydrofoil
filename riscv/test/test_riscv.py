import pytest
import os
from os.path import dirname


toplevel = dirname(dirname(dirname(__file__)))
riscvir = os.path.join(toplevel, "riscv/riscv_model_RV64.ir")
elfdir = os.path.join(toplevel, "riscv/input")
elfs = """
rv64ui-p-addi.elf rv64um-v-mul.elf rv64um-v-mulhu.elf rv64um-p-div.elf
rv64um-p-rem.elf rv64ua-v-amoadd_w.elf rv64ua-v-amomax_d.elf
"""

elfs = [os.path.join(elfdir, fn) for fn in elfs.split()]

linuxelf = os.path.join(elfdir, "rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl")
elffile32 = os.path.join(elfdir, "rv32ui-p-addi.elf")
dhryelffile = os.path.join(elfdir, "dhrystone.riscv")


# parsing

def test_parse_full_riscv():
    from pydrofoil.parse import parser, lexer, LexingError, ParsingError
    with open(riscvir, "rb") as f:
        s = f.read()
    try:
        res = parser.parse(lexer.lex(s))
    except (LexingError, ParsingError) as e:
        print e.getsourcepos()
        print s[e.getsourcepos().idx:e.getsourcepos().idx+20]
        raise


# running

@pytest.fixture(scope='session')
def riscvmain():
    from riscv.targetriscv import make_code
    return make_code()

@pytest.mark.parametrize("elf", elfs)
def test_full_riscv(riscvmain, elf):
    riscvmain(['executable', elf])

def test_load_objdump(riscvmain):
    from riscv import supportcoderiscv
    d = supportcoderiscv.parse_dump_file(os.path.join(toplevel, 'riscv/input/dhrystone.riscv.dump'))
    assert d[0x8000218a] == '.text: Proc_1 6100                	ld	s0,0(a0)'


# elf bugs

def test_elf_reader():
    from pydrofoil import elf, mem
    m = mem.BlockMemory()
    with open(linuxelf, "rb") as f:
        entrypoint = elf.elf_read_process_image(m, f)
    assert entrypoint == 0x80000000
    # used to be wrong in the segment reader
    assert m.read(0x0000000080000D42, 2) == 0x4e4c

def test_elf_reader32():
    from pydrofoil import elf, mem
    m = mem.BlockMemory()
    with open(elffile32, "rb") as f:
        entrypoint = elf.elf_read_process_image(m, f)
    assert entrypoint == 0x80000000
    assert m.read(0x0000000080000000, 2) == 0x6f


#

def test_translation_dtb():
    from riscv import supportcoderiscv
    from rpython.translator.interactive import Translation

    def main():
        g = supportcoderiscv.Globals()
        g._init_ranges()

    t = Translation(main, [])
    t.rtype() # check that it's rpython

def test_compare_dtbs():
    from riscv import supportcoderiscv
    g = supportcoderiscv.Globals()
    g._create_dtb()
    with open("riscv/input/rv64-64mb.dtb", "rb") as f:
        target = f.read()
    assert target == g.dtb

# testing disassembly

def test_dis_instructions(riscvmain):
    from riscv import supportcoderiscv
    from riscv.generated import outriscv
    elf = elfs[0]
    m = riscvmain._machinecls()
    entry = supportcoderiscv.load_sail(m, elf)
    supportcoderiscv.init_sail(m, entry)
    m.g.config_print_instr = False
    m.g.config_print_reg = False
    m.g.config_print_mem_access = False
    m.g.config_print_platform = False

    expected = [
        "auipc t0, 0",
        "addi a1, t0, 32",
        "csrrs a0, mhartid, zero",
        "ld t0, 24(t0)",
        "jalr zero, t0, 0",
        "jal zero, 76",
        "csrrs a0, mhartid, zero",
        "bne a0, zero, 0"
    ]
    for instr in expected:
        m.run_sail(1, False)
        assert outriscv.func_zassembly_forwards(m, outriscv.func_zext_decode(m, m._reg_zinstbits)) == instr
    res = []
    for i in range(258 - len(expected)):
        m.run_sail(1, False)
        res.append(outriscv.func_zassembly_forwards(m, outriscv.func_zext_decode(m, m._reg_zinstbits)))
    assert "illegal" not in "\n".join(res)
