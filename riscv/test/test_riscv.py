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


def test_opt_mem_read_risc(riscvmain):
    from rpython.translator.interactive import Translation
    from rpython.translator.backendopt.ssa import SSI_to_SSA
    from rpython.rlib.rarithmetic import r_uint, intmask
    from pydrofoil import mem as mem_mod
    from rpython.translator.backendopt.stat import print_statistics
    from pydrofoil import bitvector
    
    outriscv = riscvmain.outriscv
    Machine = riscvmain.Machine
    machine = Machine()
    machine.init_model()
    machine.g.mem = mem_mod.FlatMemory(False)
    outriscv.func_zwithin_phys_mem(machine, r_uint(12), *bitvector.int_fromint(2))
    def f(addr):
        addr = r_uint(addr)
        access = outriscv.Union_zAccessType_zReadz3z5unit.singleton
        #return outriscv.func_zwithin_phys_mem(machine, addr, *bitvector.int_fromint(2))
        res = outriscv.func_zmem_read(machine, access, addr, 8, False, False, False)
        return res is not None
    t = Translation(f, [int], withsmallfuncsets=5)
    t.rtype()
    t.backendopt()
    g = [g for g in t.driver.translator.graphs if "within_phys_mem" in g.name][0]
    print_statistics(g, t.driver.translator)
    SSI_to_SSA(g)

