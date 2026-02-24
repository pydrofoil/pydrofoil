import pytest
import os
from os.path import dirname


toplevel = dirname(dirname(dirname(__file__)))
elfdir = os.path.join(toplevel, "cheririscv/input")

oob_write_elf = os.path.join(elfdir, 'oob_write.elf')


# running

@pytest.fixture(scope='session')
def cheririscvmain():
    from cheririscv.targetcheririscv import make_code
    return make_code()

def test_cheri_oob_write(cheririscvmain):
    cheririscvmain(['executable', oob_write_elf, "--verbose", "--inst-limit", "400"])


#

# testing disassembly

def test_dis_instructions(cheririscvmain):
    from cheririscv import supportcodecheririscv
    from cheririscv.generated import outriscv
    elf = oob_write_elf
    m = cheririscvmain._machinecls()
    supportcodecheririscv.init_mem(m)
    entry = supportcodecheririscv.load_sail(m, elf)
    m._reg_zPC = supportcodecheririscv.init_sail(m, entry)
    m.g.config_print_instr = False
    m.g.config_print_reg = False
    m.g.config_print_mem_access = False
    m.g.config_print_platform = False

    expected = [
        "auipc t0, 0x0",
        "addi a1, t0, 0x20",
        "csrrs a0, mhartid, zero",
        "ld t0, 0x18(t0)",
        "jalr zero, 0x0(t0)",
        "addi t6, zero, 0x3",
        "slli t6, t6, 0xb",
        "csrrw zero, mstatus, t6",
        "cspecialrw ct0, ddc, cnull",
        "addi t1, zero, 0x2",
    ]
    for instr in expected:
        m.run_sail(1, False)
        assert outriscv.func_zassembly_forwards(m, outriscv.func_zext_decode(m, m._reg_zinstbits)) == instr

