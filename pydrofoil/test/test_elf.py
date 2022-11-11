import os
from os.path import dirname

from pydrofoil import elf

toplevel = dirname(dirname(dirname(__file__)))

elffile = os.path.join(toplevel, "riscv/input/rv64ui-p-addi.elf")
elffile32 = os.path.join(toplevel, "riscv/input/rv32ui-p-addi.elf")

def test_elf_riscv64():
    with open(elffile, "rb") as f:
        img = elf.elf_reader(f)
    section1, section2 = img.sections
    assert section1.name == ".text.init"
    assert section2.name == ".tohost"

    assert section1.addr == 0x80000000
    assert section2.addr == 0x80001000

def test_elf_riscv32():
    with open(elffile32, "rb") as f:
        img = elf.elf_reader(f)
    section1, section2 = img.sections
    assert section1.name == ".text.init"
    assert section2.name == ".tohost"

    assert section1.addr == 0x80000000
    assert section2.addr == 0x80001000

