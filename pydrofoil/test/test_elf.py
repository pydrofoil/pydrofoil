import os

from pydrofoil import elf

elffile = os.path.join(os.path.dirname(__file__), "rv64ui-p-addi.elf")
elffile2 = os.path.join(os.path.dirname(__file__), "rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl")

def test_elf_riscv64():
    with open(elffile, "rb") as f:
        img = elf.elf_reader(f)
    section1, section2 = img.sections
    assert section1.name == ".text.init"
    assert section2.name == ".tohost"

    assert section1.addr == 0x80000000
    assert section2.addr == 0x80001000

