import os

from pydrofoil import elf

elffile = os.path.join(os.path.dirname(__file__), "rv64ui-p-addi.elf")

def test_elf_riscv64():
    with open(elffile, "rb") as f:
        img = elf.elf_reader(f, is_64bit=True)
    section1, section2 = img.sections
    assert section1.name == ".text.init"
    assert section2.name == ".tohost"

    assert section1.addr == 0x80000000
    assert section2.addr == 0x80001000
