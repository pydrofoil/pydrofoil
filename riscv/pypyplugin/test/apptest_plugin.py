import os
from os.path import dirname

toplevel = dirname(dirname(dirname(__file__)))
elfdir = os.path.join(toplevel, "input")

def test_right_import():
    print(_pydrofoil.__dict__)
    assert hasattr(_pydrofoil, "RISCV64")

def test_step():
    cpu = _pydrofoil.RISCV64(os.path.join(elfdir, "rv64ui-p-addi.elf"))
    cpu.step()

def test_read_register():
    cpu = _pydrofoil.RISCV64(os.path.join(elfdir, "rv64ui-p-addi.elf"))
    assert cpu.read_register("pc") == 0x1000 # rom base at the start

