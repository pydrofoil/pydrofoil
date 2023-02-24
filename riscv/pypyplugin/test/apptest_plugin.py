import os
from os.path import dirname

toplevel = dirname(dirname(dirname(__file__)))
elfdir = os.path.join(toplevel, "input")

def test_right_import():
    print(pydrofoil.__dict__)
    assert hasattr(pydrofoil, "RISCV64")

def test_step():
    cpu = pydrofoil.RISCV64(os.path.join(elfdir, "rv64ui-p-addi.elf"))
    cpu.step()

