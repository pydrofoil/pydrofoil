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

def test_read_write_register():
    cpu = _pydrofoil.RISCV64(os.path.join(elfdir, "rv64ui-p-addi.elf"))
    assert cpu.read_register("pc") == 0x1000 # rom base at the start
    cpu.step() # execute auipc x5,0
    assert cpu.read_register("pc") == 0x1004
    assert cpu.read_register("x5") == 0x1000

    cpu.write_register("x5", 111)
    assert cpu.read_register("x5") == 111
    cpu.write_register("pc", 0x1000)
    cpu.step() # should re-execute the auipc
    assert cpu.read_register("pc") == 0x1004
    assert cpu.read_register("x5") == 0x1000
