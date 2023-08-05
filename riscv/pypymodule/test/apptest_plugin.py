from pytest import raises

import os
from os.path import dirname

toplevel = dirname(dirname(dirname(__file__)))
elfdir = os.path.join(toplevel, "input")
addielf = os.path.join(elfdir, "rv64ui-p-addi.elf")
mulelf = os.path.join(elfdir, "rv64um-v-mul.elf")

def test_right_import():
    print(_pydrofoil.__dict__)
    assert hasattr(_pydrofoil, "RISCV64")

def test_step():
    cpu = _pydrofoil.RISCV64(addielf)
    cpu.step()

def test_run():
    cpu = _pydrofoil.RISCV64(addielf)
    cpu.run(100)
    assert cpu.read_register("pc") == 0x800001e8

def test_read_write_register():
    cpu = _pydrofoil.RISCV64(addielf)
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

def test_read_write_ram():
    cpu = _pydrofoil.RISCV64()
    ram_base = 0x80000000
    instr = 0b1001010010111 # auipc x5, 1
    cpu.write_memory(ram_base, instr)
    assert cpu.read_memory(ram_base) == instr
    cpu.write_register("pc", ram_base)
    cpu.step()
    assert cpu.read_register("pc") == ram_base + 4
    assert cpu.read_register("x5") == ram_base + (1 << 12)

def test_read_write_ram_out_of_bounds():
    cpu = _pydrofoil.RISCV64()
    for outofbounds in [64 * 1024 * 1024, 2**56]:
        with raises(IndexError):
            cpu.read_memory(outofbounds)
        with raises(IndexError):
            cpu.write_memory(outofbounds, 1)

def test_step_ticks():
    cpu = _pydrofoil.RISCV64(addielf)
    for i in range(100):
        assert cpu.read_register("mtime") == 0
        cpu.step()
    cpu.step()
    assert cpu.read_register("mtime") == 1


def test_step_monitor_mem_read():
    cpu = _pydrofoil.RISCV64(addielf)
    mem_accesses = cpu.step_monitor_mem()
    assert mem_accesses == [
        ("read_executable", 0x0000000000001000, 2, 0x0297),
        ("read_executable", 0x0000000000001002, 2, 0x0),
    ]
    cpu.step()
    cpu.step()
    mem_accesses = cpu.step_monitor_mem()
    assert mem_accesses == [
        ("read_executable", 0x000000000000100C, 2, 0xB283),
        ("read_executable", 0x000000000000100E, 2, 0x0182),
        ("read", 0x0000000000001018, 8, 0x0000000080000000),
    ]

def test_step_monitor_mem_write():
    cpu = _pydrofoil.RISCV64(mulelf)
    for i in range(34):
        cpu.step()
    mem_accesses = cpu.step_monitor_mem()
    assert mem_accesses == [
        ("read_executable", 0x0000000080002914, 2, 0xB823),
        ("read_executable", 0x0000000080002916, 2, 0x6ED8),
        ("write", 0x0000000080004000, 8, 0x0000000020001401),
    ]

def test_enum_register():
    cpu = _pydrofoil.RISCV64(mulelf)
    for i in range(34):
        cpu.step()
    assert cpu.read_register("cur_privilege") == "Machine"
