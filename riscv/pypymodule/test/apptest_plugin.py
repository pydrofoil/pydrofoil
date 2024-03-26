from pytest import raises

import os
from os.path import dirname

toplevel = dirname(dirname(dirname(__file__)))
elfdir = os.path.join(toplevel, "input")
addielf = os.path.join(elfdir, "rv64ui-p-addi.elf")
mulelf = os.path.join(elfdir, "rv64um-v-mul.elf")
addielf32 = os.path.join(elfdir, "rv32ui-p-addi.elf")
linuxbbl = os.path.join(elfdir, "rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl")

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

def test_run32():
    cpu = _pydrofoil.RISCV32(addielf32)
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
        ("read", 0x0000000000001000, 2, 0x0297),
        ("read", 0x0000000000001002, 2, 0x0),
    ]
    cpu.step()
    cpu.step()
    mem_accesses = cpu.step_monitor_mem()
    assert mem_accesses == [
        ("read", 0x000000000000100C, 2, 0xB283),
        ("read", 0x000000000000100E, 2, 0x0182),
        ("read", 0x0000000000001018, 8, 0x0000000080000000),
    ]

def test_step_monitor_mem_write():
    cpu = _pydrofoil.RISCV64(mulelf)
    for i in range(34):
        cpu.step()
    mem_accesses = cpu.step_monitor_mem()
    assert mem_accesses == [
        ("read", 0x0000000080002914, 2, 0xB823),
        ("read", 0x0000000080002916, 2, 0x6ED8),
        ("write", 0x0000000080004000, 8, 0x0000000020001401),
    ]

def test_enum_register():
    cpu = _pydrofoil.RISCV64(mulelf)
    for i in range(3):
        cpu.step()
    assert cpu.read_register("cur_privilege") == "Machine"
    with raises(ValueError) as excinfo:
        cpu.write_register("cur_privilege", "ABC")
    assert str(excinfo.value) == "unknown enum value 'ABC' for enum Privilege"

def test_various_registers():
    cpu = _pydrofoil.RISCV64(mulelf)
    cpu.step()
    assert cpu.read_register("htif_done") == False
    cpu.write_register("htif_done", 12)
    assert cpu.read_register("htif_done") == True
    assert cpu.read_register("misa") == 0x800000000034112d

def test_register_info():
    cpu = _pydrofoil.RISCV64()
    rs = dict(cpu.register_info())
    assert rs["pc"] == 'bits(64)'
    assert rs["htif_done"] == 'bool'
    assert rs["mstatush"] == 'bitfield Mstatush'

def test_memory_info():
    cpu = _pydrofoil.RISCV64()
    info = cpu.memory_info()
    assert info == [(0, 0x800000), (0x80000000, 0x4000000 + 0x80000000)]

def test_set_verbosity():
    # smoke test
    cpu = _pydrofoil.RISCV64(addielf)
    cpu.set_verbosity(False)
    print("starting")
    cpu.run(10)
    print("ending")
    cpu.set_verbosity(True)
    cpu.run(10)

def test_dtb():
    cpu = _pydrofoil.RISCV64(dtb=True)
    assert cpu.read_memory(0x1020, 4) == 0xEDFE0DD0

def test_linux():
    cpu = _pydrofoil.RISCV64(linuxbbl, dtb=True)
    cpu.run(100)
    assert cpu.read_register("x15") == 0x0000000030030000

def test_dis_last_instruction():
    cpu = _pydrofoil.RISCV64(linuxbbl, dtb=True)
    cpu.step()
    res = cpu.disassemble_last_instruction()
    assert res == 'auipc t0, 0x0'
    cpu.step()
    res = cpu.disassemble_last_instruction()
    assert res == "addi a1, t0, 0x20"
