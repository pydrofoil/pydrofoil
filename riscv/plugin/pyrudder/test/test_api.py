import pyrudder
import pytest

def test_read_write_ram():
    cpu = pyrudder.RISCV64()
    ram_base = 0x80000000
    instr = 0b1001010010111 # auipc x5, 1
    cpu.write_memory(ram_base, instr)
    assert cpu.read_memory(ram_base) == instr
    cpu.write_register("pc", ram_base)
    cpu.step()
    assert cpu.read_register("pc") == ram_base + 4
    assert cpu.read_register("x5") == ram_base + (1 << 12)

def test_step_callback():
    cpu = pyrudder.RISCV64()
    has_been_called = False
    def step_callback(cpu):
        nonlocal has_been_called
        has_been_called = True
    cpu.register_callback("step", step_callback)
    ram_base = 0x80000000
    instr = 0b1001010010111 # auipc x5, 1
    cpu.write_memory(ram_base, instr)
    cpu.write_register("pc", ram_base)
    cpu.step()
    assert has_been_called

def test_unknown_register_name():
    cpu = pyrudder.RISCV64()
    with pytest.raises(ValueError):
        cpu.read_register("not_a_register")

def test_alt_register_names_read():
    cpu = pyrudder.RISCV64()

    ALT_NAMES = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]

    # write via internal names (x1, x2, etc.)
    for i in range(1, 32):
        cpu.write_register("x" + str(i), i)

    # read via alternative names (ra, sp, etc.)
    for i in range(32):
        assert cpu.read_register(ALT_NAMES[i]) == cpu.read_register("x" + str(i))

def test_alt_register_names_write():
    cpu = pyrudder.RISCV64()

    ALT_NAMES = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]

    # write via alternative names (ra, sp, etc.)
    for i in range(32):
        cpu.write_register(ALT_NAMES[i], i)

    # read via internal names (x1, x2, etc.)
    for i in range(32):
        assert cpu.read_register("x" + str(i)) == cpu.read_register(ALT_NAMES[i])

def test_memory_read_callback():
    cpu = pyrudder.RISCV64()
    ram_base = 0x80000000
    has_been_called = False
    def read_callback(cpu, addr, size, value):
        nonlocal has_been_called
        has_been_called = True
        assert addr == ram_base
        assert size == 1
        assert value == 151
    cpu.register_callback("memory_read", read_callback)
    instr1 = 0b001010010111 # auipc x5, 0
    instr2 = 0b00101000001010000011 # lb x5, 0(x5)
    cpu.write_memory(ram_base, instr1)
    cpu.write_memory(ram_base + 4, instr2)
    cpu.write_register("pc", ram_base)
    cpu.step()
    cpu.step()
    assert cpu.read_register("x5") & 0xff == 151
    assert has_been_called

def test_memory_write_callback():
    cpu = pyrudder.RISCV64()
    ram_base = 0x80000000
    has_been_called = False
    def write_callback(cpu, addr, size, value):
        nonlocal has_been_called
        has_been_called = True
        assert addr == ram_base + 4
        assert size == 1
        assert value == 7
    cpu.register_callback("memory_write", write_callback)
    instr1 = 0b11100000000000010010011 # addi x1, x0, 7
    instr2 = 0b001010010111 # auipc x5, 0
    instr3 = 0b0000100101000000000100011 # sb x1, 0(x5)
    cpu.write_memory(ram_base, instr1)
    cpu.write_memory(ram_base + 4, instr2)
    cpu.write_memory(ram_base + 8, instr3)
    cpu.write_register("pc", ram_base)
    cpu.step()
    cpu.step()
    cpu.step()
    assert cpu.read_register("x1") == 7
    assert has_been_called
