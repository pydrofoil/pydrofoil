import pydrofoil
import pytest

def test_read_write_ram():
    cpu = pydrofoil.RISCV64()
    ram_base = 0x80000000
    instr = 0b1001010010111 # auipc x5, 1
    cpu.write_memory(ram_base, instr)
    assert cpu.read_memory(ram_base) == instr
    cpu.write_register("pc", ram_base)
    cpu.step()
    assert cpu.read_register("pc") == ram_base + 4
    assert cpu.read_register("x5") == ram_base + (1 << 12)

def test_step_callback():
    cpu = pydrofoil.RISCV64()
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
    cpu = pydrofoil.RISCV64()
    with pytest.raises(ValueError):
        cpu.read_register("not_a_register")

def test_alt_register_names_read():
    cpu = pydrofoil.RISCV64()

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
    cpu = pydrofoil.RISCV64()

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