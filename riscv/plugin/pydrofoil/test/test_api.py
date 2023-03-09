import pydrofoil

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