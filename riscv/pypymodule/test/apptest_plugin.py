from pytest import raises, skip

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
    for i in range(100):
        cpu.step()
        res = cpu.disassemble_last_instruction()
        print(i, res)
        assert not res.startswith("illegal")

# types

def test_union_types_exist():
    _pydrofoil.RISCV64().types.ADDIW
    _pydrofoil.RISCV64().types.ast



def test_union():
    m = _pydrofoil.RISCV64()
    ast = m.types.ADDIW(2045, 3, 5)
    assert isinstance(ast, m.types.ast)
    a, b, c = ast
    assert a == 2045
    assert b == 3
    assert c == 5

def test_union_repr():
    m = _pydrofoil.RISCV64()
    ast = m.types.ADDIW(2045, 3, 5)
    assert repr(ast) == 'ADDIW(bitvector(12, 0x7FD), bitvector(5, 0b00011), bitvector(5, 0b00101))'

def test_union_eq():
    m = _pydrofoil.RISCV64()
    ast1 = m.types.ADDIW(2045, 3, 5)
    ast2 = m.types.ADDIW(2045, 3, 5)
    ast3 = m.types.ADDIW(2045, 3, 6)
    assert ast1 == ast2
    assert ast1 != ast3

def test_union_enum():
    m = _pydrofoil.RISCV64()
    clsname = 'Some<Eread_kind%>'
    SomeReadKind = getattr(m.types, clsname)
    s = SomeReadKind('Read_plain')
    assert s[0] == 'Read_plain'

#def test_union_pattern_matching():
#    m = _pydrofoil.RISCV64()
#    ADDIW = m.types.ADDIW
#    ast = ADDIW(2045, 3, 5)
#    match ast:
#        case ADDIW(a, b, c):
#            pass
#        case _:
#            assert 0
#    assert a == 2045
#    assert b == 3
#    assert c == 5

def test_struct():
    skip("bitvector support missing")
    tlb = _pydrofoil.RISCV64().types.TLB_Entry(1, 2, False, 3, 4, 5, 6, 7, 8)
    assert tlb.age == 8
    tlb.age = 12
    assert tlb.age == 12

def test_tuplestruct():
    m = _pydrofoil.RISCV64()
    assert m.lowlevel.encdec_mul_op_backwards(3) == (True, False, False)

# functions

def test_call_function():
    m = _pydrofoil.RISCV64()
    assert m.lowlevel.privLevel_to_bits("User")       == 0b00
    assert m.lowlevel.privLevel_to_bits("Machine")    == 0b11
    assert m.lowlevel.privLevel_to_bits("Supervisor") == 0b01

def test_call_function_writeCSR():
    m = _pydrofoil.RISCV64()
    old = m.read_register("misa")
    new = old | (0b111 << 27)
    m.lowlevel.writeCSR(0x301, new)
    val = m.read_register("misa")
    assert val == old

def test_lowlevel_docstring():
    doc = _pydrofoil.RISCV64().lowlevel.__doc__
    print(doc)
    assert "legalize_satp64" in doc

def test_lowlevel_dir():
    assert "legalize_xepc" in dir(_pydrofoil.RISCV64().lowlevel)

def test_call_assembly_forwards():
    m = _pydrofoil.RISCV64()
    ast = m.types.ADDIW(2045, 3, 5)
    res = m.lowlevel.assembly_forwards(ast)
    assert res == 'addiw t0, gp, 0x7fd'

def test_call_encdec_backwards():
    m = _pydrofoil.RISCV64()
    ast = m.lowlevel.encdec_backwards(0x7793)
    res = m.lowlevel.assembly_forwards(ast)
    assert res == 'andi a5, zero, 0x0'

def test_call_rx():
    m = _pydrofoil.RISCV64()
    assert m.lowlevel.rX(0) == 0


# bitvectors

def test_bv_basics():
    b0 = _pydrofoil.bitvector(2, 0)
    assert b0 == _pydrofoil.bitvector(2, 0)
    assert repr(b0) == "bitvector(2, 0b00)"
    assert len(b0) == 2

def test_bv_getitem():
    b0 = _pydrofoil.bitvector(6, 0b110100)
    assert b0[0] == 0
    assert b0[1] == 0
    assert b0[2] == 1
    assert b0[1:3] == _pydrofoil.bitvector(2, 0b10)
