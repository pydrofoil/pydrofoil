from pytest import raises, skip

def setup_module(mod):
    import _pydrofoil
    mod._pydrofoil = _pydrofoil

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
    assert cpu.read_register("pc") == 0x800001f0

def test_reset():
    cpu = _pydrofoil.RISCV64(addielf)
    cpu.run(100)
    assert cpu.read_register("pc") == 0x800001f0
    cpu.reset()
    assert cpu.read_register("pc") == 0x1000
    assert cpu.read_register("x1") == 0x0

def test_run32():
    cpu = _pydrofoil.RISCV32(addielf32)
    cpu.run(100)
    assert cpu.read_register("pc") == 0x800001f0

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
    assert cpu.read_register("misa") == 0x800000000034112F

def test_register_info():
    _pydrofoil.sailtypes.Tuple # side effect :-(
    cpu = _pydrofoil.RISCV64()
    rs = dict(cpu.register_info())
    assert rs["pc"].width == 64
    assert isinstance(rs["htif_done"], _pydrofoil.sailtypes.Bool)
    # XXX assert rs["mstatush"] == 'bitfield Mstatush'

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

def test_union_types_have_sail_types():
    cls = _pydrofoil.sailtypes.Union
    assert isinstance(_pydrofoil.RISCV64().types.ast.sail_type, cls)
    assert isinstance(_pydrofoil.RISCV64().types.ast.sail_type, cls)


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

def test_union_hash():
    m = _pydrofoil.RISCV64()
    ast1 = m.types.ADDIW(2045, 3, 5)
    ast1a = m.types.ADDIW(2045, 3, 5)
    ast2 = m.types.ADDIW(2045, 3, 12)
    assert ast1 == ast1a
    assert ast1 != ast2
    assert hash(ast1) == hash(ast1a)
    assert hash(ast1) != hash(ast2)

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
    bv = _pydrofoil.bitvector(16, 0xf)
    bv64 = _pydrofoil.bitvector(64, 0xf)
    tlb = _pydrofoil.RISCV64().types.TLB_Entry(bv64, bv, False, bv64, bv64, bv64, bv64, bv64, bv64)
    assert tlb.age == bv64

def test_struct_sail_type():
    cls = _pydrofoil.sailtypes.Struct
    typ = _pydrofoil.RISCV64().types.TLB_Entry.sail_type
    assert isinstance(typ, cls)
    assert typ.name == "TLB_Entry"
    assert len(typ.fields) == 9
    fields = dict(typ.fields)
    assert isinstance(fields['age'], _pydrofoil.sailtypes.SmallFixedBitVector)
    assert fields['age'].width == 64

def test_struct_type():
    m = _pydrofoil.RISCV64()
    struct = m.lowlevel.encdec_mul_op_backwards(3)
    assert struct.high == True
    assert struct.signed_rs1 == False
    assert struct.signed_rs2 == False
    assert repr(struct) == 'mul_op(True, False, False)'

def test_convert_fvec():
    m = _pydrofoil.RISCV64()
    res = m.read_register('pmpcfg_n')
    assert res == [_pydrofoil.bitvector(8, 0)] * 64
    m.write_register('pmpcfg_n', [_pydrofoil.bitvector(8, 0)] * 64)

def test_big_fixed_bitvectors():
    m = _pydrofoil.RISCV64()
    big = m.read_register('vr1')
    assert len(big) == 65536
    assert big == 0

def test_compact_union():
    m = _pydrofoil.RISCV64()
    x = m.lowlevel.read_kind_of_flags_specialized_o_o_False(True, True, False)
    assert x[0] == 'Read_RISCV_strong_acquire'
    assert x == x
    assert repr(x) == "Some<Eread_kind%>('Read_RISCV_strong_acquire')"

# functions

def test_call_function():
    m = _pydrofoil.RISCV64()
    assert m.lowlevel.privLevel_to_bits("User")       == 0b00
    assert m.lowlevel.privLevel_to_bits("Machine")    == 0b11
    assert m.lowlevel.privLevel_to_bits("Supervisor") == 0b01

def test_call_function_argument_error():
    m = _pydrofoil.RISCV64()
    with raises(TypeError):
        m.lowlevel.privLevel_to_bits(1234)

def test_call_function_write_CSR():
    m = _pydrofoil.RISCV64()
    old = m.read_register("misa")
    new = old | (0b111 << 27)
    m.lowlevel.write_CSR(0x301, new)
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

def test_call_encdec_forwards():
    m = _pydrofoil.RISCV64()
    ast = m.lowlevel.encdec_backwards(0x7793)
    enc = m.lowlevel.encdec_forwards(ast)
    assert enc == 0x7793

def test_packed_struct_fields():
    m = _pydrofoil.RISCV64()
    res = m.lowlevel.read_ram_specialized_o_o_o_False("Read_plain",2,3,4)
    assert res == (_pydrofoil.bitvector(24, 0x000000), ())

    at = getattr(m.types, 'Execute<u>')()
    res = m.lowlevel.phys_mem_read_specialized_o_o_o_o_o_True_False(at,2,4,False,False,True,False)
    assert repr(res) == 'MemValue<(b,u)>(bitvector(32, 0x00000000), ())'

def test_call_rx():
    m = _pydrofoil.RISCV64()
    assert m.lowlevel.rX(0) == 0

def test_call_rx_crash():
    m = _pydrofoil.RISCV64()
    with raises(_pydrofoil.SailAssertionError):
        m.lowlevel.rX(100)

def test_sailfunction_doc():
    m = _pydrofoil.RISCV64()
    doc = m.lowlevel.encdec_backwards.__doc__
    assert "encdec_backwards" in doc

def test_sailfunction_type():
    m = _pydrofoil.RISCV64()
    typ = m.lowlevel.encdec_backwards.sail_type
    assert isinstance(typ, _pydrofoil.sailtypes.Function)
    assert len(typ.arguments) == 1
    assert isinstance(typ.arguments[0], _pydrofoil.sailtypes.SmallFixedBitVector)
    assert typ.arguments[0].width == 32
    assert isinstance(typ.result, _pydrofoil.sailtypes.Union)
    assert typ.result.name == "ast"
    assert isinstance(typ.result.constructors, list)
    name, typ = typ.result.constructors[0]
    assert name == 'ADDIW'
    assert isinstance(typ, _pydrofoil.sailtypes.Tuple)
    assert typ[0].width == 12

def test_sailfunction_type_enum():
    m = _pydrofoil.RISCV64()
    typ = m.lowlevel.privLevel_to_bits.sail_type
    argtyp, = typ.arguments
    assert isinstance(argtyp, _pydrofoil.sailtypes.Enum)
    assert argtyp.elements == ['User', 'Supervisor', 'Machine']
    assert argtyp.name == "Privilege"

def test_lowlevel_attribute_error():
    m = _pydrofoil.RISCV64()
    with raises(AttributeError) as info:
        assert m.lowlevel.privLevel_to_bats
    assert str(info.value) == "'lowlevel' object has no attribute 'privLevel_to_bats'"

def test_lowlevel_unit_argument():
    m = _pydrofoil.RISCV64()
    assert m.lowlevel.get_vlen_pow() == 9

def test_bound_lowlevel_repr():
    m = _pydrofoil.RISCV64()
    assert repr(m.lowlevel.get_vlen_pow) == f'<bound sail function .lowlevel.get_vlen_pow of {m}>'

# ________________________________________________
# bitvectors

def test_bv_basics():
    b0 = _pydrofoil.bitvector(2, 0)
    assert b0 == _pydrofoil.bitvector(2, 0)
    assert repr(b0) == "bitvector(2, 0b00)"
    assert len(b0) == 2

def test_bv_negative_width():
    with raises(ValueError):
        _pydrofoil.bitvector(-1, 0)

def test_bv_getitem():
    b0 = _pydrofoil.bitvector(6, 0b110100)
    assert b0[0] == 0
    assert b0[1] == 0
    assert b0[2] == 1
    assert b0[1:3] == _pydrofoil.bitvector(2, 0b10)

def test_bv_signed_unsigned():
    b0 = _pydrofoil.bitvector(6, 0b110100)
    assert b0.unsigned() == 0b110100
    assert b0.signed() == -12

def test_bv_binary():
    b0 = _pydrofoil.bitvector(6, 0b110100)
    b1 = _pydrofoil.bitvector(6, 0b010010)
    assert b0 & b1 == b1 & b0 == _pydrofoil.bitvector(6, 0b010000)
    assert b0 & 0b010010 == 0b110100 & b1 == b0 & b1

    assert b0 | b1 == b1 | b0 == _pydrofoil.bitvector(6, 0b110110)
    assert b0 | 0b010010 == 0b110100 | b1 == b0 | b1

    assert b0 ^ b1 == b1 ^ b0 == _pydrofoil.bitvector(6, 0b100110)
    assert b0 ^ 0b010010 == 0b110100 ^ b1 == b0 ^ b1

    assert b0 + b1 == b1 + b0 == _pydrofoil.bitvector(6, 0b000110)
    assert b0 + 0b010010 == 0b110100 + b1 == b0 + b1

    assert b0 - b1 == _pydrofoil.bitvector(6, 0b100010)
    assert b0 - 0b010010 == b0 - b1

    assert ~b0 == _pydrofoil.bitvector(6, 0b001011)

def test_bv_extend():
    b0 = _pydrofoil.bitvector(6, 0b110100)
    assert b0.zero_extend(10) == _pydrofoil.bitvector(10, 0b110100)
    b0 = _pydrofoil.bitvector(6, 0b110100)
    assert b0.sign_extend(10) == _pydrofoil.bitvector(10, 0b1111110100)

def test_bv_append():
    b0 = _pydrofoil.bitvector(6, 0b110100)
    b1 = _pydrofoil.bitvector(4, 0b1100)
    assert b0 @ b1 == _pydrofoil.bitvector(10, 0b1101001100)

def test_bitvector_to_int():
    b0 = _pydrofoil.bitvector(6, 7)
    assert list(range(10))[b0] == 7
    assert int(b0) == 7

def test_bitvector_hash():
    m = _pydrofoil.RISCV64()
    val = 0b110100
    bv1 = _pydrofoil.bitvector(6, val)
    bv1a = _pydrofoil.bitvector(6, val)
    bv2 = _pydrofoil.bitvector(7, val)
    bv3 = _pydrofoil.bitvector(6, 0b110101)
    assert bv1 == bv1a
    assert bv1 != bv2
    assert bv1 != bv3
    assert hash(bv1) == hash(bv1a)
    assert hash(bv1) != hash(bv2)
    assert hash(bv1) != hash(bv3)

def test_bitvector_neg():
    b0 = _pydrofoil.bitvector(6, 0b110100)
    assert -b0 == 0 - b0

def test_bitvector_bool():
    m = _pydrofoil.RISCV64()
    for i in range(2**5):
        bv = _pydrofoil.bitvector(5, i)
        assert bool(bv) == (i != 0)
        bv = _pydrofoil.bitvector(128, i)
        assert bool(bv) == (i != 0)
        bv = _pydrofoil.bitvector(2000, i)
        assert bool(bv) == (i != 0)
        assert bool(-bv) == (i != 0)

def test_bitvector_shift():
    m = _pydrofoil.RISCV64()
    bv = _pydrofoil.bitvector(5, 0b10100)
    assert bv << 1 == _pydrofoil.bitvector(5, 0b1000)
    with raises(TypeError) as e:
        bv >> 1
    assert "rshift is not implemented. use .arithmetic_rshift() or .logical_rshift()." in str(e.value)
    assert bv.arithmetic_rshift(1) == _pydrofoil.bitvector(5, 0b11010)
    assert _pydrofoil.bitvector(5, 0b100).arithmetic_rshift(1) == _pydrofoil.bitvector(5, 0b10)
    assert bv.logical_rshift(1) == _pydrofoil.bitvector(5, 0b01010)

def test_bitvector_big():
    m = _pydrofoil.RISCV64()
    bv = _pydrofoil.bitvector(128, 2**100)
    assert bv == 2**100

# ________________________________________________
# memory interception

def test_step_intercept_mem():
    mem = {}
    def read(addr):
        return mem.get(addr, _pydrofoil.bitvector(64, 0))
    def write(addr, value):
        mem[addr] = value

    callbacks = _pydrofoil.Callbacks(mem_read8_intercept=read, mem_write8_intercept=write)
    cpu = _pydrofoil.RISCV64(addielf, callbacks=callbacks)
    cpu.run(100)
    assert cpu.read_register("pc") == 0x800001f0
    assert mem[_pydrofoil.bitvector(64, 0x0000000010000000)] == _pydrofoil.bitvector(64, 0x34202F7304C0006F)
    assert cpu.memory_info() == [(0x1000, 0x80001047)]

def test_step_monitor_mem_with_callbacks():
    mem = {}
    def read(addr):
        return mem.get(addr, _pydrofoil.bitvector(64, 0))
    def write(addr, value):
        mem[addr] = value

    callbacks = _pydrofoil.Callbacks(mem_read8_intercept=read, mem_write8_intercept=write)
    cpu = _pydrofoil.RISCV64(addielf, callbacks=callbacks)
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


# ________________________________________________
# testing the sail types

def test_sailtype_new():
    assert _pydrofoil.sailtypes.Bool() is _pydrofoil.sailtypes.Bool() # singleton
    assert _pydrofoil.sailtypes.Unit() is _pydrofoil.sailtypes.Unit() # singleton
    assert _pydrofoil.sailtypes.GenericBitVector() is _pydrofoil.sailtypes.GenericBitVector() # singleton
    with raises(TypeError):
        _pydrofoil.sailtypes.Struct()
    assert _pydrofoil.sailtypes.SmallFixedBitVector(23).width == 23
    for invalid_width in [-1, 0, 65, 1090123]:
        with raises(ValueError):
            _pydrofoil.sailtypes.SmallFixedBitVector(invalid_width)
    with raises(ValueError):
        _pydrofoil.sailtypes.BigFixedBitVector(64)
    assert _pydrofoil.sailtypes.BigFixedBitVector(2321).width == 2321

def test_sailtype_repr():
    assert repr(_pydrofoil.sailtypes.SmallFixedBitVector(12)) == "_pydrofoil.sailtypes.SmallFixedBitVector(12)"
    assert repr(_pydrofoil.sailtypes.BigFixedBitVector(121)) == "_pydrofoil.sailtypes.BigFixedBitVector(121)"
    cpu = _pydrofoil.RISCV64()
    rs = dict(cpu.register_info())
    assert repr(rs['cur_privilege']) == '<_pydrofoil.sailtypes.Enum Privilege { User Supervisor Machine }>'
    assert repr(_pydrofoil.sailtypes.MachineInt()) == "_pydrofoil.sailtypes.MachineInt()"
    assert repr(_pydrofoil.sailtypes.GenericBitVector()) == "_pydrofoil.sailtypes.GenericBitVector()"

def test_fvec():
    cpu = _pydrofoil.RISCV64()
    rs = dict(cpu.register_info())
    fvectype = rs['mhpmevent']
    assert fvectype.of.width == 64
    assert repr(fvectype) == "<_pydrofoil.sailtypes.FVec 32 _pydrofoil.sailtypes.SmallFixedBitVector(64)>"
    assert isinstance(fvectype, _pydrofoil.sailtypes.FVec)

def test_union_repr():
    cpu = _pydrofoil.RISCV64()
    assert repr(cpu.lowlevel.accessToFault.sail_type.arguments[0]) == '<_pydrofoil.sailtypes.Union AccessType<u>>'

def test_struct_repr():
    cpu = _pydrofoil.RISCV64()
    assert repr(cpu.lowlevel.check_PTE_permission.sail_type.arguments[4]) == '<_pydrofoil.sailtypes.Struct PTE_Flags>'

def test_tuple_repr():
    cpu = _pydrofoil.RISCV64()
    assert repr(dict(cpu.types.ast.sail_type.constructors)['ITYPE']) == '<_pydrofoil.sailtypes.Tuple (_pydrofoil.sailtypes.SmallFixedBitVector(12), _pydrofoil.sailtypes.SmallFixedBitVector(5), _pydrofoil.sailtypes.SmallFixedBitVector(5), <_pydrofoil.sailtypes.Enum iop { RISCV_ADDI RISCV_SLTI RISCV_SLTIU RISCV_XORI RISCV_ORI RISCV_ANDI }>)>'

def test_function_repr():
    cpu = _pydrofoil.RISCV64()
    assert repr(cpu.lowlevel.check_PTE_permission.sail_type) == '<_pydrofoil.sailtypes.Function (<_pydrofoil.sailtypes.Union AccessType<u>>, <_pydrofoil.sailtypes.Enum Privilege { User Supervisor Machine }>, _pydrofoil.sailtypes.Bool(), _pydrofoil.sailtypes.Bool(), <_pydrofoil.sailtypes.Struct PTE_Flags>, _pydrofoil.sailtypes.SmallFixedBitVector(64), _pydrofoil.sailtypes.Unit()) -> <_pydrofoil.sailtypes.Union PTE_Check>>'

def test_fixedbitvector_base_class():
    assert isinstance(_pydrofoil.sailtypes.SmallFixedBitVector(12), _pydrofoil.sailtypes.FixedBitVector)
    assert isinstance(_pydrofoil.sailtypes.BigFixedBitVector(122), _pydrofoil.sailtypes.FixedBitVector)

    # but constructing a FixedBitVector gives one of the subclasses
    assert isinstance(_pydrofoil.sailtypes.FixedBitVector(12), _pydrofoil.sailtypes.SmallFixedBitVector)
    assert isinstance(_pydrofoil.sailtypes.FixedBitVector(122), _pydrofoil.sailtypes.BigFixedBitVector)

