from pydrofoil.parse import *

import os

thisdir = os.path.dirname(__file__)
cir = os.path.join(thisdir, "nand2tetris/generated/nand2tetris.jib")
riscvir = os.path.join(thisdir, "riscv/riscv_model_RV64.ir")

def test_lex_full():
    with open(cir, "rb") as f:
        s = f.read()
    try:
        for tok in lexer.lex(s):
            pass
    except LexingError as e:
        print s[e.getsourcepos().idx:e.getsourcepos().idx+20]
        assert 0

def test_lex_binary():
    tok, = lexer.lex("0b0100101")

def test_parse_enum():
    res = parser.parse(lexer.lex("""
enum zjump {
  zJDONT,
  zJGT,
  zJEQ,
  zJGE,
  zJLT,
  zJNE,
  zJLE,
  zJMP
}
"""))
    assert res.declarations[0] == Enum(
        'zjump', ['zJDONT', 'zJGT', 'zJEQ', 'zJGE', 'zJLT', 'zJNE', 'zJLE', 'zJMP'])

def test_struct():
    res = parser.parse(lexer.lex("""
struct zXContextReg {
  zXContextReg_chunk_0: %bv64
}
"""))
    assert res.declarations[0] == Struct('zXContextReg',
        ['zXContextReg_chunk_0'],
        [NamedType('%bv64')],
    )

def xtest_let():
    res = parser.parse(lexer.lex("""
let (zdefault_meta: %unit) {
  zz40 : %unit `2 75:30-75:32;
  zz40 = () `2 75:30-75:32;
  zdefault_meta = zz40 `2 75:4-75:16;
}
}"""))
    assert res.declarations[0] == Let("ztrace", NamedType("%bool"),
        [
            LocalVarDeclaration('zgsz30_lz30', NamedType('%bool')),
            Assignment('zgsz30_lz30', Var('false')),
            Assignment('ztrace', Var('zgsz30_lz30')),
        ])

def test_reftype():
    res = parser.parse(lexer.lex("""
val zzzzz7azzJzzKTLBEntryz3__deref = "reg_deref" : (&(%struct zTLBEntry)) ->  %struct zTLBEntry
"""))
    assert res.declarations[0].typ.argtype == TupleType([RefType(StructType('zTLBEntry'))])

def test_vectype():

    res = parser.parse(lexer.lex("""
register zGPR : %vec(%bv64)
"""))
    assert res.declarations[0].typ == VecType(NamedType("%bv64"))

def test_globalval():
    res = parser.parse(lexer.lex("""
val zeq_bool = "eq_bool" : (%bool, %bool) ->  %bool
val zneq_int : (%i, %i) ->  %bool

"""))
    assert res.declarations == [
        GlobalVal('zeq_bool', '"eq_bool"', FunctionType(TupleType([NamedType('%bool')] * 2), NamedType('%bool'))),
        GlobalVal('zneq_int', None, FunctionType(TupleType([NamedType('%i')] * 2), NamedType('%bool'))),
    ]

def test_register():
    res = parser.parse(lexer.lex("""
register zPC : %bv16
"""))
    assert res.declarations == [
        Register('zPC', NamedType('%bv16'))
    ]

def test_pragma():
    res = parser.parse(lexer.lex("""
#tuplestruct ztuplez3z5bool_z5bool_z5bool ztuplez3z5bool_z5bool_z5bool0 ztuplez3z5bool_z5bool_z5bool1 ztuplez3z5bool_z5bool_z5bool2
"""))
    assert res.declarations == [
        Pragma('tuplestruct', 'ztuplez3z5bool_z5bool_z5bool ztuplez3z5bool_z5bool_z5bool0 ztuplez3z5bool_z5bool_z5bool1 ztuplez3z5bool_z5bool_z5bool2'.split())
    ]


def test_function():
    res = parser.parse(lexer.lex("""
fn zneq_int(zx, zy) {
  zz40 : %bool `0 100:26-100:48;
  zz40 = zeq_int(zx, zy) `0 100:35-100:47;
  return = znot_bool(zz40) `0 100:26-100:48;
  end;
}
"""))

    assert res.declarations[0] == Function(
        name='zneq_int',
        args=['zx', 'zy'],
        body=[
            LocalVarDeclaration(name='zz40', sourcepos='`0 100:26-100:48', typ=NamedType('%bool'), value=None),
            Operation(args=[Var(name='zx'), Var(name='zy')], name='zeq_int', result='zz40', sourcepos='`0 100:35-100:47'),
            Operation(args=[Var(name='zz40')], name='znot_bool', result='return', sourcepos='`0 100:26-100:48'),
            End()],
    )


def test_function4():
    res = parser.parse(lexer.lex("""
fn zdecode(zmergez3var) {
  zz40 : %union zoptionzIUinstrzIzKzK `1 99:16-100:39;
  zz435 : %bv16 `1 99:23-99:41;
  zz435 = zmergez3var `1 99:23-99:41;
  zz436 : %bv1 `1 99:23-99:41;
  zz450 : %i `1 99:23-99:41;
  zz450 = zz5i64zDzKz5i(15) `1 99:23-99:41;
  zz451 : %i `1 99:23-99:41;
  zz451 = zz5i64zDzKz5i(15) `1 99:23-99:41;
  zz452 : %bv `1 99:23-99:41;
  zz452 = zz435 `1 99:23-99:41;
  zz453 : %bv `1 99:23-99:41;
  zz453 = zsubrange_bits(zz452, zz450, zz451) `1 99:23-99:41;
  zz436 = zz453 `1 99:23-99:41;
  zz437 : %bool `1 99:16-100:39;
  zz448 : %bv `1 99:23-99:41;
  zz448 = zz436 `1 99:23-99:41;
  zz449 : %bv `1 99:23-99:41;
  zz449 = 0b0 `1 99:23-99:41;
  zz437 = zeq_bits(zz448, zz449) `1 99:23-99:41;
  jump @not(zz437) goto 21 `1 99:16-100:39;
  goto 22;
  goto 44;
  zz438 : %bv15 `1 100:3-100:39;
  zz444 : %i `1 99:29-99:30;
  zz444 = zz5i64zDzKz5i(14) `1 99:29-99:30;
  zz445 : %i `1 99:29-99:30;
  zz445 = zz5i64zDzKz5i(0) `1 99:29-99:30;
  zz446 : %bv `1 99:29-99:30;
  zz446 = zz435 `1 99:29-99:30;
  zz447 : %bv `1 99:29-99:30;
  zz447 = zsubrange_bits(zz446, zz444, zz445) `1 99:29-99:30;
  zz438 = zz447 `1 99:29-99:30;
  zz439 : %union zinstr `1 100:3-100:39;
  zz440 : %bv16 `1 100:8-100:38;
  zz441 : %i `1 100:14-100:37;
  zz441 = zz5i64zDzKz5i(16) `1 100:14-100:37;
  zz442 : %bv `1 100:14-100:37;
  zz442 = zz438 `1 100:14-100:37;
  zz443 : %bv `1 100:14-100:37;
  zz443 = zsail_zzero_extend(zz442, zz441) `1 100:14-100:37;
  zz440 = zz443 `1 100:14-100:37;
  zz439 = zAINST(zz440) `1 100:8-100:38;
  zz40 = zSomezIUinstrzIzKzK(zz439) `1 100:3-100:39;
  goto 118;
  zz41 : %bv16 `1 118:23-118:90;
  zz41 = zmergez3var `1 118:23-118:90;
  zz42 : %bv3 `1 118:23-118:90;
  zz431 : %i `1 118:23-118:90;
  zz431 = zz5i64zDzKz5i(15) `1 118:23-118:90;
  zz432 : %i `1 118:23-118:90;
  zz432 = zz5i64zDzKz5i(13) `1 118:23-118:90;
  zz433 : %bv `1 118:23-118:90;
  zz433 = zz41 `1 118:23-118:90;
  zz434 : %bv `1 118:23-118:90;
  zz434 = zsubrange_bits(zz433, zz431, zz432) `1 118:23-118:90;
  zz42 = zz434 `1 118:23-118:90;
  zz43 : %bool `1 99:16-100:39;
  zz429 : %bv `1 118:23-118:90;
  zz429 = zz42 `1 118:23-118:90;
  zz430 : %bv `1 118:23-118:90;
  zz430 = 0b111 `1 118:23-118:90;
  zz43 = zeq_bits(zz429, zz430) `1 118:23-118:90;
  jump @not(zz43) goto 64 `1 99:16-100:39;
  goto 65;
  goto 117;
  zz44 : %bv3 `1 119:4-119:82;
  zz425 : %i `1 118:76-118:80;
  zz425 = zz5i64zDzKz5i(2) `1 118:76-118:80;
  zz426 : %i `1 118:76-118:80;
  zz426 = zz5i64zDzKz5i(0) `1 118:76-118:80;
  zz427 : %bv `1 118:76-118:80;
  zz427 = zz41 `1 118:76-118:80;
  zz428 : %bv `1 118:76-118:80;
  zz428 = zsubrange_bits(zz427, zz425, zz426) `1 118:76-118:80;
  zz44 = zz428 `1 118:76-118:80;
  zz45 : %bv3 `1 118:59-118:63;
  zz421 : %i `1 118:59-118:63;
  zz421 = zz5i64zDzKz5i(5) `1 118:59-118:63;
  zz422 : %i `1 118:59-118:63;
  zz422 = zz5i64zDzKz5i(3) `1 118:59-118:63;
  zz423 : %bv `1 118:59-118:63;
  zz423 = zz41 `1 118:59-118:63;
  zz424 : %bv `1 118:59-118:63;
  zz424 = zsubrange_bits(zz423, zz421, zz422) `1 118:59-118:63;
  zz45 = zz424 `1 118:59-118:63;
  zz46 : %bv6 `1 118:45-118:46;
  zz417 : %i `1 118:45-118:46;
  zz417 = zz5i64zDzKz5i(11) `1 118:45-118:46;
  zz418 : %i `1 118:45-118:46;
  zz418 = zz5i64zDzKz5i(6) `1 118:45-118:46;
  zz419 : %bv `1 118:45-118:46;
  zz419 = zz41 `1 118:45-118:46;
  zz420 : %bv `1 118:45-118:46;
  zz420 = zsubrange_bits(zz419, zz417, zz418) `1 118:45-118:46;
  zz46 = zz420 `1 118:45-118:46;
  zz47 : %bv1 `1 118:31-118:32;
  zz413 : %i `1 118:31-118:32;
  zz413 = zz5i64zDzKz5i(12) `1 118:31-118:32;
  zz414 : %i `1 118:31-118:32;
  zz414 = zz5i64zDzKz5i(12) `1 118:31-118:32;
  zz415 : %bv `1 118:31-118:32;
  zz415 = zz41 `1 118:31-118:32;
  zz416 : %bv `1 118:31-118:32;
  zz416 = zsubrange_bits(zz415, zz413, zz414) `1 118:31-118:32;
  zz47 = zz416 `1 118:31-118:32;
  zz48 : %union zinstr `1 119:4-119:82;
  zz49 : %struct ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump `1 119:9-119:81;
  zz410 : %enum zarithmetic_op `1 119:9-119:81;
  zz410 = zdecode_compute_backwards(zz46) `1 119:18-119:35;
  zz411 : %struct ztuplez3z5bool_z5bool_z5bool `1 119:9-119:81;
  zz411 = zdecode_destination(zz45) `1 119:37-119:61;
  zz412 : %enum zjump `1 119:9-119:81;
  zz412 = zdecode_jump_backwards(zz44) `1 119:63-119:80;
  zz49 = struct ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump {ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 = zz47, ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 = zz410, ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2 = zz411, ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 = zz412} `1 119:9-119:81;
  zz48 = zCINST(zz49) `1 119:9-119:81;
  zz40 = zSomezIUinstrzIzKzK(zz48) `1 119:4-119:82;
  goto 118;
  zz40 = zNonezIUinstrzIzKzK(()) `1 121:27-121:33;
  return = zz40 `1 99:16-100:39;
  end;
}
"""))

def test_zassign_dest():
    res = parser.parse(lexer.lex("""
val zassign_dest : (%struct ztuplez3z5bool_z5bool_z5bool, %bv16) ->  %unit

fn zassign_dest(zgsz381, zvalue) {
  zz40 : %bool `1 149:22-149:23;
  zz40 = zgsz381.ztuplez3z5bool_z5bool_z5bool0 `1 149:22-149:23;
  zz41 : %bool `1 149:32-149:33;
  zz41 = zgsz381.ztuplez3z5bool_z5bool_z5bool1 `1 149:32-149:33;
  zz42 : %bool `1 149:42-149:43;
  zz42 = zgsz381.ztuplez3z5bool_z5bool_z5bool2 `1 149:42-149:43;
  zz44 : %unit `1 150:4-150:38;
  jump zz42 goto 10 `1 150:4-150:38;
  zz44 = () `1 150:38-150:38;
  goto 11;
  zz44 = zwrite_mem(zA, zvalue) `1 150:16-150:35;
  zz43 : %unit `1 151:4-151:28;
  jump zz40 goto 15 `1 151:4-151:28;
  zz43 = () `1 151:28-151:28;
  goto 17;
  zA = zvalue `1 151:20-151:25;
  zz43 = () `1 151:16-151:25;
  jump zz41 goto 20 `1 152:4-152:28;
  return = () `1 152:28-152:28;
  goto 22;
  zD = zvalue `1 152:20-152:25;
  return = () `1 152:16-152:25;
  end;
}
    """))


def test_jump_struct_expr():
    res = parser.parse(lexer.lex("""
fn zexception_handler(zcur_priv, zctl, zpc) {
  zz40 : %bv64 `25 470:2-527:3;
  jump struct ztuplez3z5enumz0zzPrivilege_z5unionz0zzctl_result {ztuplez3z5enumz0zzPrivilege_z5unionz0zzctl_result0 = zcur_priv, ztuplez3z5enumz0zzPrivilege_z5unionz0zzctl_result1 = zctl}.ztuplez3z5enumz0zzPrivilege_z5unionz0zzctl_result1 is zCTL_TRAP goto 43 `25 471:8-471:19;
  zz484 : %struct zsync_exception `25 471:17-471:18;
  zz484 = struct ztuplez3z5enumz0zzPrivilege_z5unionz0zzctl_result {ztuplez3z5enumz0zzPrivilege_z5unionz0zzctl_result0 = zcur_priv, ztuplez3z5enumz0zzPrivilege_z5unionz0zzctl_result1 = zctl}.ztuplez3z5enumz0zzPrivilege_z5unionz0zzctl_result1 as zCTL_TRAP `25 471:17-471:18;
  zz485 : %enum zPrivilege `25 472:6-476:88;
  end;
}
"""))

def test_parse_full():
    with open(cir, "rb") as f:
        s = f.read()
    try:
        res = parser.parse(lexer.lex(s))
    except LexingError as e:
        print s[e.getsourcepos().idx:e.getsourcepos().idx+20]
        assert 0


def test_struct_element_assignment_nested():
    res = parser.parse(lexer.lex("""
fn zExceptionSyndrome(zexceptype) {
  zz40.zpaddress.zpaspace = z__UNKNOWN_PASpace(()) `7 1009:25-1009:44;
  end;
}
"""))

def test_uint64c():

    res = parser.parse(lexer.lex("""
fn zAESSubBytes(zop) {
  zz4100 : %bv = UINT64_C(0) `7 147407:41-147407:112;
  zz45 : %unit `7 147409:4-147411:5;
  zz45 = () `7 147409:4-147411:5;
  return = zz41 `11868;
  end;
}
"""))
