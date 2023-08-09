import pytest
from pydrofoil.makecode import *

from rpython.rlib import rarithmetic

import os

thisdir = os.path.dirname(__file__)
cir = os.path.join(thisdir, "nand2tetris/generated/nand2tetris.jib")
excir = os.path.join(thisdir, "exc/exc.ir")
outpy = os.path.join(thisdir, "nand2tetris/generated/nand_rpython.py")

addrom = os.path.join(os.path.dirname(os.path.dirname(__file__)), "test", "nand2tetris", "input", "Add.hack.bin")
sumrom = os.path.join(os.path.dirname(os.path.dirname(__file__)), "test", "nand2tetris", "input", "sum.hack.bin")

def test_enum():
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    res = parse_and_make_code("""
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
""", support_code)
    assert "class Enum_zjump" in res
    assert """\
    zJDONT = 0
    zJGT = 1
    zJEQ = 2
    zJGE = 3
    zJLT = 4
    zJNE = 5
    zJLE = 6
    zJMP = 7
""" in res

def test_union():
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    res = parse_and_make_code("""
union zinstr {
  zAINST: %bv16,
  zCINST: (%bv1, (%bool, %bool, %bool), %bool)
}
""", support_code)
    assert "class Union_zinstr" in res
    assert "class Union_zinstr_zAINST(Union_zinstr):" in res
    assert "class Union_zinstr_zCINST(Union_zinstr):" in res

@pytest.mark.xfail
def test_exceptions(capsys):
    import py
    s = """
union zexception {
  zEpair: (%i64, %i64),
  zEstring: %string,
  zEunknown: %unit
}

val znot_bool = "not" : (%bool) ->  %bool

val zeq_int = "eq_int" : (%i, %i) ->  %bool

val zeq_bool = "eq_bool" : (%bool, %bool) ->  %bool

val zprint = "print_endline" : (%string) ->  %unit

val zprint_int = "print_int" : (%string, %i) ->  %unit

val zf : (%unit) ->  %unit

fn zf(zgsz30) {
  zgaz30_lz30 : %union zexception;
  zgaz30_lz30 = zEstring("test");
  current_exception = zgaz30_lz30;
  have_exception = true;
  throw_location = "fail_exception.sail 14:16 - 14:38";
  arbitrary;
}

val zg : (%unit) ->  %string

fn zg(zgsz31) {
  zgsz33_lz32 : %unit;
  zgsz33_lz32 = zprint("in g()");
  return = "g return";
  end;
}

val zmain : (%unit) ->  %unit

fn zmain(zgsz34) {
  zgsz39_lz320 : %unit;
  zgaz32_lz331 : %string;
  zgaz32_lz331 = zg(());
  jump have_exception goto 5 ` "unknown location";
  goto 6;
  goto 21;
  zgsz38_lz332 : %unit;
  zgsz38_lz332 = zprint(zgaz32_lz331);
  zgsz37_lz330 : %unit;
  zgsz37_lz330 = zf(());
  jump have_exception goto 12 ` "unknown location";
  goto 13;
  goto 21;
  zgaz33_lz327 : %union zexception;
  zgsz35_lz329 : (%i64, %i64);
  zgsz35_lz329.0 = 42;
  zgsz35_lz329.1 = 24;
  zgaz33_lz327 = zEpair(zgsz35_lz329);
  current_exception = zgaz33_lz327;
  have_exception = true;
  throw_location = "fail_exception.sail 30:4 - 30:24";
  jump @not(have_exception) goto 41 ` "fail_exception.sail 27:2 - 39:3";
  have_exception = false;
  jump current_exception is zEunknown goto 26 ` "fail_exception.sail 33:4 - 33:14";
  zgsz39_lz320 = zprint("Caught Eunknown");
  goto 41;
  jump current_exception is zEpair goto 33 ` "fail_exception.sail 34:4 - 34:15";
  zx_lz324 : %i64;
  zx_lz324 = current_exception as zEpair.ztup0;
  zy_lz325 : %i64;
  zy_lz325 = current_exception as zEpair.ztup1;
  zgsz39_lz320 = zprint("Caught Epair");
  goto 41;
  jump current_exception is zEstring goto 40 ` "fail_exception.sail 35:4 - 35:16";
  zstr_lz322 : %string;
  zstr_lz322 = current_exception as zEstring;
  zgsz312_lz323 : %unit;
  zgsz312_lz323 = zprint("Caught Estring");
  zgsz39_lz320 = zprint(zstr_lz322);
  goto 41;
  have_exception = true;
  zgsz338_lz321 : %unit;
  zgsz338_lz321 = zgsz39_lz320;
  zgsz314_lz318 : %unit;
  zgsz314_lz318 = ();
  jump @not(have_exception) goto 48 ` "fail_exception.sail 40:2 - 42:3";
  have_exception = false;
  zgsz314_lz318 = zprint("Unreachable!");
  zgsz337_lz319 : %unit;
  zgsz337_lz319 = zgsz314_lz318;
  zgsz317_lz311 : %unit;
  zgaz35_lz316 : %union zexception;
  zgsz316_lz317 : (%i64, %i64);
  zgsz316_lz317.0 = 33;
  zgsz316_lz317.1 = 1;
  zgaz35_lz316 = zEpair(zgsz316_lz317);
  current_exception = zgaz35_lz316;
  have_exception = true;
  throw_location = "fail_exception.sail 43:6 - 43:25";
  jump @not(have_exception) goto 70 ` "fail_exception.sail 43:2 - 49:3";
  have_exception = false;
  jump current_exception is zEpair goto 69 ` "fail_exception.sail 44:4 - 44:15";
  zx_lz313 : %i64;
  zx_lz313 = current_exception as zEpair.ztup0;
  zgsz318_lz315 : %unit;
  zgsz318_lz315 = zprint("2nd try Caught Epair");
  zgsz320_lz314 : %i = zx_lz313;
  zgsz317_lz311 = zprint_int("x = ", zgsz320_lz314);
  goto 70;
  zgsz317_lz311 = ();
  zgsz336_lz312 : %unit;
  zgsz336_lz312 = zgsz317_lz311;
  zgsz322_lz35 : %unit;
  zgaz36_lz310 : %union zexception;
  zgaz36_lz310 = zEunknown(());
  current_exception = zgaz36_lz310;
  have_exception = true;
  throw_location = "fail_exception.sail 50:6 - 50:23";
  jump @not(have_exception) goto 93 ` "fail_exception.sail 50:2 - 54:3";
  have_exception = false;
  zgsz325_lz37 : %unit;
  zgaz37_lz38 : %string;
  zgaz37_lz38 = zg(());
  jump have_exception goto 85 ` "unknown location";
  goto 86;
  goto 89;
  zgsz323_lz39 : %unit;
  zgsz323_lz39 = ();
  zgsz325_lz37 = zgsz323_lz39;
  jump @not(have_exception) goto 92 ` "fail_exception.sail 51:9 - 53:5";
  have_exception = false;
  zgsz325_lz37 = zprint("caught old exception");
  zgsz322_lz35 = zgsz325_lz37;
  zgsz335_lz36 : %unit;
  zgsz335_lz36 = zgsz322_lz35;
  zgsz330_lz31 : %unit;
  zgsz328_lz33 : %unit;
  zgaz38_lz34 : %union zexception;
  zgaz38_lz34 = zEunknown(());
  current_exception = zgaz38_lz34;
  have_exception = true;
  throw_location = "fail_exception.sail 56:8 - 56:24";
  jump @not(have_exception) goto 108 ` "fail_exception.sail 56:4 - 58:5";
  have_exception = false;
  jump current_exception is zEstring goto 107 ` "fail_exception.sail 57:6 - 57:16";
  zgsz328_lz33 = ();
  goto 108;
  have_exception = true;
  zgsz330_lz31 = zgsz328_lz33;
  jump @not(have_exception) goto 115 ` "fail_exception.sail 55:2 - 62:3";
  have_exception = false;
  jump current_exception is zEunknown goto 114 ` "fail_exception.sail 60:4 - 60:14";
  zgsz330_lz31 = zprint("Fall through OK");
  goto 115;
  zgsz330_lz31 = ();
  zgsz334_lz32 : %unit;
  zgsz334_lz32 = zgsz330_lz31;
  zgsz333_lz30 : %unit;
  zgsz333_lz30 = zf(());
  jump have_exception goto 121 ` "unknown location";
  goto 122;
  goto 124;
  return = ();
  end;
  arbitrary;
}
"""
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    res = parse_and_make_code(s, support_code)
    d = {}
    res = py.code.Source(res)
    exec res.compile() in d
    machine = d['Machine']()
    d['func_zmain'](machine, ())
    out, err = capsys.readouterr()
    assert out == """\
in g()
g return
Caught Estring
test
2nd try Caught Epair
x = 33
in g()
Fall through OK
"""
    assert machine.have_exception

@pytest.mark.xfail
def test_exceptions2(capsys):
    import py
    with open(excir, "rb") as f:
        s = f.read()
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    res = parse_and_make_code(s, support_code)
    res = py.code.Source(res)
    d = {}
    exec res.compile() in d
    machine = d['Machine']()
    d['func_zmain'](machine, ())
    out, err = capsys.readouterr()
    assert out == """\
i = 1
i = 2
i = 3
i = 3
i = 2
i = 1
j = 1
j = 2
j = 3
k = 0x01
k = 0x02
k = 0x03
Caught
Looping
Caught inner exception
Caught outer exception
Outer handler
Outer handler
Once
Once
ok
ok
R = 3
"""
    assert machine.have_exception

def test_full_nand():
    import py
    from pydrofoil.test.nand2tetris import supportcodenand
    from rpython.translator.interactive import Translation
    with open(cir, "rb") as f:
        s = f.read()
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    res = parse_and_make_code(s, support_code)
    with open(outpy, "w") as f:
        f.write(res)

    # bit of a hack
    from pydrofoil.test.nand2tetris.generated import nand_rpython as out
    supportcodenand.load_rom(addrom)
    zmymain = out.func_zmymain
    machine = out.Machine()
    zmymain(machine, rarithmetic.r_uint(10), True)
    assert machine._reg_zD == 5
    assert machine._reg_zA == 0
    assert machine._reg_zPC == 11
    supportcodenand.load_rom(sumrom)
    zmymain(out.Machine(), rarithmetic.r_uint(2000), True)
    assert supportcodenand.my_read_mem(machine, 17) == 5050

    def main():
        supportcodenand.load_rom(addrom)
        zmymain(out.Machine(), 10, False)
    t = Translation(main, [])
    t.rtype() # check that it's rpython

def test_real(capsys):
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    res = parse_and_make_code('''
        val zz5i64zDzKz5i = "%i64->%i" : (%i64) ->  %i

val zz5stringzDzKz5real = "%string->%real" : (%string) ->  %real

union zexception {
  z__dummy_exnz3: %unit
}

val zprint_int = "print_int" : (%string, %i) ->  %unit

val zneg_real = "neg_real" : (%real) ->  %real

val zmult_real = "mult_real" : (%real, %real) ->  %real

val zsub_real = "sub_real" : (%real, %real) ->  %real

val zadd_real = "add_real" : (%real, %real) ->  %real

val zdiv_real = "div_real" : (%real, %real) ->  %real

val zsqrt = "sqrt_real" : (%real) ->  %real

val zabs_real = "abs_real" : (%real) ->  %real

val zfloor = "round_down" : (%real) ->  %i

val zceil = "round_up" : (%real) ->  %i

val zto_real = "to_real" : (%i) ->  %real

val zeq_real = "eq_real" : (%real, %real) ->  %bool

val zlt_real = "lt_real" : (%real, %real) ->  %bool

val zgt_real = "gt_real" : (%real, %real) ->  %bool

val zlteq_real = "lteq_real" : (%real, %real) ->  %bool

val zgteq_real = "gteq_real" : (%real, %real) ->  %bool

val zpow_real = "real_power" : (%real, %i) ->  %real

val zprint_real = "print_real" : (%string, %real) ->  %unit

val ztest : (%real, %i) ->  %unit

fn ztest(zx, zn) {
  zz455 : %unit `0 9:2-9:24;
  zz455 = zprint_int("test: ", zn) `0 9:2-9:24;
  zz454 : %unit `0 10:2-10:25;
  zz454 = zprint_real("show: ", zx) `0 10:2-10:25;
  zz452 : %real `0 11:2-11:34;
  zz452 = zneg_real(zx) `0 11:22-11:33;
  zz453 : %unit `0 11:2-11:34;
  zz453 = zprint_real("neg: ", zz452) `0 11:2-11:34;
  zz450 : %real `0 12:2-12:29;
  zz450 = zmult_real(zx, zx) `0 12:23-12:28;
  zz451 : %unit `0 12:2-12:29;
  zz451 = zprint_real("mult: ", zz450) `0 12:2-12:29;
  zz447 : %real `0 13:2-13:30;
  zz449 : %real `0 13:22-13:29;
  zz449 = zz5stringzDzKz5real("1.0") `0 13:22-13:29;
  zz447 = zsub_real(zx, zz449) `0 13:22-13:29;
  zz448 : %unit `0 13:2-13:30;
  zz448 = zprint_real("sub: ", zz447) `0 13:2-13:30;
  zz444 : %real `0 14:2-14:30;
  zz446 : %real `0 14:22-14:29;
  zz446 = zz5stringzDzKz5real("1.0") `0 14:22-14:29;
  zz444 = zadd_real(zx, zz446) `0 14:22-14:29;
  zz445 : %unit `0 14:2-14:30;
  zz445 = zprint_real("add: ", zz444) `0 14:2-14:30;
  zz441 : %real `0 15:2-15:30;
  zz443 : %real `0 15:22-15:29;
  zz443 = zz5stringzDzKz5real("2.0") `0 15:22-15:29;
  zz441 = zdiv_real(zx, zz443) `0 15:22-15:29;
  zz442 : %unit `0 15:2-15:30;
  zz442 = zprint_real("div: ", zz441) `0 15:2-15:30;
  zz439 : %real `0 16:2-16:31;
  zz439 = zsqrt(zx) `0 16:23-16:30;
  zz440 : %unit `0 16:2-16:31;
  zz440 = zprint_real("sqrt: ", zz439) `0 16:2-16:31;
  zz437 : %real `0 17:2-17:35;
  zz437 = zabs_real(zx) `0 17:23-17:34;
  zz438 : %unit `0 17:2-17:35;
  zz438 = zprint_real("abs1: ", zz437) `0 17:2-17:35;
  zz434 : %real `0 18:2-18:45;
  zz436 : %real `0 18:23-18:44;
  zz436 = zneg_real(zx) `0 18:32-18:43;
  zz434 = zabs_real(zz436) `0 18:23-18:44;
  zz435 : %unit `0 18:2-18:45;
  zz435 = zprint_real("abs2: ", zz434) `0 18:2-18:45;
  zz432 : %i `0 19:2-19:32;
  zz432 = zfloor(zx) `0 19:23-19:31;
  zz433 : %unit `0 19:2-19:32;
  zz433 = zprint_int("floor: ", zz432) `0 19:2-19:32;
  zz430 : %i `0 20:2-20:30;
  zz430 = zceil(zx) `0 20:22-20:29;
  zz431 : %unit `0 20:2-20:30;
  zz431 = zprint_int("ceil: ", zz430) `0 20:2-20:30;
  zz427 : %real `0 21:2-21:44;
  zz429 : %i `0 21:26-21:43;
  zz429 = zfloor(zx) `0 21:34-21:42;
  zz427 = zto_real(zz429) `0 21:26-21:43;
  zz428 : %unit `0 21:2-21:44;
  zz428 = zprint_real("to_real: ", zz427) `0 21:2-21:44;
  zz422 : %bool `0 22:2-26:3;
  zz426 : %real `0 22:6-22:15;
  zz426 = zz5stringzDzKz5real("16.0") `0 22:6-22:15;
  zz422 = zeq_real(zx, zz426) `0 22:6-22:15;
  zz423 : %unit `0 22:2-26:3;
  jump zz422 goto 68 `0 22:2-26:3;
  zz425 : %i `0 25:4-25:27;
  zz425 = zz5i64zDzKz5i(0) `0 25:4-25:27;
  zz423 = zprint_int("equal: ", zz425) `0 25:4-25:27;
  goto 71;
  zz424 : %i `0 23:8-23:31;
  zz424 = zz5i64zDzKz5i(1) `0 23:8-23:31;
  zz423 = zprint_int("equal: ", zz424) `0 23:8-23:31;
  zz417 : %bool `0 28:2-33:3;
  zz421 : %real `0 28:6-28:14;
  zz421 = zz5stringzDzKz5real("17.0") `0 28:6-28:14;
  zz417 = zlt_real(zx, zz421) `0 28:6-28:14;
  zz418 : %unit `0 28:2-33:3;
  jump zz417 goto 81 `0 28:2-33:3;
  zz420 : %i `0 32:4-32:24;
  zz420 = zz5i64zDzKz5i(0) `0 32:4-32:24;
  zz418 = zprint_int("lt: ", zz420) `0 32:4-32:24;
  goto 84;
  zz419 : %i `0 29:4-29:24;
  zz419 = zz5i64zDzKz5i(1) `0 29:4-29:24;
  zz418 = zprint_int("lt: ", zz419) `0 29:4-29:24;
  zz412 : %bool `0 34:2-39:3;
  zz416 : %real `0 34:5-34:13;
  zz416 = zz5stringzDzKz5real("18.0") `0 34:5-34:13;
  zz412 = zgt_real(zx, zz416) `0 34:5-34:13;
  zz413 : %unit `0 34:2-39:3;
  jump zz412 goto 94 `0 34:2-39:3;
  zz415 : %i `0 38:4-38:24;
  zz415 = zz5i64zDzKz5i(0) `0 38:4-38:24;
  zz413 = zprint_int("gt: ", zz415) `0 38:4-38:24;
  goto 97;
  zz414 : %i `0 35:4-35:24;
  zz414 = zz5i64zDzKz5i(1) `0 35:4-35:24;
  zz413 = zprint_int("gt: ", zz414) `0 35:4-35:24;
  zz47 : %bool `0 40:2-45:3;
  zz411 : %real `0 40:5-40:14;
  zz411 = zz5stringzDzKz5real("17.0") `0 40:5-40:14;
  zz47 = zlteq_real(zx, zz411) `0 40:5-40:14;
  zz48 : %unit `0 40:2-45:3;
  jump zz47 goto 107 `0 40:2-45:3;
  zz410 : %i `0 44:4-44:26;
  zz410 = zz5i64zDzKz5i(0) `0 44:4-44:26;
  zz48 = zprint_int("lteq: ", zz410) `0 44:4-44:26;
  goto 110;
  zz49 : %i `0 41:4-41:26;
  zz49 = zz5i64zDzKz5i(1) `0 41:4-41:26;
  zz48 = zprint_int("lteq: ", zz49) `0 41:4-41:26;
  zz42 : %bool `0 46:2-51:3;
  zz46 : %real `0 46:5-46:15;
  zz46 = zz5stringzDzKz5real("18.49") `0 46:5-46:15;
  zz42 = zgteq_real(zx, zz46) `0 46:5-46:15;
  zz43 : %unit `0 46:2-51:3;
  jump zz42 goto 120 `0 46:2-51:3;
  zz45 : %i `0 50:4-50:26;
  zz45 = zz5i64zDzKz5i(0) `0 50:4-50:26;
  zz43 = zprint_int("gteq: ", zz45) `0 50:4-50:26;
  goto 123;
  zz44 : %i `0 47:4-47:26;
  zz44 = zz5i64zDzKz5i(1) `0 47:4-47:26;
  zz43 = zprint_int("gteq: ", zz44) `0 47:4-47:26;
  zz40 : %real `0 52:2-52:39;
  zz41 : %i `0 52:24-52:38;
  zz41 = zz5i64zDzKz5i(2) `0 52:24-52:38;
  zz40 = zpow_real(zx, zz41) `0 52:24-52:38;
  return = zprint_real("power: ", zz40) `0 52:2-52:39;
  end;
}

val zmain : (%unit) ->  %unit

fn zmain(zgsz337) {
  zz48 : %real `0 80:2-80:15;
  zz48 = zz5stringzDzKz5real("16.0") `0 80:2-80:15;
  zz49 : %i `0 80:2-80:15;
  zz49 = zz5i64zDzKz5i(0) `0 80:2-80:15;
  zz410 : %unit `0 80:2-80:15;
  zz410 = ztest(zz48, zz49) `0 80:2-80:15;
  zz45 : %real `0 81:2-81:15;
  zz45 = zz5stringzDzKz5real("17.0") `0 81:2-81:15;
  zz46 : %i `0 81:2-81:15;
  zz46 = zz5i64zDzKz5i(1) `0 81:2-81:15;
  zz47 : %unit `0 81:2-81:15;
  zz47 = ztest(zz45, zz46) `0 81:2-81:15;
  zz42 : %real `0 82:2-82:16;
  zz42 = zz5stringzDzKz5real("18.49") `0 82:2-82:16;
  zz43 : %i `0 82:2-82:16;
  zz43 = zz5i64zDzKz5i(2) `0 82:2-82:16;
  zz44 : %unit `0 82:2-82:16;
  zz44 = ztest(zz42, zz43) `0 82:2-82:16;
  zz40 : %real `0 83:2-83:16;
  zz40 = zz5stringzDzKz5real("28.09") `0 83:2-83:16;
  zz41 : %i `0 83:2-83:16;
  zz41 = zz5i64zDzKz5i(3) `0 83:2-83:16;
  return = ztest(zz40, zz41) `0 83:2-83:16;
  end;
}

val zinitializze_registers : (%unit) ->  %unit

fn zinitializze_registers(zgsz349) {
  return = () `1;
  end;
}

files "../../test/c/real.sail"                      ''', support_code)
    import py
    d = {}
    res = py.code.Source(res)
    exec res.compile() in d
    machine = d['Machine']()
    d['func_zmain'](machine, ())
    out, err = capsys.readouterr()

