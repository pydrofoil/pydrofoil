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


