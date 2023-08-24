import time
from rpython.rlib import jit
from pydrofoil import mem as mem_mod
from pydrofoil.supportcode import *
from pydrofoil.supportcode import Globals as BaseGlobals

def parseint(s):
    from rpython.rlib.rarithmetic import string_to_int
    return string_to_int(s, 0, no_implicit_octal=True,
                         allow_underscores=True)

# globals etc

def check_file_missing(fn):
    try:
        os.stat(fn)
    except OSError:
        print "ERROR: file does not exist: %s" % (fn, )
        return True
    return False


def get_main(outarm):
    Machine = outarm.Machine

    def get_printable_location(pc):
        return hex(pc)

    driver = jit.JitDriver(
        get_printable_location=get_printable_location,
        greens=['pc'],
        reds='auto',
        name="arm",
        is_recursive=True)

    step = outarm.func_zstep_model

    def jitstep(machine, *args):
        driver.jit_merge_point(pc=machine._reg_z_PC)
        jit.promote(machine.g)
        jit.promote(machine._reg_z_PC)
        return step(machine, *args)
    outarm.func_zstep_model = jitstep

    setinstr = outarm.func_z__SetThisInstr
    def jitsetinstr(machine, opcode):
        jit.promote(opcode)
        return setinstr(machine, opcode)
    outarm.func_z__SetThisInstr = jitsetinstr

    def main(argv):
        from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
        from arm import supportcodearm
        machine = Machine()

        limit = 0
        str_limit = parse_args(argv, "-l", "--inst-limit")
        if str_limit:
            limit = parseint(str_limit)
            print "instruction limit", limit
        machine.g.max_cycle_count = limit

        verbosity = 0
        str_verbosity = parse_args(argv, "-v", "--verbosity")
        if str_verbosity:
            verbosity = parseint(str_verbosity)
            print "verbosity", hex(verbosity)
        machine.g.sail_verbosity = r_uint(verbosity)

        binaries = parse_args(argv, "-b", "--binary", many=True)
        for binary in binaries:
            offset, filename = binary.split(',', 2)
            offset = parseint(offset)
            if check_file_missing(filename):
                return -1
            print "loading binary blob", filename, "at offset", hex(offset)
            load_raw_single(machine, r_uint(offset), filename)

        jitopts = parse_args(argv, "--jit")
        if jitopts:
            try:
                jit.set_user_param(None, jitopts)
            except ValueError:
                print "invalid jit option"
                return 1

        configs = parse_args(argv, "-C", "--model-config", many=True)
        for config in configs:
            configname, value = config.split('=', 2)
            value = parseint(value)
            print "setting config value", configname, "to", hex(value)
            outarm.func_z__SetConfig(machine, configname, bitvector.Integer.fromint(value))
        assert len(argv) == 1
        print "done, starting main"
        t1 = time.time()
        try:
            outarm.func_zmain(machine, ())
        finally:
            t2 = time.time()
            print "ran for %s(s), %s instructions, KIPS: %s" % (t2 - t1, machine.g.cycle_count, machine.g.cycle_count / (t2 - t1))
        return 0
    main.mod = outarm
    return main


class Globals(BaseGlobals):
    _immutable_fields_ = ['max_cycle_count?', 'verbosity?']
    def __init__(self):
        BaseGlobals.__init__(self)
        self.cycle_count = 0
        self.max_cycle_count = 0


def make_dummy(name):
    def dummy(machine, *args):
        if objectmodel.we_are_translated():
            print "not implemented!", name
            raise ValueError
        import pdb; pdb.set_trace()
        return 123
    dummy.func_name += name
    globals()[name] = dummy


def platform_branch_announce(machine, *args):
    return ()

def reset_registers(machine, *args):
    return ()

def load_raw(machine, offsets, filenames):
    assert len(offsets) == len(filenames)
    for i in range(len(offsets)):
        offset = offsets[i]
        fn = filenames[i]
        load_raw_single(machine, offset, fn)

def load_raw_single(machine, offset, fn):
    f = open(fn, 'rb')
    try:
        content = f.read()
        for i, byte in enumerate(content):
            machine.g.mem.write(offset + i, 1, r_uint(ord(byte)))
    finally:
        f.close()

def elf_entry(machine, _):
    return bitvector.Integer.fromint(0x80000000)

def cycle_count(machine, _):
    machine.g.cycle_count += 1
    max_cycle_count = machine.g.max_cycle_count
    if max_cycle_count and machine.g.cycle_count >= max_cycle_count:
        print "[Sail] TIMEOUT: exceeded %s cycles" % (max_cycle_count, )
        raise SystemExit
    return ()

cyclecount = 0

def get_cycle_count(machine, _):
    return bitvector.Integer.fromint(machine.g.cycle_count)

def sail_get_verbosity(machine, _):
    return machine.g.sail_verbosity
