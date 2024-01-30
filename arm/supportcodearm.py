import time
from rpython.rlib import jit
from rpython.rlib import rsignal
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

PARAMETERS = jit.PARAMETERS.copy()
PARAMETERS['trace_limit'] = 50000
PARAMETERS['enable_opts'] = "intbounds:rewrite:virtualize:string:pure:earlyforce:heap"
PARAMETERS['pureop_historylength'] = 256

JIT_HELP = ["Advanced JIT options:", '', '']
JIT_HELP.extend([" %s=<value>\n     %s (default: %s)\n" % (
    key, jit.PARAMETER_DOCS[key], value)
    for key, value in PARAMETERS.items()]
)
JIT_HELP.extend([" off", "    turn JIT off", "", " help", "    print this page"])
JIT_HELP = "\n".join(JIT_HELP)


def get_main(outarm):
    #Globals._pydrofoil_enum_read_ifetch_value = outarm.Enum_zread_kind.zRead_ifetch

    Machine = outarm.Machine
    def get_printable_location(pc):
        return hex(pc)

    driver = jit.JitDriver(
        get_printable_location=get_printable_location,
        greens=['pc'],
        reds=['machine'],
        name="arm",
        is_recursive=True)

    step = outarm.func_zstep_model

    def jitstep(machine, *args):
        if machine.g.sail_verbosity:
            return step(machine, *args)
        # otherwise just do the main work here
        while 1:
            jit.promote(machine.g)
            promote_pc = machine.g.promote_pc
            if promote_pc:
                pc = machine._reg_z_PC
            else:
                pc = 0
            driver.jit_merge_point(machine=machine, pc=pc)
            jit.promote(machine.g)
            if machine.g.promote_pc:
                jit.promote(pc)
            step(machine, ())
            if machine.have_exception:
                return ()
            cycle_count(machine, ())
    outarm.func_zstep_model = jitstep

    setinstr = outarm.func_z__SetThisInstrDetails
    def jitsetinstr(machine, enc, opcode, cond):
        # approach: promote the top 12 bits of opcode, but do it 4 bits at a
        # time, to make sure we don't just get a linear search. start from the
        # highest bits, because that's where the instruction-specific bits are
        jit.jit_debug("arm-opcode", opcode)
        jit.promote(opcode & 0xf0000000)
        jit.promote(opcode & 0x0f000000)
        jit.promote(opcode & 0x00f00000)
        # this would not be needed with knownbits but well
        jit.promote(opcode >> 21)
        #jit.promote(opcode & 0x000f0000)
        #jit.promote(opcode & 0x0000f000)
        #jit.promote(opcode & 0x00000f00)
        #jit.promote(opcode & 0x000000f0)
        #jit.promote(opcode & 0x0000000f)
        return setinstr(machine, enc, opcode, cond)
    outarm.func_z__SetThisInstrDetails = jitsetinstr

    for name, func in outarm.__dict__.iteritems():
        if "IMPDEF" in name:
            func = objectmodel.specialize.arg(1)(func)
            objectmodel.always_inline(func)
        if "func_zMem_read__1" in name:
            jit.unroll_safe(func)
        if "func_zMem_set__1" in name:
            jit.unroll_safe(func)
        if "MemSingle_" in name:
            jit.unroll_safe(func)
        if "S1Translate" in name:
            jit.unroll_safe(func)
        if "S2Translate" in name:
            jit.unroll_safe(func)
        if "S1Walk" in name:
            jit.unroll_safe(func)
        if "MaybeZeroSVEUppers" in name:
            jit.unroll_safe(func)
        if "DataMemZero" in name:
            jit.unroll_safe(func)
        if "instrs_integer_arithmetic" in name:
            jit.unroll_safe(func)
        if "ArchitectureReset" in name:
            jit.dont_look_inside(func)

    def main(argv):
        try:
            return _main(argv)
        except CycleLimitReached:
            return 0
        except CtrlCPressed:
            return 1
        except OSError as e:
            errno = e.errno
            try:
                msg = os.strerror(errno)
            except ValueError:
                msg = 'ERROR [errno %d]' % (errno, )
            else:
                msg = 'ERROR [errno %d] %s' % (errno, msg)
            print msg
            return -1
        except IOError as e:
            print "ERROR [errno %s] %s" % (e.errno, e.strerror or '')
            return -2
        except BaseException as e:
            if objectmodel.we_are_translated():
                from rpython.rlib.debug import debug_print_traceback
                debug_print_traceback()
                print "unexpected internal exception (please report a bug): %r" % (e, )
                print "internal traceback dumped to stderr"
                return -3
            else:
                raise

    def _main(argv):
        from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
        from arm import supportcodearm

        jit.set_param(driver, "enable_opts", "intbounds:rewrite:virtualize:string:pure:earlyforce:heap")
        jit.set_param(driver, "trace_limit", 50000)
        jit.set_param(driver, "pureop_historylength", 256)

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

        jitopts = parse_args(argv, "--jit")
        if jitopts:
            if jitopts == "help":
                print JIT_HELP
                return 0
            try:
                jit.set_user_param(None, jitopts)
            except ValueError:
                print "invalid jit option"
                return 1
        machine.g.promote_pc = parse_flag(argv, "--promote-pc")

        configs = parse_args(argv, "-C", "--model-config", many=True)

        repeat = parse_args(argv, "--repeat")
        repeats = 1
        if repeat:
            repeats = parseint(repeat)
            print "will do", repeats, "repetitions"
        if len(argv) != 1:
            print "unrecognized option:", argv[1]
            return 1
        print "done, starting main"
        for i in range(repeats):
            outarm.func_zinitializze_registers(machine, ())
            machine.g.mem.__init__()
            for binary in binaries:
                offset, filename = binary.split(',', 2)
                offset = parseint(offset)
                if check_file_missing(filename):
                    return -1
                print "loading binary blob", filename, "at offset", hex(offset)
                load_raw_single(machine, r_uint(offset), filename)
            for config in configs:
                configname, value = config.split('=', 2)
                value = parseint(value)
                print "setting config value", configname, "to", hex(value)
                outarm.func_z__SetConfig(machine, configname, bitvector.Integer.fromint(value))

            machine.g.cycle_count = 0
            if objectmodel.we_are_translated():
                rsignal.pypysig_setflag(rsignal.SIGINT)
            t1 = time.time()
            try:
                outarm.func_zmain(machine, ())
            except CycleLimitReached:
                if i == repeats - 1:
                    raise
            except Exception as e:
                if not objectmodel.we_are_translated():
                    import pdb;pdb.xpm()
                raise
            finally:
                t2 = time.time()
                print "ran for %s(s), %s instructions, KIPS: %s" % (t2 - t1, machine.g.cycle_count, machine.g.cycle_count / (t2 - t1) / 1000)
        return 0
    main.mod = outarm
    return main


class Globals(BaseGlobals):
    _immutable_fields_ = ['max_cycle_count?', 'verbosity?', 'promote_pc?', 'sail_verbosity?']
    def __init__(self):
        BaseGlobals.__init__(self)
        self.cycle_count = 0
        self.max_cycle_count = 0
        self.sail_verbosity = 0
        self.promote_pc = False


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

class CycleLimitReached(Exception):
    pass

class CtrlCPressed(Exception):
    pass

def cycle_count(machine, _):
    machine.g.cycle_count += 1
    max_cycle_count = machine.g.max_cycle_count
    p = rsignal.pypysig_getaddr_occurred()
    if max_cycle_count and machine.g.cycle_count >= max_cycle_count:
        print "[Sail] TIMEOUT: exceeded %s cycles" % (max_cycle_count, )
        raise CycleLimitReached
    if objectmodel.we_are_translated() and p.c_value < 0:
        print "[Sail] CTRL-C was pressed"
        raise CtrlCPressed
    return ()

cyclecount = 0

def get_cycle_count(machine, _):
    return bitvector.Integer.fromint(machine.g.cycle_count)

def sail_get_verbosity(machine, _):
    return machine.g.sail_verbosity

make_dummy("emulator_read_tag")
make_dummy("emulator_write_tag")

@unwrap("o o o i")
def read_mem_ifetch(machine, request, addr_size, addr, n):
    from pydrofoil.supportcode import _platform_read_mem_slowpath
    assert addr_size in (64, 32)
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        res = mem.read(addr, n, executable_flag=True)
        return bitvector.SmallBitVector(n*8, res)
    else:
        return _platform_read_mem_slowpath(machine, mem, 0, addr, n)

@unwrap("o o o i")
def read_mem_exclusive(machine, request, addr_size, addr, n):
    return read_mem_o_o_o_i(machine, request, addr_size, addr, n)

@unwrap("o o o i")
def read_mem(machine, request, addr_size, addr, n):
    from pydrofoil.supportcode import _platform_read_mem_slowpath
    assert addr_size in (64, 32)
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        res = mem.read(addr, n, executable_flag=False)
        return bitvector.SmallBitVector(n*8, res)
    else:
        return _platform_read_mem_slowpath(machine, mem, 0, addr, n)

@unwrap("o o o i o")
def write_mem(machine, request, addr_size, addr, n, data):
    from pydrofoil.supportcode import _platform_write_mem_slowpath
    assert addr_size in (64, 32)
    assert data.size() == n * 8
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        mem.write(addr, n, data.touint())
    else:
        _platform_write_mem_slowpath(machine, mem, 0, addr, n, data)
    return True

write_mem_exclusive = write_mem
