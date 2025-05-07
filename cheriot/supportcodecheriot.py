import os

from pydrofoil.supportcode import *
from pydrofoil.bitvector import Integer
from pydrofoil import elf
from pydrofoil import mem as mem_mod

from rpython.rlib.nonconst import NonConstant
from rpython.rlib.objectmodel import we_are_translated, always_inline, specialize
from rpython.rlib.jit import JitDriver, promote
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
from rpython.rlib.rrandom import Random
from rpython.rlib import jit
from rpython.rlib import rsignal
from rpython.rlib import debug as rdebug

import time

class ExitNow(Exception):
    pass

VERSION = "0.0.1-alpha0"


def write_mem(machine, addr, content): # write a single byte
    jit.promote(machine.g).mem.write(addr, 1, content)
    return True

@always_inline
@unwrap("o o o i")
def platform_read_mem(machine, read_kind, addr_size, addr, n):
    assert n <= 8
    addr = addr.touint()
    res = jit.promote(machine.g).mem.read(addr, n)
    return bitvector.SmallBitVector(n*8, res) # breaking abstracting a bit, but much more efficient

def platform_read_mem_o_i_bv_i(machine, read_kind, addr_size, addr, n):
    return jit.promote(machine.g).mem.read(addr, n)

@always_inline
def platform_write_mem(machine, write_kind, addr_size, addr, n, data):
    n = n.toint()
    assert n <= 8
    assert addr_size == 64
    assert data.size() == n * 8
    jit.promote(machine.g).mem.write(addr.touint(), n, data.touint())
    return True

@always_inline
def read_tag_bool(machine, addr):
    addr <<= 3 # this is log2_cap_size in the cheriot model
    return machine.g.mem.read_tag_bit(addr)

@always_inline
def write_tag_bool(machine, addr, tag):
    addr <<= 3 # this is log2_cap_size in the cheriot model
    return machine.g.mem.write_tag_bit(addr, tag)


class Globals(object):
    _immutable_fields_ = [
        'config_print_platform?', 'config_print_mem_access?',
        'config_print_reg?', 'config_print_instr?', 'config_print_rvfi?',
        'config_print_exception?',
        'rv_clint_base?', 'rv_clint_size?', 'rv_htif_tohost?',
        'rv_rom_base?', 'rv_rom_size?', 'mem?',
        'rv_insns_per_tick?',
        '_mem_ranges?[*]',
    ]

    def __init__(self):
        self.mem = None
        self.rv_enable_pmp                  = False
        self.rv_enable_zfinx                = False
        self.rv_enable_rvc                  = True
        self.rv_enable_next                 = False
        self.rv_enable_writable_misa        = True
        self.rv_enable_fdext                = True
        self.rv_enable_dirty_update         = False
        self.rv_enable_misaligned           = False
        self.rv_enable_vext                 = True
        self.rv_enable_writable_fiom        = True
        self.rv_mtval_has_illegal_inst_bits = False

        self.rv_ram_base = r_uint(0x80000000)
        self.rv_ram_size = r_uint(0x4000000)

        self.rv_rom_base = r_uint(0x1000)
        self.rv_rom_size = r_uint(0x100)

        self.random = Random(1)

        self.rv_clint_base = r_uint(0x2000000)
        self.rv_clint_size = r_uint(0xc0000)

        self.rv_htif_tohost = r_uint(0x80001000)
        self.rv_insns_per_tick = 100

        self.dtb = None

        self.term_fd = 1

        self.reservation = r_uint(0)
        self.reservation_valid = False

        self.dump_dict = {}

        self.config_print_instr = True
        self.config_print_reg = True
        self.config_print_mem_access = True
        self.config_print_platform = True
        self.config_print_exception = True
        self.config_print_rvfi = False

        self.cpu_hz = 1000000000 # 1 GHz

    def _create_dtb(self):
        from pydrofoil.dtb import DeviceTree
        isa_spec = b"rv32imac"
        mmu_spec = b"sv32"
        d = DeviceTree()
        with d.begin_node(b""):
            d.add_property_u32(b"#address-cells", 2)
            d.add_property_u32(b"#size-cells", 2)
            d.add_property(b"compatible", b"ucbbar,spike-bare-dev")
            d.add_property(b"model", b"ucbbar,spike-bare")
            with d.begin_node(b"cpus"):
                d.add_property_u32(b"#address-cells", 1)
                d.add_property_u32(b"#size-cells", 0)
                d.add_property_u32(b"timebase-frequency", self.cpu_hz // self.rv_insns_per_tick)
                with d.begin_node(b"cpu@0"):
                    d.add_property(b"device_type", b"cpu")
                    d.add_property_u32(b"reg", 0)
                    d.add_property(b"status", b"okay")
                    d.add_property(b"compatible", b"riscv")
                    d.add_property(b"riscv,isa", isa_spec)
                    d.add_property(b"mmu-type", b"riscv," + mmu_spec)
                    d.add_property_u32(b"clock-frequency", self.cpu_hz)
                    with d.begin_node_with_handle(b"interrupt-controller") as CPU0_intc:
                        d.add_property_u32(b"#interrupt-cells", 1)
                        d.add_property_empty(b"interrupt-controller")
                        d.add_property(b"compatible", b"riscv,cpu-intc")
            with d.begin_node(b"memory@%x" % (self.rv_ram_base, )):
                d.add_property(b"device_type", b"memory")
                d.add_property_u64_list(b"reg", [self.rv_ram_base, self.rv_ram_size])
            with d.begin_node(b"soc"):
                d.add_property_u32(b"#address-cells", 2)
                d.add_property_u32(b"#size-cells", 2)
                d.add_property_list(b"compatible", [b"ucbbar,spike-bare-soc", b"simple-bus"])
                d.add_property_empty(b"ranges")
                with d.begin_node("clint@%x" % (self.rv_clint_base, )):
                    d.add_property(b"compatible", b"riscv,clint0")
                    d.add_property_u32_list(b"interrupts-extended", [CPU0_intc, 3, CPU0_intc, 7])
                    d.add_property_u64_list(b"reg", [self.rv_clint_base, self.rv_clint_size])
            with d.begin_node("htif"):
                d.add_property(b"compatible", b"ucb,htif0")
        self.dtb = d.to_binary()


def rv_16_random_bits(machine):
    # pseudo-random for determinism for now
    return r_uint(machine.g.random.genrand32()) & r_uint(0xffff)


# C externs

def sys_enable_rvc(machine, _):
    return machine.g.rv_enable_rvc

def sys_enable_next(machine, _):
    return machine.g.rv_enable_next

def sys_enable_fdext(machine, _):
    return machine.g.rv_enable_fdext

def sys_enable_zfinx(machine, _):
    return machine.g.rv_enable_zfinx

def sys_enable_writable_misa(machine, _):
    return machine.g.rv_enable_writable_misa

def plat_enable_dirty_update(machine, _):
    return machine.g.rv_enable_dirty_update

def plat_enable_misaligned_access(machine, _):
    return machine.g.rv_enable_misaligned

def plat_mtval_has_illegal_inst_bits(machine, _):
    return machine.g.rv_mtval_has_illegal_inst_bits

def plat_enable_pmp(machine, _):
    return machine.g.rv_enable_pmp

def plat_ram_base(machine, _):
    return machine.g.rv_ram_base

def plat_ram_size(machine, _):
    return machine.g.rv_ram_size

def plat_rom_base(machine, _):
    return machine.g.rv_rom_base

def plat_rom_size(machine, _):
    return machine.g.rv_rom_size

def sys_enable_vext(machine, _):
    return machine.g.rv_enable_vext

def sys_enable_writable_fiom(machine, _):
    return machine.g.rv_enable_writable_fiom

def sys_pmp_count(machine, _):
    return 0 # XXX
def sys_pmp_grain(machine, _):
    return 0 # XXX

def plat_uart_base(machine, _):
    return 0x10000000 # XXX make configurable or something
def plat_uart_size(machine, _):
    return 0x100

# Provides entropy for the scalar cryptography extension.
def plat_get_16_random_bits(machine, _):
    return rv_16_random_bits(machine)

def plat_clint_base(machine, _):
    return machine.g.rv_clint_base

def plat_clint_size(machine, _):
    return machine.g.rv_clint_size


def load_reservation(machine, addr):
    machine.g.reservation = addr
    machine.g.reservation_valid = True
    #print "reservation <- 0x%x" % (addr, )
    return ()

@specialize.argtype(0)
def check_mask(machine):
    return r_uint(0x00000000FFFFFFFF) if is_32bit_model(machine) else r_uint(0xffffffffffffffff)

def match_reservation(machine, addr):
    mask = check_mask(machine)
    ret = machine.g.reservation_valid and (machine.g.reservation & mask) == (addr & mask)
    return ret

def cancel_reservation(machine, _):
    machine.g.reservation_valid = False
    return ()

def plat_term_write(machine, s):
    import os
    os.write(machine.g.term_fd, chr(s & 0xff))
    return ()

def plat_insns_per_tick(machine, _):
    pass

def plat_htif_tohost(machine, _):
    return machine.g.rv_htif_tohost

def memea(len, n):
    return ()


# sim stuff

@specialize.argtype(0)
def init_sail(machine, elf_entry):
    machine.init_model()
    machine._reg_zPC = r_uint(elf_entry) # boot at elf entry

@specialize.argtype(0)
def is_32bit_model(machine):
    return True

def parse_dump_file(fn):
    with open(fn) as f:
        content = f.read()
    dump = {}
    section = '?'
    function = '?'
    for line in content.splitlines(False):
        line = line.strip()
        if not line:
            continue
        if line.startswith("Disassembly of section "):
            section = line[len("Disassembly of section "):]
        elif line.endswith(">:"):
            pos = line.rfind("<")
            if pos < 0:
                continue
            endpos = len(line) - 2
            assert endpos >= 0
            function = line[pos + 1: endpos]
        else:
            pos = line.find(":")
            if pos < 0:
                continue
            address = line[:pos]
            res = line[pos + 1:].strip()
            intaddress = r_uint(0)
            for c in address:
                charval = -1
                if '0' <= c <= '9':
                    charval = ord(c) - ord('0')
                elif 'a' <= c <= 'f':
                    charval = ord(c) - ord('a') + 10
                elif 'A' <= c <= 'F':
                    charval = ord(c) - ord('A') + 10
                else:
                    break
                intaddress = intaddress * r_uint(16) + r_uint(charval)
            else:
                dump[intaddress] = "%s %s %s" % (section, function, res)
    return dump

helptext = """
Usage: %s [options] <elf_file>

Run the CHERIoT emulator on elf_file.

--help                          print this information and exit
"""

def print_help(program):
    print helptext % program

JIT_HELP = ["Advanced JIT options:", '', '']
JIT_HELP.extend([" %s=<value>\n     %s (default: %s)\n" % (
    key, jit.PARAMETER_DOCS[key], value)
    for key, value in jit.PARAMETERS.items()]
)
JIT_HELP.extend([" off", "    turn JIT off", "", " help", "    print this page"])
JIT_HELP = "\n".join(JIT_HELP)

def print_help_jit():
    print JIT_HELP

def check_file_missing(fn):
    try:
        os.stat(fn)
    except OSError:
        print "ERROR: file does not exist: %s" % (fn, )
        return True
    return False

def main(argv, *machineclasses):
    try:
        return _main(argv, *machineclasses)
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
    except ExitNow:
        return -4
    except BaseException as e:
        if we_are_translated():
            from rpython.rlib.debug import debug_print_traceback
            debug_print_traceback()
            print "unexpected internal exception (please report a bug): %r" % (e, )
            print "internal traceback dumped to stderr"
            return -3
        else:
            raise

def _main(argv, *machineclasses):
    if parse_flag(argv, "--help"):
        print_help(argv[0])
        return 0

    blob = parse_args(argv, "-b", "--device-tree-blob")
    limit = 0
    str_limit = parse_args(argv, "-l", "--inst-limit")
    if str_limit:
        limit = int(str_limit)
        print "instruction limit", limit

    dump_file = parse_args(argv, "--dump")
    per_tick = parse_args(argv, "--instructions-per-tick")

    jitopts = parse_args(argv, "--jit")
    if jitopts:
        if jitopts == "help":
            print_help_jit()
            return 0
        try:
            jit.set_user_param(None, jitopts)
        except ValueError:
            print "invalid jit option"
            return 1

    disable_vext = parse_flag(argv, "--disable-vext")

    verbose = parse_flag(argv, "--verbose")

    print_kips = parse_flag(argv, "--print-kips")

    rv32 = parse_flag(argv, "--rv32")
    if rv32:
        assert len(machineclasses) == 2
        machinecls = machineclasses[1]
    else:
        machinecls = machineclasses[0]

    # Initialize model so that we can check or report its architecture.
    if len(argv) == 1:
        print_help(argv[0])
        return 1
    file = argv[1]
    if len(argv) == 3:
        iterations = int(argv[2])
    else:
        iterations = 1
    #init_logs()

    machine = machinecls()
    if blob:
        if check_file_missing(blob):
            return -1
        with open(blob, "rb") as f:
            machine.g.dtb = f.read()
    else:
        machine.g._create_dtb()
    if check_file_missing(file):
        return -1
    print "Running file", file

    if disable_vext:
        machine.g.rv_enable_vext = False

    if not verbose:
        machine.g.config_print_instr = False
        machine.g.config_print_reg = False
        machine.g.config_print_mem_access = False
        machine.g.config_print_platform = False
        machine.g.config_print_exception = False
    entry = load_sail(machine, file)
    init_sail(machine, entry)
    if dump_file:
        if check_file_missing(dump_file):
            return -1
        print "dump file", dump_file
        machine.g.dump_dict = parse_dump_file(dump_file)
    if per_tick:
        ipt = int(per_tick)
        machine.g.rv_insns_per_tick = ipt

    # prepare SIGINT signal handler
    if we_are_translated():
        rsignal.pypysig_setflag(rsignal.SIGINT)

    for i in range(iterations):
        machine.run_sail(limit, print_kips)
        if i:
            init_sail(machine, entry)
    #flush_logs()
    #close_logs()
    return 0



def load_sail(machine, fn):
    g = machine.g
    oldmem = g.mem
    if oldmem:
        oldmem.close()
    mem = mem_mod.TaggedFlatMemory(size=g.rv_ram_size, base_addr=g.rv_ram_base)
    #mem = mem_mod.TaggedBlockMemory()
    g.mem = mem
    with open(fn, "rb") as f:
        entrypoint = elf.elf_read_process_image(mem, f) # load process image
    with open(fn, "rb") as f:
        img = elf.elf_reader(f) # for the symbols

    g.rv_htif_tohost = r_uint(img.get_symbol('tohost'))
    print "tohost located at 0x%x" % g.rv_htif_tohost

    print "ELF Entry @ 0x%x" % entrypoint
    assert entrypoint == 0x80000000 # XXX for now
    return entrypoint

# printing


def print_instr(machine, s):
    if machine.g.config_print_instr:
        print s
    return ()

def print_reg(machine, s):
    if machine.g.config_print_reg:
        print s
    return ()

def print_mem_access(machine, s):
    if machine.g.config_print_mem_access:
        print s
    return ()

def print_platform(machine, s):
    if machine.g.config_print_platform:
        print s
    return ()

def get_config_print_instr(machine, _):
    return machine.g.config_print_instr
def get_config_print_reg(machine, _):
    return machine.g.config_print_reg
def get_config_print_mem(machine, _):
    return machine.g.config_print_mem_access
def get_config_print_platform(machine, _):
    return machine.g.config_print_platform
def get_config_print_exception(machine, _):
    return machine.g.config_print_exception

@specialize.argtype(0)
def promote_addr_region(machine, addr, width, executable_flag):
    g = jit.promote(machine.g)
    addr = intmask(addr)
    jit.jit_debug("promote_addr_region", width, executable_flag, jit.isconstant(width))
    if not jit.we_are_jitted() or not jit.isconstant(width):
        return
    if executable_flag:
        jit.promote(addr)
        jit.jit_debug("ram ifetch", intmask(addr))
        mem = jit.promote(machine.g).mem
        # read and ignore the result, the JIT will do the rest
        res = mem.read(r_uint(addr), width, executable_flag=True)
        return

def patch_checked_mem_function(outriscv, name):
    func = getattr(outriscv, name)
    varnames = func.func_code.co_varnames
    if "read" in name:
        assert varnames[:4] == ('machine', 'zt', 'zpaddr', 'zwidth')
        def patched(machine, zt, zpaddr, zwidth, *args):
            executable_flag = outriscv.Union_zAccessTypezIEext_access_typez5zK_zExecutezIEext_access_typez5zK.check_variant(zt)
            promote_addr_region(machine, zpaddr, zwidth, executable_flag)
            return func(machine, zt, zpaddr, zwidth, *args)
        patched.func_name += "_" + func.func_name
        setattr(outriscv, name, patched)
    else:
        assert "write" in name
        assert varnames[:4] == ('machine', 'zwk', 'zpaddr', 'zwidth')
        def patched(machine, zwk, zpaddr, zwidth, *args):
            promote_addr_region(machine, zpaddr, zwidth, False)
            return func(machine, zwk, zpaddr, zwidth, *args)
        patched.func_name += "_" + func.func_name
        setattr(outriscv, name, patched)


def get_main(outriscv):
    if "g" not in RegistersBase._immutable_fields_:
        RegistersBase._immutable_fields_.append("g")

    prefix = "cheriot"

    def get_printable_location(pc, do_show_times, insn_limit, tick, pcc_bits, g):
        if tick:
            return "TICK 0x%x" % (pc, )
        capstring = outriscv.func_zcapToString(None, outriscv.func_zcapBitsToCapability(None, True, pcc_bits))
        if g.dump_dict and pc in g.dump_dict:
            return "%s %s: %s" % (prefix, capstring, g.dump_dict[pc])
        return capstring

    driver = JitDriver(
        get_printable_location=get_printable_location,
        greens=['pc', 'do_show_times', 'insn_limit', 'tick', 'pcc_bits', 'g'],
        reds=['step_no', 'insn_cnt', 'machine'],
        virtualizables=['machine'],
        name=prefix,
        is_recursive=True)

    for name in dir(outriscv):
        if name.startswith("func_zchecked_mem_"):
            patch_checked_mem_function(outriscv, name)

    @jit.not_in_trace
    def disassemble_current_inst(pc, m):
        if rdebug.have_debug_prints_for('jit-log-opt'):
            instbits = m._reg_zinstbits
            if instbits & 0b11 != 0b11:
                # compressed instruction
                ast = outriscv.func_zencdec_compressed_backwards(m, m._reg_zinstbits)
            else:
                ast = outriscv.func_zext_decode(m, m._reg_zinstbits)
            dis = outriscv.func_zassembly_forwards(m, ast)
            m.g.dump_dict[pc] = dis

    class Machine(outriscv.Machine):
        _immutable_fields_ = ['g']
        _virtualizable_ = ['_reg_ztlb39', '_reg_ztlb48', '_reg_zminstret', '_reg_zPC', '_reg_znextPC', '_reg_zmstatus', '_reg_zmip', '_reg_zmie', '_reg_zsatp', '_reg_zx1', '_reg_zPCC', '_reg_znextPCC']

        def __init__(self):
            outriscv.Machine.__init__(self)
            self.g = Globals()

        def tick_clock(self):
            return outriscv.func_ztick_clock(self, ())

        def tick_platform(self):
            return outriscv.func_ztick_platform(self, ())

        def word_width_bytes(self, width):
            return outriscv.func_zword_width_bytes(self, width)

        def init_model(self):
            return outriscv.func_zinit_model(self, ())

        def step(self, *args):
            return outriscv.func_zstep(self, *args)

        def run_sail(self, insn_limit, do_show_times):
            step_no = 0
            insn_cnt = 0
            tick = False

            self.g.interval_start = self.g.total_start = time.time()
            prev_pc = 0
            g = self.g
            pcc_bits = outriscv.func_zcapToBits(self, self._reg_zPCC)

            while 1:
                driver.jit_merge_point(pc=self._reg_zPC, tick=tick,
                        insn_limit=insn_limit, step_no=step_no, insn_cnt=insn_cnt,
                        do_show_times=do_show_times, machine=self, g=g, pcc_bits=pcc_bits)


                if self._reg_zhtif_done or not (insn_limit == 0 or step_no < insn_limit):
                    break
                jit.promote(self.g)
                if tick:
                    if insn_cnt == g.rv_insns_per_tick:
                        insn_cnt = 0
                        self.tick_clock()
                        self.tick_platform()
                    else:
                        assert do_show_times and (step_no & 0xfffff) == 0
                        curr = time.time()
                        print "kips:", 0x100000 / 1000. / (curr - g.interval_start)
                        g.interval_start = curr
                    tick = False
                    pcc_bits = outriscv.func_zcapToBits(self, self._reg_zPCC)
                    continue
                # run a Sail step

                if jit.we_are_jitted():
                    # transfer the knowledge from the green pcc_bits to the real pcc register
                    self._reg_zPCC = outriscv.func_zcapBitsToCapability(self, True, pcc_bits)

                prev_pc = self._reg_zPC
                stepped = self.step(Integer.fromint(step_no))
                if self.have_exception:
                    print "ended with exception!"
                    print self.current_exception
                    print "from", self.throw_location
                    raise ValueError
                rv_insns_per_tick = g.rv_insns_per_tick
                if stepped:
                    if jit.we_are_jitted():
                        disassemble_current_inst(prev_pc, self)

                    step_no += 1
                    if rv_insns_per_tick:
                        insn_cnt += 1

                tick_cond = (do_show_times and (step_no & 0xffffffff) == 0) | (
                        rv_insns_per_tick and insn_cnt == rv_insns_per_tick)
                if tick_cond:
                    tick = True
                elif prev_pc >= self._reg_zPC: # backward jump
                    if we_are_translated():
                        p = rsignal.pypysig_getaddr_occurred()
                        if p.c_value < 0:
                            # ctrl-c was pressed
                            break
                    pcc_bits = outriscv.func_zcapToBits(self, self._reg_zPCC)
                    driver.can_enter_jit(pc=self._reg_zPC, tick=tick,
                            insn_limit=insn_limit, step_no=step_no, insn_cnt=insn_cnt,
                            do_show_times=do_show_times, machine=self, g=g, pcc_bits=pcc_bits)
                    continue
                pcc_bits = outriscv.func_zcapToBits(self, self._reg_zPCC)

            # loop end

            interval_end = time.time()
            p = rsignal.pypysig_getaddr_occurred()
            ctrlc = False
            if we_are_translated() and p.c_value < 0:
                print "CTRL-C was pressed"
                ctrlc = True
            elif self._reg_zhtif_exit_code == 0:
                print "SUCCESS"
            else:
                print "FAILURE:", self._reg_zhtif_exit_code
                if not we_are_translated():
                    raise ValueError
            print "Instructions: %s" % (step_no, )
            print "Total time (s): %s" % (interval_end - self.g.total_start)
            print "Perf: %s Kips" % (step_no / 1000. / (interval_end - self.g.total_start), )
            if ctrlc:
                raise ExitNow


    Machine.__name__ += "32"

    def bound_main(argv):
        return main(argv, Machine)
    bound_main._machinecls = Machine

    # a bit of micro-optimization
    # XXX add back later
    #always_inline(outriscv.func_zread_ram)
    #always_inline(outriscv.func_zphys_mem_read)
    #always_inline(outriscv.func_zwrite_ram)
    #always_inline(outriscv.func_zphys_mem_write)
    #always_inline(outriscv.func_zwithin_phys_mem)
    return bound_main
