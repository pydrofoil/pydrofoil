import os

from pydrofoil.supportcode import *
from pydrofoil.supportcode import _platform_read_mem_slowpath, _platform_write_mem_slowpath
from pydrofoil.bitvector import Integer
from pydrofoil import elf
from pydrofoil import mem as mem_mod

from rpython.rlib.nonconst import NonConstant
from rpython.rlib.objectmodel import we_are_translated, always_inline, specialize
from rpython.rlib.jit import JitDriver, promote
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
from rpython.rlib.rrandom import Random
from rpython.rlib import jit
from rpython.rlib import debug as rdebug
from rpython.rlib import rsignal

import time

class ExitNow(Exception):
    pass

VERSION = "0.0.1-alpha0"

with open(os.path.join(os.path.dirname(__file__), "riscv_model_version")) as f:
    SAIL_RISCV_VERSION = f.read().strip()


@unwrap("o o o i o")
def write_mem(machine, write_kind, addr_size, addr, n, data):
    assert addr_size in (64, 32)
    assert data.size() == n * 8
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        mem.write(addr, n, data.touint())
    else:
        _platform_write_mem_slowpath(machine, mem, write_kind, addr, n, data)
    return True

@unwrap("o o o i o")
def write_mem_exclusive(machine, write_kind, addr_size, addr, n, data):
    assert addr_size in (64, 32)
    assert data.size() == n * 8
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        mem.write(addr, n, data.touint())
    else:
        _platform_write_mem_slowpath(machine, mem, write_kind, addr, n, data)
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

# rough memory layout:
# | rom | clint | .... | ram <htif inside> ram

@jit.not_in_trace
def _observe_addr_range(machine, addr, width, ranges):
    index = _find_index(ranges, addr, width)
    jit.promote(machine.g)._mem_addr_range_next = index

@jit.elidable
def _get_likely_addr_range(g, ranges):
    # not really at all elidable, but it does not matter. the result is only
    # used to produce some guards
    return g._mem_addr_range_next

def _find_index(ranges, addr, width):
    for index, (start, stop) in enumerate(ranges):
        if start <= addr and addr + width < stop:
            return index
    return -1

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
    jit.promote(width)
    _observe_addr_range(machine, addr, width, g._mem_ranges)
    range_index = _get_likely_addr_range(g, g._mem_ranges)
    if range_index < 0 or width > 8:
        return
    # the next line produces two guards
    if g._mem_ranges[range_index][0] <= addr and addr < g._mem_ranges[range_index][1] - width:
        if width == 1:
            mask = 0
        elif width == 2:
            mask = 0b1
        elif width == 4:
            mask = 0b11
        elif width == 8:
            mask = 0b111
        else:
            return
        jit.promote(addr & ((r_uint(1)<<63) | mask) == 0)
    return

class Globals(object):
    _immutable_fields_ = [
        'config_print_platform?', 'config_print_mem_access?',
        'config_print_reg?', 'config_print_instr?', 'config_print_rvfi?',
        'rv_clint_base?', 'rv_clint_size?', 'rv_htif_tohost?',
        'rv_rom_base?', 'rv_rom_size?', 'mem?',
        'rv_ram_base?', 'rv_ram_size?',
        'rv_enable_dirty_update?', 'rv_enable_misaligned?',
        'rv_insns_per_tick?',
        '_mem_ranges?[*]',
        'rv64'
    ]

    def __init__(self, rv64=True):
        self.rv64 = rv64
        self._mem_addr_range_next = -1
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
        self.rv_enable_bext                 = True
        self.rv_enable_svinval              = True
        self.rv_enable_zicboz               = True
        self.rv_enable_zicbom               = True
        self.rv_enable_zcb                  = True
        self.rv_enable_writable_fiom        = True
        self.rv_mtval_has_illegal_inst_bits = False

        self.rv_ram_base = r_uint(0x80000000)
        self.rv_ram_size = r_uint(0x4000000)

        self.rv_rom_base = r_uint(0x1000)
        self.rv_rom_size = r_uint(0x100)
        self.rv_cache_block_size_exp = 6
        self.rv_writable_hpm_counters = r_uint(0xFFFFFFFF)

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
        self.config_print_rvfi = False

        self.cpu_hz = 1000000000 # 1 GHz

    def _init_ranges(self):
        self._mem_ranges = [
            (intmask(self.rv_rom_base), intmask(self.rv_rom_base + self.rv_rom_size)),
            (intmask(self.rv_clint_base), intmask(self.rv_clint_base + self.rv_clint_size)),
            (intmask(self.rv_ram_base), intmask(self.rv_htif_tohost)),
            (intmask(self.rv_htif_tohost), intmask(self.rv_htif_tohost + 16)),
            (intmask(self.rv_htif_tohost + 16), intmask(self.rv_ram_base + self.rv_ram_size)),
        ]
        for a, b in self._mem_ranges:
            assert b >= 8

    def _create_dtb(self):
        from pydrofoil.dtb import DeviceTree
        if self.rv64:
            isa_spec = b"rv64imac"
            mmu_spec = b"sv39"
        else:
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


DEFAULT_RSTVEC = 0x00001000

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

def sys_enable_bext(machine, _):
    return machine.g.rv_enable_bext

def sys_enable_svinval(machine, _):
    return machine.g.rv_enable_svinval

def sys_enable_zcb(machine, _):
    return machine.g.rv_enable_svinval

def sys_enable_zicboz(machine, _):
    return machine.g.rv_enable_zicboz

def sys_enable_zicbom(machine, _):
    return machine.g.rv_enable_zicbom

def sys_writable_hpm_counters(machine, _):
    return machine.g.rv_writable_hpm_counters

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

def plat_cache_block_size_exp(machine, _):
    return machine.g.rv_cache_block_size_exp

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

def speculate_conditional(machine, _):
    return True

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

def instr_announce(machine, _):
    return ()

# sim stuff

@specialize.argtype(0)
def init_sail(machine, elf_entry):
    machine.init_model()
    return init_sail_reset_vector(machine, elf_entry)

@specialize.argtype(0)
def is_32bit_model(machine):
    return not machine.rv64

@specialize.argtype(0)
def init_sail_reset_vector(machine, entry):
    RST_VEC_SIZE = 8
    reset_vec = [ # 32 bit entries
        r_uint(0x297),                                      # auipc  t0,0x0
        r_uint(0x28593 + (RST_VEC_SIZE * 4 << 20)),         # addi   a1, t0, &dtb
        r_uint(0xf1402573),                                 # csrr   a0, mhartid
        r_uint(0x0182a283)  # lw     t0,24(t0)
        if is_32bit_model(machine) else
        r_uint(0x0182b283), # ld     t0,24(t0)
        r_uint(0x28067),                                    # jr     t0
        r_uint(0),
        r_uint(entry & 0xffffffff),
        r_uint(entry >> 32),
    ]


    rv_rom_base = DEFAULT_RSTVEC
    addr = r_uint(rv_rom_base)
    for i, fourbytes in enumerate(reset_vec):
        for j in range(4):
            machine.g.mem.write(addr, 1, fourbytes & 0xff)
            #write_mem(machine, addr, fourbytes & 0xff) # little endian
            addr += 1
            fourbytes >>= 8
        assert fourbytes == 0
    if machine.g.dtb:
        for i, char in enumerate(machine.g.dtb):
            machine.g.mem.write(addr, 1, r_uint(ord(char)))
            #write_mem(machine, addr, r_uint(ord(char)))
            addr += 1

    align = 0x1000
    # zero-fill to page boundary
    rom_end = r_uint((addr + align - 1) / align * align)
    for i in range(intmask(addr), rom_end):
        #write_mem(machine, addr, 0)
        machine.g.mem.write(addr, 1, 0)
        addr += 1

    # set rom size
    rv_rom_size = rom_end - rv_rom_base
    if machine.g.rv_rom_size != rv_rom_size:
        machine.g.rv_rom_size = rv_rom_size

    # boot at reset vector
    return r_uint(rv_rom_base)

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

Run the Pydrofoil RISC-V emulator on elf_file.

--rv32                          run emulator in 32bit mode
-l/--inst-limit <limit>         exit after limit instructions have been executed
--instructions-per-tick <num>   tick the emulated clock every num instructions (default: 100)
--verbose                       print a detailed trace of every instruction executed
--print-kips                    print kip/s every 2**20 instructions
--jit <options>                 set JIT options (try --jit help for details)
--dump <file>                   load elf file disassembly from file
-b/--device-tree-blob <file>    load dtb from file (usually not needed, Pydrofoil has a dtb built-in)
--disable-vext                  disable vector extension
-d/--enable-dirty-update        enable dirty update
-m/--enable-misaligned          enable misagligned memory accesses
-i/--mtval-has-illegal-inst-bits
--ram-size <num>                set emulated RAM size (in MiB)
--version                       print the version of pydrofoil-riscv
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
    jit.set_param(None, "trace_limit", 20000)
    if parse_flag(argv, "--help"):
        print_help(argv[0])
        return 0

    version = parse_flag(argv, "--version")
    if version:
        print "pydrofoil-riscv %s (Sail model version: %s)" % (VERSION, SAIL_RISCV_VERSION)
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

    enable_misaligned = parse_flag(argv, "-m", "--enable-misaligned")
    enable_dirty_update = parse_flag(argv, "-d", "--enable-dirty-update")
    mtval_has_illegal_inst_bits = parse_flag(argv, "-i", "--mtval-has-illegal-inst-bits")

    disable_vext = parse_flag(argv, "--disable-vext")

    enable_zfinx = parse_flag(argv, "--enable-zfinx")
    enable_writable_fiom = parse_flag(argv, "--enable-writable-fiom")
    enable_svinval = parse_flag(argv, "--enable-svinval")
    enable_zcb = parse_flag(argv, "--enable-zcb")
    enable_zicbom = parse_flag(argv, "--enable-zicbom")
    enable_zicboz = parse_flag(argv, "--enable-zicboz")

    ram_size = parse_args(argv, "-z", "--ram-size")

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
    if ram_size:
        ram_size = int(ram_size)
        print "setting ram-size to %s MiB" % ram_size
        machine.g.rv_ram_size = r_uint(ram_size << 20)
    init_mem(machine)
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
    if enable_misaligned:
        machine.g.rv_enable_misaligned = True
    if enable_dirty_update:
        machine.g.rv_enable_dirty_update = True
    if mtval_has_illegal_inst_bits:
        machine.g.rv_mtval_has_illegal_inst_bits = True

    if not verbose:
        machine.g.config_print_instr = False
        machine.g.config_print_reg = False
        machine.g.config_print_mem_access = False
        machine.g.config_print_platform = False
    entry = load_sail(machine, file)
    machine.set_pc(init_sail(machine, entry))
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

    machine.g._init_ranges()

    for i in range(iterations):
        machine.run_sail(limit, print_kips)
        if i:
            machine.set_pc(init_sail(machine, entry))
    #flush_logs()
    #close_logs()
    return 0

def get_printable_location(pc, do_show_times, insn_limit, tick, g):
    if tick:
        return "TICK 0x%x" % (pc, )
    if g.dump_dict and pc in g.dump_dict:
        return "0x%x: %s" % (pc, g.dump_dict[pc])
    return hex(pc)

def init_mem(machine, memwrappercls=None):
    g = machine.g
    oldmem = g.mem
    if oldmem:
        oldmem.close()
    mem1 = mem_mod.FlatMemory(False)
    mem2 = mem_mod.FlatMemory(False, g.rv_ram_size)
    mem = mem_mod.SplitMemory(mem1, 0, mem1.size, mem2, g.rv_ram_base, g.rv_ram_size)
    if memwrappercls is not None:
        mem = memwrappercls(mem)
    g.mem = mem

def load_sail(machine, fn):
    g = machine.g
    mem = machine.g.mem
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

def patch_checked_mem_function(outriscv, name):
    func = getattr(outriscv, name)
    varnames = func.func_code.co_varnames
    if "read" in name:
        assert varnames[:5] == ('machine', 'zt', 'zpriv', 'zpaddr', 'zwidth')
        def patched(machine, zt, zpriv, zpaddr, zwidth, *args):
            executable_flag = outriscv.Union_zAccessTypezIuzK_zExecutezIuzK.check_variant(zt)
            promote_addr_region(machine, zpaddr, zwidth, executable_flag)
            return func(machine, zt, zpriv, zpaddr, zwidth, *args)
        patched.func_name += "_" + func.func_name
        setattr(outriscv, name, patched)
    else:
        assert "write" in name
        assert varnames[:3] == ('machine', 'zpaddr', 'zwidth')
        def patched(machine, zpaddr, zwidth, *args):
            promote_addr_region(machine, zpaddr, zwidth, False)
            return func(machine, zpaddr, zwidth, *args)
        patched.func_name += "_" + func.func_name
        setattr(outriscv, name, patched)


def patch_tlb(outriscv):
    func = outriscv.func_ztranslate_TLB_hit
    def translate_tlb_hit(machine, zsv_params, zasid, zptb, zvAddr, zac, zpriv, zmxr, zdo_sum, zext_ptw, ztlb_index, zent):
        mask = jit.promote(zent.zvAddrMask)
        jit.record_exact_value(zent.zvMatchMask, ~mask)
        if zac is outriscv.Union_zAccessTypezIuzK_zExecutezIuzK.singleton:
            jit.record_exact_value(zent.zpAddr & mask, r_uint(0))
        res = func(machine, zsv_params, zasid, zptb, zvAddr, zac, zpriv, zmxr, zdo_sum, zext_ptw, ztlb_index, zent)
        return res
    outriscv.func_ztranslate_TLB_hit = translate_tlb_hit


def get_main(outriscv, rv64):
    if "g" not in RegistersBase._immutable_fields_:
        RegistersBase._immutable_fields_.append("g")

    Globals._pydrofoil_enum_read_ifetch_value = outriscv.Enum_zread_kind.zRead_ifetch

    if rv64:
        prefix = "rv64"
    else:
        prefix = "rv32"

    def get_printable_location(pc, do_show_times, insn_limit, tick, need_step_no, g):
        if tick:
            return "TICK 0x%x" % (pc, )
        suffix = ''
        if need_step_no:
            suffix = ' need_step'
        if g.dump_dict and pc in g.dump_dict:
            return "%s 0x%x: %s%s" % (prefix, pc, g.dump_dict[pc], suffix)
        return "%s 0x%x%s" % (prefix, pc, suffix)

    driver = JitDriver(
        get_printable_location=get_printable_location,
        greens=['pc', 'do_show_times', 'insn_limit', 'tick', 'need_step_no', 'g'],
        reds=['insn_cnt', 'machine'],
        virtualizables=['machine'],
        name=prefix,
        is_recursive=True)

    for name in dir(outriscv):
        if name.startswith("func_zchecked_mem_"):
            patch_checked_mem_function(outriscv, name)
    if rv64:
        patch_tlb(outriscv)

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
        _virtualizable_ = ['_reg_zminstret', '_reg_zPC', '_reg_zinstbits', '_reg_znextPC', '_reg_zmstatus', '_reg_zmip', '_reg_zmie', '_reg_zsatp', '_reg_zx1', '_reg_zx15']

        def __init__(self):
            outriscv.Machine.__init__(self)
            self.g = Globals(rv64=rv64)

        def set_pc(self, value):
            self._reg_zPC = value

        def tick_clock(self):
            return outriscv.func_ztick_clock(self, ())

        def tick_platform(self):
            return outriscv.func_ztick_platform(self, ())

        def init_model(self):
            return outriscv.func_zinit_model(self, ())

        def step(self, *args):
            return outriscv.func_zstep(self, *args)

        def disassemble_last_instruction(self):
            instbits = self._reg_zinstbits
            if instbits & 0b11 != 0b11: # compressed
                ast = outriscv.func_zencdec_compressed_backwards(
                    self, instbits)
            else:
                ast = outriscv.func_zext_decode(
                    self, instbits)
            return outriscv.func_zassembly_forwards(
                self, ast)

        def run_sail(self, insn_limit, do_show_times):
            self.step_no = 0
            # we update self.step_no only every TICK, *unless*:
            # - we want to continually print kps
            # - we want to print every instruction
            # - we are less than one TICK away from the insn_limit
            need_step_no = do_show_times or self.g.config_print_instr or (insn_limit and insn_limit - self.step_no < self.g.rv_insns_per_tick)
            insn_cnt = 0
            tick = False

            self.g.interval_start = self.g.total_start = time.time()
            prev_pc = 0
            g = self.g

            while 1:
                driver.jit_merge_point(pc=self._reg_zPC, tick=tick,
                        insn_limit=insn_limit, need_step_no=need_step_no, insn_cnt=insn_cnt,
                        do_show_times=do_show_times, machine=self, g=g)
                if self._reg_zhtif_done or (insn_limit != 0 and need_step_no and self.step_no >= insn_limit):
                    break
                jit.promote(self.g)
                if tick:
                    if not need_step_no:
                        # self.step_no wasn't updated since the last tick
                        self.step_no += insn_cnt
                    if insn_cnt == g.rv_insns_per_tick:
                        insn_cnt = 0
                        self.tick_clock()
                        self.tick_platform()
                    else:
                        assert do_show_times and (self.step_no & 0xfffff) == 0
                        curr = time.time()
                        print "kips:", 0x100000 / 1000. / (curr - g.interval_start)
                        g.interval_start = curr
                    tick = False
                    need_step_no = do_show_times or self.g.config_print_instr or (insn_limit and insn_limit - self.step_no < self.g.rv_insns_per_tick)
                    continue
                # run a Sail step
                prev_pc = self._reg_zPC
                jit.promote(self._reg_zmstatus.zbits)
                jit.promote(self._reg_zmisa.zbits)
                if need_step_no:
                    step_no = Integer.fromint(self.step_no)
                else:
                    step_no = None
                stepped = self.step(step_no)
                if self.have_exception:
                    print "ended with exception!"
                    print self.current_exception
                    print "from", self.throw_location
                    raise ValueError
                rv_insns_per_tick = g.rv_insns_per_tick
                if stepped:
                    if jit.we_are_jitted():
                        disassemble_current_inst(prev_pc, self)

                    if need_step_no:
                        self.step_no += 1
                    if rv_insns_per_tick:
                        insn_cnt += 1

                tick_cond = (do_show_times and (self.step_no & 0xffffffff) == 0) | (
                        rv_insns_per_tick and insn_cnt == rv_insns_per_tick)
                if tick_cond:
                    tick = True
                elif prev_pc >= self._reg_zPC: # backward jump
                    if we_are_translated():
                        p = rsignal.pypysig_getaddr_occurred()
                        if p.c_value < 0:
                            # ctrl-c was pressed
                            break
                    driver.can_enter_jit(pc=self._reg_zPC, tick=tick,
                            insn_limit=insn_limit, need_step_no=need_step_no, insn_cnt=insn_cnt,
                            do_show_times=do_show_times, machine=self, g=g)
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
            print "Instructions: %s" % (self.step_no, )
            print "Total time (s): %s" % (interval_end - self.g.total_start)
            print "Perf: %s Kips" % (self.step_no / 1000. / (interval_end - self.g.total_start), )
            if ctrlc:
                raise ExitNow


    Machine.rv64 = rv64
    Machine.__name__ += "64" if rv64 else "32"

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
