from pydrofoil.supportcode import *
from pydrofoil.bitvector import Integer
from pydrofoil import elf

from rpython.rlib.objectmodel import we_are_translated, always_inline
from rpython.rlib.jit import elidable, unroll_safe, hint, JitDriver, promote
from rpython.rlib import jit
from rpython.rlib.rarithmetic import r_uint, intmask
from rpython.rlib.rrandom import Random

import time

MEM_STATUS_IMMUTABLE = 'i'
MEM_STATUS_NORMAL = 'n'
MEM_STATUS_MUTABLE = 'm'

class Version(object):
    pass

class Block(object):
    _immutable_fields_ = ['data', 'status', 'version?']
    PAGE_BITS = 9
    PAGE_SIZE = 1 << 9
    PAGE_MASK = PAGE_SIZE - 1

    def __init__(self, size):
        self.version = Version()
        self.data = [r_uint(0)] * size
        self.status = [MEM_STATUS_NORMAL] * size

    def write_word(self, block_offset, value):
        if self.status[block_offset] == MEM_STATUS_IMMUTABLE:
            oldval = self.data[block_offset]
            if oldval != value:
                self._invalidate(block_offset)
        self.data[block_offset] = value

    def _invalidate(self, block_offset):
        print "invalidating", block_offset
        pagestart = block_offset & ~self.PAGE_MASK
        self.version = Version()
        for bo in range(pagestart, pagestart + self.PAGE_MASK + 1):
            self.status[bo] = MEM_STATUS_MUTABLE

    def read_word(self, block_offset, is_constant_addr=False):
        if is_constant_addr:
            status = self._get_status_page(block_offset, self.version)
            if status == MEM_STATUS_IMMUTABLE:
                return self._immutable_read(block_offset, self.version)
        return self.data[block_offset]

    @jit.elidable_promote('1,2')
    def _immutable_read(self, block_offset, version):
        assert version is self.version
        return self.data[block_offset]

    @jit.elidable_promote('1,2')
    def _get_status_page(self, block_offset, version):
        assert version is self.version
        return self.status[block_offset]

    def mark_executable(self, block_offset):
        status = self._get_status_page(block_offset, self.version)
        # if it's immutable, or already discovered to me mutable, don't do
        # anything
        if status == MEM_STATUS_IMMUTABLE or status == MEM_STATUS_MUTABLE:
            return
        self._mark_page_immutable(block_offset)

    def _mark_page_immutable(self, block_offset):
        pagestart = block_offset & ~self.PAGE_MASK
        self.version = Version()
        for bo in range(pagestart, pagestart + self.PAGE_MASK + 1):
            assert self.status[bo] != MEM_STATUS_MUTABLE
            self.status[bo] = MEM_STATUS_IMMUTABLE


class BlockMemory(object):
    ADDRESS_BITS_BLOCK = 20 # 1 MB
    BLOCK_SIZE = 2 ** ADDRESS_BITS_BLOCK
    BLOCK_MASK = BLOCK_SIZE - 1

    def __init__(self):
        self.blocks = {}
        self.last_block = None
        self.last_block_addr = r_uint(0)

    def get_block(self, block_addr):
        last_block = self.last_block
        if last_block is not None and block_addr == self.last_block_addr:
            block = last_block
        else:
            block = self._get_block(block_addr)
            self.last_block = block
            self.last_block_addr = block_addr
        return block

    @elidable
    def _get_block(self, block_addr):
        if block_addr in self.blocks:
            return self.blocks[block_addr]
        res = self.blocks[block_addr] = Block(self.BLOCK_SIZE // 8)
        return res

    def is_aligned(self, addr, num_bytes):
        if num_bytes == 1:
            return True
        elif num_bytes == 2:
            return addr & 0b1 == 0
        elif num_bytes == 4:
            return addr & 0b11 == 0
        elif num_bytes == 8:
            return addr & 0b111 == 0
        else:
            assert 0, "invalid num_bytes"

    @always_inline
    def _split_addr(self, start_addr, num_bytes):
        block_addr = start_addr >> self.ADDRESS_BITS_BLOCK
        block = self.get_block(block_addr)
        start_addr = start_addr & self.BLOCK_MASK
        block_offset = start_addr >> 3
        inword_addr = start_addr & 0b111
        # little endian
        if num_bytes == 8:
            mask = r_uint(0) - 1
        else:
            mask = (r_uint(1) << (num_bytes * 8)) - 1
        return block, block_offset, inword_addr, mask

    def read(self, start_addr, num_bytes):
        if not self.is_aligned(start_addr, num_bytes):
            # not aligned! slow path
            return self._unaligned_read(start_addr, num_bytes)
        return self._aligned_read(start_addr, num_bytes)

    def _aligned_read(self, start_addr, num_bytes):
        block, block_offset, inword_addr, mask = self._split_addr(start_addr, num_bytes)
        data = block.read_word(block_offset, jit.isconstant(start_addr))
        if num_bytes == 8:
            assert inword_addr == 0
            return data
        return (data >> (inword_addr * 8)) & mask

    @unroll_safe
    def _unaligned_read(self, start_addr, num_bytes):
        value = r_uint(0)
        for i in range(num_bytes - 1, -1, -1):
            value = value << 8
            value = value | self._aligned_read(start_addr + i, 1)
        return value

    def write(self, start_addr, num_bytes, value):
        if not self.is_aligned(start_addr, num_bytes):
            # not aligned! slow path
            return self._unaligned_write(start_addr, num_bytes, value)
        return self._aligned_write(start_addr, num_bytes, value)

    def _aligned_write(self, start_addr, num_bytes, value):
        block, block_offset, inword_addr, mask = self._split_addr(start_addr, num_bytes)
        if num_bytes == 8:
            assert inword_addr == 0
            block.write_word(block_offset, value)
            return
        assert value & ~mask == 0
        olddata = block.read_word(block_offset)
        mask <<= inword_addr * 8
        value <<= inword_addr * 8
        block.write_word(block_offset, (olddata & ~mask) | value)

    @unroll_safe
    def _unaligned_write(self, start_addr, num_bytes, value):
        for i in range(num_bytes):
            self._aligned_write(start_addr + i, 1, value & 0xff)
            value = value >> 8
        assert not value

    def mark_executable(self, addr):
        block, block_offset, _, _ = self._split_addr(addr, 1)
        block.mark_executable(block_offset)


def write_mem(addr, content): # write a single byte
    g.mem.write(addr, 1, content)
    return True

def platform_read_mem(read_kind, addr_size, addr, n):
    n = n.toint()
    assert n <= 8
    assert addr_size == 64
    res = g.mem.read(addr.touint(), n)
    return bitvector.from_ruint(n*8, res)

def platform_write_mem(write_kind, addr_size, addr, n, data):
    n = n.toint()
    assert n <= 8
    assert addr_size == 64
    assert data.size == n * 8
    g.mem.write(addr.touint(), n, data.touint())
    return True

class Globals(object):
    _immutable_fields_ = ['mem?', 'rv_rom_size?']

g = Globals()
g.mem = None
g.rv_enable_pmp                  = False
g.rv_enable_zfinx                = False
g.rv_enable_rvc                  = True
g.rv_enable_next                 = False
g.rv_enable_writable_misa        = True
g.rv_enable_fdext                = True
g.rv_enable_dirty_update         = False
g.rv_enable_misaligned           = False
g.rv_mtval_has_illegal_inst_bits = False

g.rv_ram_base = r_uint(0x80000000)
g.rv_ram_size = r_uint(0x4000000)

g.rv_rom_base = r_uint(0x1000)
g.rv_rom_size = r_uint(0x100)

g.random = Random(1)

DEFAULT_RSTVEC = 0x00001000

def rv_16_random_bits():
    # pseudo-random for determinism for now
    return r_uint(g.random.genrand32()) & r_uint(0xffff)

g.rv_clint_base = r_uint(0x2000000)
g.rv_clint_size = r_uint(0xc0000)

g.rv_htif_tohost = r_uint(0x80001000)
g.rv_insns_per_tick = r_uint(100)

g.dtb = None

g.term_fd = 1

# C externs

def sys_enable_rvc(_):
    return g.rv_enable_rvc

def sys_enable_next(_):
    return g.rv_enable_next

def sys_enable_fdext(_):
    return g.rv_enable_fdext

def sys_enable_zfinx(_):
    return g.rv_enable_zfinx

def sys_enable_writable_misa(_):
    return g.rv_enable_writable_misa

def plat_enable_dirty_update(_):
    return g.rv_enable_dirty_update

def plat_enable_misaligned_access(_):
    return g.rv_enable_misaligned

def plat_mtval_has_illegal_inst_bits(_):
    return g.rv_mtval_has_illegal_inst_bits

def plat_enable_pmp(_):
    return g.rv_enable_pmp

def plat_ram_base(_):
    return g.rv_ram_base

def plat_ram_size(_):
    return g.rv_ram_size

def plat_rom_base(_):
    return g.rv_rom_base

def plat_rom_size(_):
    return g.rv_rom_size

# Provides entropy for the scalar cryptography extension.
def plat_get_16_random_bits(_):
    return rv_16_random_bits()

def plat_clint_base(_):
    return g.rv_clint_base

def plat_clint_size(_):
    return g.rv_clint_size

g.reservation = r_uint(0)
g.reservation_valid = False

def load_reservation(addr):
    g.reservation = addr
    g.reservation_valid = True
    print "reservation <- 0x%x" % (addr, )
    return ()

def speculate_conditional(_):
    return True

def check_mask():
    from pydrofoil.test import outriscv
    return r_uint(0x00000000FFFFFFFF) if outriscv.l.zxlen_val == 32 else r_uint(0xffffffffffffffff)

def match_reservation(addr):
    mask = check_mask()
    ret = g.reservation_valid and ((g.reservation & mask) == (addr & mask))
    return ret

def cancel_reservation(_):
    g.reservation_valid = False
    return ()

def plat_term_write(s):
    import os
    os.write(g.term_fd, chr(s & 0xff))
    return ()

def plat_insns_per_tick(_):
    pass

def plat_htif_tohost(_):
    return g.rv_htif_tohost

def memea(len, n):
    return ()


# sim stuff

def plat_term_write_impl(c):
    os.write(1, c)

def init_sail(elf_entry):
    from pydrofoil.test import outriscv
    outriscv.func_zinit_model(())
    init_sail_reset_vector(elf_entry)
    if not g.rv_enable_rvc:
        # this is probably unnecessary now; remove
        outriscv.func_z_set_Misa_C(outriscv.r.zmisa, 0)

def is_32bit_model():
    return False # for now

def init_sail_reset_vector(entry):
    from pydrofoil.test import outriscv
    RST_VEC_SIZE = 8
    reset_vec = [ # 32 bit entries
        r_uint(0x297),                                      # auipc  t0,0x0
        r_uint(0x28593 + (RST_VEC_SIZE * 4 << 20)),         # addi   a1, t0, &dtb
        r_uint(0xf1402573),                                 # csrr   a0, mhartid
        r_uint(0x0182a283)  # lw     t0,24(t0)
        if is_32bit_model() else
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
            write_mem(addr, fourbytes & 0xff) # little endian
            addr += 1
            fourbytes >>= 8
        assert fourbytes == 0
    assert not g.dtb
    #if (dtb && dtb_len) {
    #  for (size_t i = 0; i < dtb_len; i++)
    #    write_mem(addr++, dtb[i]);
    #}

    align = 0x1000
    # zero-fill to page boundary
    rom_end = r_uint((addr + align - 1) / align * align)
    for i in range(intmask(addr), rom_end):
        write_mem(addr, 0)
        addr += 1

    # set rom size
    g.rv_rom_size = rom_end - rv_rom_base
    # boot at reset vector
    outriscv.r.zPC = r_uint(rv_rom_base)

def main(argv):
    from pydrofoil.test import outriscv
    from rpython.rlib import jit

    # crappy jit argument handling
    for i in range(len(argv)):
        if argv[i] == "--jit":
            if len(argv) == i + 1:
                print "missing argument after --jit"
                return 2
            jitarg = argv[i + 1]
            del argv[i:i+2]
            jit.set_user_param(None, jitarg)
            break

    # Initialize model so that we can check or report its architecture.
    outriscv.model_init()
    if len(argv) == 1:
        print("usage: %s <elf file>" % (argv[0], ))
        return 1
    file = argv[1]
    if len(argv) == 3:
        iterations = int(argv[2])
    else:
        iterations = 1
    #init_logs()

    entry = load_sail(file)
    for i in range(iterations):
        init_sail(entry)
        run_sail()
        if i:
            outriscv.model_init()
    #flush_logs()
    #close_logs()
    return 0

def get_printable_location(pc):
    from pydrofoil.test import outriscv
    ast = outriscv.func_zdecode(g.last_instr)
    dis = outriscv.func_zprint_insn(ast)
    return hex(pc) + ": " + dis

driver = JitDriver(
    get_printable_location=get_printable_location,
    greens=['pc'], reds='auto')


def run_sail():
    from pydrofoil.test import outriscv
    step_no = 0
    insn_cnt = 0
    total_insns = 0
    insn_limit = 100000
    do_show_times = True

    interval_start = time.time()

    while not outriscv.r.zhtif_done and (insn_limit == 0 or total_insns < insn_limit):
        driver.jit_merge_point(pc=outriscv.r.zPC)
        jit.promote(outriscv.r.zPC)
        # run a Sail step
        #print step_no, hex(outriscv.r.zPC)
        stepped = outriscv.func_zstep(Integer.fromint(step_no))
        if stepped:
            step_no += 1
            insn_cnt += 1
            total_insns += 1

        if do_show_times and (total_insns & 0xfffff) == 0:
            curr = time.time()
            print "kips:", 0x100000 / (interval_start - curr)
            interval_start = curr

        if insn_cnt == g.rv_insns_per_tick:
            insn_cnt = 0
            outriscv.func_ztick_clock(())
            outriscv.func_ztick_platform(())
    interval_end = time.time()
    if outriscv.r.zhtif_exit_code == 0:
        print "SUCCESS"
    else:
        print "FAILURE", outriscv.r.zhtif_exit_code
        raise ValueError
    if do_show_times:
        print "Instructions: %s" % (total_insns, )
        print "Perf: %s Kips" % (total_insns / 1000. / (interval_end - interval_start), )


def load_sail(fn):
    from pydrofoil.test import outriscv
    with open(fn, "rb") as f:
        img = elf.elf_reader(f, is_64bit=outriscv.l.zxlen_val == 64)

    sections = img.get_sections()
    entrypoint = -1
    mem = BlockMemory()
    g.mem = mem

    for section in sections:
        start_addr = r_uint(section.addr)
        for i, data in enumerate(section.data):
            mem.write(start_addr + i, 1, r_uint(ord(data)))
        if section.name == ".tohost":
            entrypoint = intmask(section.addr)

    entrypoint = 0x80000000 # XXX hardcoded for now
    print "tohost located at 0x%x" % (entrypoint, )
    assert entrypoint == 0x80000000 # XXX for now
    return entrypoint

# printing

g.config_print_instr = True
g.config_print_reg = True
g.config_print_mem_access = True
g.config_print_platform = True
g.config_print_rvfi = False

def print_string(prefix, msg):
    print prefix, msg
    return ()

def print_instr(s):
    print s
    return ()

print_reg = print_instr
print_mem_access = print_reg
print_platform = print_reg

def get_config_print_instr(_):
    return g.config_print_instr
def get_config_print_reg(_):
    return g.config_print_reg
def get_config_print_mem(_):
    return g.config_print_mem_access
def get_config_print_platform(_):
    return g.config_print_platform

def get_main():
    from pydrofoil.test import outriscv
    orig = outriscv.func_zdecode
    def func_zdecode(x):
        promote(x)
        g.last_instr = x
        return orig(x)
    outriscv.func_zdecode = func_zdecode
    orig_phys_mem_read = outriscv.func_zphys_mem_read
    def func_zphys_mem_read(t, paddr, *args):
        execute = isinstance(t, outriscv.Union_zAccessType_zExecute)
        if execute:
            promote(paddr)
            g.mem.mark_executable(paddr)
        res = orig_phys_mem_read(t, paddr, *args)
        if execute:
            if isinstance(res, outriscv.Union_zMemoryOpResult_zMemValuez3z8z5bvzCz0z5unitz9):
                val = res.utup0
                if isinstance(val, bitvector.SmallBitVector):
                    promote(val.val)
        return res
    outriscv.func_zphys_mem_read = func_zphys_mem_read
    return main
