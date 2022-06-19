from pydrofoil.supportcode import *
from pydrofoil import elf

from rpython.rlib.objectmodel import we_are_translated
from rpython.rlib.jit import elidable, unroll_safe, hint
from rpython.rlib.rarithmetic import r_uint, intmask
from rpython.rlib.rrandom import Random

import time

class BlockMemory(object):
    ADDRESS_BITS_BLOCK = 20 # 1 MB
    BLOCK_SIZE = 2 ** ADDRESS_BITS_BLOCK
    BLOCK_MASK = BLOCK_SIZE - 1

    def __init__(self):
        self.blocks = {}

    @unroll_safe
    def read(self, start_addr, num_bytes):
        block = self.get_block(start_addr >> self.ADDRESS_BITS_BLOCK)
        start_addr = start_addr & self.BLOCK_MASK
        assert 1 <= num_bytes <= 8
        value = 0
        for i in range(num_bytes - 1, -1, -1):
            value = value << 8
            value = value | ord(block[start_addr + i])
        return r_uint(value)

    def get_block(self, block_addr):
        if block_addr in self.blocks:
            return self.blocks[block_addr]
        res = self.blocks[block_addr] = ["\x00"] * self.BLOCK_SIZE
        return res

    @unroll_safe
    def write(self, start_addr, num_bytes, value):
        block = self.get_block(start_addr >> self.ADDRESS_BITS_BLOCK)
        start_addr = start_addr & self.BLOCK_MASK
        assert 1 <= num_bytes <= 8
        for i in range(num_bytes):
            block[start_addr + i] = chr(value & 0xFF)
            value = value >> 8

def write_mem(addr, content): # write a single byte
    g.mem.write(addr, 1, content)

def platform_read_mem(read_kind, addr_size, addr, n):
    n = n.toint()
    assert n <= 8
    assert addr_size == 64
    res = g.mem.read(addr.val, n)
    print "read mem", addr.val, n, "=>", hex(res)
    return bitvector.GenericBitVector(n*8, rbigint.fromint(res))

def platform_write_mem(*args): import pdb;pdb.set_trace(); return 123

class Globals(object):
    pass

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

#unit load_reservation(addr)
#{
#  reservation = addr;
#  reservation_valid = true;
#  /* fprintf(stderr, "reservation <- %0" PRIx64 "\n", reservation); */
#  return UNIT;
#}

def speculate_conditional(_):
    return True

#static mach_bits check_mask(void)
#{
#  return (zxlen_val == 32) ? 0x00000000FFFFFFFF : -1;
#}
#
#bool match_reservation(mach_bits addr)
#{
#  mach_bits mask = check_mask();
#  bool ret = reservation_valid && (reservation & mask) == (addr & mask);
#  /*
#  fprintf(stderr, "reservation(%c): %0" PRIx64 ", key=%0" PRIx64 ": %s\n",
#	  reservation_valid ? 'v' : 'i', reservation, addr, ret ? "ok" : "fail");
#  */
#
#  return ret;
#}
#
#unit cancel_reservation()
#{ /* fprintf(stderr, "reservation <- none\n"); */
#  reservation_valid = false;
#  return UNIT;
#}
#
#unit plat_term_write(mach_bits s)
#{ char c = s & 0xff;
#  plat_term_write_impl(c);
#  return UNIT;
#}

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
        outriscv.z_set_Misa_C(outriscv.r.zmisa, 0)

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
            write_mem(addr, fourbytes & 0xff) # XXX endianness?
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

def process_args(argv):
    return argv[1]

def main(argv):
    from pydrofoil.test import outriscv
    # Initialize model so that we can check or report its architecture.
    outriscv.model_init()
    file = process_args(argv)
    #init_logs()

    t1 = time.time()
    entry = load_sail(file)
    init_sail(entry)
    t2 = time.time()

    run_sail()
    #flush_logs()
    #close_logs()

def run_sail():
    from pydrofoil.test import outriscv
    step_no = 0
    insn_cnt = 0
    total_insns = 0
    insn_limit = 100000
    do_show_times = True

    interval_start = time.time()

    while (insn_limit == 0 or total_insns < insn_limit): # xxx removed zhtif_done
        # run a Sail step
        print step_no, outriscv.r.zPC
        stepped = outriscv.func_zstep(step_no)
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
            outriscv.ztick_clock(())
            outriscv.ztick_platform(())

def load_sail(fn):
    from pydrofoil.test import outriscv
    with open(fn, "rb") as f:
        img = elf.elf_reader(f, is_64bit=outriscv.l.zxlen_val == 64)

    sections = img.get_sections()
    entrypoint = -1
    mem = BlockMemory()
    g.mem = mem

    for section in sections:
        start_addr = section.addr
        for i, data in enumerate(section.data):
            mem.write(start_addr + i, 1, ord(data))
        if section.name == ".tohost":
            entrypoint = intmask(section.addr)

    entrypoint = 0x80000000 # XXX hardcoded for now
    print "tohost located at 0x%x" % (entrypoint, )
    assert entrypoint == 0x80000000 # XXX for now
    return entrypoint
