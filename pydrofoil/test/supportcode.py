from rpython.rlib import rarithmetic
from rpython.rlib.rbigint import rbigint
from pydrofoil import bitvector

class Memory(object):
    pass

MEM = Memory()
MEM.rom = [rarithmetic.r_uint(0)]

def load_rom(fn):
    f = open(fn, "rb")
    content = f.read()
    f.close()
    l = []
    data = rarithmetic.r_uint(0)
    i = 0
    for byte in content:
        if i & 1 == 0:
            data = rarithmetic.r_uint(ord(byte))
        else:
            l.append(rarithmetic.r_uint(ord(byte) << 8) | data)
        i += 1
    MEM.rom = l[:]

def my_read_rom(addr):
    if addr < len(MEM.rom):
        return rarithmetic.r_uint(MEM.rom[addr])
    return rarithmetic.r_uint(0)

MEM.mem = [rarithmetic.r_uint(0)] * 65536

def my_read_mem(addr):
    return MEM.mem[addr]
def my_write_mem(addr, val):
    MEM.mem[addr] = val
def not_(b):
    return not b
def and_bool(a, b):
    return not b
def my_print_debug(cycle_count, pc, a, d):
    print "PC: %s, A: %s, D: %s, cycle count: %s" % (pc, a, d, cycle_count)

# generic helpers

def zero_extend(a, b):
    return a

def add_bits_int(a, b):
    return a.add_int(b)

def fast_signed(op, n):
    if n == 64:
        return rarithmetic.intmask(op)
    assert n > 0
    u1 = rarithmetic.r_uint(1)
    m = u1 << (n - 1)
    op = op & ((u1 << n) - 1) # mask off higher bits to be sure
    return rarithmetic.intmask((op ^ m) - m)

def raise_type_error():
    raise TypeError

def eq_int(a, b):
    assert isinstance(a, rbigint)
    return a.eq(b)

def safe_rshift(n, shift):
    if shift >= 64:
        return rarithmetic.r_uint(0)
    return n >> shift
