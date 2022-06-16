from rpython.rlib import rarithmetic
from rpython.rlib.rbigint import rbigint

def my_read_rom(addr):
    l = [
    0b0000000000000010, # @2
    0b1110110000010000, # D=A
    0b0000000000000011, # @3
    0b1110000010010000, # D=D+A
    0b0000000000000000, # @0
    0b1110001100001000, # M=D
    ]
    if addr < len(l):
        return rarithmetic.r_uint(l[addr])
    return rarithmetic.r_uint(0)
mem = [0] * 65536
def my_read_mem(addr):
    return mem[addr]
def my_write_mem(addr, val):
    mem[addr]=val
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
    return a.add(b)

def fast_signed(op, n):
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
