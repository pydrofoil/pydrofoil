from rpython.rlib import rarithmetic
from rpython.rlib.rbigint import rbigint
from pydrofoil import bitvector
from pydrofoil.supportcode import *

# for nand2tetris CPU

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
def my_print_debug(cycle_count, pc, a, d):
    print "PC: %s, A: %s, D: %s, cycle count: %s" % (pc, a, d, cycle_count)

