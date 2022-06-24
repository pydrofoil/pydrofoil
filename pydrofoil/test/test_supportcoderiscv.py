import random
from pydrofoil.test import supportcoderiscv
from rpython.rlib.rarithmetic import r_uint, intmask

class TBM(supportcoderiscv.BlockMemory):
    ADDRESS_BITS_BLOCK = 7 # to flush out corner cases and have less massive prints
    BLOCK_SIZE = 2 ** ADDRESS_BITS_BLOCK
    BLOCK_MASK = BLOCK_SIZE - 1
    

def test_mem():
    mem = TBM()
    addresses = range(100) + [mem.BLOCK_MASK + i for i in range(-100, 100)]
    for size in [1, 2, 4, 8]:
        for addr in addresses:
            data = r_uint(random.randrange(2**(size*8)))
            mem.write(r_uint(addr), size, data)
            assert mem.read(r_uint(addr), size) == data

