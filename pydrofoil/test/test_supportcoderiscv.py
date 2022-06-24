import random
from pydrofoil.test import supportcoderiscv
from rpython.rlib.rarithmetic import r_uint, intmask

class TBM(supportcoderiscv.BlockMemory):
    ADDRESS_BITS_BLOCK = 7 # to flush out corner cases and have less massive prints
    BLOCK_SIZE = 2 ** ADDRESS_BITS_BLOCK
    BLOCK_MASK = BLOCK_SIZE - 1
    

def test_mem_write_read():
    mem = TBM()
    addresses = range(100) + [mem.BLOCK_MASK + i for i in range(-100, 100)]
    for size in [1, 2, 4, 8]:
        for base_addr in addresses:
            for consec in range(1, 20):
                data = [r_uint(random.randrange(2**(size*8))) for _ in range(consec)]
                for offset in range(consec):
                    mem.write(r_uint(base_addr + offset * size), size, data[offset])
                for offset in range(consec):
                    assert mem.read(r_uint(base_addr + offset * size), size) == data[offset]

