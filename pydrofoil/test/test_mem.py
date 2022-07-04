import pytest

import os
import random
from pydrofoil import mem
from rpython.rlib.rarithmetic import r_uint, intmask

elffile = os.path.join(os.path.dirname(__file__), "rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl")

class TBM(mem.BlockMemory):
    ADDRESS_BITS_BLOCK = 7 # to flush out corner cases and have less massive prints
    BLOCK_SIZE = 2 ** ADDRESS_BITS_BLOCK
    BLOCK_MASK = BLOCK_SIZE - 1


@pytest.mark.parametrize("memcls", [TBM, mem.FlatMemory])
def test_mem_write_read(memcls):
    mem = memcls()
    assert mem.read(r_uint(1), 1) == 0
    addresses = range(100) + [TBM.BLOCK_MASK + i for i in range(-100, 100)]
    # cleck little endianness
    mem.write(r_uint(8), 8, r_uint(0x0102030405060708))
    assert mem.read(r_uint(8), 1) == r_uint(0x08)
    assert mem.read(r_uint(9), 1) == r_uint(0x07)
    assert mem.read(r_uint(10), 1) == r_uint(0x06)
    assert mem.read(r_uint(11), 1) == r_uint(0x05)
    assert mem.read(r_uint(12), 1) == r_uint(0x04)
    assert mem.read(r_uint(13), 1) == r_uint(0x03)
    assert mem.read(r_uint(14), 1) == r_uint(0x02)
    assert mem.read(r_uint(15), 1) == r_uint(0x01)
    for size in [1, 2, 4, 8]:
        for base_addr in addresses:
            for consec in range(1, 20):
                data = [r_uint(random.randrange(2**(size*8))) for _ in range(consec)]
                for offset in range(consec):
                    addr = r_uint(base_addr + offset * size)
                    mem.write(addr, size, data[offset])
                for offset in range(consec):
                    addr = r_uint(base_addr + offset * size)
                    assert mem.read(addr, size) == data[offset]
    mem.close()

def test_elf_reader():
    from pydrofoil import elf
    m = mem.BlockMemory()
    with open(elffile, "rb") as f:
        entrypoint = elf.elf_read_process_image(m, f)
    assert entrypoint == 0x80000000
    # used to be wrong in the segment reader
    assert m.read(0x0000000080000D42, 2) == 0x4e4c


