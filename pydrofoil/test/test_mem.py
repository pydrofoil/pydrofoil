import pytest

import os
import random
from pydrofoil import mem
from rpython.rlib.rarithmetic import r_uint, intmask

elffile = os.path.join(os.path.dirname(__file__), "rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl")
dhryelffile = os.path.join(os.path.dirname(__file__), "dhrystone.riscv")

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


def test_invalidation_logic():
    m = mem.FlatMemory()
    m.write(0, 8, 0x0a1b2c3d4e5f6789)
    m.write(8, 8, 0xdeaddeaddeaddead)
    assert m._aligned_read(0, 8, False) == 0x0a1b2c3d4e5f6789
    assert set(m.status) == {mem.MEM_STATUS_NORMAL}
    v1 = m.version

    m.mark_page_executable(0)
    v2 = m.version
    assert v1 is not v2
    assert m.status[:512] == [mem.MEM_STATUS_IMMUTABLE] * 512
    assert set(m.status[512:]) == {mem.MEM_STATUS_NORMAL}

    m.mark_page_executable(1)
    v3 = m.version
    assert v2 is v3
    assert m.status[:512] == [mem.MEM_STATUS_IMMUTABLE] * 512
    assert set(m.status[512:]) == {mem.MEM_STATUS_NORMAL}

    m.write(8, 8, 0xdeaddeaddeaddead) # same value!
    v3 = m.version
    assert v2 is v3
    assert m.status[:512] == [mem.MEM_STATUS_IMMUTABLE] * 512
    assert set(m.status[512:]) == {mem.MEM_STATUS_NORMAL}

    for val in [1, 2, 3, 4]:
        m.write(8, 8, val) # different value!
        assert m.status[:512] == [mem.MEM_STATUS_MUTABLE] * 512
        assert set(m.status[512:]) == {mem.MEM_STATUS_NORMAL}
    v4 = m.version
    assert v4 is not v3

    m.mark_page_executable(0) # re-marking as executable does nothing
    assert m.status[:512] == [mem.MEM_STATUS_MUTABLE] * 512
    assert set(m.status[512:]) == {mem.MEM_STATUS_NORMAL}
    v5 = m.version
    assert v4 is v5

def test_immutable_reads():
    m = mem.FlatMemory()
    m.write(0, 8, 0x0a1b2c3d4e5f6789)
    m.write(8, 8, 0xdeaddeaddeaddead)
    m.mark_page_executable(0)

    assert m.read(0, 8, True) == 0x0a1b2c3d4e5f6789
    assert m.read(8, 8, True) == 0xdeaddeaddeaddead

    read_offsets = []
    def _immutable_read(offset, v):
        read_offsets.append(offset)
        return offset
    m._immutable_read = _immutable_read

    for i in range(512):
        assert m.read(i * 8, 8, True) == i
    assert read_offsets == range(512)

def test_elf_reader_mark_immutable():
    from pydrofoil import elf
    mem1 = mem.FlatMemory(False)
    mem2 = mem.FlatMemory(False)
    m = mem.SplitMemory(mem1, 0, mem1.size, mem2, 0x80000000, mem2.size)
    with open(dhryelffile, "rb") as f:
        entrypoint = elf.elf_read_process_image(m, f)
    assert mem2.status.count(mem.MEM_STATUS_IMMUTABLE) == 2048
    assert mem2.status[0x2000>>3] == mem.MEM_STATUS_IMMUTABLE
    assert mem2.status[0x28ae>>3] == mem.MEM_STATUS_IMMUTABLE
