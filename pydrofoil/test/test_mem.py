import pytest

import os
import random
from pydrofoil import mem
from rpython.rlib.rarithmetic import r_uint, intmask


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

def test_invalidation_logic():
    m = mem.FlatMemory()
    m.write(0, 8, 0x0a1b2c3d4e5f6789)
    m.write(8, 8, 0xdeaddeaddeaddead)
    assert m._aligned_read(0, 8, False) == 0x0a1b2c3d4e5f6789
    assert set(m.status) == {mem.MEM_STATUS_NORMAL}
    v1 = m.version

    assert m._aligned_read(0, 8, True) == 0x0a1b2c3d4e5f6789
    v2 = m.version
    # going from normal -> immutable does not change version
    assert v1 is v2
    assert m.status[0] == mem.MEM_STATUS_IMMUTABLE
    assert set(m.status[1:]) == {mem.MEM_STATUS_NORMAL}

    assert m._aligned_read(8, 8, True) == 0xdeaddeaddeaddead
    v3 = m.version
    assert v2 is v3
    assert m.status[:2] == [mem.MEM_STATUS_IMMUTABLE] * 2
    assert set(m.status[2:]) == {mem.MEM_STATUS_NORMAL}

    m.write(8, 8, 0xdeaddeaddeaddead) # same value!
    v3 = m.version
    assert v2 is v3
    assert m.status[:2] == [mem.MEM_STATUS_IMMUTABLE] * 2
    assert set(m.status[2:]) == {mem.MEM_STATUS_NORMAL}

    for val in [1, 2, 3, 4]:
        m.write(8, 8, val) # different value!
        assert m.status[:2] == [mem.MEM_STATUS_IMMUTABLE, mem.MEM_STATUS_MUTABLE]
        assert set(m.status[2:]) == {mem.MEM_STATUS_NORMAL}
    v4 = m.version
    assert v4 is not v3

    # re-reading as executable does not change the status
    assert m._aligned_read(8, 8, True) == 4
    assert m.status[:2] == [mem.MEM_STATUS_IMMUTABLE, mem.MEM_STATUS_MUTABLE]
    assert set(m.status[2:]) == {mem.MEM_STATUS_NORMAL}
    v5 = m.version
    assert v4 is v5

    # writing to a normal word does not change the status or the version
    m._aligned_write(16, 8, 0x17)
    assert m.status[:2] == [mem.MEM_STATUS_IMMUTABLE, mem.MEM_STATUS_MUTABLE]
    assert set(m.status[2:]) == {mem.MEM_STATUS_NORMAL}
    v6 = m.version
    assert v4 is v6


def test_immutable_reads():
    m = mem.FlatMemory()
    m.write(0, 8, 0x0a1b2c3d4e5f6789)
    m.write(8, 8, 0xdeaddeaddeaddead)

    assert m.read(0, 8, True) == 0x0a1b2c3d4e5f6789
    assert m.read(8, 8, True) == 0xdeaddeaddeaddead

    read_offsets = []
    def _immutable_read(offset, v):
        read_offsets.append(offset)
        return offset
    m._immutable_read = _immutable_read

    # reading anything as executable marks is immutable
    for i in range(512):
        assert m.read(i * 8, 8, True) == i
    assert read_offsets == range(512)

    # but not if its mutable
    del read_offsets[:]
    m.write(0, 8, 17)
    assert m.read(0, 8, True) == 17
    assert read_offsets == []

def test_block_caching():
    m = TBM()
    assert m.last_block_addr == r_uint(-1)
    m.write(r_uint(8), 8, r_uint(0x0102030405060708))
    assert m.last_block_addr == r_uint(0)
    assert m.last_block[8 >> 3] == r_uint(0x0102030405060708)
    block1 = m.last_block

    m.write(r_uint(0x10000008), 8, r_uint(0xfa11))
    assert m.last_block_addr == r_uint(0x200000)
    assert m.last_block[8 >> 3] == r_uint(0xfa11)
    block2 = m.last_block
    assert block2 is not block1

    assert m.read(r_uint(8), 8, False) == r_uint(0x0102030405060708)
    assert m.last_block_addr == r_uint(0)
    assert m.last_block is block1

    assert m.read(r_uint(0x10000008), 8, True) == r_uint(0xfa11)
    assert m.last_block_addr == r_uint(0)
    assert m.last_block is block1
    assert m.last_block_addr_executable == r_uint(0x200000)
    assert m.last_block_executable is block2

def test_block_caching_platform():
    from pydrofoil import supportcode, bitvector
    class FakeMachine(object):
        class g(object):
            _pydrofoil_enum_read_ifetch_value = 1
            mem = TBM()
    machine = FakeMachine()
    m = machine.g.mem
    m.write(r_uint(8), 8, r_uint(0x0102030405060708))
    block1 = m.last_block
    m.write(r_uint(0x10000008), 8, r_uint(0xfa11))
    block2 = m.last_block

    read_kind_normal = 0
    read_kind_ifetch = machine.g._pydrofoil_enum_read_ifetch_value
    assert supportcode.platform_read_mem(
        machine,
        read_kind_normal,
        64,
        bitvector.from_ruint(64, r_uint(8)),
        bitvector.Integer.fromint(8)).touint() == r_uint(0x0102030405060708)
    assert m.last_block_addr == r_uint(0)
    assert m.last_block is block1

    assert supportcode.platform_read_mem(
        machine,
        read_kind_ifetch,
        64,
        bitvector.from_ruint(64, r_uint(0x10000008)),
        bitvector.Integer.fromint(8)).touint() == r_uint(0xfa11)
    assert m.last_block_addr == r_uint(0)
    assert m.last_block is block1
    assert m.last_block_addr_executable == r_uint(0x200000)
    assert m.last_block_executable is block2
