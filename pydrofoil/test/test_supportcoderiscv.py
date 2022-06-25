import random
from pydrofoil.test import supportcoderiscv
from rpython.rlib.rarithmetic import r_uint, intmask
from rpython.rlib import jit

class TBM(supportcoderiscv.BlockMemory):
    ADDRESS_BITS_BLOCK = 7 # to flush out corner cases and have less massive prints
    BLOCK_SIZE = 2 ** ADDRESS_BITS_BLOCK
    BLOCK_MASK = BLOCK_SIZE - 1
    

def test_mem_write_read():
    mem = TBM()
    assert mem.read(r_uint(1), 1) == 0
    addresses = range(100) + [mem.BLOCK_MASK + i for i in range(-100, 100)]
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

def test_invalidation_logic():
    mem = supportcoderiscv.BlockMemory()
    mem.write(0, 8, 0x0a1b2c3d4e5f6789)
    mem.write(8, 8, 0xdeaddeaddeaddead)
    block = mem.blocks[0]
    assert block.read_word(0, False) == 0x0a1b2c3d4e5f6789
    assert set(block.status) == {supportcoderiscv.MEM_STATUS_NORMAL}
    v1 = block.version

    mem.mark_executable(0)
    v2 = block.version
    assert v1 is not v2
    assert block.status[:512] == [supportcoderiscv.MEM_STATUS_IMMUTABLE] * 512
    assert set(block.status[512:]) == {supportcoderiscv.MEM_STATUS_NORMAL}

    mem.mark_executable(1)
    v3 = block.version
    assert v2 is v3
    assert block.status[:512] == [supportcoderiscv.MEM_STATUS_IMMUTABLE] * 512
    assert set(block.status[512:]) == {supportcoderiscv.MEM_STATUS_NORMAL}

    mem.write(8, 8, 0xdeaddeaddeaddead) # same value!
    assert block.status[:512] == [supportcoderiscv.MEM_STATUS_IMMUTABLE] * 512
    assert set(block.status[512:]) == {supportcoderiscv.MEM_STATUS_NORMAL}

    for val in [1, 2, 3, 4]:
        mem.write(8, 8, val) # different value!
        assert block.status[:512] == [supportcoderiscv.MEM_STATUS_MUTABLE] * 512
        assert set(block.status[512:]) == {supportcoderiscv.MEM_STATUS_NORMAL}
    v4 = block.version
    assert v4 is not v3

def test_immutable_reads():
    mem = supportcoderiscv.BlockMemory()
    mem.write(0, 8, 0x0a1b2c3d4e5f6789)
    mem.write(8, 8, 0xdeaddeaddeaddead)
    mem.mark_executable(0)

    block = mem.blocks[0]
    assert block.read_word(0, True) == 0x0a1b2c3d4e5f6789
    assert block.read_word(1, True) == 0xdeaddeaddeaddead

    read_offsets = []
    def _immutable_read(offset, v):
        read_offsets.append(offset)
        return offset
    block._immutable_read = _immutable_read

    for i in range(512):
        assert block.read_word(i, True) == i
    assert read_offsets == range(512)

