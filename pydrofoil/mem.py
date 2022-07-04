from rpython.rlib.nonconst import NonConstant
from rpython.rlib.objectmodel import we_are_translated, always_inline
from rpython.rlib.rarithmetic import r_uint, intmask
from rpython.rlib import jit
from rpython.rlib import rmmap
from rpython.rtyper.lltypesystem import rffi, lltype

class MemBase(object):
    def close(self):
        pass

    def is_aligned(self, addr, num_bytes=8):
        if num_bytes == 1:
            return True
        elif num_bytes == 2:
            return addr & 0b1 == 0
        elif num_bytes == 4:
            return addr & 0b11 == 0
        elif num_bytes == 8:
            return addr & 0b111 == 0
        else:
            assert 0, "invalid num_bytes"

    def read(self, start_addr, num_bytes, executable_flag=False):
        if not self.is_aligned(start_addr, num_bytes):
            # not aligned! slow path
            return self._unaligned_read(start_addr, num_bytes, executable_flag)
        return self._aligned_read(start_addr, num_bytes, executable_flag)

    def _aligned_read(self, start_addr, num_bytes, executable_flag):
        raise NotImplementedError

    @jit.unroll_safe
    def _unaligned_read(self, start_addr, num_bytes, executable_flag=False):
        value = r_uint(0)
        for i in range(num_bytes - 1, -1, -1):
            value = value << 8
            value = value | self._aligned_read(start_addr + i, 1, executable_flag)
        return value

    def write(self, start_addr, num_bytes, value):
        if not self.is_aligned(start_addr, num_bytes):
            # not aligned! slow path
            return self._unaligned_write(start_addr, num_bytes, value)
        return self._aligned_write(start_addr, num_bytes, value)

    def _aligned_write(self, start_addr, num_bytes, value):
        raise NotImplementedError

    @jit.unroll_safe
    def _unaligned_write(self, start_addr, num_bytes, value):
        for i in range(num_bytes):
            self._aligned_write(start_addr + i, 1, value & 0xff)
            value = value >> 8
        assert not value

    def mark_page_executable(self, start_addr):
        pass

MEM_STATUS_IMMUTABLE = 'i'
MEM_STATUS_NORMAL = 'n'
MEM_STATUS_MUTABLE = 'm'

class Version(object):
    pass


class FlatMemory(MemBase):
    SIZE = 64 * 1024 * 1024 // 8 # 64 MB

    PAGE_BITS = 9
    PAGE_SIZE = 1 << 9
    PAGE_MASK = PAGE_SIZE - 1

    _immutable_fields_ = ['mem?', 'version?', 'status']

    def __init__(self, mmap=False, size=SIZE):
        self.size = size
        if mmap:
            if we_are_translated():
                nc = NonConstant
            else:
                nc = lambda x: x
            mem = rmmap.c_mmap(
                nc(rmmap.NULL),
                nc(size),
                nc(rmmap.PROT_READ | rmmap.PROT_WRITE),
                nc(rmmap.MAP_PRIVATE | rmmap.MAP_ANONYMOUS),
                nc(-1), nc(0))
            mem = rffi.cast(rffi.UNSIGNEDP, mem)
        else:
            mem = [r_uint(0)] * (size // 8)
        self.mem = mem
        self.status = [MEM_STATUS_NORMAL] * size
        self.version = Version()

        self.mmap = mmap

    def close(self):
        if not self.mmap:
            return
        if we_are_translated():
            nc = NonConstant
        else:
            nc = lambda x: x
        rmmap.c_munmap_safe(rffi.cast(rffi.CCHARP, self.mem), nc(self.SIZE))
        self.mem = lltype.nullptr(rffi.UNSIGNEDP.TO)

    @always_inline
    def _split_addr(self, start_addr, num_bytes):
        mem_offset = start_addr >> 3
        inword_addr = start_addr & 0b111
        # little endian
        if num_bytes == 8:
            mask = r_uint(-1)
        else:
            mask = (r_uint(1) << (num_bytes * 8)) - 1
        return mem_offset, inword_addr, mask

    def _aligned_read(self, start_addr, num_bytes, executable_flag):
        if executable_flag:
            jit.promote(start_addr)
        mem_offset, inword_addr, mask = self._split_addr(start_addr, num_bytes)

        if (executable_flag and
                self._get_status_page(mem_offset, self.version) == MEM_STATUS_IMMUTABLE):
            data = self._immutable_read(mem_offset, self.version)
        else:
            data = self.mem[mem_offset]
            if executable_flag:
                jit.promote(data)
        if num_bytes == 8:
            assert inword_addr == 0
            return data
        return (data >> (inword_addr * 8)) & mask

    @jit.elidable_promote('all')
    def _immutable_read(self, mem_offset, version):
        assert version is self.version
        return self.mem[mem_offset]

    @jit.elidable_promote('all')
    def _get_status_page(self, mem_offset, version):
        assert version is self.version
        return self.status[mem_offset]

    def _aligned_write(self, start_addr, num_bytes, value):
        mem_offset, inword_addr, mask = self._split_addr(start_addr, num_bytes)
        if num_bytes == 8:
            assert inword_addr == 0
            self._write_word(mem_offset, value)
            return
        assert value & ~mask == 0
        olddata = self.mem[mem_offset]
        mask <<= inword_addr * 8
        value <<= inword_addr * 8
        self._write_word(mem_offset, (olddata & ~mask) | value)

    def _write_word(self, mem_offset, value):
        if self.status[mem_offset] == MEM_STATUS_IMMUTABLE:
            oldval = self.mem[mem_offset]
            if oldval != value:
                self._invalidate(mem_offset)
        self.mem[mem_offset] = value

    def _invalidate(self, mem_offset):
        print "invalidating", mem_offset
        pagestart = mem_offset & ~self.PAGE_MASK
        self.version = Version()
        for bo in range(pagestart, pagestart + self.PAGE_MASK + 1):
            self.status[bo] = MEM_STATUS_MUTABLE

    def mark_page_executable(self, addr):
        mem_offset, inword_addr, mask = self._split_addr(addr, 1)
        pagestart = mem_offset & ~self.PAGE_MASK
        if self.status[mem_offset] != MEM_STATUS_NORMAL:
            return
        self.version = Version()
        for mem_offset in range(pagestart, pagestart + self.PAGE_MASK + 1):
            assert self.status[mem_offset] != MEM_STATUS_MUTABLE
            self.status[mem_offset] = MEM_STATUS_IMMUTABLE


class BlockMemory(MemBase):
    ADDRESS_BITS_BLOCK = 20 # 1 MB
    BLOCK_SIZE = 2 ** ADDRESS_BITS_BLOCK
    BLOCK_MASK = BLOCK_SIZE - 1

    def __init__(self):
        self.blocks = {}
        self.last_block = None
        self.last_block_addr = r_uint(0)

    def get_block(self, block_addr):
        last_block = self.last_block
        if last_block is not None and block_addr == self.last_block_addr:
            block = last_block
        else:
            block = self._get_block(block_addr)
            self.last_block = block
            self.last_block_addr = block_addr
        return block

    @jit.elidable
    def _get_block(self, block_addr):
        if block_addr in self.blocks:
            return self.blocks[block_addr]
        res = self.blocks[block_addr] = [r_uint(0)] * (self.BLOCK_SIZE // 8)
        return res

    @always_inline
    def _split_addr(self, start_addr, num_bytes):
        block_addr = start_addr >> self.ADDRESS_BITS_BLOCK
        block = self.get_block(block_addr)
        start_addr = start_addr & self.BLOCK_MASK
        block_offset = start_addr >> 3
        inword_addr = start_addr & 0b111
        # little endian
        if num_bytes == 8:
            mask = r_uint(-1)
        else:
            mask = (r_uint(1) << (num_bytes * 8)) - 1
        return block, block_offset, inword_addr, mask

    def _aligned_read(self, start_addr, num_bytes, executable_flag):
        if executable_flag:
            jit.promote(start_addr)
        block, block_offset, inword_addr, mask = self._split_addr(start_addr, num_bytes)
        data = block[block_offset]
        if executable_flag:
            jit.promote(data)
        if num_bytes == 8:
            assert inword_addr == 0
            return data
        return (data >> (inword_addr * 8)) & mask

    def _aligned_write(self, start_addr, num_bytes, value):
        block, block_offset, inword_addr, mask = self._split_addr(start_addr, num_bytes)
        if num_bytes == 8:
            assert inword_addr == 0
            block[block_offset] = value
            return
        assert value & ~mask == 0
        olddata = block[block_offset]
        mask <<= inword_addr * 8
        value <<= inword_addr * 8
        block[block_offset] = (olddata & ~mask) | value


class SplitMemory(MemBase):
    # XXX should be generalized to N segments and auto-generated

    _immutable_fields_ = ['mem1', 'address_base1', 'address_end1', 'mem2', 'address_base2', 'address_end2']

    def __init__(self, mem1, address_base1, size1, mem2, address_base2, size2):
        self.mem1 = mem1
        self.address_base1 = address_base1
        self.address_end1 = address_base1 + size1
        assert self.is_aligned(self.address_base1)
        assert self.is_aligned(self.address_end1)

        self.mem2 = mem2
        self.address_base2 = address_base2
        self.address_end2 = address_base2 + size2
        assert self.is_aligned(self.address_base2)
        assert self.is_aligned(self.address_end2)

    def _aligned_read(self, start_addr, num_bytes, executable_flag):
        if executable_flag:
            jit.promote(start_addr)
        if self.address_base1:
            if self.address_base1 <= start_addr < self.address_end1:
                return self.mem1._aligned_read(start_addr - self.address_base1, num_bytes, executable_flag)
        else:
            if start_addr < self.address_end1:
                return self.mem1._aligned_read(start_addr, num_bytes, executable_flag)
        if self.address_base2 <= start_addr < self.address_end2:
            return self.mem2._aligned_read(start_addr - self.address_base2, num_bytes, executable_flag)
        raise ValueError

    def _aligned_write(self, start_addr, num_bytes, value):
        if self.address_base1:
            if self.address_base1 <= start_addr < self.address_end1:
                return self.mem1._aligned_write(start_addr - self.address_base1, num_bytes, value)
        else:
            if start_addr < self.address_end1:
                return self.mem1._aligned_write(start_addr, num_bytes, value)
        if self.address_base2 <= start_addr < self.address_end2:
            return self.mem2._aligned_write(start_addr - self.address_base2, num_bytes, value)
        raise ValueError

    def mark_page_executable(self, start_addr):
        if self.address_base1:
            if self.address_base1 <= start_addr < self.address_end1:
                return self.mem1.mark_page_executable(start_addr - self.address_base1)
        else:
            if start_addr < self.address_end1:
                return self.mem1.mark_page_executable(start_addr)
        if self.address_base2 <= start_addr < self.address_end2:
            return self.mem2.mark_page_executable(start_addr - self.address_base2)

    def close(self):
        self.mem1.close()
        self.mem2.close()
