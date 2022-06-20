from rpython.rlib.rbigint import rbigint
from rpython.rlib.rarithmetic import r_uint, intmask

class SmallBitVector(object):
    def __init__(self, size, val):
        self.size = size # number of bits
        self.val = val # r_uint
        assert isinstance(val, r_uint)

class GenericBitVector(object):
    def __init__(self, size, rval):
        assert size > 0
        self.size = size
        self.rval = rval # rbigint

    def _size_mask(self, val):
        return val.and_(rbigint.fromint(1).lshift(self.size).int_sub(1))

    def add_int(self, i):
        return GenericBitVector(self.size, self._size_mask(self.rval.add(i)))

    def sub_int(self, i):
        return GenericBitVector(self.size, self._size_mask(self.rval.sub(i)))

    def print_bits(self):
        print "GenericBitVector<%s, %s>" % (self.size, self.rval.hex())

    def shiftl(self, i):
        return GenericBitVector(self.size, self._size_mask(self.rval.lshift(i)))

    def shiftr(self, i):
        return GenericBitVector(self.size, self._size_mask(self.rval.rshift(i)))

    def xor(self, other):
        return GenericBitVector(self.size, self._size_mask(self.rval.xor(other.rval)))

    def or_(self, other):
        return GenericBitVector(self.size, self._size_mask(self.rval.or_(other.rval)))

    def and_(self, other):
        return GenericBitVector(self.size, self._size_mask(self.rval.and_(other.rval)))

    def invert(self):
        return GenericBitVector(self.size, self._size_mask(self.rval.invert()))

    def subrange(self, n, m):
        width = n - m + 1
        return GenericBitVector(width, self.rval.rshift(m))

    def sign_extend(self, i):
        if i == self.size:
            return self
        assert i > self.size
        highest_bit = self.rval.rshift(self.size - 1).int_and_(1).toint()
        if not highest_bit:
            return GenericBitVector(i, self.rval)
        else:
            extra_bits = i - self.size
            bits = rbigint.fromint(1).lshift(extra_bits).int_sub(1).lshift(self.size)
            return GenericBitVector(i, bits.or_(self.rval))

    def update_bit(self, pos, bit):
        mask = rbigint.fromint(1).lshift(pos)
        if bit:
            return GenericBitVector(self.size, self.rval.or_(mask))
        else:
            return GenericBitVector(self.size, self._size_mask(self.rval.and_(mask.invert())))

    def signed(self):
        n = self.size
        assert n > 0
        u1 = rbigint.fromint(1)
        m = u1.lshift(n - 1)
        op = self.rval
        op = op.and_((u1.lshift(n)).int_sub(1)) # mask off higher bits to be sure
        return op.xor(m).sub(m)
