from rpython.rlib.rbigint import rbigint
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck
from rpython.rlib.rstring import (
    ParseStringError, ParseStringOverflowError)

def from_ruint(size, val):
    if size <= 64:
        return SmallBitVector(size, val, True)
    return GenericBitVector(size, rbigint.fromrarith_int(val), True)

def from_bigint(size, rval):
    if size <= 64:
        return SmallBitVector(size, BitVector.rbigint_mask(size, rval).touint())
    return GenericBitVector(size, rval, True)

class BitVector(object):
    _attrs_ = ['size']

    def __init__(self, size):
        self.size = size

    @staticmethod
    def rbigint_mask(size, rval):
        return rval.and_(rbigint.fromint(1).lshift(size).int_sub(1))

class SmallBitVector(BitVector):
    def __init__(self, size, val, normalize=False):
        self.size = size # number of bits
        assert isinstance(val, r_uint)
        if normalize and size != 64:
            val = val & ((r_uint(1) << size) - 1)
        self.val = val # r_uint

    def __repr__(self):
        return "<SmallBitVector %s 0x%x>" % (self.size, self.val)

    def _check_size(self, other):
        assert other.size == self.size
        assert isinstance(other, SmallBitVector)
        return other

    def add_int(self, i):
        if isinstance(i, SmallInteger):
            if i.val > 0:
                return SmallBitVector(self.size, self.val + r_uint(i.val), True)
        # XXX can be better
        return from_bigint(self.size, self.rbigint_mask(self.size, self.tobigint().add(i.tobigint())))

    def sub_int(self, i):
        if isinstance(i, SmallInteger):
            if i.val > 0:
                return SmallBitVector(self.size, self.val - r_uint(i.val), True)
        # XXX can be better
        return from_bigint(self.size, self.rbigint_mask(self.size, self.tobigint().sub(i.tobigint())))

    def print_bits(self):
        print self.__repr__()

    def lshift(self, i):
        return SmallBitVector(self.size, self.val << i, True)

    def rshift(self, i):
        return SmallBitVector(self.size, self.val >> i)

    def lshift_bits(self, other):
        return SmallBitVector(self.size, self.val << other.touint(), True)

    def rshift_bits(self, other):
        return SmallBitVector(self.size, self.val >> other.touint())

    def xor(self, other):
        assert isinstance(other, SmallBitVector)
        return SmallBitVector(self.size, self.val ^ other.val, True)

    def and_(self, other):
        assert isinstance(other, SmallBitVector)
        return SmallBitVector(self.size, self.val & other.val, True)

    def or_(self, other):
        assert isinstance(other, SmallBitVector)
        return SmallBitVector(self.size, self.val | other.val, True)

    def invert(self):
        return SmallBitVector(self.size, ~self.val, True)

    def subrange(self, n, m):
        width = n - m + 1
        return SmallBitVector(width, self.val >> m, True)

    def sign_extend(self, i):
        if i == self.size:
            return self
        assert i <= 64
        assert i > self.size
        highest_bit = (self.val >> (self.size - 1)) & 1
        if not highest_bit:
            return from_ruint(i, self.val)
        else:
            assert i <= 64 # otherwise more complicated
            extra_bits = i - self.size
            bits = ((r_uint(1) << extra_bits) - 1) << self.size
            return from_ruint(i, bits | self.val)

    def update_bit(self, pos, bit):
        mask = r_uint(1) << pos
        if bit:
            return SmallBitVector(self.size, self.val | mask)
        else:
            return SmallBitVector(self.size, self.val & ~mask, True)

    def update_subrange(self, n, m, s):
        width = s.size
        assert width == n - m + 1
        mask = ~(((r_uint(1) << width) - 1) << m)
        return SmallBitVector(self.size, (self.val & mask) | (s.touint() << m), True)

    def signed(self):
        n = self.size
        if n == 64:
            return Integer.fromint(intmask(self.val))
        assert n > 0
        u1 = r_uint(1)
        m = u1 << (n - 1)
        op = self.val & ((u1 << n) - 1) # mask off higher bits to be sure
        return Integer.fromint(intmask((op ^ m) - m))

    def unsigned(self):
        return Integer.from_ruint(self.val)

    def eq(self, other):
        other = self._check_size(other)
        return self.val == other.val

    def toint(self):
        return intmask(self.val)

    def touint(self):
        return self.val

    def tobigint(self):
        return rbigint.fromrarith_int(self.val)


class GenericBitVector(BitVector):
    def __init__(self, size, rval, normalize=False):
        assert size > 0
        self.size = size
        if normalize:
            rval = self._size_mask(rval)
        self.rval = rval # rbigint

    def __repr__(self):
        return "<GenericBitVector %s %r>" % (self.size, self.rval)

    def _size_mask(self, val):
        return self.rbigint_mask(self.size, val)

    def add_int(self, i):
        return GenericBitVector(self.size, self._size_mask(self.rval.add(i.tobigint())))

    def sub_int(self, i):
        return GenericBitVector(self.size, self._size_mask(self.rval.sub(i.tobigint())))

    def print_bits(self):
        print "GenericBitVector<%s, %s>" % (self.size, self.rval.hex())

    def lshift(self, i):
        return GenericBitVector(self.size, self._size_mask(self.rval.lshift(i)))

    def rshift(self, i):
        return GenericBitVector(self.size, self._size_mask(self.rval.rshift(i)))

    def lshift_bits(self, other):
        return GenericBitVector(self.size, self._size_mask(self.rval.lshift(other.toint())))

    def rshift_bits(self, other):
        return GenericBitVector(self.size, self._size_mask(self.rval.rshift(other.toint())))

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
        return from_bigint(width, self.rval.rshift(m))

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

    def update_subrange(self, n, m, s):
        width = s.size
        assert width == n - m + 1
        mask = rbigint.fromint(1).lshift(width).int_sub(1).lshift(m).invert()
        return GenericBitVector(self.size, self.rval.and_(mask).or_(s.tobigint().lshift(m)))

    def signed(self):
        n = self.size
        assert n > 0
        u1 = rbigint.fromint(1)
        m = u1.lshift(n - 1)
        op = self.rval
        op = op.and_((u1.lshift(n)).int_sub(1)) # mask off higher bits to be sure
        return Integer.frombigint(op.xor(m).sub(m))

    def unsigned(self):
        return Integer.frombigint(self.rval)

    def eq(self, other):
        return self.rval.eq(other.rval)

    def toint(self):
        return self.rval.toint()

    def touint(self):
        return self.rval.touint()

    def tobigint(self):
        return self.rval


class Integer(object):
    _attrs_ = []

    @staticmethod
    def fromint(val):
        return SmallInteger(val)

    @staticmethod
    def frombigint(rval):
        return BigInteger(rval)

    @staticmethod
    def fromstr(val):
        value = 0
        try:
            return SmallInteger(string_to_int(val, 10))
        except ParseStringOverflowError as e:
            return BigInteger(rbigint._from_numberstring_parser(e.parser))

    @staticmethod
    def from_ruint(val):
        if val & (r_uint(1)<<63):
            # bigger than biggest signed int
            return BigInteger(rbigint.fromrarith_int(val))
        return SmallInteger(intmask(val))

    def tolong(self): # only for tests:
        return self.tobigint().tolong()


class SmallInteger(Integer):
    def __init__(self, val):
        self.val = val

    def __repr__(self):
        return "<SmallInteger %s>" % (self.val, )

    def toint(self):
        return self.val

    def touint(self):
        return r_uint(self.val)

    def tobigint(self):
        return rbigint.fromint(self.val)

    def slice(self, len, start):
        n = self.val >> start.toint()
        len = len.toint()
        return from_ruint(len, r_uint(n) & ((1 << len) - 1))

    def eq(self, other):
        if isinstance(other, SmallInteger):
            return self.val == other.val
        return other.eq(self)

    def lt(self, other):
        if isinstance(other, SmallInteger):
            return self.val < other.val
        return self.tobigint().lt(other.tobigint())

    def le(self, other):
        if isinstance(other, SmallInteger):
            return self.val <= other.val
        return self.tobigint().le(other.tobigint())

    def gt(self, other):
        if isinstance(other, SmallInteger):
            return self.val > other.val
        return self.tobigint().gt(other.tobigint())

    def ge(self, other):
        if isinstance(other, SmallInteger):
            return self.val >= other.val
        return self.tobigint().ge(other.tobigint())

    def add(self, other):
        if isinstance(other, SmallInteger):
            try:
                return SmallInteger(ovfcheck(self.val + other.val))
            except OverflowError:
                return BigInteger(self.tobigint().int_add(other.val))
        else:
            assert isinstance(other, BigInteger)
            return BigInteger(other.rval.int_add(self.val))

    def sub(self, other):
        if isinstance(other, SmallInteger):
            try:
                return SmallInteger(ovfcheck(self.val - other.val))
            except OverflowError:
                pass
        return BigInteger((other.tobigint().int_sub(self.val)).neg()) # XXX can do better

    def mul(self, other):
        if isinstance(other, SmallInteger):
            try:
                return SmallInteger(ovfcheck(self.val * other.val))
            except OverflowError:
                return BigInteger(self.tobigint().int_mul(other.val))
        else:
            assert isinstance(other, BigInteger)
            return BigInteger(other.rval.int_mul(self.val))


class BigInteger(Integer):
    def __init__(self, rval):
        self.rval = rval

    def __repr__(self):
        return "<BigInteger %s>" % (self.rval.str(), )

    def toint(self):
        return self.rval.toint()

    def touint(self):
        return self.rval.touint()

    def tobigint(self):
        return self.rval

    def slice(self, len, start):
        n = self.rval.rshift(start.toint())
        return from_bigint(len.toint(), n.and_(rbigint.fromint(1).lshift(len.toint()).int_sub(1)))

    def eq(self, other):
        if isinstance(other, SmallInteger):
            return self.rval.int_eq(other.val)
        assert isinstance(other, BigInteger)
        return self.rval.eq(other.rval)

    def lt(self, other):
        if isinstance(other, SmallInteger):
            return self.rval.int_lt(other.val)
        assert isinstance(other, BigInteger)
        return self.rval.lt(other.rval)

    def le(self, other):
        if isinstance(other, SmallInteger):
            return self.rval.int_le(other.val)
        assert isinstance(other, BigInteger)
        return self.rval.le(other.rval)

    def gt(self, other):
        if isinstance(other, SmallInteger):
            return self.rval.int_gt(other.val)
        assert isinstance(other, BigInteger)
        return self.rval.gt(other.rval)

    def ge(self, other):
        if isinstance(other, SmallInteger):
            return self.rval.int_ge(other.val)
        assert isinstance(other, BigInteger)
        return self.rval.ge(other.rval)

    def add(self, other):
        if isinstance(other, SmallInteger):
            return BigInteger(self.rval.int_add(other.val))
        assert isinstance(other, BigInteger)
        return BigInteger(self.rval.add(other.rval))

    def mul(self, other):
        if isinstance(other, SmallInteger):
            return BigInteger(self.rval.int_mul(other.val))
        assert isinstance(other, BigInteger)
        return BigInteger(self.rval.mul(other.rval))

    def sub(self, other):
        if isinstance(other, SmallInteger):
            return BigInteger(self.rval.int_sub(other.val))
        assert isinstance(other, BigInteger)
        return BigInteger(self.rval.sub(other.rval))
