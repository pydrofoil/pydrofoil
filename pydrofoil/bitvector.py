import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong
from rpython.rlib.objectmodel import always_inline, specialize
from rpython.rlib.rstring import (
    ParseStringError, ParseStringOverflowError)

@always_inline
@specialize.arg_or_var(0)
def from_ruint(size, val):
    if size <= 64:
        return SmallBitVector(size, val, True)
    return GenericBitVector(size, rbigint.fromrarith_int(val), True)

@always_inline
def from_bigint(size, rval):
    if size <= 64:
        return SmallBitVector(size, BitVector.rbigint_mask(size, rval).touint())
    return GenericBitVector(size, rval, True)

class BitVector(object):
    _attrs_ = []

    def size(self):
        raise NotImplementedError("abstract base class")

    def size_as_int(self):
        return Integer.fromint(self.size())

    def string_of_bits(self):
        if self.size() % 4 == 0:
            res = self.tobigint().format("0123456789ABCDEF")
            return "0x%s%s" % ("0" * max(0, self.size() // 4 - len(res)), res)
        else:
            res = self.tobigint().format("01")
            return "0b%s%s" % ("0" * max(0, self.size() - len(res)), res)

    @staticmethod
    def rbigint_mask(size, rval):
        return rval.and_(rbigint.fromint(1).lshift(size).int_sub(1))

    def tolong(self): # only for tests:
        return self.tobigint().tolong()

    def append_64(self, ui):
        return from_bigint(self.size() + 64, self.tobigint().lshift(64).or_(rbigint.fromrarith_int(ui)))

class BitVectorWithSize(BitVector):
    _attrs_ = ['_size']
    _immutable_fields_ = ['_size']

    def __init__(self, size):
        self._size = size

    def size(self):
        return self._size


class SmallBitVector(BitVectorWithSize):
    _immutable_fields_ = ['val']

    def __init__(self, size, val, normalize=False):
        self._size = size # number of bits
        assert isinstance(val, r_uint)
        if normalize and size != 64:
            val = val & ((r_uint(1) << size) - 1)
        self.val = val # r_uint

    def __repr__(self):
        return "<SmallBitVector %s 0x%x>" % (self.size(), self.val)

    def make(self, val, normalize=False):
        return SmallBitVector(self.size(), val, normalize)

    def _check_size(self, other):
        assert other.size() == self.size()
        assert isinstance(other, SmallBitVector)
        return other

    @always_inline
    def add_int(self, i):
        if isinstance(i, SmallInteger):
            if i.val > 0:
                return self.make(self.val + r_uint(i.val), True)
        return self._add_int_slow(i)

    def _add_int_slow(self, i):
        # XXX can be better
        return from_bigint(self.size(), self.rbigint_mask(self.size(), self.tobigint().add(i.tobigint())))

    def sub_int(self, i):
        if isinstance(i, SmallInteger):
            if i.val > 0:
                return self.make(self.val - r_uint(i.val), True)
        # XXX can be better
        return from_bigint(self.size(), self.rbigint_mask(self.size(), self.tobigint().sub(i.tobigint())))

    def print_bits(self):
        print self.__repr__()

    def lshift(self, i):
        assert i >= 0
        if i >= 64:
            return self.make(r_uint(0))
        return self.make(self.val << i, True)

    def rshift(self, i):
        assert i >= 0
        if i >= self.size():
            return self.make(r_uint(0))
        return self.make(self.val >> i)

    def lshift_bits(self, other):
        return self.lshift(other.toint())

    def rshift_bits(self, other):
        return self.rshift(other.toint())

    def xor(self, other):
        assert isinstance(other, SmallBitVector)
        return self.make(self.val ^ other.val, True)

    def and_(self, other):
        assert isinstance(other, SmallBitVector)
        return self.make(self.val & other.val, True)

    def or_(self, other):
        assert isinstance(other, SmallBitVector)
        return self.make(self.val | other.val, True)

    def invert(self):
        return self.make(~self.val, True)

    def subrange(self, n, m):
        width = n - m + 1
        return SmallBitVector(width, self.val >> m, True)

    def sign_extend(self, i):
        if i == self.size():
            return self
        if i > 64:
            return GenericBitVector._sign_extend(rbigint.fromrarith_int(self.val), self.size(), i)
        assert i > self.size()
        highest_bit = (self.val >> (self.size() - 1)) & 1
        if not highest_bit:
            return from_ruint(i, self.val)
        else:
            extra_bits = i - self.size()
            bits = ((r_uint(1) << extra_bits) - 1) << self.size()
            return from_ruint(i, bits | self.val)

    def read_bit(self, pos):
        assert pos < self.size()
        mask = r_uint(1) << pos
        return r_uint(bool(self.val & mask))

    def update_bit(self, pos, bit):
        assert pos < self.size()
        mask = r_uint(1) << pos
        if bit:
            return self.make(self.val | mask)
        else:
            return self.make(self.val & ~mask, True)

    def update_subrange(self, n, m, s):
        width = s.size()
        assert width <= self.size()
        if width == self.size():
            return s
        assert width == n - m + 1
        # width cannot be 64 in the next line because of the if above
        mask = ~(((r_uint(1) << width) - 1) << m)
        return self.make((self.val & mask) | (s.touint() << m), True)

    def signed(self):
        n = self.size()
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


class GenericBitVector(BitVectorWithSize):
    _immutable_fields_ = ['rval']

    def __init__(self, size, rval, normalize=False):
        assert size > 0
        self._size = size
        if normalize:
            rval = self._size_mask(rval)
        self.rval = rval # rbigint

    def make(self, rval, normalize=False):
        return GenericBitVector(self.size(), rval, normalize)

    def __repr__(self):
        return "<GenericBitVector %s %r>" % (self.size(), self.rval)

    def _size_mask(self, val):
        return self.rbigint_mask(self.size(), val)

    def add_int(self, i):
        return self.make(self._size_mask(self.rval.add(i.tobigint())))

    def sub_int(self, i):
        return self.make(self._size_mask(self.rval.sub(i.tobigint())))

    def print_bits(self):
        print "GenericBitVector<%s, %s>" % (self.size(), self.rval.hex())

    def lshift(self, i):
        return self.make(self._size_mask(self.rval.lshift(i)))

    def rshift(self, i):
        return self.make(self._size_mask(self.rval.rshift(i)))

    def lshift_bits(self, other):
        return self.make(self._size_mask(self.rval.lshift(other.toint())))

    def rshift_bits(self, other):
        return self.make(self._size_mask(self.rval.rshift(other.toint())))

    def xor(self, other):
        return self.make(self._size_mask(self.rval.xor(other.tobigint())))

    def or_(self, other):
        return self.make(self._size_mask(self.rval.or_(other.tobigint())))

    def and_(self, other):
        return self.make(self._size_mask(self.rval.and_(other.tobigint())))

    def invert(self):
        return self.make(self._size_mask(self.rval.invert()))

    def subrange(self, n, m):
        width = n - m + 1
        if m == 0:
            return from_bigint(width, self.rval)
        if width < 64: # somewhat annoying that 64 doesn't work
            mask = (r_uint(1) << width) - 1
            res = self.rval.abs_rshift_and_mask(r_ulonglong(m), intmask(mask))
            return SmallBitVector(width, r_uint(res))
        return from_bigint(width, self.rval.rshift(m))

    def sign_extend(self, i):
        if i == self.size():
            return self
        assert i > self.size()
        return self._sign_extend(self.rval, self.size(), i)

    @staticmethod
    def _sign_extend(rval, size, target_size):
        highest_bit = rval.rshift(size - 1).int_and_(1).toint()
        if not highest_bit:
            return GenericBitVector(target_size, rval)
        else:
            extra_bits = target_size - size
            bits = rbigint.fromint(1).lshift(extra_bits).int_sub(1).lshift(size)
            return GenericBitVector(target_size, bits.or_(rval))

    def read_bit(self, pos):
        return bool(self.rval.abs_rshift_and_mask(r_ulonglong(pos), 1))

    def update_bit(self, pos, bit):
        mask = rbigint.fromint(1).lshift(pos)
        if bit:
            return self.make(self.rval.or_(mask))
        else:
            return self.make(self._size_mask(self.rval.and_(mask.invert())))

    def update_subrange(self, n, m, s):
        width = s.size()
        assert width == n - m + 1
        mask = rbigint.fromint(1).lshift(width).int_sub(1).lshift(m).invert()
        return self.make(self.rval.and_(mask).or_(s.tobigint().lshift(m)))

    def signed(self):
        n = self.size()
        assert n > 0
        u1 = rbigint.fromint(1)
        m = u1.lshift(n - 1)
        op = self.rval
        op = op.and_((u1.lshift(n)).int_sub(1)) # mask off higher bits to be sure
        return Integer.frombigint(op.xor(m).sub(m))

    def unsigned(self):
        return Integer.frombigint(self.rval)

    def eq(self, other):
        assert self.size() == other.size()
        return self.rval.eq(other.tobigint())

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
    @always_inline
    def from_ruint(val):
        if val & (r_uint(1)<<63):
            # bigger than biggest signed int
            return BigInteger(rbigint.fromrarith_int(val))
        return SmallInteger(intmask(val))

    def tolong(self): # only for tests:
        return self.tobigint().tolong()


class SmallInteger(Integer):
    _immutable_fields_ = ['val']

    def __init__(self, val):
        self.val = val

    def __repr__(self):
        return "<SmallInteger %s>" % (self.val, )

    def str(self):
        return str(self.val)

    def toint(self):
        return self.val

    def touint(self):
        return r_uint(self.val)

    def tobigint(self):
        return rbigint.fromint(self.val)

    def slice(self, len, start):
        if len > 64 or start >= 64: # XXX can be more efficient
            return BigInteger._slice(self.tobigint(), len, start)
        n = self.val >> start
        if len == 64:
            return from_ruint(64, r_uint(n))
        return from_ruint(len, r_uint(n) & ((1 << len) - 1))

    def eq(self, other):
        if isinstance(other, SmallInteger):
            return self.val == other.val
        return other.eq(self)

    def lt(self, other):
        if isinstance(other, SmallInteger):
            return self.val < other.val
        assert isinstance(other, BigInteger)
        return other.rval.int_gt(self.val)

    def le(self, other):
        if isinstance(other, SmallInteger):
            return self.val <= other.val
        assert isinstance(other, BigInteger)
        return other.rval.int_ge(self.val)

    def gt(self, other):
        if isinstance(other, SmallInteger):
            return self.val > other.val
        assert isinstance(other, BigInteger)
        return other.rval.int_lt(self.val)

    def ge(self, other):
        if isinstance(other, SmallInteger):
            return self.val >= other.val
        assert isinstance(other, BigInteger)
        return other.rval.int_le(self.val)

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

    def tdiv(self, other):
        # rounds towards zero, like in C, not like in python
        if isinstance(other, SmallInteger):
            if other.val == 0:
                raise ZeroDivisionError
            if not (self.val == -2**63 and other.val == -1):
                return SmallInteger(int_c_div(self.val, other.val))
        return BigInteger(self.tobigint()).tdiv(other)

    def tmod(self, other):
        # C behaviour
        if isinstance(other, SmallInteger):
            if other.val == 0:
                raise ZeroDivisionError
            if not (self.val == -2**63 and other.val == -1):
                return SmallInteger(int_c_mod(self.val, other.val))
        return BigInteger(self.tobigint()).tmod(other)


class BigInteger(Integer):
    _immutable_fields_ = ['rval']

    def __init__(self, rval):
        self.rval = rval

    def __repr__(self):
        return "<BigInteger %s>" % (self.rval.str(), )

    def str(self):
        return self.rval.str()

    def toint(self):
        return self.rval.toint()

    def touint(self):
        return self.rval.touint()

    def tobigint(self):
        return self.rval

    def slice(self, len, start):
        return self._slice(self.rval, len, start)

    @staticmethod
    def _slice(rval, len, start):
        if start == 0:
            n = rval
        else:
            n = rval.rshift(start)
        return from_bigint(len, n.and_(rbigint.fromint(1).lshift(len).int_sub(1)))

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

    def sub(self, other):
        if isinstance(other, SmallInteger):
            return BigInteger(self.rval.int_sub(other.val))
        assert isinstance(other, BigInteger)
        return BigInteger(self.rval.sub(other.rval))

    def mul(self, other):
        if isinstance(other, SmallInteger):
            return BigInteger(self.rval.int_mul(other.val))
        assert isinstance(other, BigInteger)
        return BigInteger(self.rval.mul(other.rval))

    def tdiv(self, other):
        # rounds towards zero, like in C, not like in python
        other = other.tobigint()
        if other.sign == 0:
            raise ZeroDivisionError
        div, rem = bigint_divrem(self.tobigint(), other)
        return BigInteger(div)

    def tmod(self, other):
        other = other.tobigint()
        if other.sign == 0:
            raise ZeroDivisionError
        div, rem = bigint_divrem(self.tobigint(), other)
        return BigInteger(rem)
