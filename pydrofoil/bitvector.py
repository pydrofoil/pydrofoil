import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem, ONERBIGINT, \
        _divrem1, intsign, int_in_valid_range
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong
from rpython.rlib.objectmodel import always_inline, specialize, \
        we_are_translated, is_annotation_constant
from rpython.rlib.rstring import (
    ParseStringError, ParseStringOverflowError)
from rpython.rlib import jit

MININT = -sys.maxint - 1

@jit.elidable
def bigint_divrem1(a, n):
    assert n != MININT
    div, rem = _divrem1(a, abs(n))
    # _divrem1 leaves the sign always positive, fix
    if a.sign != intsign(n):
        div.sign = -div.sign
    if a.sign < 0 and rem > 0:
        rem = -rem
    return div, rem


@always_inline
#@specialize.arg_or_var(0, 1)
def from_ruint(size, val):
    if size <= 64:
#        if is_annotation_constant(size) and is_annotation_constant(val):
#            return _small_bit_vector_memo(size, val)
        return SmallBitVector(size, val, True)
    return SparseBitVector(size, val)

@specialize.memo()
def _small_bit_vector_memo(size, val):
    return SmallBitVector(size, val)

@always_inline
def from_bigint(size, rval):
    if size <= 64:
        return SmallBitVector(size, BitVector.rbigint_mask(size, rval).touint())
    return GenericBitVector(size, rval, True)

@always_inline
def ruint_mask(width, val):
    if width == 64:
        return val
    assert width < 64
    mask = (r_uint(1) << width) - 1
    return val & mask


def rbigint_fromrarith_int(uint):
    res = rbigint.fromrarith_int(uint)
    jit.record_known_result(uint, rbigint.touint, res)
    return res

class MaskHolder(object):
    def __init__(self, predefined=128):
        self.lst = []
        for i in range(predefined):
            self.get(i)

    @jit.elidable
    def get(self, size):
        if size >= len(self.lst):
            self.lst.extend([None] * (size - len(self.lst) + 1))
        mask = self.lst[size]
        if mask is None:
            mask = ONERBIGINT.lshift(size).int_sub(1)
            self.lst[size] = mask
        return mask

MASKS = MaskHolder()

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
        res = BitVector._rbigint_mask(size, rval)
        # rbigint_mask is idempotent
        #jit.record_known_result(res, BitVector._rbigint_mask, size, res)
        return res

    @staticmethod
    @jit.elidable
    def _rbigint_mask(size, rval):
        if rval.sign >= 0 and rval.bit_length() <= size:
            return rval
        mask = MASKS.get(size)
        return rval.and_(mask)

    def tolong(self): # only for tests:
        return self.tobigint().tolong()

    def append(self, other):
        return from_bigint(self.size() + other.size(), self.tobigint().lshift(other.size()).or_(other.tobigint()))

    def append_64(self, ui):
        return from_bigint(self.size() + 64, self.tobigint().lshift(64).or_(rbigint_fromrarith_int(ui)))

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

    def add_bits(self, other):
        assert self.size() == other.size()
        assert isinstance(other, SmallBitVector)
        return self.make(self.val + other.val, True)

    def sub_bits(self, other):
        assert self.size() == other.size()
        assert isinstance(other, SmallBitVector)
        return self.make(self.val - other.val, True)

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

    def arith_rshift(self, i):
        assert i >= 0
        size = self.size()
        if i >= size:
            i = size
        highest_bit = (self.val >> (size - 1)) & 1
        res = self.val >> i
        if highest_bit:
            res |= ((r_uint(1) << i) - 1) << (size - i)
        return SmallBitVector(size, res)

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
        assert 0 <= m <= n < self.size()
        width = n - m + 1
        return SmallBitVector(width, self.subrange_unwrapped_res(n, m))

    def subrange_unwrapped_res(self, n, m):
        assert 0 <= m <= n < self.size()
        width = n - m + 1
        return ruint_mask(width, self.val >> m)

    @always_inline
    def zero_extend(self, i):
        if i == self.size():
            return self
        assert i > self.size()
        if i > 64:
            return GenericBitVector(i, rbigint_fromrarith_int(self.val))
        return SmallBitVector(i, self.val)

    @always_inline
    def sign_extend(self, i):
        if i == self.size():
            return self
        if i > 64:
            return GenericBitVector._sign_extend(rbigint_fromrarith_int(self.val), self.size(), i)
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
        if self.size() == 64:
            if self.read_bit(63):
                raise OverflowError
        return intmask(self.val)

    def touint(self):
        return self.val

    def tobigint(self):
        return rbigint_fromrarith_int(self.val)

    def append(self, other):
        ressize = self.size() + other.size()
        if ressize > 64 or not isinstance(other, SmallBitVector):
            return BitVector.append(self, other)
        return from_ruint(ressize, (self.val << other.size()) | other.val)

    def replicate(self, i):
        size = self.size()
        if size * i <= 64:
            return SmallBitVector(size * i, self._replicate(self.val, size, i))
        gbv = GenericBitVector(size, rbigint_fromrarith_int(self.val))
        return gbv.replicate(i)

    @staticmethod
    @jit.look_inside_iff(lambda val, size, i: jit.isconstant(i))
    def _replicate(val, size, i):
        res = val
        for _ in range(i - 1):
            res = (res << size) | val
        return res

    def truncate(self, i):
        assert i <= self.size()
        return SmallBitVector(i, self.val, normalize=True)

UNITIALIZED_BV = SmallBitVector(42, r_uint(0x42))


class SparseBitVector(BitVectorWithSize):
    _immutable_fields_ = ['val']

    def __init__(self, size, val):
        assert size > 64
        self._size = size
        self.val = val

    def __repr__(self):
        return "<SparseBitVector %s %r" %(self.size(), self.val)

    def _to_generic(self):
        return GenericBitVector(self._size, rbigint_fromrarith_int(self.val))

    def add_int(self, i):
        return self._to_generic().add_int(i)
    
    def add_bits(self, other):
        return self._to_generic().add_bits(other)

    def sub_bits(self, other):
        return self._to_generic().sub_bits(other)

    def sub_int(self, i):
        return self._to_generic().sub_int(i)

    def print_bits(self):
        print "SparseBitVector<%s, %s>" % (self.size(), self.val.hex())

    def lshift(self, i):
        return self._to_generic().lshift(i)

    def rshift(self, i):
        assert i >= 0
        if i >= self.size():
            return SparseBitVector(self.size(), 0)
        return SparseBitVector(self.size(), self.val >> i)

    def arith_rshift(self, i):
        assert i >= 0
        if i >= self.size():
            return SparseBitVector(self.size(), 0)
        return SparseBitVector(self.size(), self.val >> i)

    def lshift_bits(self, other):
        return self._to_generic().lshift_bits(other)

    def rshift_bits(self, other):
        return self.rshift(other.toint())

    def xor(self, other):
        assert isinstance(other, SparseBitVector)
        return SparseBitVector(self.size(), self.val ^ other.val)

    def or_(self, other):
        assert isinstance(other, SparseBitVector)
        return SparseBitVector(self.size(), self.val | other.val)
    
    def and_(self, other):
        assert isinstance(other, SparseBitVector)
        return SparseBitVector(self.size(), self.val & other.val)
    
    def invert(self):
        return self._to_generic().invert()

    def subrange(self,n,m):
        assert 0 <= m <= n < self.size()        
        width = n - m + 1
        if width <= 64:
            return SmallBitVector(width, self.subrange_unwrapped_res(n,m))
        return SparseBitVector(width, self.val >> m)

    def subrange_unwrapped_res(self, n, m):
        assert 0 <= m <= n < self.size()
        width = n - m + 1
        return ruint_mask(width, self.val >> m)

    def zero_extend(self, i):
        if i == self.size():
            return self
        assert i > self.size()
        return SparseBitVector(i, self.val)

    def sign_extend(self, i):
        if i == self.size():
            return self
        assert i > self.size()
        return SparseBitVector(i, self.val)

    def read_bit(self, pos):
        assert pos < self.size()
        if pos >= 64:
            return False
        mask = r_uint(1) << pos
        return bool(self.val & mask)
    
    def update_bit(self, pos, bit):
        assert pos < self.size()
        if pos >= 64: 
            return self._to_generic().update_bit(pos, bit)
        mask = r_uint(1) << pos
        if bit:
            return SparseBitVector(self.size(), self.val | mask)
        else:
            return SparseBitVector(self.size(), self.val & ~mask)

    def update_subrange(self, n, m, s):
        return self._to_generic().update_subrange(n, m ,s)
    
    def signed(self):
        return Integer.from_ruint(self.val)
    
    def unsigned(self):
        return Integer.from_ruint(self.val)
    
    def eq(self, other):
        assert other.size() == self.size()
        if isinstance(other, SparseBitVector):
            return self.val == other.val
        return self._to_generic().eq(other)

    def toint(self):
        if self.read_bit(63):
            raise OverflowError
        return intmask(self.val)
    
    def touint(self):
        return self.val
    
    def tobigint(self):
        return rbigint_fromrarith_int(self.val)
    
    def replicate(self, i):
        return self._to_generic().replicate(i)
    
    def truncate(self, i):
        assert i <= self.size()
        if i < 64:
            return SmallBitVector(i, ruint_mask(i, self.val), normalize=True)
        return SparseBitVector(i, self.val)




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

    def add_bits(self, other):
        assert self.size() == other.size()
        assert isinstance(other, GenericBitVector)
        return self.make(self._size_mask(self.rval.add(other.rval)))

    def sub_bits(self, other):
        assert self.size() == other.size()
        assert isinstance(other, GenericBitVector)
        return self.make(self._size_mask(self.rval.sub(other.rval)))

    def sub_int(self, i):
        return self.make(self._size_mask(self.rval.sub(i.tobigint())))

    def print_bits(self):
        print "GenericBitVector<%s, %s>" % (self.size(), self.rval.hex())

    def lshift(self, i):
        return self.make(self._size_mask(self.rval.lshift(i)))

    def rshift(self, i):
        return self.make(self._size_mask(self.rval.rshift(i)))

    def arith_rshift(self, i):
        assert i >= 0
        size = self.size()
        if i >= size:
            i = size
        rval = self.rval
        highest_bit = rval.abs_rshift_and_mask(r_ulonglong(size - 1), 1)
        res = rval.rshift(i)
        if highest_bit:
            res = res.or_(MASKS.get(i).lshift(size - i))
        return GenericBitVector(size, res)

    def lshift_bits(self, other):
        return self.lshift(other.toint())

    def rshift_bits(self, other):
        return self.rshift(other.toint())

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
        if width < 64: # somewhat annoying that 64 doesn't work
            mask = (r_uint(1) << width) - 1
            res = self.rval.abs_rshift_and_mask(r_ulonglong(m), intmask(mask))
            return SmallBitVector(width, r_uint(res))
        if m == 0:
            return from_bigint(width, self.rval)
        rval = self.rval.rshift(m)
        if n == self.size():
            return GenericBitVector(width, rval) # no need to mask
        return from_bigint(width, rval)

    def subrange_unwrapped_res(self, n, m):
        # XXX can be better
        return self.subrange(n, m).touint()

    def zero_extend(self, i):
        if i == self.size():
            return self
        assert i > self.size()
        return GenericBitVector(i, self.rval)

    def sign_extend(self, i):
        if i == self.size():
            return self
        assert i > self.size()
        return self._sign_extend(self.rval, self.size(), i)

    @staticmethod
    def _sign_extend(rval, size, target_size):
        highest_bit = rval.abs_rshift_and_mask(r_ulonglong(size - 1), 1)
        if not highest_bit:
            return GenericBitVector(target_size, rval)
        else:
            extra_bits = target_size - size
            bits = MASKS.get(extra_bits).lshift(size)
            return GenericBitVector(target_size, bits.or_(rval))

    def read_bit(self, pos):
        return bool(self.rval.abs_rshift_and_mask(r_ulonglong(pos), 1))

    def update_bit(self, pos, bit):
        mask = ONERBIGINT.lshift(pos)
        if bit:
            return self.make(self.rval.or_(mask))
        else:
            return self.make(self._size_mask(self.rval.and_(mask.invert())))

    def update_subrange(self, n, m, s):
        width = s.size()
        assert width == n - m + 1
        mask = MASKS.get(width).lshift(m).invert()
        return self.make(self.rval.and_(mask).or_(s.tobigint().lshift(m)))

    def signed(self):
        n = self.size()
        assert n > 0
        u1 = ONERBIGINT
        m = u1.lshift(n - 1)
        op = self.rval
        op = op.and_(MASKS.get(n)) # mask off higher bits to be sure
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

    def replicate(self, i):
        size = self.size()
        res = val = self.rval
        for _ in range(i - 1):
            res = res.lshift(size).or_(val)
        return GenericBitVector(size * i, res)

    def truncate(self, i):
        assert i <= self.size()
        val = self.rbigint_mask(i, self.rval)
        if i <= 64:
            return SmallBitVector(i, val.touint(), normalize=True)
        return GenericBitVector(i, val)


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
            return BigInteger(rbigint_fromrarith_int(val))
        return SmallInteger(intmask(val))

    def tolong(self): # only for tests:
        return self.tobigint().tolong()


class SmallInteger(Integer):
    _immutable_fields_ = ['val']

    def __init__(self, val):
        if not we_are_translated():
            assert MININT <= val <= sys.maxint
        self.val = val

    def __repr__(self):
        return "<SmallInteger %s>" % (self.val, )

    def str(self):
        return str(self.val)

    def hex(self):
        return hex(self.val)

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

    def abs(self):
        if self.val == MININT:
            return BigInteger(rbigint.fromint(self.val).abs())
        return SmallInteger(abs(self.val))

    def add(self, other):
        if isinstance(other, SmallInteger):
            return SmallInteger.add_i_i(self.val, other.val)
        else:
            assert isinstance(other, BigInteger)
            return BigInteger(other.rval.int_add(self.val))

    def sub(self, other):
        if isinstance(other, SmallInteger):
            return SmallInteger.sub_i_i(self.val, other.val)
        return BigInteger((other.tobigint().int_sub(self.val)).neg()) # XXX can do better

    def mul(self, other):
        if isinstance(other, SmallInteger):
            try:
                return SmallInteger(ovfcheck(self.val * other.val))
            except OverflowError:
                return BigInteger(self.tobigint().int_mul(other.val))
        else:
            assert isinstance(other, BigInteger)
            return other.mul(self)

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

    def ediv(self, other):
        if not isinstance(other, SmallInteger) or other.val == MININT or self.val == MININT:
            return BigInteger(self.tobigint()).ediv(other)
        other = other.val
        if other == 0:
            raise ZeroDivisionError
        if other > 0:
            return SmallInteger(self.val // other)
        else:
            return SmallInteger(-(self.val // -other))

    def emod(self, other):
        if not isinstance(other, SmallInteger) or other.val == MININT or self.val == MININT:
            return BigInteger(self.tobigint()).emod(other)
        other = other.val
        if other == 0:
            raise ZeroDivisionError
        res = self.val % other
        if res < 0:
            res -= other
            assert res >= 0
        return SmallInteger(res)

    def rshift(self, i):
        assert i >= 0
        return SmallInteger(self.val >> i)

    def lshift(self, i):
        assert i >= 0
        if i < 64:
            try:
                return SmallInteger(ovfcheck(self.val << i))
            except OverflowError:
                pass
        return BigInteger(rbigint.fromint(self.val).lshift(i))

    @staticmethod
    def add_i_i(a, b):
        try:
            return SmallInteger(ovfcheck(a + b))
        except OverflowError:
            return BigInteger(rbigint.fromint(a).int_add(b))

    @staticmethod
    def sub_i_i(a, b):
        try:
            return SmallInteger(ovfcheck(a - b))
        except OverflowError:
            return BigInteger(rbigint.fromint(b).int_sub(a).neg())


class BigInteger(Integer):
    _immutable_fields_ = ['rval']

    def __init__(self, rval):
        self.rval = rval

    def __repr__(self):
        return "<BigInteger %s>" % (self.rval.str(), )

    def str(self):
        return self.rval.str()

    def hex(self):
        return self.rval.hex()

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
        return from_bigint(len, n)

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

    def abs(self):
        return BigInteger(self.rval.abs())

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
            val = other.val
            if not val:
                return SmallInteger(0)
            if val == 1:
                return self
            if val & (val - 1) == 0:
                # power of two, replace by lshift
                shift = self._shift_amount(val)
                return self.lshift(shift)
            return BigInteger(self.rval.int_mul(other.val))
        assert isinstance(other, BigInteger)
        return BigInteger(self.rval.mul(other.rval))

    def tdiv(self, other):
        # rounds towards zero, like in C, not like in python
        if isinstance(other, SmallInteger) and int_in_valid_range(other.val):
            other = other.val
            if other == 0:
                raise ZeroDivisionError
            if other > 0 and other & (other - 1) == 0 and self.rval.sign >= 0:
                # can use shift
                return self.rshift(self._shift_amount(other))
            div, rem = bigint_divrem1(self.rval, other)
            return BigInteger(div)
        other = other.tobigint()
        if other.sign == 0:
            raise ZeroDivisionError
        div, rem = bigint_divrem(self.tobigint(), other)
        return BigInteger(div)

    @staticmethod
    @jit.elidable
    def _shift_amount(poweroftwo):
        assert poweroftwo & (poweroftwo - 1) == 0
        shift = 0
        while 1 << shift != poweroftwo:
            shift += 1
        return shift

    def tmod(self, other):
        if isinstance(other, SmallInteger) and int_in_valid_range(other.val):
            other = other.val
            if other == 0:
                raise ZeroDivisionError
            div, rem = bigint_divrem1(self.rval, other)
            return SmallInteger(rem)

        other = other.tobigint()
        if other.sign == 0:
            raise ZeroDivisionError
        div, rem = bigint_divrem(self.tobigint(), other)
        return BigInteger(rem)

    def ediv(self, other):
        other = other.tobigint()
        if other.int_eq(0):
            raise ZeroDivisionError
        if other.int_gt(0):
            return BigInteger(self.rval.floordiv(other))
        else:
            return BigInteger(self.rval.floordiv(other.neg()).neg())

    def emod(self, other):
        other = other.tobigint()
        if other.int_eq(0):
            raise ZeroDivisionError
        res = self.rval.mod(other)
        if res.int_lt(0):
            res = res.sub(other)
        return BigInteger(res)

    def rshift(self, i):
        assert i >= 0
        # XXX should we check whether it fits in a SmallInteger now?
        return BigInteger(self.rval.rshift(i))

    def lshift(self, i):
        return BigInteger(self.rval.lshift(i))

