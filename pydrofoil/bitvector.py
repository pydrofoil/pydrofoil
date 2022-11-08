import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong
from rpython.rlib.objectmodel import always_inline, specialize, dont_inline
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
        return int_fromint(self.size())

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
        val, rval = i
        if rval is None:
            if val > 0:
                return self.make(self.val + r_uint(val), True)
        return self._add_int_slow(val, rval)

    def _add_int_slow(self, val, rval):
        rval = int_tobigint_components(val, rval)
        # XXX can be better
        return from_bigint(self.size(), self.rbigint_mask(self.size(), self.tobigint().add(rval)))

    @always_inline
    def sub_int(self, i):
        val, rval = i
        if rval is None:
            if val > 0:
                return self.make(self.val - r_uint(val), True)
        return self._sub_int_slow(val, rval)

    def _sub_int_slow(self, val, rval):
        rval = int_tobigint_components(val, rval)
        # XXX can be better
        return from_bigint(self.size(), self.rbigint_mask(self.size(), self.tobigint().sub(rval)))

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

    @always_inline
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

    @always_inline
    def signed(self):
        n = self.size()
        if n == 64:
            return int_fromint(intmask(self.val))
        assert n > 0
        u1 = r_uint(1)
        m = u1 << (n - 1)
        op = self.val & ((u1 << n) - 1) # mask off higher bits to be sure
        return int_fromint(intmask((op ^ m) - m))

    @always_inline
    def unsigned(self):
        return int_fromruint(self.val)

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
        return self.make(self._size_mask(self.rval.add(int_tobigint(i))))

    def sub_int(self, i):
        return self.make(self._size_mask(self.rval.sub(int_tobigint(i))))

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
        return int_frombigint(op.xor(m).sub(m))

    def unsigned(self):
        return int_frombigint(self.rval)

    def eq(self, other):
        assert self.size() == other.size()
        return self.rval.eq(other.tobigint())

    def toint(self):
        return self.rval.toint()

    def touint(self):
        return self.rval.touint()

    def tobigint(self):
        return self.rval

# integers: the type needs to be able to represent arbitrarily big integers
# 
# they are implemented in a slightly weird way, as tuples of either the form
# (intvalue, None) or (-1, rbigintvalue)
# they are passed as pairs of variables everywhere, which means in the common
# int case we don't allocate anything, except on returns of functions that
# can't be inlined

@always_inline
def int_fromint(val):
    return (val, None)

@always_inline
def int_frombigint(rval):
    return (-1, rval)

def int_fromstr(s):
    value = 0
    try:
        val = string_to_int(s, 10)
    except ParseStringOverflowError as e:
        e.parser.rewind()
        return int_frombigint(rbigint._from_numberstring_parser(e.parser))
    return int_fromint(val)

@always_inline
def int_fromruint(val):
    if val & (r_uint(1)<<63):
        # bigger than biggest signed int
        return int_frombigint(rbigint.fromrarith_int(val))
    return int_fromint(intmask(val))

@always_inline
def int_tobigint(ia):
    val, rval = ia
    return int_tobigint_components(val, rval)

def int_tobigint_components(val, rval):
    if rval is None:
        return rbigint.fromint(val)
    return rval

def int_tolong(ia):
    val, rval = ia
    if rval is None:
        return val
    return rval.tolong()

def int_tostr(ia):
    val, rval = ia
    if rval is None:
        return str(val)
    return rval.tostr()

@always_inline
def int_toint(ia):
    val, rval = ia
    if rval is None:
        return val
    return rval.toint()

@always_inline
def int_eq(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    if rvala is None:
        if rvalb is None:
            return vala == valb
    return int_eq_slowpath(vala, rvala, valb, rvalb)

@dont_inline
def int_eq_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        return rvala.int_eq(valb)
    else:
        return rvala.eq(rvalb)

@always_inline
def int_lt(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    if rvala is None:
        if rvalb is None:
            return vala < valb
    return int_lt_slowpath(vala, rvala, valb, rvalb)

@dont_inline
def int_lt_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        return rvala.int_lt(valb)
    else:
        return rvala.lt(rvalb)

@always_inline
def int_le(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    if rvala is None:
        if rvalb is None:
            return vala <= valb
    return int_le_slowpath(vala, rvala, valb, rvalb)

@dont_inline
def int_le_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        return rvala.int_le(valb)
    else:
        return rvala.le(rvalb)

@always_inline
def int_gt(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    if rvala is None:
        if rvalb is None:
            return vala > valb
    return int_gt_slowpath(vala, rvala, valb, rvalb)

@dont_inline
def int_gt_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        return rvala.int_gt(valb)
    else:
        return rvala.gt(rvalb)

@always_inline
def int_ge(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    if rvala is None:
        if rvalb is None:
            return vala >= valb
    return int_ge_slowpath(vala, rvala, valb, rvalb)

@dont_inline
def int_ge_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        return rvala.int_ge(valb)
    else:
        return rvala.ge(rvalb)

@always_inline
def int_add(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    res = None
    if rvala is None:
        if rvalb is None:
            try:
                res = ovfcheck(vala + valb)
            except OverflowError:
                pass
            else:
                return int_fromint(res)
    return int_frombigint(int_add_slowpath(vala, rvala, valb, rvalb))

@dont_inline
def int_add_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        res = rvala.int_add(valb)
    else:
        res = rvala.add(rvalb)
    return res

@always_inline
def int_sub(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    res = None
    if rvala is None:
        if rvalb is None:
            try:
                res = ovfcheck(vala - valb)
            except OverflowError:
                pass
            else:
                return int_fromint(res)
    return int_frombigint(int_sub_slowpath(vala, rvala, valb, rvalb))

@dont_inline
def int_sub_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        res = rvala.int_sub(valb)
    else:
        res = rvala.sub(rvalb)
    return res

@always_inline
def int_mul(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    res = None
    if rvala is None:
        if rvalb is None:
            try:
                res = ovfcheck(vala * valb)
            except OverflowError:
                pass
            else:
                return int_fromint(res)
    return int_frombigint(int_mul_slowpath(vala, rvala, valb, rvalb))

@dont_inline
def int_mul_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        res = rvala.int_mul(valb)
    else:
        res = rvala.mul(rvalb)
    return res

@always_inline
def int_tdiv(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    res = None
    if rvala is None:
        if rvalb is None:
            if valb == 0:
                raise ZeroDivisionError
            if not (vala == -2**63 and valb == -1):
                # no overflow
                return int_fromint(int_c_div(vala, valb))
    return int_frombigint(int_tdiv_slowpath(vala, rvala, valb, rvalb))

@dont_inline
def int_tdiv_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        rvalb = rbigint.fromint(valb)
    if rvalb.sign == 0:
        raise ZeroDivisionError
    div, rem = bigint_divrem(rvala, rvalb)
    return div

@always_inline
def int_tmod(ia, ib):
    vala, rvala = ia
    valb, rvalb = ib
    res = None
    if rvala is None:
        if rvalb is None:
            if valb == 0:
                raise ZeroDivisionError
            if not (vala == -2**63 and valb == -1):
                # no overflow
                return int_fromint(int_c_mod(vala, valb))
    return int_frombigint(int_tmod_slowpath(vala, rvala, valb, rvalb))

@dont_inline
def int_tmod_slowpath(vala, rvala, valb, rvalb):
    rvala = int_tobigint_components(vala, rvala)
    if rvalb is None:
        rvalb = rbigint.fromint(valb)
    if rvalb.sign == 0:
        raise ZeroDivisionError
    div, rem = bigint_divrem(rvala, rvalb)
    return rem

@always_inline
def int_slice(i, len, start):
    val, rval = i
    if rval is None and len <= 64 and start < 64:
        n = val >> start
        return from_ruint(len, r_uint(n))
    return int_slice_slowpath(val, rval, len, start)

@dont_inline
def int_slice_slowpath(val, rval, len, start):
    rval = int_tobigint_components(val, rval)
    if start == 0:
        n = rval
    else:
        n = rval.rshift(start)
    return from_bigint(len, n)
