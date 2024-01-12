import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem, ONERBIGINT, \
        _divrem1, intsign, int_in_valid_range
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong
from rpython.rlib.objectmodel import always_inline, specialize, \
        we_are_translated, is_annotation_constant, not_rpython
from rpython.rlib.rstring import (
    ParseStringError, ParseStringOverflowError)
from rpython.rlib import jit

MININT = -sys.maxint - 1
MAXINT = sys.maxint

@jit.elidable
def bigint_divrem1(a, n):
    assert n != MININT
    div, rem = _divrem1(a, abs(n))
    # _divrem1 leaves the sign always positive, fix
    asign = a.get_sign()
    if asign != intsign(n):
        div._set_sign(-div.get_sign())
    if asign < 0 and rem > 0:
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
    return GenericBitVector.from_bigint(size, rval)

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
        if rval.get_sign() >= 0 and rval.bit_length() <= size:
            return rval
        mask = MASKS.get(size)
        return rval.and_(mask)

    @not_rpython
    def tolong(self): # only for tests:
        return self.tobigint().tolong()

    def append(self, other):
        if isinstance(other, SmallBitVector) and other.size() == 64:
            return self.append_64(other.val)
        return GenericBitVector._append(self, other)

    def append_64(self, ui):
        raise NotImplementedError("abstract base class")

    def lshift_bits(self, other):
        return self.lshift(other.toint())

    def rshift_bits(self, other):
        return self.rshift(other.toint())

    @staticmethod
    def unpack(size, val, data):
        if size <= 64:
            assert data is None
            return SmallBitVector(size, val)
        elif data is None:
            assert data is None
            return SparseBitVector(size, val)
        else:
            return GenericBitVector(size, data)


class BitVectorWithSize(BitVector):
    _attrs_ = ['_size']
    _immutable_fields_ = ['_size']

    def __init__(self, size):
        self._size = size

    def size(self):
        return self._size

    def check_size_and_return(self, expected_width):
        if self.size() != expected_width:
            raise ValueError
        return self


class SmallBitVector(BitVectorWithSize):
    _immutable_fields_ = ['val']

    def __init__(self, size, val, normalize=False):
        self._size = size # number of bits
        assert isinstance(val, r_uint)
        if normalize and size != 64:
            val = val & ((r_uint(1) << size) - 1)
        if not normalize:
            # XXX disable after translation, later
            if size < 64:
                assert val >> size == r_uint(0)
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
            rhs = r_uint(i.val)
        else:
            assert isinstance(i, BigInteger)
            rhs = i.slice_unwrapped_res(64, 0)
        return self.make(self.val + rhs, True)

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
            return self.make(self.val - r_uint(i.val), True)
        else:
            assert isinstance(i, BigInteger)
            rhs = i.slice_unwrapped_res(64, 0)
        return self.make(self.val - rhs, True)

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
        highest_bit = self.read_bit(self.size() - 1)
        res = self.val >> i
        if highest_bit:
            res |= ((r_uint(1) << i) - 1) << (size - i)
        return SmallBitVector(size, res)

    def xor(self, other):
        assert self.size() == other.size()
        assert isinstance(other, SmallBitVector)
        return self.make(self.val ^ other.val, True)

    def and_(self, other):
        assert self.size() == other.size()
        assert isinstance(other, SmallBitVector)
        return self.make(self.val & other.val, True)

    def or_(self, other):
        assert self.size() == other.size()
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
        assert 0 < width <= 64
        return ruint_mask(width, self.val >> m)

    @always_inline
    def zero_extend(self, i):
        if i == self.size():
            return self
        assert i > self.size()
        return from_ruint(i, self.val)

    @always_inline
    def sign_extend(self, i):
        size = self.size()
        if i == size:
            return self

        if i > 64:
            if self.read_bit(size - 1):
                return GenericBitVector._sign_extend(size, [self.val], i)
            else:
                return SparseBitVector(i, self.val) 
        m = r_uint(1) << (self.size() - 1)
        return SmallBitVector(i, (self.val ^ m) - m, True)

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
        m = r_uint(1) << (n - 1)
        return Integer.fromint(intmask((self.val ^ m) - m))

    def unsigned(self):
        return Integer.from_ruint(self.val)

    def eq(self, other):
        other = self._check_size(other)
        return self.val == other.val

    def toint(self):
        if self.size() == 64 and self.read_bit(63):
                raise OverflowError
        return intmask(self.val)

    def touint(self, expected_width=0):
        if expected_width:
            assert self.size() == expected_width
        return self.val

    def tobigint(self):
        jit.jit_debug("SmallInteger.tobigint")
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
        gbv = GenericBitVector.from_bigint(size, rbigint_fromrarith_int(self.val))
        return gbv.replicate(i)

    @staticmethod
    @jit.look_inside_iff(lambda val, size, i: jit.isconstant(i))
    def _replicate(val, size, i):
        res = val
        for _ in range(i - 1):
            res = (res << size) | val
        return res

    def truncate(self, i):
        size = self.size()
        assert i <= size
        return SmallBitVector(i, self.val, normalize=i < size)

    def append_64(self, ui):
        if not self.val:
            return from_ruint(self.size() + 64, ui)
        return GenericBitVector(self.size() + 64, [ui, self.val])

    def pack(self):
        return (self.size(), self.val, None)


UNITIALIZED_BV = SmallBitVector(42, r_uint(0x42))

def rbigint_extract_ruint(self, int_other):
    from rpython.rlib.rbigint import SHIFT
    from rpython.rlib.rbigint import NULLDIGIT, _load_unsigned_digit
    assert int_other >= 0
    assert SHIFT * 2 > 64
    # wordshift, remshift = divmod(int_other, SHIFT)
    wordshift = int_other // SHIFT
    remshift = int_other - wordshift * SHIFT
    numdigits = self.numdigits()
    sign = self.get_sign()
    if sign == -1:
        # XXX needs to be better but I keep running into bugs
        return ~rbigint_extract_ruint(self.invert(), int_other)
    assert sign >= 0
    if wordshift >= numdigits:
        return r_uint(0)
    digit = self.udigit(wordshift)
    # arithmetic shift
    res = r_uint(intmask(r_uint(sign) * digit) >> remshift)
    if wordshift + 1 >= numdigits:
        return res
    return res | (self.udigit(wordshift + 1) << (SHIFT - remshift))

class SparseBitVector(BitVectorWithSize):
    _immutable_fields_ = ['val']

    def __init__(self, size, val):
        assert size > 64
        self._size = size
        assert isinstance(val, r_uint)
        self.val = val

    def __repr__(self):
        return "<SparseBitVector %s %s>"%(self.size(), self.val)

    def _to_generic(self):
        size = GenericBitVector._data_size(self.size())
        resdata = [r_uint(0)] * size
        resdata[0] = self.val
        return GenericBitVector(self._size, resdata, normalize=False)

    def add_int(self, i):
        if isinstance(i, SmallInteger):
            if i.val > 0:
                res = self.val + r_uint(i.val)
                carry = res < self.val
                if not carry:
                    return SparseBitVector(self.size(), res)
        return self._add_int_slow(i)

    def _add_int_slow(self, i):
        return self._to_generic().add_int(i)

    def add_bits(self, other):
        assert self.size() == other.size()
        if isinstance(other, SparseBitVector):
            res = self.val + other.val
            carry = res < self.val
            if not carry:
                return SparseBitVector(self.size(), res)
            other = other._to_generic() # XXX this case can be optimized
        return other.add_bits(self)

    def sub_bits(self, other):
        assert self.size() == other.size()
        if isinstance(other, SparseBitVector):
            if other.val <= self.val: #check for underflow
                return SparseBitVector(self.size(), self.val - other.val)
        return self._to_generic().sub_bits(other)

    def sub_int(self, i):
        if isinstance(i, SmallInteger):
            if 0 <= i.val <= self.val: #check for underflow
                return SparseBitVector(self.size(), self.val - r_uint(i.val))
        return self._to_generic().sub_int(i)

    def lshift(self, i):
        if i < 64:
            if (self.val >> (64 - i)) == 0:
                return SparseBitVector(self.size(), self.val << i)
        return self._to_generic().lshift(i)

    def rshift(self, i):
        assert i >= 0
        if i >= 64:
            return SparseBitVector(self.size(), r_uint(0))
        return SparseBitVector(self.size(), self.val >> i)

    def arith_rshift(self, i):
        assert i >= 0
        if i >= 64:
            return SparseBitVector(self.size(), r_uint(0))
        return SparseBitVector(self.size(), self.val >> i)

    def xor(self, other):
        if isinstance(other, SparseBitVector):
            return SparseBitVector(self.size(), self.val ^ other.val)
        return self._to_generic().xor(other)

    def or_(self, other):
        if isinstance(other, SparseBitVector):
            return SparseBitVector(self.size(), self.val | other.val)
        return self._to_generic().or_(other)

    def and_(self, other):
        if isinstance(other, SparseBitVector):
            return SparseBitVector(self.size(), self.val & other.val)
        # don't force _to_generic here, so GenericBitVector.and_ can return a
        # SparseBitVector again
        return other.and_(self)

    def invert(self):
        return self._to_generic().invert()

    def subrange(self, n, m):
        assert 0 <= m <= n < self.size()
        width = n - m + 1
        if width <= 64:
            return SmallBitVector(width, self.subrange_unwrapped_res(n,m))
        if m >= 64:
            res = r_uint(0)
        else:
            res = self.val >> m
        return SparseBitVector(width, res)

    def subrange_unwrapped_res(self, n, m):
        assert 0 <= m <= n < self.size()
        width = n - m + 1
        assert 0 < width <= 64
        if m >= 64:
            return r_uint(0)
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
        width = s.size()
        assert width <= self.size()
        if width == self.size():
            return s
        assert width == n - m + 1
        generic = False
        if width > 64:
            generic = True
        else:
            sval = s.touint()
            if m > 63:
                generic = True
            elif n >= 64:
                width = 64 - m
                if sval >> width: # upper bits aren't empty
                    generic = True
        if generic:
            return self._to_generic().update_subrange(n, m ,s)
        mask = ~(((r_uint(1) << width) - 1) << m)
        return SparseBitVector(self.size(), (self.val & mask) | (sval << m))

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

    def touint(self, expected_width=0):
        if expected_width:
            self.size() == expected_width
        return self.val

    def tobigint(self):
        jit.jit_debug("SparseBitVector.tobigint")
        return rbigint_fromrarith_int(self.val)

    def replicate(self, i):
        return self._to_generic().replicate(i)

    def truncate(self, i):
        assert i <= self.size()
        if i <= 64:
            return SmallBitVector(i, ruint_mask(i, self.val), normalize=True)
        return SparseBitVector(i, self.val)

    def append_64(self, ui):
        newsize = self.size() + 64
        if not self.val:
            return SparseBitVector(newsize, ui)
        size = GenericBitVector._data_size(newsize)
        resdata = [r_uint(0)] * size
        resdata[1] = self.val
        resdata[0] = ui
        return GenericBitVector(newsize, resdata, normalize=False)

    def pack(self):
        return (self.size(), self.val, None)

def array_from_rbigint(size, rval):
    from rpython.rlib.rbigint import SHIFT
    res = []
    index = 0
    while size > 0:
        res.append(rbigint_extract_ruint(rval, index))
        size -= 64
        index += 64
    if size != 0:
        res[-1] &= ((r_uint(1) << (size + 64)) - 1)
    return res[:]

def rbigint_from_array(data):
    res = rbigint.fromint(0)
    shift = 0
    for element in data:
        res = res.or_(rbigint.fromrarith_int(element).lshift(shift))
        shift += 64
    return res

def array_and_sign_from_rbigint(rval):
    from rpython.rlib.rbigint import SHIFT
    sign = 1
    if rval.int_lt(0):
        sign = -1
        rval = rval.neg()
    res = []
    index = 0
    while rval.int_gt(0):
        res.append(rbigint_extract_ruint(rval, 0))
        index += 64
        rval = rval.rshift(64)
    if not res:
        sign = 0
    return res[:], sign

def rbigint_from_array_and_sign(data, sign):
    res = rbigint.fromint(0)
    shift = 0
    for element in data:
        res = res.or_(rbigint.fromrarith_int(element).lshift(shift))
        shift += 64
    if sign < 0:
        res = res.neg()
    return res


class GenericBitVector(BitVectorWithSize):
    _immutable_fields_ = ['data[*]']

    def __init__(self, size, data, normalize=False):
        assert size > 0
        assert isinstance(data, list)
        self._size = size
        if normalize:
            self._size_mask(data)
        if 1: # not we_are_translated(): XXX disable later
            wordindex, bitindex = _data_indexes(size - 1)
            assert len(data) == wordindex + 1
            if bitindex < 63:
                assert data[wordindex] >> (bitindex + 1) == 0
        self.data = data # list of r_uint

    @staticmethod
    def from_bigint(size, data):
        return GenericBitVector(size, array_from_rbigint(size, data))

    def rval(self):
        return rbigint_from_array(self.data)

    @staticmethod
    @always_inline
    def _data_indexes(pos):
        return pos >> 6, pos & 63

    @staticmethod
    def _data_size(bitwidth):
        return (bitwidth >> 6) + bool(bitwidth & 63)

    def make(self, data, normalize=False):
        return GenericBitVector(self.size(), data, normalize)

    def __repr__(self):
        return "<GenericBitVector %s %s>" % (self.size(), self.rval().hex())
        return "<GenericBitVector %s [%s]>" % (self.size(), ", ".join(hex(x) for x in self.data))

    def _size_mask(self, data):
        width = self.size()
        wordindex, bitindex = _data_indexes(width - 1)
        data[wordindex] = ruint_mask(bitindex + 1, data[wordindex])
        return data

    def add_int(self, i):
        if isinstance(i, SmallInteger):
            if i.val >= 0:
                return self._add_ruint(r_uint(i.val))
            return self._sub_ruint(-r_uint(i.val))
        assert isinstance(i, BigInteger)
        jit.jit_debug("GenericBitVector.add_int")
        # XXX easy to fix
        rval = i.tobigint()
        sign = rval.get_sign()
        if sign == 0:
            return self
        elif sign >= 0:
            return self.add_bits(self.make(array_from_rbigint(self.size(), rval)))
        else:
            return self.sub_bits(self.make(array_from_rbigint(self.size(), rval.abs())))

    @jit.unroll_safe
    def add_bits(self, other):
        assert self.size() == other.size()
        if isinstance(other, GenericBitVector):
            resdata = [r_uint(0)] * len(self.data)
            carry = r_uint(0)
            selfdata = self.data
            for i, othervalue in enumerate(other.data):
                res = selfdata[i] + carry
                carry = r_uint(res < carry)
                res += othervalue
                carry += res < othervalue
                resdata[i] = res
            return self.make(resdata, True)
        else:
            assert isinstance(other, SparseBitVector)
            return self._add_ruint(other.val)

    @jit.unroll_safe
    def _add_ruint(self, othervalue):
        resdata = [r_uint(0)] * len(self.data)
        for i, value in enumerate(self.data):
            res = value + othervalue
            resdata[i] = res
            othervalue = r_uint(res < value)
        return self.make(resdata, True)

    @jit.unroll_safe
    def sub_bits(self, other):
        assert self.size() == other.size()
        resdata = [r_uint(0)] * len(self.data)
        if isinstance(other, GenericBitVector):
            carry = r_uint(0)
            selfdata = self.data
            for i, value in enumerate(other.data):
                value += carry
                carry = r_uint(value < carry)
                selfvalue = selfdata[i]
                carry += selfvalue < value
                resdata[i] = selfvalue - value
            return self.make(resdata, True)
        assert isinstance(other, SparseBitVector)
        return self._sub_ruint(other.val)

    @jit.unroll_safe
    def _sub_ruint(self, othervalue):
        resdata = [r_uint(0)] * len(self.data)
        for i, value in enumerate(self.data):
            carry = r_uint(value < othervalue)
            resdata[i] = value - othervalue
            othervalue = carry
        return self.make(resdata, True)

    def sub_int(self, i):
        if isinstance(i, SmallInteger):
            if i.val >= 0:
                self._sub_ruint(r_uint(i.val))
            else:
                self._add_ruint(-r_uint(i.val))
        jit.jit_debug("GenericBitVector.sub_int")
        rval = i.tobigint()
        sign = rval.get_sign()
        if sign == 0:
            return self
        elif sign >= 0:
            return self.sub_bits(self.make(array_from_rbigint(self.size(), rval)))
        else:
            return self.add_bits(self.make(array_from_rbigint(self.size(), rval.abs())))

    @jit.look_inside_iff(lambda self, i: jit.isconstant(i))
    def lshift(self, i):
        from rpython.rlib.rbigint import NULLDIGIT, _load_unsigned_digit
        if i < 0:
            raise ValueError("negative shift count")
        elif i == 0:
            return self
        size = self.size()
        if i >= size:
            return SparseBitVector(size, r_uint(0))
        wordshift, bitshift = _data_indexes(i)
        data = self.data
        resdata = [r_uint(0)] * len(data)
        if not bitshift:
            for i in range(len(data) - wordshift):
                resdata[i + wordshift] = data[i]
        else:
            accum = r_uint(0)
            antibitshift = 64 - bitshift
            j = 0
            for i in range(len(data) - wordshift):
                digit = data[i]
                accum |= digit << bitshift
                resdata[wordshift] = accum
                accum = digit >> antibitshift
                wordshift += 1
        return self.make(resdata, True)

    @jit.unroll_safe
    def rshift(self, i):
        if i < 0:
            raise ValueError("negative shift count")
        if i >= self.size():
            return SparseBitVector(self.size(), r_uint(0))
        if i == 0:
            return self
        wordshift, bitshift = _data_indexes(i)
        data = self.data
        resdata = [r_uint(0)] * len(data)
        if not bitshift:
            for i in range(len(data) - wordshift):
                resdata[i] = data[i + wordshift]
        else:
            antibitshift = 64 - bitshift
            accum = r_uint(0)
            for i in range(len(data) - 1, wordshift - 1, -1):
                digit = data[i]
                accum |= digit >> bitshift
                resdata[i - wordshift] = accum
                accum = digit << antibitshift
        return self.make(resdata)

    def arith_rshift(self, i):
        # XXX can do the invert rshift invert trick for negative bitvectors
        assert i >= 0
        size = self.size()
        if i >= size:
            i = size
        highest_bit = self.read_bit(size - 1)
        jit.jit_debug("GenericBitVector.arith_rshift")
        rval = self.rval()
        highest_bit = rval.abs_rshift_and_mask(r_ulonglong(size - 1), 1)
        res = rval.rshift(i)
        if highest_bit:
            res = res.or_(MASKS.get(i).lshift(size - i))
        return GenericBitVector.from_bigint(size, res)

    @jit.unroll_safe
    def xor(self, other):
        resdata = self.data[:]
        if isinstance(other, GenericBitVector):
            for i, value in enumerate(other.data):
                resdata[i] ^= value
        else:
            assert isinstance(other, SparseBitVector)
            resdata[0] ^= other.val
        return self.make(resdata)

    @jit.unroll_safe
    def or_(self, other):
        resdata = self.data[:]
        if isinstance(other, GenericBitVector):
            for i, value in enumerate(other.data):
                resdata[i] |= value
        else:
            assert isinstance(other, SparseBitVector)
            resdata[0] |= other.val
        return self.make(resdata)

    @jit.unroll_safe
    def and_(self, other):
        if isinstance(other, GenericBitVector):
            resdata = self.data[:]
            for i, value in enumerate(other.data):
                resdata[i] &= value
            return self.make(resdata)
        else:
            assert isinstance(other, SparseBitVector)
            return SparseBitVector(self.size(), self.data[0] & other.val)

    @jit.unroll_safe
    def invert(self):
        resdata = [~x for x in self.data]
        return self.make(resdata, normalize=True)

    def subrange(self, n, m):
        width = n - m + 1
        if width <= 64:
            return SmallBitVector(width, self.subrange_unwrapped_res(n, m))
        if m == 0:
            return self.truncate(width)
        return self.rshift(m).truncate(width) # XXX do it in one call

    def subrange_unwrapped_res(self, n, m):
        width = n - m + 1
        assert 0 < width <= 64
        wordshift, bitshift = _data_indexes(m)
        size = self.size()
        data = self.data
        res = data[wordshift]
        if bitshift:
            res >>= bitshift
            if wordshift + 1 < len(data):
                antibitshift = 64 - bitshift
                assert 0 <= antibitshift < 64
                res |= (data[wordshift + 1] << antibitshift)
        return ruint_mask(width, res)

    @jit.unroll_safe
    def zero_extend(self, i):
        if i == self.size():
            return self
        assert i > self.size()
        wordsize, bitsize = _data_indexes(i)
        targetsize = wordsize + bool(bitsize)
        resdata = [r_uint(0)] * targetsize
        for index, value in enumerate(self.data):
            resdata[index] = value
        return GenericBitVector(i, resdata)

    def sign_extend(self, i):
        size = self.size()
        if i == size:
            return self
        return self._sign_extend(size, self.data, i)

    @staticmethod
    @jit.unroll_safe
    def _sign_extend(size, data, i):
        assert i > size
        hbit_word_index, hbit_index = GenericBitVector._data_indexes(size - 1)
        upper_bits = -r_uint((data[hbit_word_index] >> hbit_index) & 1)
        wordsize, bitsize = GenericBitVector._data_indexes(i)
        targetsize = wordsize + bool(bitsize)
        resdata = [upper_bits] * targetsize
        lastindex, bits = GenericBitVector._data_indexes(size)
        for index in range(lastindex):
            resdata[index] = data[index]
        if bits:
            resdata[lastindex] = data[lastindex] | (upper_bits << bits)
        return GenericBitVector(i, resdata, True)

    def read_bit(self, pos):
        wordindex, bitindex = _data_indexes(pos)
        return bool((self.data[wordindex] >> bitindex) & 1)

    def update_bit(self, pos, bit):
        wordindex, bitindex = _data_indexes(pos)
        resdata = self.data[:]
        word = resdata[wordindex]
        mask = r_uint(1) << bitindex
        if bit:
            newword = word | mask
        else:
            newword = word & ~mask
        resdata[wordindex] = newword
        return GenericBitVector(self.size(), resdata)

    @jit.unroll_safe
    def update_subrange(self, n, m, other):
        width = other.size()
        assert width == n - m + 1

        start_wordindex, start_bitindex = _data_indexes(m)
        end_wordindex, end_bitindex = _data_indexes(n + 1) # exclusive
        if width <= 64:
            assert isinstance(other, SmallBitVector)
            otherdata = [other.val]
        else:
            if isinstance(other, SparseBitVector):
                otherdata = other._to_generic().data
            else:
                assert isinstance(other, GenericBitVector)
                otherdata = other.data
        resdata = self.data[:]
        if not start_bitindex:
            j = 0
            for index in range(start_wordindex, end_wordindex):
                resdata[index] = otherdata[j]
                j += 1
            accum = r_uint(0)
        else:
            accum = self.data[start_wordindex] & ((1 << start_bitindex) - 1)
            antibitshift = 64 - start_bitindex
            j = 0
            for index in range(start_wordindex, end_wordindex):
                digit = otherdata[j]
                accum |= digit << start_bitindex
                resdata[index] = accum
                accum = digit >> antibitshift
                j += 1
        if end_bitindex:
            mask = ~((r_uint(1) << end_bitindex) - 1)
            last_digit = (resdata[end_wordindex] & mask) | accum
            if start_bitindex < end_bitindex:
                last_digit |= otherdata[j] << start_bitindex
            resdata[end_wordindex] = last_digit
        return GenericBitVector(self.size(), resdata, normalize=False)

    def signed(self):
        n = self.size()
        assert n > 0
        m = ONERBIGINT.lshift(n - 1)
        jit.jit_debug("GenericBitVector.signed")
        return Integer.from_bigint(self.rval().xor(m).sub(m))

    def unsigned(self):
        return Integer.from_data_and_sign(self.data, 1)

    @jit.unroll_safe
    def eq(self, other):
        assert self.size() == other.size()
        if isinstance(other, GenericBitVector):
            return self.data == other.data
        else:
            assert isinstance(other, SparseBitVector)
            for i in range(1, len(self.data)):
                if self.data[i]:
                    return False
            return other.val == self.data[0]

    @jit.unroll_safe
    def toint(self):
        for i in range(1, len(self.data)):
            if self.data[i]:
                raise ValueError
        lastdigit = self.data[0]
        if lastdigit >> 63:
            raise ValueError
        return intmask(lastdigit)

    @jit.unroll_safe
    def touint(self, expected_width=0):
        if expected_width:
            assert self.size() == expected_width
        for i in range(1, len(self.data)):
            if self.data[i]:
                raise ValueError
        return self.data[0]

    def tobigint(self):
        jit.jit_debug("GenericBitVector.tobigint")
        return rbigint_from_array(self.data)

    @jit.unroll_safe
    def replicate(self, i):
        size = self.size()
        jit.jit_debug("GenericBitVector.replicate")
        res = val = self.rval()
        for _ in range(i - 1):
            res = res.lshift(size).or_(val)
        return GenericBitVector.from_bigint(size * i, res)

    def truncate(self, i):
        assert i >= 0
        size = self.size()
        assert i <= self.size()
        if i <= 64:
            return SmallBitVector(i, self.data[0], normalize=True)
        if i == size:
            return self
        length = GenericBitVector._data_size(i)
        assert length >= 0
        return GenericBitVector(i, self.data[:length], normalize=True)

    @staticmethod
    @jit.unroll_safe
    def _append(self, other):
        # self and other can be arbitrary bitvectors
        if isinstance(other, SmallBitVector):
            if other.size() == 64:
                return self.append_64(other.val)
        res = self.zero_extend(self.size() + other.size()).lshift(other.size())
        assert not isinstance(res, SmallBitVector)
        if isinstance(res, SparseBitVector):
            if isinstance(other, SmallBitVector):
                res.val |= other.val
                return res
        assert isinstance(res, GenericBitVector)
        if isinstance(other, SmallBitVector):
            res.data[0] |= other.val
            return res
        if isinstance(other, SparseBitVector):
            res.data[0] |= other.val
            return res
        assert isinstance(other, GenericBitVector)
        for index, otherdata in enumerate(other.data):
            res.data[index] |= otherdata
        return res

    def append_64(self, ui):
        return GenericBitVector(self.size() + 64, [ui] + self.data)

    def pack(self):
        return (self.size(), r_uint(0xdeaddead), self.data)


class Integer(object):
    _attrs_ = []

    @staticmethod
    def fromint(val):
        return SmallInteger(val)

    @staticmethod
    @not_rpython # translation time only
    def fromlong(val):
        if MININT <= val <= MAXINT:
            return SmallInteger(int(val))
        else:
            return Integer.from_bigint(rbigint.fromlong(val))

    @staticmethod
    def from_bigint(rval):
        data, sign = array_and_sign_from_rbigint(rval)
        return Integer.from_data_and_sign(data, sign)

    @staticmethod
    @jit.unroll_safe
    def from_data_and_sign(data, sign):
        assert sign in (0, 1, -1)
        # normalize
        index = len(data) - 1
        while index >= 0 and not data[index]:
            index -= 1
        if index == -1:
            return SmallInteger(0)
        # XXX if index == 0, could fit into a SmallInteger
        if index != len(data) - 1:
            end = index + 1
            assert end > 0
            data = data[:end]
        return BigInteger(data, sign)

    @staticmethod
    def fromstr(val):
        value = 0
        try:
            return SmallInteger(string_to_int(val, 10))
        except ParseStringOverflowError as e:
            e.parser.rewind()
            return Integer.from_bigint(rbigint._from_numberstring_parser(e.parser))

    @staticmethod
    @always_inline
    def from_ruint(val):
        if val & (r_uint(1)<<63):
            # bigger than biggest signed int
            return BigInteger([val], 1)
        return SmallInteger(intmask(val))

    def tolong(self): # only for tests:
        return self.tobigint().tolong()

    @staticmethod
    def unpack(val, rval):
        if rval is None:
            return SmallInteger(val)
        return BigInteger(rval, val)

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
        jit.jit_debug("SmallInteger.tobigint")
        return rbigint.fromint(self.val)

    def slice(self, len, start):
        n = self.val >> start
        if len > 64:
            if n > 0:
                return SparseBitVector(len, r_uint(n))
            jit.jit_debug("SmallInteger.slice")
            return from_bigint(len, rbigint.fromint(n))
        return from_ruint(len, r_uint(n))

    def slice_unwrapped_res(self, len, start):
        return ruint_mask(len, r_uint(self.val >> start))

    def set_slice_int(self, len, start, bv):
        if len > 64 or start + len >= 64:
            jit.jit_debug("SmallInteger.set_slice_int")
            return BigInteger._set_slice_int(self.tobigint(), len, start, bv)
        assert len == bv.size()
        out_val = self.val
        slice_one = ((1 << bv.size()) - 1) << start
        out_val = out_val & (~slice_one)
        out_val = out_val | (bv.toint() << start) & ((1 << (start + bv.size())) - 1)
        return SmallInteger(out_val)

    def eq(self, other):
        if isinstance(other, SmallInteger):
            return self.val == other.val
        return other.int_eq(self.val)

    def int_eq(self, other):
        return self.val == other

    def lt(self, other):
        if isinstance(other, SmallInteger):
            return self.val < other.val
        assert isinstance(other, BigInteger)
        selfdata, selfsign = _data_and_sign_from_int(self.val)
        return _data_lt(selfdata, selfsign, other.data, other.sign)

    def le(self, other):
        if isinstance(other, SmallInteger):
            return self.val <= other.val
        assert isinstance(other, BigInteger)
        jit.jit_debug("SmallInteger.le")
        return other.rval().int_ge(self.val)

    def gt(self, other):
        if isinstance(other, SmallInteger):
            return self.val > other.val
        assert isinstance(other, BigInteger)
        jit.jit_debug("SmallInteger.gt")
        return other.rval().int_lt(self.val)

    def ge(self, other):
        if isinstance(other, SmallInteger):
            return self.val >= other.val
        assert isinstance(other, BigInteger)
        return other.le(self)

    def abs(self):
        if self.val < 0:
            return self.neg()
        return self

    def add(self, other):
        return other.int_add(self.val)

    def int_add(self, other):
        return SmallInteger.add_i_i(self.val, other)

    def sub(self, other):
        if isinstance(other, SmallInteger):
            return SmallInteger.sub_i_i(self.val, other.val)
        if not self.val:
            return other.neg()
        return other.int_sub(self.val).neg()

    def int_sub(self, other):
        return SmallInteger.sub_i_i(self.val, other)

    def neg(self):
        if self.val == MININT:
            return BigInteger([r_uint(self.val)], 1)
        return SmallInteger(-self.val)

    def mul(self, other):
        if isinstance(other, SmallInteger):
            try:
                return SmallInteger(ovfcheck(self.val * other.val))
            except OverflowError:
                jit.jit_debug("SmallInteger.mul ovf")
                return Integer.from_bigint(self.tobigint().int_mul(other.val))
        else:
            assert isinstance(other, BigInteger)
            return other.mul(self)

    def int_mul(self, other):
        return SmallInteger.mul_i_i(self.val, other)

    def tdiv(self, other):
        # rounds towards zero, like in C, not like in python
        if isinstance(other, SmallInteger):
            if other.val == 0:
                raise ZeroDivisionError
            if not (self.val == -2**63 and other.val == -1):
                return SmallInteger(int_c_div(self.val, other.val))
            return self.abs()
        jit.jit_debug("SmallInteger.tdiv")
        assert isinstance(other, BigInteger)
        div, rem = bigint_divrem(self.tobigint(), other.tobigint())
        return Integer.from_bigint(div)

    def tmod(self, other):
        # C behaviour
        if isinstance(other, SmallInteger):
            if other.val == 0:
                raise ZeroDivisionError
            if not (self.val == -2**63 and other.val == -1):
                return SmallInteger(int_c_mod(self.val, other.val))
            return SmallInteger(0) # anything % -1 == 0
        assert isinstance(other, BigInteger)
        jit.jit_debug("SmallInteger.tmod")
        other = other.tobigint()
        if other.get_sign() == 0:
            raise ZeroDivisionError
        div, rem = bigint_divrem(self.tobigint(), other)
        return Integer.from_bigint(rem)

    def ediv(self, other):
        if not isinstance(other, SmallInteger) or other.val == MININT or self.val == MININT:
            jit.jit_debug("SmallInteger.ediv")
            return Integer.from_bigint(self.tobigint()).ediv(other)
        other = other.val
        if other == 0:
            raise ZeroDivisionError
        if other > 0:
            return SmallInteger(self.val // other)
        else:
            return SmallInteger(-(self.val // -other))

    def emod(self, other):
        if not isinstance(other, SmallInteger) or other.val == MININT or self.val == MININT:
            jit.jit_debug("SmallInteger.emod")
            return Integer.from_bigint(self.tobigint()).emod(other)
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
        return self.lshift_i_i(self.val, i)

    @staticmethod
    def lshift_i_i(a, i):
        if not a:
            return SmallInteger(0)
        if i < 64:
            try:
                return SmallInteger(ovfcheck(a << i))
            except OverflowError:
                pass
        jit.jit_debug("SmallInteger.lshift_i_i ovf")
        return Integer.from_bigint(rbigint.fromint(a).lshift(i))

    @staticmethod
    def add_i_i(a, b):
        try:
            return SmallInteger(ovfcheck(a + b))
        except OverflowError:
            jit.jit_debug("SmallInteger.add_i_i ovf")
            return Integer.from_bigint(rbigint.fromint(a).int_add(b))

    @staticmethod
    def sub_i_i(a, b):
        try:
            return SmallInteger(ovfcheck(a - b))
        except OverflowError:
            jit.jit_debug("SmallInteger.sub_i_i ovf")
            return Integer.from_bigint(rbigint.fromint(b).int_sub(a).neg())

    @staticmethod
    def mul_i_i(a, b):
        try:
            return SmallInteger(ovfcheck(a * b))
        except OverflowError:
            return Integer.from_bigint(rbigint.fromint(a).int_mul(b))

    def pack(self):
        return (self.val, None)


class BigInteger(Integer):
    _immutable_fields_ = ['data[*]', 'sign']

    def __init__(self, data, sign):
        self.data = data
        self.sign = sign

    def __repr__(self):
        return "<BigInteger %s>" % (self.rval().str(), )

    def rval(self):
        jit.jit_debug("BigInteger.rval")
        return rbigint_from_array_and_sign(self.data, self.sign)

    def str(self):
        jit.jit_debug("BigInteger.str")
        return self.rval().str()

    def hex(self):
        jit.jit_debug("BigInteger.hex")
        return self.rval().hex()

    def toint(self):
        jit.jit_debug("BigInteger.toint")
        return self.rval().toint()

    def touint(self):
        jit.jit_debug("BigInteger.touint")
        return self.rval().touint()

    def tolong(self):
        res = 0
        shift = 0
        for digit in self.data:
            res |= int(digit) << shift
            shift += 64
        return res * self.sign

    def tobigint(self):
        jit.jit_debug("BigInteger.tobigint")
        return self.rval()

    def slice(self, len, start):
        if len <= 64:
            return SmallBitVector(len, self.slice_unwrapped_res(len, start))
        jit.jit_debug("BitInteger.slice")
        if start == 0:
            n = self.rval()
        else:
            n = self.rshift(start).tobigint()
        return from_bigint(len, n)

    def set_slice_int(self, len, start, bv):
        jit.jit_debug("BigInteger.set_slice_int")
        return self._set_slice_int(self.rval(), len, start, bv)

    @staticmethod
    def _set_slice_int(rval, len, start, bv):
        assert len == bv.size()
        slice_one = MASKS.get(bv.size()).lshift(start)
        out_val = rval.and_(slice_one.invert())
        jit.jit_debug("BigInteger._set_slice_int")
        out_val = out_val.or_(bv.tobigint().lshift(start))
        return Integer.from_bigint(out_val)

    def slice_unwrapped_res(self, length, start):
        if self.sign == 0:
            return r_uint(0)
        elif self.sign == -1:
            # invert self, via ~x = -(x+1)
            jit.jit_debug("BigInteger.slice_unwrapped_res could be better")
            res = self.int_add(1).neg().slice_unwrapped_res(length, start)
            return ruint_mask(length, ~res)
        wordindex, bitindex = _data_indexes(start)
        if wordindex >= len(self.data):
            return r_uint(0)
        res = self.data[wordindex] >> bitindex
        if bitindex:
            antibitshift = 64 - bitindex
            if wordindex + 1 < len(self.data):
                res |= self.data[wordindex + 1] << antibitshift
        return ruint_mask(length, res)

    @jit.unroll_safe
    def eq(self, other):
        if isinstance(other, SmallInteger):
            return self.int_eq(other.val)
        assert isinstance(other, BigInteger)
        if self.sign != other.sign:
            return False
        if len(self.data) != len(other.data):
            return False
        for index in range(len(self.data)):
            if self.data[index] != other.data[index]:
                return False
        return True

    def int_eq(self, other):
        if self.sign != intsign(other):
            return False
        other = r_uint(other)
        if self.sign == 0:
            return True
        if len(self.data) != 1:
            return False
        if self.sign < 0:
            other = -other
        return self.data[0] == other

    def lt(self, other):
        if isinstance(other, SmallInteger):
            # XXX could be improved, but the logic is definitely right
            otherdata, othersign = _data_and_sign_from_int(other.val)
        else:
            assert isinstance(other, BigInteger)
            othersign = other.sign
            otherdata = other.data
        return _data_lt(self.data, self.sign, otherdata, othersign)

    def le(self, other):
        return not other.lt(self)

    def gt(self, other):
        return other.lt(self)

    def ge(self, other):
        return not self.lt(other)

    def abs(self):
        if self.sign != -1:
            return self
        return BigInteger(self.data, 1)

    def add(self, other):
        if self.sign == 0:
            return other
        if isinstance(other, SmallInteger):
            if not other.val:
                return self
            return self.int_add(other.val)
        assert isinstance(other, BigInteger)
        othersign = other.sign
        if othersign == 0:
            return self
        otherdata = other.data
        return self._add_data(otherdata, othersign)

    def _add_data(self, otherdata, othersign):
        if self.sign == othersign:
            resultdata, sign = _data_add(self.data, otherdata)
        else:
            resultdata, sign = _data_sub(otherdata, self.data)
        return Integer.from_data_and_sign(resultdata, sign * othersign)

    def int_add(self, other):
        if not other:
            return self
        if not self.sign:
            return SmallInteger(other)
        # XXX could be improved, but the logic is definitely right
        otherdata, othersign = _data_and_sign_from_int(other)
        return self._add_data(otherdata, othersign)

    def sub(self, other):
        if isinstance(other, SmallInteger):
            if not self.sign:
                return other.neg()
            return self.int_sub(other.val)
        assert isinstance(other, BigInteger)
        othersign = other.sign
        if othersign == 0:
            return self
        otherdata = other.data
        if self.sign == 0:
            return Integer.from_data_and_sign(otherdata, -othersign)
        return self._sub_data(otherdata, othersign)

    def _sub_data(self, otherdata, othersign):
        assert self.sign
        assert othersign
        if self.sign == othersign:
            resultdata, sign = _data_sub(self.data, otherdata)
        else:
            resultdata, sign = _data_add(self.data, otherdata)
        return Integer.from_data_and_sign(resultdata, sign * self.sign)

    def int_sub(self, other):
        if not other:
            return self
        if not self.sign:
            return SmallInteger(other).neg()
        # XXX could be improved, but the logic is definitely right
        otherdata, othersign = _data_and_sign_from_int(other)
        return self._sub_data(otherdata, othersign)

    def neg(self):
        return Integer.from_data_and_sign(self.data, -self.sign)

    def mul(self, other):
        if isinstance(other, SmallInteger):
            return self.int_mul(other.val)
        assert isinstance(other, BigInteger)
        jit.jit_debug("BigInteger.mul")
        return Integer.from_bigint(self.rval().mul(other.rval()))

    def int_mul(self, other):
        if not other:
            return SmallInteger(0)
        if other == 1:
            return self
        if other & (other - 1) == 0:
            shift = self._shift_amount(other)
            return self.lshift(shift)
        jit.jit_debug("BigInteger.int_mul")
        return Integer.from_bigint(self.rval().int_mul(other))

    def tdiv(self, other):
        # rounds towards zero, like in C, not like in python
        if isinstance(other, SmallInteger) and int_in_valid_range(other.val):
            other = other.val
            if other == 0:
                raise ZeroDivisionError
            if other > 0 and other & (other - 1) == 0 and self.sign >= 0:
                # can use shift
                return self.rshift(self._shift_amount(other))
            jit.jit_debug("BigInteger.tdiv")
            div, rem = bigint_divrem1(self.rval(), other)
            return Integer.from_bigint(div)
        jit.jit_debug("BigInteger.tdiv")
        other = other.tobigint()
        if other.get_sign() == 0:
            raise ZeroDivisionError
        div, rem = bigint_divrem(self.tobigint(), other)
        return Integer.from_bigint(div)

    @staticmethod
    @jit.elidable
    def _shift_amount(poweroftwo):
        assert poweroftwo & (poweroftwo - 1) == 0
        shift = 0
        while 1 << shift != poweroftwo:
            shift += 1
        return shift

    def tmod(self, other):
        jit.jit_debug("BigInteger.tmod")
        if isinstance(other, SmallInteger) and int_in_valid_range(other.val):
            other = other.val
            if other == 0:
                raise ZeroDivisionError
            div, rem = bigint_divrem1(self.rval(), other)
            return SmallInteger(rem)

        other = other.tobigint()
        if other.get_sign() == 0:
            raise ZeroDivisionError
        div, rem = bigint_divrem(self.tobigint(), other)
        return Integer.from_bigint(rem)

    def ediv(self, other):
        jit.jit_debug("BigInteger.ediv")
        other = other.tobigint()
        if other.int_eq(0):
            raise ZeroDivisionError
        if other.int_gt(0):
            return Integer.from_bigint(self.rval().floordiv(other))
        else:
            return Integer.from_bigint(self.rval().floordiv(other.neg()).neg())

    def emod(self, other):
        jit.jit_debug("BigInteger.emod")
        other = other.tobigint()
        if other.int_eq(0):
            raise ZeroDivisionError
        res = self.rval().mod(other)
        if res.int_lt(0):
            res = res.sub(other)
        return Integer.from_bigint(res)

    @jit.unroll_safe
    def rshift(self, i):
        assert i >= 0
        if i == 0 or self.sign == 0:
            return self
        if self.sign < 0:
            jit.jit_debug("BigInteger.rshift negative")
            return Integer.from_bigint(self.rval().rshift(i))

        wordshift, bitshift = _data_indexes(i)
        data = self.data
        newsize = len(data) - wordshift
        if newsize <= 0:
            return SmallInteger(0)

        resdata = [r_uint(0)] * newsize
        if not bitshift:
            for i in range(newsize):
                resdata[i] = data[i + wordshift]
        else:
            antibitshift = 64 - bitshift
            accum = r_uint(0)
            for i in range(len(data) - 1, wordshift - 1, -1):
                digit = data[i]
                accum |= digit >> bitshift
                resdata[i - wordshift] = accum
                accum = digit << antibitshift
        return Integer.from_data_and_sign(resdata, 1)

    def lshift(self, i):
        assert i >= 0
        if i == 0 or self.sign == 0:
            return self
        resdata = self._lshift_data(self.data, i)
        return Integer.from_data_and_sign(resdata, self.sign)

    @staticmethod
    @jit.look_inside_iff(lambda data, i: jit.isconstant(i))
    def _lshift_data(data, i):
        wordshift, bitshift = _data_indexes(i)
        if not bitshift:
            resdata = [r_uint(0)] * wordshift + data
        else:
            accum = r_uint(0)
            newsize = len(data) + wordshift + 1
            resdata = [r_uint(0)] * newsize
            antibitshift = 64 - bitshift
            j = 0
            for i in range(len(data)):
                digit = data[i]
                accum |= digit << bitshift
                resdata[wordshift] = accum
                accum = digit >> antibitshift
                wordshift += 1
            resdata[wordshift] = accum
        return resdata

    def pack(self):
        jit.jit_debug("BigInteger.pack")
        return (self.sign, self.data)


# common helper functions for manipulating arrays of digits

@always_inline
def _data_indexes(pos):
    return pos >> 6, pos & 63

def intsign(i):
    if i == 0:
        return 0
    return -1 if i < 0 else 1

@always_inline
def _data_and_sign_from_int(value):
    if not value:
        return [], 0
    sign = intsign(value)
    return [r_uint(sign) * r_uint(value)], sign

@jit.unroll_safe
def _data_add(selfdata, otherdata):
    size_self = len(selfdata)
    size_other = len(otherdata)
    assert size_self and size_other

    # Ensure selfdata is the larger of the two:
    if size_self < size_other:
        selfdata, otherdata = otherdata, selfdata
        size_self, size_other = size_other, size_self
    resdata = [r_uint(0)] * (size_self + 1)
    index = 0
    carry = r_uint(0)
    i = 0
    for i, othervalue in enumerate(otherdata):
        res = selfdata[i] + carry
        carry = r_uint(res < carry)
        res += othervalue
        carry += res < othervalue
        resdata[i] = res
    for i in range(size_other, size_self):
        res = selfdata[i] + carry
        carry = r_uint(res < carry)
        resdata[i] = res
    resdata[i + 1] = carry
    return resdata, 1

@jit.unroll_safe
def _data_sub(selfdata, otherdata):
    size_self = len(selfdata)
    size_other = len(otherdata)
    sign = 1

    # Ensure selfdata is the larger of the two:
    if size_self < size_other:
        sign = -1
        selfdata, otherdata = otherdata, selfdata
        size_self, size_other = size_other, size_self
    elif size_self == size_other:
        # Find highest digit where selfdata and otherdata differ:
        i = size_self - 1
        while i >= 0 and selfdata[i] == otherdata[i]:
            i -= 1
        if i < 0:
            return [], 0
        if selfdata[i] < otherdata[i]:
            sign = -1
            selfdata, otherdata = otherdata, selfdata
        size_self = size_other = i+1

    resdata = [r_uint(0)] * size_self
    carry = r_uint(0)
    i = 0
    while i < size_other:
        value = otherdata[i]
        value += carry
        carry = r_uint(value < carry)
        selfvalue = selfdata[i]
        carry += selfvalue < value
        resdata[i] = selfvalue - value
        i += 1
    while i < size_self:
        selfvalue = selfdata[i]
        resdata[i] = selfvalue - carry
        carry = r_uint(selfvalue < carry)
        i += 1
    assert carry == 0
    return resdata, sign

@jit.unroll_safe
def _data_lt(selfdata, selfsign, otherdata, othersign):
    if selfsign > othersign:
        return False
    if selfsign < othersign:
        return True
    ld1 = len(selfdata)
    ld2 = len(otherdata)
    if ld1 > ld2:
        if othersign > 0:
            return False
        else:
            return True
    elif ld1 < ld2:
        if othersign > 0:
            return True
        else:
            return False
    i = ld1 - 1
    while i >= 0:
        d1 = selfdata[i]
        d2 = otherdata[i]
        if d1 < d2:
            if othersign > 0:
                return True
            else:
                return False
        elif d1 > d2:
            if othersign > 0:
                return False
            else:
                return True
        i -= 1
    return False

