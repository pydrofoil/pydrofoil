import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong
from rpython.rlib.objectmodel import always_inline, specialize, dont_inline
from rpython.rlib.rstring import (
    ParseStringError, ParseStringOverflowError)

# implement bitvectors in a weird way. they are triples:
# (size, value-as-ruint or -1, None or value-as-rbigint)
# this is done so we can pass them as three local variables everywhere and need
# no allocation in a lot of situations.

# rules for what needs an inline:
# - everything that returns a triple should be inlined
# - all the complicated bigint calculation should be hidden if possible


@always_inline
@specialize.arg_or_var(0)
def from_ruint(size, val):
    if size <= 64:
        return small_bv(size, val, True)
    return big_bv(size, rbigint.fromrarith_int(val), True)

@always_inline
def from_bigint(size, rval):
    if size <= 64:
        return small_bv(size, bigint_size_mask(size, rval).touint())
    return big_bv(size, rval, True)

@always_inline
def from_int(size, val):
    return from_ruint(size, r_uint(val))

@always_inline
def small_bv(size, val, normalize=False):
    assert size <= 64
    assert isinstance(val, r_uint)
    if normalize and size != 64:
        val = val & ((r_uint(1) << size) - 1)
    return (size, val, None)

@always_inline
def big_bv(size, rval, normalize=False):
    assert size > 64
    if normalize:
        rval = bigint_size_mask(size, rval)
    return (size, r_uint(-1), rval)

@dont_inline
def bigint_size_mask(size, rval):
    return rval.and_(rbigint.fromint(1).lshift(size).int_sub(1))

@always_inline
def bv_size(bv):
    size, val, rval = bv
    return size

@always_inline
def bv_size_as_int(bv):
    size, val, rval = bv
    return int_fromint(size)

def bv_string_of_bits(bv):
    size = bv[0]
    rval = bv_tobigint(bv)
    if size % 4 == 0:
        res = rval.format("0123456789ABCDEF")
        return "0x%s%s" % ("0" * max(0, size // 4 - len(res)), res)
    else:
        res = rval.format("01")
        return "0b%s%s" % ("0" * max(0, size - len(res)), res)

def bv_tolong(bv): # only for tests
    return bv_tobigint(bv).tolong()

def bv_signed(bv):
    size, val, rval = bv
    if rval is None:
        if size == 64:
            return int_fromint(intmask(val))
        assert size > 0
        u1 = r_uint(1)
        m = u1 << (size - 1)
        op = val & ((u1 << size) - 1) # mask off higher bits to be sure
        return int_fromint(intmask((op ^ m) - m))
    else:
        assert size > 64
        u1 = rbigint.fromint(1)
        m = u1.lshift(size - 1)
        op = rval
        op = op.and_((u1.lshift(size)).int_sub(1)) # mask off higher bits to be sure
        return int_frombigint(op.xor(m).sub(m))

def bv_unsigned(bv):
    size, val, rval = bv
    if rval is None:
        return int_fromruint(val)
    else:
        return int_frombigint(rval)

def bv_lshift(bv, i):
    size, val, rval = bv
    if rval is None:
        assert i >= 0
        if i >= 64:
            return small_bv(size, r_uint(0))
        return small_bv(size, val << i, True)
    else:
        return big_bv(size, rval.lshift(i), True)

def bv_rshift(bv, i):
    size, val, rval = bv
    if rval is None:
        assert i >= 0
        if i >= size:
            return small_bv(size, r_uint(0))
        return small_bv(size, val >> i)
    else:
        return big_bv(size, rval.rshift(i), True)

def bv_lshift_bits(self, other):
    return bv_lshift(self, bv_toint(other))

def bv_rshift_bits(self, other):
    return bv_rshift(self, bv_toint(other))

def bv_and(self, other):
    sizea, vala, rvala = self
    sizeb, valb, rvalb = other
    assert sizea == sizeb
    if rvala is None:
        assert rvalb is None
        return small_bv(sizea, vala & valb, True)
    else:
        assert rvalb is not None
        return big_bv(sizea, rvala.and_(rvalb), True)

def bv_or(self, other):
    sizea, vala, rvala = self
    sizeb, valb, rvalb = other
    assert sizea == sizeb
    if rvala is None:
        assert rvalb is None
        return small_bv(sizea, vala | valb, True)
    else:
        assert rvalb is not None
        return big_bv(sizea, rvala.or_(rvalb), True)

def bv_xor(self, other):
    sizea, vala, rvala = self
    sizeb, valb, rvalb = other
    assert sizea == sizeb
    if rvala is None:
        assert rvalb is None
        return small_bv(sizea, vala ^ valb, True)
    else:
        assert rvalb is not None
        return big_bv(sizea, rvala.xor(rvalb), True)

def bv_invert(bv):
    size, val, rval = bv
    if rval is None:
        return small_bv(size, ~val, True)
    else:
        return big_bv(size, rval.invert(), True)

def bv_eq(self, other):
    sizea, vala, rvala = self
    sizeb, valb, rvalb = other
    assert sizea == sizeb
    if rvala is None:
        assert rvalb is None
        return vala == valb
    else:
        assert rvalb is not None
        return rvala.eq(valb)

def bv_toint(bv):
    size, val, rval = bv
    if rval is None:
        return intmask(val)
    else:
        return rval.toint()

def bv_touint(bv):
    size, val, rval = bv
    if rval is None:
        return val
    else:
        return rval.touint()

def bv_tobigint(bv):
    size, val, rval = bv
    if rval is None:
        return rbigint.fromrarith_int(val)
    else:
        return rval

def bv_read_bit(bv, pos):
    size, val, rval = bv
    assert pos < size
    if rval is None:
        mask = r_uint(1) << pos
        return r_uint(bool(val & mask))
    else:
        return r_uint(bool(rval.abs_rshift_and_mask(r_ulonglong(pos), 1)))

def bv_subrange(bv, n, m):
    size, val, rval = bv
    width = n - m + 1
    if rval is None:
        return small_bv(width, val >> m, True)
    else:
        if m == 0:
            return from_bigint(width, rval)
        if width < 64: # somewhat annoying that 64 doesn't work
            mask = (r_uint(1) << width) - 1
            res = rval.abs_rshift_and_mask(r_ulonglong(m), intmask(mask))
            return small_bv(width, r_uint(res))
        return big_bv(width, rval.rshift(m), True)

@always_inline
def bv_update_bit(bv, pos, bit):
    size, val, rval = bv
    assert pos < size
    if rval is None:
        mask = r_uint(1) << pos
        if bit:
            return small_bv(size, val | mask)
        else:
            return small_bv(size, val & ~mask, True)
    else:
        rval = _bv_update_bit_bigint(size, rval, pos, bit)
        return big_bv(size, rval)

@dont_inline
def _bv_update_bit_bigint(size, rval, pos, bit):
    mask = rbigint.fromint(1).lshift(pos)
    if bit:
        return rval.or_(mask)
    else:
        rval = rval.and_(mask.invert())
        return bigint_size_mask(size, rval)

def bv_update_subrange(bv, n, m, s):
    size, vala, rvala = bv
    width, valb, rvalb = s
    assert width == n - m + 1
    assert width <= size
    if rvala is None:
        assert rvalb is None
        if width == size:
            return s
        # width cannot be 64 in the next line because of the if above
        mask = ~(((r_uint(1) << width) - 1) << m)
        return small_bv(size, (vala & mask) | (valb << m), True)
    else:
        # XXX put slowpath into its own function
        mask = rbigint.fromint(1).lshift(width).int_sub(1).lshift(m).invert()
        return big_bv(rvala.and_(mask).or_(bv_tobigint(s).lshift(m)))

@always_inline
def bv_add_int(bv, i):
    size, val, rval = bv
    vali, rvali = i
    if rval is None and rvali is None and vali > 0:
        return small_bv(size, val + r_uint(vali), True)
    return from_bigint(size, _bv_add_int_slow(size, val, rval, vali, rvali))

@dont_inline
def _bv_add_int_slow(size, val, rval, vali, rvali):
    # XXX can be better
    rvali = int_tobigint_components(vali, rvali)
    rval = bv_tobigint((size, val, rval))
    return rval.add(rvali)


@always_inline
def bv_sub_int(bv, i):
    size, val, rval = bv
    vali, rvali = i
    if rval is None and rvali is None and vali > 0:
        return small_bv(size, val - r_uint(vali), True)
    return from_bigint(size, _bv_sub_int_slow(size, val, rval, vali, rvali))

@dont_inline
def _bv_sub_int_slow(size, val, rval, vali, rvali):
    # XXX can be better
    rvali = int_tobigint_components(vali, rvali)
    rval = bv_tobigint((size, val, rval))
    return rval.sub(rvali)

@always_inline
def bv_sign_extend(bv, i):
    size, val, rval = bv
    if i == size:
        return (size, val, rval)
    if rval is None and i <= 64:
        assert i > size
        highest_bit = (val >> (size - 1)) & 1
        if not highest_bit:
            return from_ruint(i, val)
        else:
            extra_bits = i - size
            bits = ((r_uint(1) << extra_bits) - 1) << size
            return from_ruint(i, bits | val)
    else:
        # either i > 64 or rval is not None
        rval = bv_tobigint(bv)
        assert i > size
        return from_bigint(i, _bv_sign_extend_slow(size, val, rval, i))

@dont_inline
def _bv_sign_extend_slow(size, val, rval, target_size):
    rval = bv_tobigint((size, val, rval))
    highest_bit = rval.rshift(size - 1).int_and_(1).toint()
    if not highest_bit:
        return rval
    else:
        extra_bits = target_size - size
        bits = rbigint.fromint(1).lshift(extra_bits).int_sub(1).lshift(size)
        return bits.or_(rval)


def append_64(self, ui):
    xxx
    return from_bigint(self.size() + 64, self.tobigint().lshift(64).or_(rbigint.fromrarith_int(ui)))



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
