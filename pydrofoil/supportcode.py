from rpython.rlib import rarithmetic
from rpython.rlib.rbigint import rbigint
from pydrofoil import bitvector


# generic helpers

def zero_extend(a, b):
    return a

def add_bits_int(a, b):
    return a.add_int(b)

def fast_signed(op, n):
    if n == 64:
        return rarithmetic.intmask(op)
    assert n > 0
    u1 = rarithmetic.r_uint(1)
    m = u1 << (n - 1)
    op = op & ((u1 << n) - 1) # mask off higher bits to be sure
    return rarithmetic.intmask((op ^ m) - m)

def raise_type_error():
    raise TypeError

def eq_int(a, b):
    assert isinstance(a, rbigint)
    return a.eq(b)

def safe_rshift(n, shift):
    if shift >= 64:
        return rarithmetic.r_uint(0)
    return n >> shift

def print_bits(s, b):
    print s,
    b.print_bits()

def reg_deref(s):
    return s

# vector stuff

def vector_update(res, l, index, element):
    # super weird, the C backend does the same
    if res is not l:
        l = l[:]
    l[index] = element
    return l

def vector_update_subrange(l, n, m, s):
    width = s.size
    assert width == n.toint() - m.toint() + 1
    mask = rbigint.fromint(1).lshift(width).int_sub(1).lshift(m.toint()).invert()
    return bitvector.GenericBitVector(l.size, l.rval.and_(mask).or_(s.rval.lshift(m.toint())))
