from rpython.rlib import rarithmetic
from rpython.rlib.rbigint import rbigint
from pydrofoil import bitvector


# unimplemented

def and_bits(*args): import pdb;pdb.set_trace(); return 123
def cancel_reservation(*args): import pdb;pdb.set_trace(); return 123
def concat_str(*args): import pdb;pdb.set_trace(); return 123
def decimal_string_of_bits(*args): import pdb;pdb.set_trace(); return 123
def emod_int(*args): import pdb;pdb.set_trace(); return 123
def eq_bits(*args): import pdb;pdb.set_trace(); return 123
def eq_string(*args): import pdb;pdb.set_trace(); return 123
def length(*args): import pdb;pdb.set_trace(); return 123
def load_reservation(*args): import pdb;pdb.set_trace(); return 123
def match_reservation(*args): import pdb;pdb.set_trace(); return 123
def max_int(*args): import pdb;pdb.set_trace(); return 123
def min_int(*args): import pdb;pdb.set_trace(); return 123
def not_bits(*args): import pdb;pdb.set_trace(); return 123
def or_bits(*args): import pdb;pdb.set_trace(); return 123
def plat_enable_dirty_update(*args): import pdb;pdb.set_trace(); return 123
def plat_enable_misaligned_access(*args): import pdb;pdb.set_trace(); return 123
def plat_enable_pmp(*args): import pdb;pdb.set_trace(); return 123
def platform_barrier(*args): import pdb;pdb.set_trace(); return 123
def platform_write_mem_ea(*args): import pdb;pdb.set_trace(); return 123
def plat_mtval_has_illegal_inst_bits(*args): import pdb;pdb.set_trace(); return 123
def print_endline(*args): import pdb;pdb.set_trace(); return 123
def print_instr(*args): import pdb;pdb.set_trace(); return 123
def print_int(*args): import pdb;pdb.set_trace(); return 123
def print_mem_access(*args): import pdb;pdb.set_trace(); return 123
def print_platform(*args): import pdb;pdb.set_trace(); return 123
def print_reg(*args): import pdb;pdb.set_trace(); return 123
def print_string(*args): import pdb;pdb.set_trace(); return 123
def shift_bits_left(*args): import pdb;pdb.set_trace(); return 123
def shift_bits_right(*args): import pdb;pdb.set_trace(); return 123
def shiftr(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16add(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16div(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16eq(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16le(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16lt(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16mul(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16muladd(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16sqrt(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16sub(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16tof32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16tof64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16toi32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16toi64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16toui32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f16toui64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32add(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32div(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32eq(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32le(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32lt(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32mul(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32muladd(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32sqrt(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32sub(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32tof16(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32tof64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32toi32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32toi64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32toui32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f32toui64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64add(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64div(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64eq(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64le(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64lt(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64mul(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64muladd(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64sqrt(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64sub(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64tof16(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64tof32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64toi32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64toi64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64toui32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_f64toui64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_i32tof16(*args): import pdb;pdb.set_trace(); return 123
def softfloat_i32tof32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_i32tof64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_i64tof16(*args): import pdb;pdb.set_trace(); return 123
def softfloat_i64tof32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_i64tof64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_ui32tof16(*args): import pdb;pdb.set_trace(); return 123
def softfloat_ui32tof32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_ui32tof64(*args): import pdb;pdb.set_trace(); return 123
def softfloat_ui64tof16(*args): import pdb;pdb.set_trace(); return 123
def softfloat_ui64tof32(*args): import pdb;pdb.set_trace(); return 123
def softfloat_ui64tof64(*args): import pdb;pdb.set_trace(); return 123
def string_drop(*args): import pdb;pdb.set_trace(); return 123
def string_length(*args): import pdb;pdb.set_trace(); return 123
def string_of_bits(*args): import pdb;pdb.set_trace(); return 123
def string_of_int(*args): import pdb;pdb.set_trace(); return 123
def string_startswith(*args): import pdb;pdb.set_trace(); return 123
def string_take(*args): import pdb;pdb.set_trace(); return 123
def sub_bits(*args): import pdb;pdb.set_trace(); return 123
def sub_bits_int(*args): import pdb;pdb.set_trace(); return 123
def sub_int(*args): import pdb;pdb.set_trace(); return 123
def sub_nat(*args): import pdb;pdb.set_trace(); return 123
def tdiv_int(*args): import pdb;pdb.set_trace(); return 123
def tmod_int(*args): import pdb;pdb.set_trace(); return 123
def update_fbits(*args): import pdb;pdb.set_trace(); return 123
def vector_access(*args): import pdb;pdb.set_trace(); return 123
def vector_subrange(*args): import pdb;pdb.set_trace(); return 123
def xor_bits(*args): import pdb;pdb.set_trace(); return 123
def zeros(*args): import pdb;pdb.set_trace(); return 123

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

def sign_extend(gbv, lint):
    size = lint.toint()
    return gbv.sign_extend(size)

def raise_type_error():
    raise TypeError

def eq_int(a, b):
    assert isinstance(a, rbigint)
    return a.eq(b)

def eq_bit(a, b):
    return a == b

def safe_rshift(n, shift):
    if shift >= 64:
        return rarithmetic.r_uint(0)
    return n >> shift

def lteq(ia, ib):
    return ia.le(ib)

def lt(ia, ib):
    return ia.lt(ib)

def gt(ia, ib):
    return ia.gt(ib)

def gteq(ia, ib):
    return ia.ge(ib)

def add_int(ia, ib):
    return ia.add(ib)

def sub_int(ia, ib):
    return ia.sub(ib)

def mult_int(ia, ib):
    return ia.mul(ib)

def print_bits(s, b):
    print s,
    b.print_bits()

def reg_deref(s):
    return s

def not_(b):
    return not b

def sail_assert(*args):
    pass

def eq_anything(a, b):
    return a == b

def eq_bool(a, b):
    return a == b

def shiftl(gbv, i):
    return gbv.shiftl(i.toint())

def shift_bits_left(gbv, gbva):
    return gbv.shiftl(gbva.rval.toint())

def sail_unsigned(gbv):
    return gbv.rval

def sail_signed(gbv):
    return gbv.signed()

# vector stuff

def vector_update_inplace(res, l, index, element):
    # super weird, the C backend does the same
    if res is not l:
        l = l[:]
    l[index] = element
    return l

def vector_update(l, index, element):
    # bitvector
    return l.update_bit(index.toint(), element)

def vector_update_subrange(l, n, m, s):
    width = s.size
    assert width == n.toint() - m.toint() + 1
    mask = rbigint.fromint(1).lshift(width).int_sub(1).lshift(m.toint()).invert()
    return bitvector.GenericBitVector(l.size, l.rval.and_(mask).or_(s.rval.lshift(m.toint())))


def elf_tohost(_):
    return rbigint.fromint(0)

def get_slice_int(len, n, start):
    n = n.rshift(start.toint())
    return bitvector.GenericBitVector(len.toint(), n.and_(rbigint.fromint(1).lshift(len.toint()).int_sub(1)))

def platform_barrier(_):
    return ()

def platform_write_mem_ea(write_kind, addr_size, addr, n):
    return ()
