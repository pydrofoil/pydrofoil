from rpython.rlib import rarithmetic, objectmodel
from rpython.rlib.rbigint import rbigint
from pydrofoil import bitvector

@objectmodel.specialize.call_location()
def dummy(*args):
    if objectmodel.we_are_translated():
        raise ValueError
    import pdb; pdb.set_trace()
    return 123

# unimplemented

def and_bits(*args): return dummy(*args)
def cancel_reservation(*args): return dummy(*args)
def emod_int(*args): return dummy(*args)
def eq_string(*args): return dummy(*args)
def length(*args): return dummy(*args)
def load_reservation(*args): return dummy(*args)
def match_reservation(*args): return dummy(*args)
def max_int(*args): return dummy(*args)
def min_int(*args): return dummy(*args)
def not_bits(*args): return dummy(*args)
def or_bits(*args): return dummy(*args)
def plat_enable_dirty_update(*args): return dummy(*args)
def plat_enable_misaligned_access(*args): return dummy(*args)
def plat_enable_pmp(*args): return dummy(*args)
def platform_barrier(*args): return dummy(*args)
def platform_write_mem_ea(*args): return dummy(*args)
def plat_mtval_has_illegal_inst_bits(*args): return dummy(*args)
def print_endline(*args): return dummy(*args)
def print_instr(*args): return dummy(*args)
def print_int(*args): return dummy(*args)
def print_mem_access(*args): return dummy(*args)
def print_platform(*args): return dummy(*args)
def print_reg(*args): return dummy(*args)
def print_string(*args): return dummy(*args)
def shift_bits_left(*args): return dummy(*args)
def shift_bits_right(*args): return dummy(*args)
def shiftr(*args): return dummy(*args)
def softfloat_f16add(*args): return dummy(*args)
def softfloat_f16div(*args): return dummy(*args)
def softfloat_f16eq(*args): return dummy(*args)
def softfloat_f16le(*args): return dummy(*args)
def softfloat_f16lt(*args): return dummy(*args)
def softfloat_f16mul(*args): return dummy(*args)
def softfloat_f16muladd(*args): return dummy(*args)
def softfloat_f16sqrt(*args): return dummy(*args)
def softfloat_f16sub(*args): return dummy(*args)
def softfloat_f16tof32(*args): return dummy(*args)
def softfloat_f16tof64(*args): return dummy(*args)
def softfloat_f16toi32(*args): return dummy(*args)
def softfloat_f16toi64(*args): return dummy(*args)
def softfloat_f16toui32(*args): return dummy(*args)
def softfloat_f16toui64(*args): return dummy(*args)
def softfloat_f32add(*args): return dummy(*args)
def softfloat_f32div(*args): return dummy(*args)
def softfloat_f32eq(*args): return dummy(*args)
def softfloat_f32le(*args): return dummy(*args)
def softfloat_f32lt(*args): return dummy(*args)
def softfloat_f32mul(*args): return dummy(*args)
def softfloat_f32muladd(*args): return dummy(*args)
def softfloat_f32sqrt(*args): return dummy(*args)
def softfloat_f32sub(*args): return dummy(*args)
def softfloat_f32tof16(*args): return dummy(*args)
def softfloat_f32tof64(*args): return dummy(*args)
def softfloat_f32toi32(*args): return dummy(*args)
def softfloat_f32toi64(*args): return dummy(*args)
def softfloat_f32toui32(*args): return dummy(*args)
def softfloat_f32toui64(*args): return dummy(*args)
def softfloat_f64add(*args): return dummy(*args)
def softfloat_f64div(*args): return dummy(*args)
def softfloat_f64eq(*args): return dummy(*args)
def softfloat_f64le(*args): return dummy(*args)
def softfloat_f64lt(*args): return dummy(*args)
def softfloat_f64mul(*args): return dummy(*args)
def softfloat_f64muladd(*args): return dummy(*args)
def softfloat_f64sqrt(*args): return dummy(*args)
def softfloat_f64sub(*args): return dummy(*args)
def softfloat_f64tof16(*args): return dummy(*args)
def softfloat_f64tof32(*args): return dummy(*args)
def softfloat_f64toi32(*args): return dummy(*args)
def softfloat_f64toi64(*args): return dummy(*args)
def softfloat_f64toui32(*args): return dummy(*args)
def softfloat_f64toui64(*args): return dummy(*args)
def softfloat_i32tof16(*args): return dummy(*args)
def softfloat_i32tof32(*args): return dummy(*args)
def softfloat_i32tof64(*args): return dummy(*args)
def softfloat_i64tof16(*args): return dummy(*args)
def softfloat_i64tof32(*args): return dummy(*args)
def softfloat_i64tof64(*args): return dummy(*args)
def softfloat_ui32tof16(*args): return dummy(*args)
def softfloat_ui32tof32(*args): return dummy(*args)
def softfloat_ui32tof64(*args): return dummy(*args)
def softfloat_ui64tof16(*args): return dummy(*args)
def softfloat_ui64tof32(*args): return dummy(*args)
def softfloat_ui64tof64(*args): return dummy(*args)
def string_drop(*args): return dummy(*args)
def string_take(*args): return dummy(*args)
def sub_bits(*args): return dummy(*args)
def sub_bits_int(*args): return dummy(*args)
def sub_int(*args): return dummy(*args)
def sub_nat(*args): return dummy(*args)
def tdiv_int(*args): return dummy(*args)
def tmod_int(*args): return dummy(*args)
def update_fbits(*args): return dummy(*args)
def vector_access(*args): return dummy(*args)
def vector_subrange(*args): return dummy(*args)
def xor_bits(*args): return dummy(*args)
def zeros(*args): return dummy(*args)

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

def eq_bits(gvba, gvbb):
    return gvba.rval.eq(gvbb.rval)

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

@objectmodel.specialize.argtype(0)
def reg_deref(s):
    return s

def not_(b):
    return not b

def sail_assert(*args):
    pass

@objectmodel.specialize.argtype(0, 1)
def eq_anything(a, b):
    return a == b

def eq_bool(a, b):
    return a == b

def shiftl(gbv, i):
    return gbv.shiftl(i.toint())

def shiftr(gbv, i):
    return gbv.shiftr(i.toint())

def shift_bits_left(gbv, gbva):
    return gbv.shiftl(gbva.rval.toint())

def sail_unsigned(gbv):
    return gbv.rval

def sail_signed(gbv):
    return gbv.signed()

# vector stuff

@objectmodel.specialize.argtype(0, 1, 3)
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


# strings

def concat_str(a, b):
    return a + b

def string_length(s): return dummy(*args)
def string_of_bits(gbv):
    res = gbv.rval.format("0123456789ABCDEF")
    return "0x%s%s" % ("0" * max(0, 8 - len(res)), res)

def decimal_string_of_bits(sbits):
    return str(sbits)
    
def string_of_int(r):
    return r.str()
def string_startswith(*args): return dummy(*args)
