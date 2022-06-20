from rpython.rlib import rarithmetic, objectmodel
from rpython.rlib.rbigint import rbigint
from pydrofoil import bitvector

@objectmodel.specialize.call_location()
def make_dummy(name):
    def dummy(*args):
        if objectmodel.we_are_translated():
            print "not implemented!", name
            raise ValueError
        import pdb; pdb.set_trace()
        return 123
    dummy.func_name += name
    globals()[name] = dummy

# unimplemented

make_dummy('and_bits')
make_dummy('emod_int')
make_dummy('eq_string')
make_dummy('max_int')
make_dummy('min_int')
make_dummy('not_bits')
make_dummy('or_bits')
make_dummy('plat_enable_dirty_update')
make_dummy('plat_enable_misaligned_access')
make_dummy('plat_enable_pmp')
make_dummy('platform_barrier')
make_dummy('platform_write_mem_ea')
make_dummy('plat_mtval_has_illegal_inst_bits')
make_dummy('print_endline')
make_dummy('print_int')
make_dummy('print_mem_access')
make_dummy('print_platform')
make_dummy('print_reg')
make_dummy('print_string')
make_dummy('shift_bits_right')
make_dummy('shiftr')
make_dummy('softfloat_f16add')
make_dummy('softfloat_f16div')
make_dummy('softfloat_f16eq')
make_dummy('softfloat_f16le')
make_dummy('softfloat_f16lt')
make_dummy('softfloat_f16mul')
make_dummy('softfloat_f16muladd')
make_dummy('softfloat_f16sqrt')
make_dummy('softfloat_f16sub')
make_dummy('softfloat_f16tof32')
make_dummy('softfloat_f16tof64')
make_dummy('softfloat_f16toi32')
make_dummy('softfloat_f16toi64')
make_dummy('softfloat_f16toui32')
make_dummy('softfloat_f16toui64')
make_dummy('softfloat_f32add')
make_dummy('softfloat_f32div')
make_dummy('softfloat_f32eq')
make_dummy('softfloat_f32le')
make_dummy('softfloat_f32lt')
make_dummy('softfloat_f32mul')
make_dummy('softfloat_f32muladd')
make_dummy('softfloat_f32sqrt')
make_dummy('softfloat_f32sub')
make_dummy('softfloat_f32tof16')
make_dummy('softfloat_f32tof64')
make_dummy('softfloat_f32toi32')
make_dummy('softfloat_f32toi64')
make_dummy('softfloat_f32toui32')
make_dummy('softfloat_f32toui64')
make_dummy('softfloat_f64add')
make_dummy('softfloat_f64div')
make_dummy('softfloat_f64eq')
make_dummy('softfloat_f64le')
make_dummy('softfloat_f64lt')
make_dummy('softfloat_f64mul')
make_dummy('softfloat_f64muladd')
make_dummy('softfloat_f64sqrt')
make_dummy('softfloat_f64sub')
make_dummy('softfloat_f64tof16')
make_dummy('softfloat_f64tof32')
make_dummy('softfloat_f64toi32')
make_dummy('softfloat_f64toi64')
make_dummy('softfloat_f64toui32')
make_dummy('softfloat_f64toui64')
make_dummy('softfloat_i32tof16')
make_dummy('softfloat_i32tof32')
make_dummy('softfloat_i32tof64')
make_dummy('softfloat_i64tof16')
make_dummy('softfloat_i64tof32')
make_dummy('softfloat_i64tof64')
make_dummy('softfloat_ui32tof16')
make_dummy('softfloat_ui32tof32')
make_dummy('softfloat_ui32tof64')
make_dummy('softfloat_ui64tof16')
make_dummy('softfloat_ui64tof32')
make_dummy('softfloat_ui64tof64')
make_dummy('string_drop')
make_dummy('string_take')
make_dummy('string_startswith')
make_dummy('string_length(s)')
make_dummy('sub_bits')
make_dummy('sub_bits_int')
make_dummy('sub_int')
make_dummy('sub_nat')
make_dummy('tdiv_int')
make_dummy('tmod_int')
make_dummy('update_fbits')
make_dummy('vector_access')
make_dummy('vector_subrange')
make_dummy('xor_bits')
make_dummy('zeros')

# generic helpers

def zero_extend(a, b):
    return a

def add_bits_int(a, b):
    return a.add_int(b)

def sub_bits_int(a, b):
    return a.sub_int(b)

def length(gbv):
    return rbigint.fromint(gbv.size)

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

def xor_bits(gvba, gvbb):
    return gvba.xor(gvbb)

def and_bits(gvba, gvbb):
    return gvba.and_(gvbb)

def or_bits(gvba, gvbb):
    return gvba.or_(gvbb)

def not_bits(gvba):
    return gvba.invert()

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
    return ()

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

def shift_bits_right(gbv, gbva):
    return gbv.shiftr(gbva.rval.toint())

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

def vector_subrange(l, n, m):
    return l.subrange(n.toint(), m.toint())


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


def string_of_bits(gbv):
    res = gbv.rval.format("0123456789ABCDEF")
    return "0x%s%s" % ("0" * max(0, 8 - len(res)), res)

def decimal_string_of_bits(sbits):
    return str(sbits)
    
def string_of_int(r):
    return r.str()

