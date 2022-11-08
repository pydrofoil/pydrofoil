from rpython.rlib import objectmodel
from rpython.rlib.rbigint import rbigint
from rpython.rlib.rarithmetic import r_uint, intmask
from pydrofoil import bitvector

@objectmodel.specialize.call_location()
def make_dummy(name):
    def dummy(machine, *args):
        if objectmodel.we_are_translated():
            print "not implemented!", name
            raise ValueError
        import pdb; pdb.set_trace()
        return 123
    dummy.func_name += name
    globals()[name] = dummy

# unimplemented

make_dummy('eq_string')
make_dummy('plat_enable_dirty_update')
make_dummy('plat_enable_misaligned_access')
make_dummy('plat_enable_pmp')
make_dummy('platform_barrier')
make_dummy('print_int')
make_dummy('print_mem_access')
make_dummy('print_platform')
make_dummy('print_reg')
make_dummy('print_string')
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
make_dummy('string_length')
make_dummy('sub_bits')
make_dummy('sub_nat')
make_dummy('tmod_int')
make_dummy('vector_access')
make_dummy('zeros')

# generic helpers

def raise_type_error():
    raise TypeError


# bit vectors

def zero_extend(machine, a, b):
    return a

def fast_signed(machine, op, n):
    if n == 64:
        return intmask(op)
    assert n > 0
    u1 = r_uint(1)
    m = u1 << (n - 1)
    op = op & ((u1 << n) - 1) # mask off higher bits to be sure
    return intmask((op ^ m) - m)

@objectmodel.always_inline
def add_bits_int(machine, a, b):
    return a.add_int(b)

def sub_bits_int(machine, a, b):
    return a.sub_int(b)

def length(machine, gbv):
    return gbv.size_as_int()

def sign_extend(machine, gbv, lint):
    size = bitvector.int_toint(lint)
    return gbv.sign_extend(size)

def eq_bits(machine, gvba, gvbb):
    return gvba.eq(gvbb)

def xor_bits(machine, gvba, gvbb):
    return gvba.xor(gvbb)

def and_bits(machine, gvba, gvbb):
    return gvba.and_(gvbb)

def or_bits(machine, gvba, gvbb):
    return gvba.or_(gvbb)

def not_bits(machine, gvba):
    return gvba.invert()

def print_bits(machine, s, b):
    print s + b.string_of_bits()
    return ()

@objectmodel.always_inline
def shiftl(machine, gbv, i):
    return gbv.lshift(bitvector.int_toint(i))

@objectmodel.always_inline
def shiftr(machine, gbv, i):
    return gbv.rshift(bitvector.int_toint(i))

def shift_bits_left(machine, gbv, gbva):
    return gbv.lshift_bits(gbva)

def shift_bits_right(machine, gbv, gbva):
    return gbv.rshift_bits(gbva)

@objectmodel.always_inline
def sail_unsigned(machine, gbv):
    return gbv.unsigned()

@objectmodel.always_inline
def sail_signed(machine, gbv):
    return gbv.signed()

def append_64(machine, bv, v):
    return bv.append_64(v)

@objectmodel.always_inline
def vector_update(machine, bv, index, element):
    return bv.update_bit(bitvector.int_toint(index), element)

@objectmodel.always_inline
def vector_access(machine, bv, index):
    return bv.read_bit(bitvector.int_toint(index))

def update_fbits(fb, index, element):
    assert 0 <= index < 64
    if element:
        return fb | (r_uint(1) << index)
    else:
        return fb & ~(r_uint(1) << index)

def vector_update_subrange(machine, bv, n, m, s):
    return bv.update_subrange(bitvector.int_toint(n), bitvector.int_toint(m), s)

def vector_subrange(machine, bv, n, m):
    return bv.subrange(bitvector.int_toint(n), bitvector.int_toint(m))

def string_of_bits(machine, gbv):
    return gbv.string_of_bits()

def decimal_string_of_bits(machine, sbits):
    return str(sbits)


# integers

@objectmodel.always_inline
def eq_int(machine, ia, ib):
    return bitvector.int_eq(ia, ib)

def eq_bit(machine, a, b):
    return a == b

@objectmodel.always_inline
def lteq(machine, ia, ib):
    return bitvector.int_le(ia, ib)

@objectmodel.always_inline
def lt(machine, ia, ib):
    return bitvector.int_lt(ia, ib)

@objectmodel.always_inline
def gt(machine, ia, ib):
    return bitvector.int_gt(ia, ib)

@objectmodel.always_inline
def gteq(machine, ia, ib):
    return bitvector.int_ge(ia, ib)

@objectmodel.always_inline
def add_int(machine, ia, ib):
    return bitvector.int_add(ia, ib)

@objectmodel.always_inline
def sub_int(machine, ia, ib):
    return bitvector.int_sub(ia, ib)

@objectmodel.always_inline
def mult_int(machine, ia, ib):
    return bitvector.int_mul(ia, ib)

def tdiv_int(machine, ia, ib):
    return bitvector.int_tdiv(ia, ib)

@objectmodel.always_inline
def tmod_int(machine, ia, ib):
    return bitvector.int_tmod(ia, ib)

@objectmodel.always_inline
def emod_int(machine, ia, ib):
    a = bitvector.int_toint(ia)
    b = bitvector.int_toint(ib)
    if a < 0 or b < 0:
        print "emod_int with negative args not implemented yet", a, b
        raise ValueError # risc-v only needs the positive small case
    return bitvector.int_fromint(a % b)

@objectmodel.always_inline
def max_int(machine, ia, ib):
    if bitvector.int_gt(ia, ib):
        return ia
    return ib

@objectmodel.always_inline
def min_int(machine, ia, ib):
    if bitvector.int_lt(ia, ib):
        return ia
    return ib

@objectmodel.always_inline
def get_slice_int(machine, len, n, start):
    return bitvector.int_slice(n, bitvector.int_toint(len), bitvector.int_toint(start))

def safe_rshift(machine, n, shift):
    assert shift >= 0
    if shift >= 64:
        return r_uint(0)
    return n >> shift

@objectmodel.always_inline
def print_int(machine, s, i):
    print s + bitvector.int_tostr(i)
    return ()

def not_(machine, b):
    return not b

def eq_bool(machine, a, b):
    return a == b

def string_of_int(machine, ia):
    return bitvector.int_tostr(ia)


# various

@objectmodel.specialize.argtype(1)
def reg_deref(machine, s):
    return s

def sail_assert(cond, st):
    if not objectmodel.we_are_translated() and not cond:
        import pdb; pdb.set_trace()
    assert cond, st

def print_endline(machine, s):
    print s
    return ()

# vector stuff

@objectmodel.specialize.argtype(1, 2, 4)
def vector_update_inplace(machine, res, l, index, element):
    # super weird, the C backend does the same
    if res is not l:
        l = l[:]
    l[index] = element
    return l

def elf_tohost(machine, _):
    return bitvector.int_fromint(0)

def platform_barrier(machine, _):
    return ()

def platform_write_mem_ea(machine, write_kind, addr_size, addr, n):
    return ()


# strings

def concat_str(machine, a, b):
    return a + b


# argument handling

def parse_args(argv, shortname, longname="", want_arg=True):
    # crappy argument handling
    for i in range(len(argv)):
        if argv[i] == shortname or argv[i] == longname:
            if not want_arg:
                res = argv[i]
                del argv[i]
                return res
            if len(argv) == i + 1:
                print "missing argument after " + argv[i]
                raise ValueError
            jitarg = argv[i + 1]
            del argv[i:i+2]
            return jitarg



class RegistersBase(object):
    have_exception = False
    throw_location = None
    current_exception = None
