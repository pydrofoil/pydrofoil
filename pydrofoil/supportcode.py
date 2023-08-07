from rpython.rlib import objectmodel, unroll
from rpython.rlib.rbigint import rbigint
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
from pydrofoil import bitvector
import pydrofoil.softfloat as softfloat

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

all_unwraps = {}

def unwrap(spec):
    argspecs = tuple(spec.split())
    it = unroll.unrolling_iterable(enumerate(argspecs))
    def wrap(func):
        def wrappedfunc(machine, *args):
            newargs = ()
            for i, spec in it:
                arg = args[i]
                if spec == "o":
                    newargs += (arg, )
                elif spec == "i":
                    newargs += (bitvector.int_toint(arg), )
                else:
                    assert 0, "unknown spec"
            return func(machine, *newargs)
        unwrapped_name = func.func_name + "_" + "_".join(argspecs)
        globals()[unwrapped_name] = func
        wrappedfunc.func_name += "_" + func.func_name
        all_unwraps[func.func_name] = (argspecs, unwrapped_name)
        return wrappedfunc
    return wrap

# unimplemented

make_dummy('eq_string')
make_dummy('plat_enable_dirty_update')
make_dummy('plat_enable_misaligned_access')
make_dummy('plat_enable_pmp')
make_dummy('platform_barrier')
make_dummy('print_mem_access')
make_dummy('print_platform')
make_dummy('print_reg')
make_dummy('print_string')
make_dummy('string_drop')
make_dummy('string_take')
make_dummy('string_startswith')
make_dummy('string_length')
make_dummy('sub_nat')
make_dummy('tmod_int')
make_dummy('zeros')

# generic helpers

def raise_type_error():
    raise TypeError


# bit vectors

@objectmodel.always_inline
def _mask(width, val):
    if width == 64:
        return val
    assert width < 64
    mask = (r_uint(1) << width) - 1
    return val & mask

def signed_bv(machine, op, n):
    if n == 64:
        return intmask(op)
    assert n > 0
    u1 = r_uint(1)
    m = u1 << (n - 1)
    op = op & ((u1 << n) - 1) # mask off higher bits to be sure
    return intmask((op ^ m) - m)

@objectmodel.always_inline
def unsigned_bv_wrapped_res(machine, op, n):
    return bitvector.int_fromruint(op)

@objectmodel.always_inline
def unsigned_bv(machine, op, n):
    if n == 64 and (op & (r_uint(1) << 63)):
        raise ValueError
    return intmask(op)

@objectmodel.always_inline
def add_bits_int(machine, a, b):
    return bitvector.bv_add_int(a, b)

@objectmodel.always_inline
def add_bits_int_bv_i(machine, a, width, b):
    if b >= 0:
        return _mask(width, a + r_uint(b))
    return _add_bits_int_bv_i_slow(a, width, b)

def _add_bits_int_bv_i_slow(a, width, b):
    return bitvector.from_ruint(width, a).add_int(bitvector.int_fromint(b))

@objectmodel.always_inline
def add_bits(machine, a, b):
    return bitvector.bv_add(a, b)

def add_bits_bv_bv(machine, a, b, width):
    return _mask(width, a + b)

def sub_bits_int(machine, a, b):
    return bitvector.bv_sub_int(a, b)

@objectmodel.always_inline
def sub_bits(machine, a, b):
    return bitvector.bv_sub(a, b)

def sub_bits_bv_bv(machine, a, b, width):
    return _mask(width, a - b)

def length(machine, gbv):
    return bitvector.bv_size_as_int(gbv)

@unwrap("o i")
@objectmodel.always_inline
def sign_extend(machine, gbv, size):
    return bitvector.bv_sign_extend(gbv, size)

@unwrap("o i")
@objectmodel.always_inline
def zero_extend(machine, gbv, size):
    return bitvector.bv_zero_extend(gbv, size)

@objectmodel.always_inline
def zero_extend_bv_i_i(machine, bv, width, targetwidth):
    return bv # XXX correct?

@objectmodel.always_inline
def eq_bits(machine, gvba, gvbb):
    return bitvector.bv_eq(gvba, gvbb)

def eq_bits_bv_bv(machine, bva, bvb):
    return bva == bvb

@objectmodel.always_inline
def neq_bits(machine, gvba, gvbb):
    return not bitvector.bv_eq(gvba, gvbb)

def neq_bits_bv_bv(machine, bva, bvb):
    return bva != bvb

@objectmodel.always_inline
def xor_bits(machine, gvba, gvbb):
    return bitvector.bv_xor(gvba, gvbb)

def xor_vec_bv_bv(machine, bva, bvb):
    return bva ^ bvb

@objectmodel.always_inline
def and_bits(machine, gvba, gvbb):
    return bitvector.bv_and(gvba, gvbb)

def and_vec_bv_bv(machine, bva, bvb):
    return bva & bvb

@objectmodel.always_inline
def or_bits(machine, gvba, gvbb):
    return bitvector.bv_or(gvba, gvbb)

def or_vec_bv_bv(machine, bva, bvb):
    return bva | bvb

@objectmodel.always_inline
def not_bits(machine, gvba):
    return bitvector.bv_invert(gvba)

def not_vec_bv(machine, bva, width):
    return _mask(width, ~bva)

def print_bits(machine, s, b):
    print s + bitvector.bv_string_of_bits(b)
    return ()

@unwrap("o i")
@objectmodel.always_inline
def shiftl(machine, gbv, i):
    return bitvector.bv_lshift(gbv, i)

def shiftl_bv_i(machine, a, width, i):
    return _mask(width, a << i)

@unwrap("o i")
@objectmodel.always_inline
def shiftr(machine, gbv, i):
    return bitvector.bv_rshift(gbv, i)

@objectmodel.always_inline
def shift_bits_left(machine, gbv, gbva):
    return bitvector.bv_lshift_bits(gbv, gbva)

@objectmodel.always_inline
def shift_bits_right(machine, gbv, gbva):
    return bitvector.bv_rshift_bits(gbv, gbva)

@objectmodel.always_inline
def sail_unsigned(machine, gbv):
    return bitvector.bv_unsigned(gbv)

@objectmodel.always_inline
def sail_signed(machine, gbv):
    return bitvector.bv_signed(gbv)

def append(machine, bv1, bv2):
    return bitvector.bv_append(bv1, bv2)

def bitvector_concat_bv_bv(machine, bv1, width, bv2):
    return (bv1 << width) | bv2


@objectmodel.always_inline
@unwrap("o i o")
def vector_update(machine, bv, index, element):
    return bitvector.bv_update_bit(bv, index, element)

@unwrap("o i")
@objectmodel.always_inline
def vector_access(machine, bv, index):
    return bitvector.bv_read_bit(bv, index)

def vector_access_bv_i(machine, bv, index):
    if index == 0:
        return bv & r_uint(1)
    return r_uint(1) & safe_rshift(None, bv, r_uint(index))

def update_fbits(machine, fb, index, element):
    assert 0 <= index < 64
    if element:
        return fb | (r_uint(1) << index)
    else:
        return fb & ~(r_uint(1) << index)

@unwrap("o i i o")
@objectmodel.always_inline
def vector_update_subrange(machine, bv, n, m, s):
    return bitvector.bv_update_subrange(bv, n, m, s)

@unwrap("o i i")
@objectmodel.always_inline
def vector_subrange(machine, bv, n, m):
    return bitvector.bv_subrange(bv, n, m)

@objectmodel.always_inline
def slice_fixed_bv_i_i(machine, v, n, m):
    res = safe_rshift(None, v, m)
    width = n - m + 1
    return _mask(width, res)

def string_of_bits(machine, gbv):
    return bitvector.bv_string_of_bits(gbv)

def decimal_string_of_bits(machine, sbits):
    return str(sbits)


# integers

@objectmodel.always_inline
def eq_int(machine, ia, ib):
    return bitvector.int_eq(ia, ib)

def eq_int_i_i(machine, a, b):
    return a == b

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

def add_i_i_wrapped_res(machine, a, b):
    return bitvector.int_add_i_i(a, b)

@objectmodel.always_inline
def sub_int(machine, ia, ib):
    return bitvector.int_sub(ia, ib)

def sub_i_i_wrapped_res(machine, a, b):
    return bitvector.int_sub_i_i(a, b)

@objectmodel.always_inline
def mult_int(machine, ia, ib):
    return bitvector.int_mul(ia, ib)

def tdiv_int(machine, ia, ib):
    return bitvector.int_tdiv(ia, ib)

@objectmodel.always_inline
def tmod_int(machine, ia, ib):
    return bitvector.int_tmod(ia, ib)

@unwrap("i i")
@objectmodel.always_inline
def emod_int(machine, a, b):
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

@unwrap("i o i")
@objectmodel.always_inline
def get_slice_int(machine, len, n, start):
    return bitvector.int_slice(n, len, start)

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

@objectmodel.specialize.arg_or_var(1)
@objectmodel.always_inline
def int_to_int64(machine, r):
    if objectmodel.is_annotation_constant(r):
        return _int_to_int64_memo(r)
    return bitvector.int_toint(r)

@objectmodel.specialize.memo()
def _int_to_int64_memo(r):
    return bitvector.int_toint(r)

def int64_to_int(machine, i):
    return bitvector.int_fromint(i)

def string_to_int(machine, s):
    return bitvector.int_fromstr(s)

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
    
# softfloat

def softfloat_f16sqrt(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f16sqrt(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32sqrt(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f32sqrt(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64sqrt(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f64sqrt(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16tof32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f16tof32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16tof64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f16tof64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16toi32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f16toi32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16toi64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f16toi64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16toui32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f16toui32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16toui64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f16toui64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32tof16(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f32tof16(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32tof64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f32tof64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32toi32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f32toi32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32toi64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f32toi64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32toui32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f32toui32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32toui64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f32toui64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64tof16(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f64tof16(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64tof32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f64tof32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64toui64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f64toui64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64toi32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f64toi32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64toi64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f64toi64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64toui32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.f64toui32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_i32tof16(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.i32tof16(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_i32tof32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.i32tof32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_i32tof64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.i32tof64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_i64tof16(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.i64tof16(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_i64tof32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.i64tof32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_i64tof64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.i64tof64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_ui32tof16(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.ui32tof16(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_ui32tof32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.ui32tof32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_ui32tof64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.ui32tof64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_ui64tof16(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.ui64tof16(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_ui64tof32(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.ui64tof32(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_ui64tof64(machine, rm, v1):
    machine._reg_zfloat_result = softfloat.ui64tof64(rm, v1)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16add(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f16add(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16sub(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f16sub(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16mul(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f16mul(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16div(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f16div(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32add(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f32add(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32sub(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f32sub(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32mul(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f32mul(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32div(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f32div(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64add(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f64add(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64sub(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f64sub(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64mul(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f64mul(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64div(machine, rm, v1, v2):
    machine._reg_zfloat_result = softfloat.f64div(rm, v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16eq(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f16eq(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16le(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f16le(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16lt(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f16lt(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32eq(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f32eq(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32le(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f32le(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32lt(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f32lt(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64eq(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f64eq(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64le(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f64le(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64lt(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f64lt(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16muladd(machine, rm, v1, v2, v3):
    machine._reg_zfloat_result = softfloat.f16muladd(rm, v1, v2, v3)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32muladd(machine, rm, v1, v2, v3):
    machine._reg_zfloat_result = softfloat.f32muladd(rm, v1, v2, v3)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64muladd(machine, rm, v1, v2, v3):
    machine._reg_zfloat_result = softfloat.f64muladd(rm, v1, v2, v3)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

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
    _immutable_fields_ = []

    have_exception = False
    throw_location = None
    current_exception = None

    def __init__(self):
        pass

class ObjectBase(object):
    _attrs_ = []

class LetsBase(object):
    _attrs_ = []
