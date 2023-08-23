import os

from rpython.rlib import objectmodel, unroll, jit
from rpython.rlib.rbigint import rbigint
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
from pydrofoil import bitvector
from pydrofoil.bitvector import Integer
import pydrofoil.softfloat as softfloat
from pydrofoil.real import Real

STDERR = 2

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
                    newargs += (arg.toint(), )
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
make_dummy('sub_nat')
make_dummy('undefined_int')
make_dummy("prerr_int")
make_dummy("sail_putchar")
make_dummy("wakeup_request")
make_dummy("set_slice_int")
make_dummy("undefined_range")
make_dummy("arith_shiftr")

make_dummy("softfloat_f16lt_quiet")
make_dummy("softfloat_f32lt_quiet")
make_dummy("softfloat_f64lt_quiet")
make_dummy("softfloat_f16le_quiet")
make_dummy("softfloat_f32le_quiet")
make_dummy("softfloat_f64le_quiet")
make_dummy("softfloat_f16roundToInt")
make_dummy("softfloat_f32roundToInt")
make_dummy("softfloat_f64roundToInt")


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
    return bitvector.Integer.from_ruint(op)

@objectmodel.always_inline
def unsigned_bv(machine, op, n):
    if n == 64 and (op & (r_uint(1) << 63)):
        raise ValueError
    return intmask(op)

@objectmodel.always_inline
def add_bits_int(machine, a, b):
    return a.add_int(b)

@objectmodel.always_inline
def add_bits_int_bv_i(machine, a, width, b):
    if b >= 0:
        return _mask(width, a + r_uint(b))
    return _add_bits_int_bv_i_slow(a, width, b)

def _add_bits_int_bv_i_slow(a, width, b):
    return bitvector.from_ruint(width, a).add_int(bitvector.SmallInteger.fromint(b))

@objectmodel.always_inline
def add_bits(machine, a, b):
    return a.add_bits(b)

def add_bits_bv_bv(machine, a, b, width):
    return _mask(width, a + b)

def sub_bits_int(machine, a, b):
    return a.sub_int(b)

@objectmodel.always_inline
def sub_bits(machine, a, b):
    return a.sub_bits(b)

def sub_bits_bv_bv(machine, a, b, width):
    return _mask(width, a - b)

def length(machine, gbv):
    return gbv.size_as_int()

@unwrap("o i")
@objectmodel.always_inline
def sign_extend(machine, gbv, size):
    return gbv.sign_extend(size)

@unwrap("o i")
@objectmodel.always_inline
def zero_extend(machine, gbv, size):
    return gbv.zero_extend(size)

@objectmodel.always_inline
def zero_extend_bv_i_i(machine, bv, width, targetwidth):
    return bv # XXX correct?

def eq_bits(machine, gvba, gvbb):
    return gvba.eq(gvbb)

def eq_bits_bv_bv(machine, bva, bvb):
    return bva == bvb

def neq_bits(machine, gvba, gvbb):
    return not gvba.eq(gvbb)

def neq_bits_bv_bv(machine, bva, bvb):
    return bva != bvb

def xor_bits(machine, gvba, gvbb):
    return gvba.xor(gvbb)

def xor_vec_bv_bv(machine, bva, bvb):
    return bva ^ bvb

def and_bits(machine, gvba, gvbb):
    return gvba.and_(gvbb)

def and_vec_bv_bv(machine, bva, bvb):
    return bva & bvb

def or_bits(machine, gvba, gvbb):
    return gvba.or_(gvbb)

def or_vec_bv_bv(machine, bva, bvb):
    return bva | bvb

def not_bits(machine, gvba):
    return gvba.invert()

def not_vec_bv(machine, bva, width):
    return _mask(width, ~bva)

def print_bits(machine, s, b):
    print s + b.string_of_bits()
    return ()

def prerr_bits(machine, s, b):
    os.write(STDERR, "%s%s\n" % (s, b.string_of_bits()))
    return ()


@unwrap("o i")
def shiftl(machine, gbv, i):
    return gbv.lshift(i)

def shiftl_bv_i(machine, a, width, i):
    return _mask(width, a << i)

@unwrap("o i")
def shiftr(machine, gbv, i):
    return gbv.rshift(i)

def shift_bits_left(machine, gbv, gbva):
    return gbv.lshift_bits(gbva)

def shift_bits_right(machine, gbv, gbva):
    return gbv.rshift_bits(gbva)

@unwrap("o i")
def replicate_bits(machine, bv, repetition):
    return bv.replicate(repetition)


def sail_unsigned(machine, gbv):
    return gbv.unsigned()

def sail_signed(machine, gbv):
    return gbv.signed()

def append(machine, bv1, bv2):
    return bv1.append(bv2)

def bitvector_concat_bv_bv(machine, bv1, width, bv2):
    return (bv1 << width) | bv2

def append_64(machine, bv, v):
    return bv.append_64(v)

@unwrap("o i o")
@objectmodel.specialize.argtype(1, 3)
def vector_update(machine, bv, index, element):
    return bv.update_bit(index, element)

@objectmodel.specialize.argtype(1, 3)
def _vector_update_list_o_i_o(machine, vec, index, element):
    res = bv[:] # XXX Sail C does this without a copy
    res[index] = element
    return res

@unwrap("o i")
@objectmodel.specialize.argtype(1)
def vector_access(machine, vec, index):
    if isinstance(vec, list):
        return vec[index]
    return vec.read_bit(index)

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
def vector_update_subrange(machine, bv, n, m, s):
    return bv.update_subrange(n, m, s)

@unwrap("o i i")
@objectmodel.always_inline
def vector_subrange(machine, bv, n, m):
    return bv.subrange(n, m)

def slice(machine, bv, start, length):
    start = start.toint()
    length = length.toint()
    return bv.subrange(start + length - 1, start)

def set_slice(machine, _len, _slen, bv, start, bv_new):
    start = start.toint()
    return bv.update_subrange(start + bv_new.size() - 1, start, bv_new)

@objectmodel.always_inline
def slice_fixed_bv_i_i(machine, v, n, m):
    res = safe_rshift(None, v, m)
    width = n - m + 1
    return _mask(width, res)

def string_of_bits(machine, gbv):
    return gbv.string_of_bits()

def decimal_string_of_bits(machine, sbits):
    return str(sbits)

def uint64c(num):
    if not objectmodel.we_are_translated():
        import pdb; pdb.set_trace()
    return bitvector.from_ruint(64, r_uint(num))

def zeros(machine, num):
    return bitvector.from_ruint(num.toint(), r_uint(0))

def undefined_bitvector(machine, num):
    return zeros(machine, num)

@unwrap("o i")
def sail_truncate(machine, bv, i):
    return bv.truncate(i)


# integers

def eq_int(machine, a, b):
    assert isinstance(a, Integer)
    return a.eq(b)

def eq_int_i_i(machine, a, b):
    return a == b

def eq_bit(machine, a, b):
    return a == b

def lteq(machine, ia, ib):
    return ia.le(ib)

def lt(machine, ia, ib):
    return ia.lt(ib)

def gt(machine, ia, ib):
    return ia.gt(ib)

def gteq(machine, ia, ib):
    return ia.ge(ib)

def add_int(machine, ia, ib):
    return ia.add(ib)

def add_i_i_wrapped_res(machine, a, b):
    return bitvector.SmallInteger.add_i_i(a, b)

def sub_int(machine, ia, ib):
    return ia.sub(ib)

def sub_i_i_wrapped_res(machine, a, b):
    return bitvector.SmallInteger.sub_i_i(a, b)

def mult_int(machine, ia, ib):
    return ia.mul(ib)

def tdiv_int(machine, ia, ib):
    return ia.tdiv(ib)

def tmod_int(machine, ia, ib):
    return ia.tmod(ib)

@unwrap("i i")
def ediv_int(machine, a, b):
    if a < 0 or b < 0:
        print "emod_int with negative args not implemented yet", a, b
        raise ValueError # arm only needs the positive small case
    return Integer.fromint(a // b)

@unwrap("i i")
def emod_int(machine, a, b):
    if a < 0 or b < 0:
        print "emod_int with negative args not implemented yet", a, b
        raise ValueError # risc-v only needs the positive small case
    return Integer.fromint(a % b)

def max_int(machine, ia, ib):
    if ia.gt(ib):
        return ia
    return ib

def min_int(machine, ia, ib):
    if ia.lt(ib):
        return ia
    return ib

@unwrap("i o i")
def get_slice_int(machine, len, n, start):
    return n.slice(len, start)

def safe_rshift(machine, n, shift):
    assert shift >= 0
    if shift >= 64:
        return r_uint(0)
    return n >> shift

def print_int(machine, s, i):
    print s + i.str()
    return ()

def not_(machine, b):
    return not b

def eq_bool(machine, a, b):
    return a == b

def string_of_int(machine, r):
    return r.str()

@objectmodel.specialize.arg_or_var(1)
def int_to_int64(machine, r):
    if objectmodel.is_annotation_constant(r):
        return _int_to_int64_memo(r)
    return r.toint()

@objectmodel.specialize.memo()
def _int_to_int64_memo(r):
    return r.toint()

def int64_to_int(machine, i):
    return Integer.fromint(i)

def string_to_int(machine, s):
    return Integer.fromstr(s)


def undefined_int(machine, _):
    return Integer.fromint(0)

@unwrap("i")
def pow2(machine, x):
    return Integer.frombigint(rbigint.fromint(2).int_pow(x))

def neg_int(machine, x):
    return Integer.fromint(0).sub(x)

def dec_str(machine, x):
    return x.str()

def hex_str(machine, x):
    return x.hex()

@unwrap("o i")
def shl_int(machine, i, shift):
    return i.lshift(shift)

@unwrap("o i")
def shr_int(machine, i, shift):
    return i.rshift(shift)

def shl_mach_int(machine, i, shift):
    return i << shift

def shr_mach_int(machine, i, shift):
    return i >> shift

def abs_int(machine, i):
    return i.abs()


# real

def neg_real(machine, r):
    return r.neg()

def abs_real(machine, r):
    return r.abs()

def add_real(machine, a, b):
    return a.add(b)

def sub_real(machine, a, b):
    return a.sub(b)

def mult_real(machine, a, b):
    return a.mul(b)

def div_real(machine, a, b):
    return a.div(b)

def round_up(machine, r):
    return Integer.frombigint(r.ceil())

def round_down(machine, r):
    return Integer.frombigint(r.floor())

def eq_real(machine, a, b):
    return a.eq(b)

def lt_real(machine, a, b):
    return a.lt(b)

def gt_real(machine, a, b):
    return a.gt(b)

def lteq_real(machine, a, b):
    return a.le(b)

def gteq_real(machine, a, b):
    return a.ge(b)

def real_power(machine, r, si):
    n = si.toint()
    return r.pow(n)

def sqrt_real(machine, r):
    return r.sqrt()

def string_to_real(machine, str):
    return Real.fromstr(str)

def print_real(machine, s, r):
    print s + r.num.str()+"/"+r.den.str()
    return ()

def to_real(machine, i):
    return Real(i.tobigint(), rbigint.fromint(1))

def undefined_real(machine, _):
    return Real.fromint(12, 19)


# various

@objectmodel.specialize.argtype(1)
def reg_deref(machine, s):
    return s

def sail_assert(cond, st):
    if not objectmodel.we_are_translated() and not cond:
        import pdb; pdb.set_trace()
    assert cond, st
    return ()

def print_endline(machine, s):
    print s
    return ()

def prerr_endline(machine, s):
    os.write(STDERR, s + "\n")
    return ()

def undefined_bool(machine, _):
    return False

def undefined_unit(machine, _):
    return ()

# list weirdnesses

@objectmodel.specialize.argtype(1)
def internal_pick(machine, lst):
    return lst.head

# vector stuff

@objectmodel.specialize.argtype(1, 2, 4)
def vector_update_inplace(machine, res, l, index, element):
    # super weird, the C backend does the same
    if res is not l:
        l = l[:]
    l[index] = element
    return l

def undefined_vector(machine, size, element):
    return [element] * size.toint()


def elf_tohost(machine, _):
    return Integer.fromint(0)

def platform_barrier(machine, _):
    return ()

def platform_write_mem_ea(machine, write_kind, addr_size, addr, n):
    return ()


# strings

def concat_str(machine, a, b):
    return a + b

def eq_string(machine, a, b):
    return a == b

def string_length(machine, s):
    return Integer.fromint(len(s))
    
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

# memory emulation


def read_mem(machine, address):
    return machine.g.mem.read(address, 1)

def write_mem(machine, address, data):
    machine.g.mem.write(address, 1, data)
    return ()

def platform_read_mem(machine, read_kind, addr_size, addr, n):
    n = n.toint()
    assert addr_size in (64, 32)
    res = machine.g.mem.read(addr.touint(), n)
    return bitvector.SmallBitVector(n*8, res)

def platform_write_mem(machine, write_kind, addr_size, addr, n, data):
    n = n.toint()
    assert addr_size in (64, 32)
    assert data.size() == n * 8
    jit.promote(machine.g).mem.write(addr.touint(), n, data.touint())
    return ()


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

class Globals(object):
    def __init__(self):
        from pydrofoil import mem as mem_mod
        self.mem = mem_mod.BlockMemory()

