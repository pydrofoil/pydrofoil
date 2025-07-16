import os

from pypy.interpreter.baseobjspace import W_Root

from rpython.rlib import objectmodel, unroll, jit
from rpython.rlib.rbigint import rbigint, ONERBIGINT
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
from pydrofoil import bitvector
from pydrofoil.bitvector import Integer, ruint_mask as _mask
import pydrofoil.softfloat as softfloat
from pydrofoil.real import Real

STDOUT = 1
STDERR = 2

DEBUG_PRINT_BUILTINS = False

if DEBUG_PRINT_BUILTINS:
    def always_inline(func):
        return func

    objectmodel.always_inline = always_inline

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
        wrappedfunc.__dict__.update(func.__dict__)
        unwrapped_name = func.func_name + "_" + "_".join(argspecs)
        func.func_globals[unwrapped_name] = func
        if func.func_name in purefunctions:
            purefunctions[func.func_name] = wrappedfunc
            purefunctions[unwrapped_name] = func
        wrappedfunc.func_name += "_" + func.func_name
        all_unwraps[func.func_name] = (argspecs, unwrapped_name)
        return wrappedfunc
    return wrap

purefunctions = {}

def purefunction(func):
    purefunctions[func.func_name] = func
    name = func.func_name
    @objectmodel.specialize.argtype(0)
    def print_args(arg, *args):
        if isinstance(arg, int):
            print arg,
        elif isinstance(arg, r_uint):
            print arg,
        elif isinstance(arg, str):
            print arg,
        elif isinstance(arg, bool):
            print arg,
        elif isinstance(arg, bitvector.Integer):
            print arg.__repr__(),
        elif isinstance(arg, bitvector.BitVector):
            print arg.__repr__(),
        else:
            print "unknown",
        if not args:
            return
        print_args(*args)

    def wrapped_func(machine, *args):
        print name,
        if args:
            print_args(*args)
        res = func(machine, *args)
        print "->",
        print_args(res)
        print
        return res
    wrapped_func.func_name = name
    if DEBUG_PRINT_BUILTINS:
        return wrapped_func
    else:
        return func

# unimplemented

make_dummy('plat_enable_dirty_update')
make_dummy('plat_enable_misaligned_access')
make_dummy('plat_enable_pmp')
make_dummy('platform_barrier')
make_dummy('print_mem_access')
make_dummy('print_platform')
make_dummy('print_reg')
make_dummy('string_drop')
make_dummy('string_take')
make_dummy('string_startswith')
make_dummy('sub_nat')
make_dummy("wakeup_request")
make_dummy("set_slice_int")
make_dummy("undefined_range")

make_dummy("softfloat_f16roundToInt")
make_dummy("softfloat_f32roundToInt")
make_dummy("softfloat_f64roundToInt")


# generic helpers

def raise_type_error(msg=''):
    if msg:
        print "INTERNAL ERROR", msg
    raise TypeError


# bit vectors

@purefunction
def signed_bv(machine, op, n):
    if n == 64:
        return intmask(op)
    assert n > 0
    u1 = r_uint(1)
    m = u1 << (n - 1)
    op = op & ((u1 << n) - 1) # mask off higher bits to be sure
    return intmask((op ^ m) - m)

@objectmodel.always_inline
@purefunction
def unsigned_bv_wrapped_res(machine, op, n):
    return bitvector.Integer.from_ruint(op)

@objectmodel.always_inline
@purefunction
def unsigned_bv64_rshift_int_result(machine, op, n):
    assert 0 < n < 64
    return intmask(op >> n)

@objectmodel.always_inline
@purefunction
def unsigned_bv(machine, op, n):
    if n == 64 and (op & (r_uint(1) << 63)):
        raise ValueError
    return intmask(op)

@objectmodel.always_inline
@purefunction
@objectmodel.specialize.argtype(1, 2)
def add_bits_int(machine, a, b):
    return a.add_int(b)

@objectmodel.always_inline
@purefunction
def add_bits_int_bv_i(machine, a, width, b):
    return _mask(width, a + r_uint(b))

@objectmodel.always_inline
@purefunction
def add_bits(machine, a, b):
    return a.add_bits(b)

@purefunction
def add_bits_bv_bv(machine, a, b, width):
    return _mask(width, a + b)

@purefunction
def sub_bits_int(machine, a, b):
    return a.sub_int(b)

@objectmodel.always_inline
@purefunction
def sub_bits_int_bv_i(machine, a, width, b):
    return _mask(width, a - r_uint(b))

@objectmodel.always_inline
@purefunction
def sub_bits(machine, a, b):
    return a.sub_bits(b)

@purefunction
def sub_bits_bv_bv(machine, a, b, width):
    return _mask(width, a - b)

@purefunction
def length(machine, gbv):
    return gbv.size_as_int()

@purefunction
def length_unwrapped_res(machine, gbv):
    return gbv.size()

@unwrap("o i")
@purefunction
@objectmodel.always_inline
def sign_extend(machine, gbv, size):
    return gbv.sign_extend(size)

@objectmodel.always_inline
@purefunction
def sign_extend_bv_i_i(machine, bv, width, targetwidth):
    m = r_uint(1) << (width - 1)
    return _mask(targetwidth, (bv ^ m) - m)

@purefunction
def sign_extend_o_i_unwrapped_res(machine, bv, size):
    assert size <= 64
    assert isinstance(bv, bitvector.SmallBitVector)
    return sign_extend_bv_i_i(machine, bv.touint(), bv.size(), size)

@unwrap("o i")
@objectmodel.always_inline
@purefunction
def zero_extend(machine, gbv, size):
    return gbv.zero_extend(size)

@objectmodel.always_inline
@purefunction
def zero_extend_bv_i_i(machine, bv, width, targetwidth):
    return bv # XXX correct?

@purefunction
def zero_extend_o_i_unwrapped_res(machine, bv, size):
    assert size <= 64
    assert isinstance(bv, bitvector.SmallBitVector)
    return bv.touint()

@purefunction
def eq_bits(machine, gvba, gvbb):
    return gvba.eq(gvbb)

@purefunction
def eq_bits_bv_bv(machine, bva, bvb):
    return bva == bvb

@purefunction
def neq_bits(machine, gvba, gvbb):
    return not gvba.eq(gvbb)

@purefunction
def neq_bits_bv_bv(machine, bva, bvb):
    return bva != bvb

@purefunction
def xor_bits(machine, gvba, gvbb):
    return gvba.xor(gvbb)

@purefunction
def xor_vec_bv_bv(machine, bva, bvb):
    return bva ^ bvb

@purefunction
def and_bits(machine, gvba, gvbb):
    return gvba.and_(gvbb)

@purefunction
def and_vec_bv_bv(machine, bva, bvb):
    return bva & bvb

@purefunction
def or_bits(machine, gvba, gvbb):
    return gvba.or_(gvbb)

@purefunction
def or_vec_bv_bv(machine, bva, bvb):
    return bva | bvb

@purefunction
def not_bits(machine, gvba):
    return gvba.invert()

@purefunction
def not_vec_bv(machine, bva, width):
    return _mask(width, ~bva)

def print_bits(machine, s, b):
    print s + b.string_of_bits()
    return ()

def print_string(machine, *args):
    print _tup_join(*args)
    return ()

def _tup_join(*args):
    if len(args) == 0:
        return ''
    if len(args) == 1:
        return args[0]
    else:
        return args[0] + _tup_join(*args[1:])


def prerr_bits(machine, s, b):
    os.write(STDERR, "%s%s\n" % (s, b.string_of_bits()))
    return ()


@unwrap("o i")
@purefunction
def shiftl(machine, gbv, i):
    return gbv.lshift(abs(i))

@purefunction
def shiftl_bv_i(machine, a, width, i):
    return _mask(width, a << i)

@unwrap("o i")
@purefunction
def shiftr(machine, gbv, i):
    return gbv.rshift(i)

@purefunction
def shiftr_bv_i(machine, a, width, i):
    return _mask(width, a >> i)

@purefunction
@unwrap("o i")
def arith_shiftr(machine, gbv, i):
    return gbv.arith_rshift(i)

@purefunction
def arith_shiftr_bv_i(machine, a, width, i):
    signed = signed_bv(machine, a, width)
    return _mask(width, r_uint(signed >> i))

@purefunction
def shift_bits_left(machine, gbv, gbva):
    return gbv.lshift_bits(gbva)

@purefunction
def shift_bits_right(machine, gbv, gbva):
    return gbv.rshift_bits(gbva)

@unwrap("o i")
@purefunction
def replicate_bits(machine, bv, repetition):
    return bv.replicate(repetition)

def replicate_bv_i_i(machine, bv, width, repetition):
    return bitvector.SmallBitVector._replicate(bv, width, repetition)

@purefunction
def sail_unsigned(machine, gbv):
    return gbv.unsigned()

@purefunction
def sail_signed(machine, gbv):
    return gbv.signed()

@purefunction
def append(machine, bv1, bv2):
    return bv1.append(bv2)

@purefunction
def bitvector_concat_bv_bv(machine, bv1, width, bv2):
    return (bv1 << width) | bv2

@purefunction
def bitvector_concat_bv_gbv_wrapped_res(machine, bv1, width, gbv):
    return gbv.prepend_small(width, bv1)

@purefunction
def bitvector_concat_bv_n_zeros_wrapped_res(machine, bv1, width, nzeros):
    return bitvector.bv_concat_n_zero_bits(width, bv1, nzeros)

@purefunction
def bitvector_concat_bv_gbv_truncate_to(machine, bv1, width, gbv, target_width):
    return gbv.prepend_small_then_truncate_unwrapped_res(width, bv1, target_width)

@purefunction
def bitvector_concat_bv_bv_n_zeros_truncate(machine, bv1, width1, bv2, width2, nzeros, target_width):
    res = (bv1 << width2) | bv2
    res <<= nzeros
    return _mask(target_width, res)

@purefunction
def append_64(machine, bv, v):
    return bv.append_64(v)

@unwrap("o i o")
@purefunction
def vector_update(machine, bv, index, element):
    return bv.update_bit(index, element)

@unwrap("o i")
@purefunction
def vector_access(machine, vec, index):
    return vec.read_bit(index)

@purefunction
def vector_access_bv_i(machine, bv, index):
    if index == 0:
        return bv & r_uint(1)
    return r_uint(1) & safe_rshift(None, bv, index)

@purefunction
def zupdate_fbits(machine, fb, index, element):
    assert 0 <= index < 64
    if element:
        return fb | (r_uint(1) << index)
    else:
        return fb & ~(r_uint(1) << index)

@unwrap("o i i o")
@purefunction
def vector_update_subrange(machine, bv, n, m, s):
    return bv.update_subrange(n, m, s)

@purefunction
def vector_update_subrange_fixed_bv_i_i_bv(machine, bv, n, m, s):
    width = n - m + 1
    ones = _mask(width, r_uint(-1))
    mask = ~(ones << m)
    return (bv & mask) | (s << m)

@unwrap("o i i")
@objectmodel.always_inline
@purefunction
@objectmodel.specialize.argtype(1)
def vector_subrange(machine, bv, n, m):
    return bv.subrange(n, m)

@objectmodel.always_inline
@purefunction
@objectmodel.specialize.argtype(1)
def vector_subrange_o_i_i_unwrapped_res(machine, bv, n, m):
    return bv.subrange_unwrapped_res(n, m)

@unwrap("o i i")
@purefunction
@objectmodel.specialize.argtype(1)
def slice(machine, bv, start, length):
    return bv.subrange(start + length - 1, start)

@objectmodel.always_inline
@purefunction
@objectmodel.specialize.argtype(1)
def vector_slice_o_i_i_unwrapped_res(machine, bv, start, length):
    return bv.subrange_unwrapped_res(start + length - 1, start)

@unwrap("i i o i o")
@purefunction
@objectmodel.specialize.argtype(3)
def set_slice(machine, _len, _slen, bv, start, bv_new):
    return bv.update_subrange(start + bv_new.size() - 1, start, bv_new)

@objectmodel.always_inline
@purefunction
def vector_subrange_fixed_bv_i_i(machine, v, n, m):
    res = safe_rshift(None, v, m)
    width = n - m + 1
    # XXX if we pass in the width of v here, we can not do the mask
    return _mask(width, res)

@objectmodel.always_inline
@purefunction
def slice_fixed_bv_i_i(machine, v, start, length):
    return vector_subrange_fixed_bv_i_i(machine, v, start + length - 1, start)

@purefunction
def string_of_bits(machine, gbv):
    return gbv.string_of_bits()

@purefunction
def decimal_string_of_bits(machine, sbits):
    return str(sbits)

def uint64c(machine, num):
    if not objectmodel.we_are_translated():
        import pdb; pdb.set_trace()
    assert num == r_uint(0)
    return bitvector.from_ruint(0, r_uint(num))

@unwrap("i")
@purefunction
def zeros(machine, num):
    return bitvector.from_ruint(num, r_uint(0))

@unwrap("i")
@purefunction
def ones(machine, num):
    if num <= 64:
        return bitvector.from_ruint(num, r_uint(-1))
    else:
        return bitvector.from_bigint(num, rbigint.fromint(-1))

@purefunction
def ones_zero_extended_unwrapped_res(machine, num_ones, width):
    num_ones = min(num_ones, width)
    assert num_ones <= 64
    return safe_lshift(None, r_uint(1), num_ones) - 1

@unwrap("i")
@purefunction
def undefined_bitvector(machine, num):
    return bitvector.from_ruint(num, r_uint(0))

@unwrap("o i")
@purefunction
def sail_truncate(machine, bv, i):
    return bv.truncate(i)

@purefunction
def truncate_unwrapped_res(machine, bv, length):
    return bv.subrange_unwrapped_res(length - 1, 0)

@unwrap("o i")
@purefunction
def sail_truncateLSB(machine, bv, i):
    return bv.truncate_lsb(i)

@purefunction
def truncate_bv_i(machine, bv, i):
    return _mask(i, bv)

@unwrap("o")
@purefunction
def count_leading_zeros(machine, bv):
    return bitvector.Integer.fromint(bv.count_leading_zeros())

@unwrap("o")
@purefunction
def count_trailing_zeros(machine, bv):
    return bitvector.Integer.fromint(bv.count_trailing_zeros())

@objectmodel.always_inline
@purefunction
def pack_smallfixedbitvector(machine, width, val):
    if not objectmodel.we_are_translated() and machine == "constfolding":
        from pydrofoil.ir import CantFold
        raise CantFold
    return width, val, None

@objectmodel.always_inline
@purefunction
def pack_machineint(machine, val):
    if not objectmodel.we_are_translated() and machine == "constfolding":
        from pydrofoil.ir import CantFold
        raise CantFold
    return val, None

@objectmodel.always_inline
@purefunction
def packed_field_cast_smallfixedbitvector(machine, targetwidth, (width, val, data)):
    if not objectmodel.we_are_translated() and machine == "constfolding":
        from pydrofoil.ir import CantFold
        raise CantFold
    assert width == targetwidth
    return val

@objectmodel.always_inline
@purefunction
def packed_field_int_to_int64(machine, (val, data)):
    # equivalent to Integer.unpack(val, data).toint()
    if not objectmodel.we_are_translated() and machine == "constfolding":
        from pydrofoil.ir import CantFold
        raise CantFold
    if data is None:
        return val
    return bitvector.BigInteger._sign_and_data_toint(val, data)


# for debugging

def debug_check_bv_fits(bv, size):
    assert _mask(size, bv) == bv
    return bv

# integers

@purefunction
@objectmodel.specialize.argtype(1)
def eq_int(machine, a, b):
    assert isinstance(a, Integer)
    return a.eq(b)

@purefunction
def eq_int_i_i(machine, a, b):
    return a == b

@purefunction
def eq_int_o_i(machine, a, b):
    return a.int_eq(b)

@purefunction
def eq_bit(machine, a, b):
    return a == b

@purefunction
@objectmodel.specialize.argtype(1)
def lteq(machine, ia, ib):
    if not objectmodel.we_are_translated():
        if isinstance(ia, int) and isinstance(ib, int):
            assert machine == "constfolding"
            return ia <= ib # const folding only
    return ia.le(ib)

@purefunction
@objectmodel.specialize.argtype(1)
def lt(machine, ia, ib):
    if not objectmodel.we_are_translated():
        if isinstance(ia, int) and isinstance(ib, int):
            assert machine == "constfolding"
            return ia < ib # const folding only
    return ia.lt(ib)

@purefunction
@objectmodel.specialize.argtype(1)
def gt(machine, ia, ib):
    if not objectmodel.we_are_translated():
        if isinstance(ia, int) and isinstance(ib, int):
            assert machine == "constfolding"
            return ia > ib # const folding only
    return ia.gt(ib)

@purefunction
@objectmodel.specialize.argtype(1)
def gteq(machine, ia, ib):
    if not objectmodel.we_are_translated():
        if isinstance(ia, int) and isinstance(ib, int):
            assert machine == "constfolding"
            return ia >= ib # const folding only
    return ia.ge(ib)

@objectmodel.not_rpython
@purefunction
def eq(machine, ia, ib):
    assert not objectmodel.we_are_translated()
    assert machine == "constfolding"
    if type(ia) is int:
        assert type(ib) is int
        return ia == ib
    import pdb;pdb.set_trace()

@purefunction
def lt_unsigned64(machine, ua, ub):
    assert isinstance(ua, r_uint)
    assert isinstance(ub, r_uint)
    return ua < ub

@purefunction
def lteq_unsigned64(machine, ua, ub):
    assert isinstance(ua, r_uint)
    assert isinstance(ub, r_uint)
    return ua <= ub

@purefunction
def gteq_unsigned64(machine, ua, ub):
    assert isinstance(ua, r_uint)
    assert isinstance(ub, r_uint)
    return ua >= ub

@purefunction
@objectmodel.specialize.argtype(1)
def add_int(machine, ia, ib):
    return ia.add(ib)

@purefunction
def add_o_i_wrapped_res(machine, a, b):
    return a.int_add(b)

@purefunction
def add_unsigned_bv64_unsigned_bv64_wrapped_res(machine, a, b):
    res = a + b
    if res < a:
        a = bitvector.Integer.from_ruint(a)
        b = bitvector.Integer.from_ruint(b)
        return a.add(b)
    else:
        return Integer.from_ruint(res)

@purefunction
def lteq_add4_unsigned_bv64(machine, a, b, c, d):
    # returns a + b <= c + d, where a, b, c, d are 64 bit bvs, interpreted as unsigned ints
    x = a + b
    y = c + d
    if x >= a and y >= c: # both unsigned adds don't overflow
        return x <= y
    else:
        # slow path, unlikely
        a = bitvector.Integer.from_ruint(a)
        b = bitvector.Integer.from_ruint(b)
        c = bitvector.Integer.from_ruint(c)
        d = bitvector.Integer.from_ruint(d)
        x = a.add(b)
        y = c.add(d)
        return x.le(y)


@purefunction
def add_i_i_wrapped_res(machine, a, b):
    return bitvector.SmallInteger.add_i_i(a, b)

@purefunction
def add_i_i_must_fit(machine, a, b):
    try:
        return ovfcheck(a + b)
    except OverflowError:
        assert 0, "must not happen"

@purefunction
@objectmodel.specialize.argtype(1)
def sub_int(machine, ia, ib):
    return ia.sub(ib)

@purefunction
def sub_i_i_wrapped_res(machine, a, b):
    return bitvector.SmallInteger.sub_i_i(a, b)

@purefunction
def sub_i_i_must_fit(machine, a, b):
    try:
        return ovfcheck(a - b)
    except OverflowError:
        assert 0, "must not happen"

@purefunction
def sub_o_i_wrapped_res(machine, a, b):
    return a.int_sub(b)

@objectmodel.always_inline
@purefunction
def sub_i_o_wrapped_res(machine, a, b):
    if isinstance(b, bitvector.SmallInteger):
        return bitvector.SmallInteger.sub_i_i(a, b.val)
    return bitvector.Integer.fromint(a).sub(b)

@purefunction
@objectmodel.specialize.argtype(1)
def mult_int(machine, ia, ib):
    return ia.mul(ib)

@purefunction
def mult_o_i_wrapped_res(machine, a, b):
    return a.int_mul(b)

@purefunction
def mult_i_i_wrapped_res(machine, a, b):
    return bitvector.SmallInteger.mul_i_i(a, b)

@purefunction
def mult_i_i_must_fit(machine, a, b):
    try:
        return ovfcheck(a * b)
    except OverflowError:
        assert 0, "must not happen"

@purefunction
@objectmodel.specialize.argtype(1)
def tdiv_int(machine, ia, ib):
    return ia.tdiv(ib)

@purefunction
def tdiv_int_i_i(machine, a, b):
    from rpython.rlib.rarithmetic import int_c_div
    if b == 0:
        raise ZeroDivisionError
    assert b != -1
    return int_c_div(a, b)

@purefunction
@objectmodel.specialize.argtype(1)
def tmod_int(machine, ia, ib):
    return ia.tmod(ib)

@purefunction
@objectmodel.specialize.argtype(1)
def ediv_int(machine, a, b):
    return a.ediv(b)

@purefunction
def ediv_int_i_ipos(machine, a, b):
    assert b >= 2
    return a // b

@purefunction
@objectmodel.specialize.argtype(1)
def emod_int(machine, a, b):
    return a.emod(b)

@purefunction
@objectmodel.specialize.argtype(1)
def max_int(machine, ia, ib):
    if ia.gt(ib):
        return ia
    return ib

@purefunction
@objectmodel.specialize.argtype(1)
def min_int(machine, ia, ib):
    if ia.lt(ib):
        return ia
    return ib

@unwrap("i o i")
@purefunction
def get_slice_int(machine, len, n, start):
    return n.slice(len, start)

@purefunction
def get_slice_int_i_o_i_unwrapped_res(machine, len, n, start):
    return n.slice_unwrapped_res(len, start)

@purefunction
def get_slice_int_i_i_i(machine, len, i, start):
    return _mask(len, r_uint(i >> start))

def safe_rshift(machine, n, shift):
    assert shift >= 0
    if shift >= 64:
        return r_uint(0)
    return n >> shift

def safe_lshift(machine, n, shift):
    assert shift >= 0
    if shift >= 64:
        return r_uint(0)
    return n << shift

def print_int(machine, s, i):
    print s + i.str()
    return ()

def prerr_int(machine, s, i):
    os.write(STDERR, s + i.str() + "\n")
    return ()

@purefunction
def not_(machine, b):
    return not b

def eq_bool(machine, a, b):
    return a == b

def string_of_int(machine, r):
    return r.str()

@purefunction
@objectmodel.specialize.arg_or_var(1)
def int_to_int64(machine, r):
    if objectmodel.is_annotation_constant(r):
        return _int_to_int64_memo(r)
    return r.toint()

@objectmodel.specialize.memo()
def _int_to_int64_memo(r):
    return r.toint()

@purefunction
def int64_to_int(machine, i):
    return Integer.fromint(i)

@purefunction
def string_to_int(machine, s):
    return Integer.fromstr(s)

@purefunction
def undefined_int(machine, _):
    return Integer.fromint(0)

@unwrap("i")
@purefunction
def pow2(machine, x):
    assert x >= 0
    if x < 63:
        return Integer.fromint(1 << x)
    return Integer.from_bigint(ONERBIGINT.lshift(x))

@purefunction
def neg_int(machine, x):
    return x.neg()

@purefunction
def dec_str(machine, x):
    return x.str()

@purefunction
def hex_str(machine, x):
    return x.hex()

@unwrap("o i")
@purefunction
def shl_int(machine, i, shift):
    return i.lshift(shift)

@purefunction
def shl_int_i_i_wrapped_res(machine, i, shift):
    return bitvector.SmallInteger.lshift_i_i(i, shift)

@purefunction
def shl_int_i_i_must_fit(machine, i, shift):
    try:
        return ovfcheck(i << shift)
    except OverflowError:
        assert 0, "must not happen"

@unwrap("o i")
@purefunction
def shr_int(machine, i, shift):
    return i.rshift(shift)

@purefunction
def shl_mach_int(machine, i, shift):
    return i << shift

@purefunction
def shr_mach_int(machine, i, shift):
    return i >> shift

@purefunction
def abs_int(machine, i):
    return i.abs()

def pow_int(machine, i, j):
    return i.pow(j)

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
    return Integer.from_bigint(r.ceil())

def round_down(machine, r):
    return Integer.from_bigint(r.floor())

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

@unwrap("o i")
def real_power(machine, r, n):
    return r.pow(n)

def sqrt_real(machine, r):
    return r.sqrt()

def string_to_real(machine, str):
    return Real.fromstr(str)

def print_real(machine, s, r):
    print s + r.num.str()+"/"+r.den.str()
    return ()

def to_real(machine, i):
    jit.jit_debug("integer to_real")
    return Real(i.tobigint(), ONERBIGINT, normalized=True)

@purefunction
def undefined_real(machine, _):
    return Real.fromint(12, 19)


# various

@objectmodel.specialize.argtype(1)
def reg_deref(machine, s):
    if isinstance(s, RegRef):
        return s.deref(machine)
    return s

@objectmodel.always_inline
def sail_assert(machine, cond, st):
    if not objectmodel.we_are_translated() and not cond:
        import pdb; pdb.set_trace()
    assert cond, st
    return ()

def print_endline(machine, s):
    print s
    return ()

def print_(machine, s):
    os.write(STDOUT, s)
    return ()

def prerr_endline(machine, s):
    os.write(STDERR, s + "\n")
    return ()

def sail_putchar(machine, i):
    os.write(STDOUT, chr(i.toint() & 0xff))
    return ()

@purefunction
def undefined_bool(machine, _):
    return False

@purefunction
def undefined_unit(machine, _):
    return ()

# list weirdnesses

@objectmodel.specialize.argtype(1)
def internal_pick(machine, lst):
    return lst.head
if not DEBUG_PRINT_BUILTINS:
    internal_pick = purefunction(internal_pick)

@purefunction
def cons(machine, a, b):
    assert 0, "unreachable at runtime, see GlobalVal.makecode"

# vector stuff

@objectmodel.specialize.argtype(2, 4)
def vector_update_inplace(machine, res, l, index, element):
    # super weird, the C backend does the same
    l = l[:]
    l[index] = element
    return l

@objectmodel.specialize.argtype(1, 3)
def vector_update_list(machine, l, index, element):
    l = l[:]
    l[index] = element
    return l

@unwrap("i o")
@objectmodel.specialize.argtype(2)
def vector_init(machine, length, element):
    return [element] * length

@purefunction
def vec_length_unwrapped_res(machine, l):
    return len(l)

@objectmodel.specialize.argtype(1, 3)
def helper_vector_update_inplace_o_i_o(machine, vec, index, element):
    if vec is None:
        raise TypeError
    vec[index] = element

@objectmodel.specialize.argtype(2)
def undefined_vector(machine, size, element):
    return [element] * size.toint()

def vec_gbv_to_vec_bv8(machine, vector):
    assert isinstance(vector, list)
    if not objectmodel.we_are_translated():
        import pdb; pdb.set_trace()
    return [x.touint(8) for x in vector]

def vec_gbv_to_vec_bv16(machine, vector):
    assert isinstance(vector, list)
    if not objectmodel.we_are_translated():
        import pdb; pdb.set_trace()
    return [x.touint(16) for x in vector]


def elf_tohost(machine, _):
    return Integer.fromint(0)

def platform_barrier(machine, _):
    return ()

def platform_write_mem_ea(machine, write_kind, addr_size, addr, n):
    return ()


# strings

@purefunction
def concat_str(machine, a, b):
    return a + b

@purefunction
def eq_string(machine, a, b):
    return a == b

@purefunction
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

def softfloat_f16le_quiet(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f16le_quiet(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f16lt_quiet(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f16lt_quiet(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32le_quiet(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f32le_quiet(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f32lt_quiet(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f32lt_quiet(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64le_quiet(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f64le_quiet(v1, v2)
    machine._reg_zfloat_fflags = softfloat.get_exception_flags()
    return 0

def softfloat_f64lt_quiet(machine, v1, v2):
    machine._reg_zfloat_result = softfloat.f64lt_quiet(v1, v2)
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


@unwrap("o o o i")
def read_mem(machine, read_kind, addr_size, addr, n):
    assert addr_size in (64, 32)
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        res = mem.read(addr, n)
        return bitvector.SmallBitVector(n*8, res)
    else:
        return _platform_read_mem_slowpath(machine, mem, read_kind, addr, n)

@unwrap("o o o i")
def read_mem_exclusive(machine, read_kind, addr_size, addr, n):
    assert addr_size in (64, 32)
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        res = mem.read(addr, n)
        return bitvector.SmallBitVector(n*8, res)
    else:
        return _platform_read_mem_slowpath(machine, mem, read_kind, addr, n)

@unwrap("o o o i")
def read_mem_ifetch(machine, read_kind, addr_size, addr, n):
    assert addr_size in (64, 32)
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        res = mem.read(addr, n, executable_flag=True)
        return bitvector.SmallBitVector(n*8, res)
    else:
        return _platform_read_mem_slowpath(machine, mem, read_kind, addr, n)

@unwrap("o o o i")
def platform_read_mem(machine, read_kind, addr_size, addr, n):
    assert addr_size in (64, 32)
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        res = mem.read(addr, n)
        return bitvector.SmallBitVector(n*8, res)
    else:
        return _platform_read_mem_slowpath(machine, mem, read_kind, addr, n)

def platform_read_mem_o_i_bv_i(machine, read_kind, addr_size, addr, n):
    mem = jit.promote(machine.g).mem
    return mem.read(addr, n)

def fast_read_mem_i_bv_i_isfetch(machine, addr_size, addr, n, isfetch):
    mem = jit.promote(machine.g).mem
    return mem.read(addr, n, executable_flag=isfetch)

@jit.unroll_safe
def _platform_read_mem_slowpath(machine, mem, read_kind, addr, n):
    value = None
    for i in range(n - 1, -1, -1):
        byteval = mem.read(addr + i, 1)
        nextbyte = bitvector.SmallBitVector(8, byteval)
        if value is None:
            value = nextbyte
        else:
            value = value.append(nextbyte)
    return value

@unwrap("o o o i o")
def platform_write_mem(machine, write_kind, addr_size, addr, n, data):
    assert addr_size in (64, 32)
    assert data.size() == n * 8
    mem = jit.promote(machine.g).mem
    addr = addr.touint()
    if n == 1 or n == 2 or n == 4 or n == 8:
        mem.write(addr, n, data.touint())
    else:
        _platform_write_mem_slowpath(machine, mem, write_kind, addr, n, data)
    return True

@jit.unroll_safe
def _platform_write_mem_slowpath(machine, mem, write_kind, addr, n, data):
    #if not objectmodel.we_are_translated():
    #    import pdb; pdb.set_trace()
    start = 0
    stop = 7
    for i in range(n):
        byte = data.subrange_unwrapped_res(stop, start)
        mem.write(addr + i, 1, byte)
        stop += 8
        start += 8
    assert start == data.size()

# isla stuff

@objectmodel.always_inline
def branch_announce(machine, addrsize, addr):
    return ()

@objectmodel.always_inline
def monomorphize(machine, addr):
    return addr

make_dummy("read_register_from_vector")
make_dummy("write_register_from_vector")

make_dummy("emulator_read_tag")
make_dummy("emulator_write_tag")

# argument handling

@objectmodel.specialize.arg(4)
def parse_args(argv, shortname, longname="", want_arg=True, many=False):
    # crappy argument handling
    reslist = []
    if many:
        assert want_arg
    i = 0
    while i < len(argv):
        if argv[i] == shortname or argv[i] == longname:
            if not want_arg:
                res = argv[i]
                del argv[i]
                return res
            if len(argv) == i + 1:
                print "missing argument after " + argv[i]
                raise ValueError
            arg = argv[i + 1]
            del argv[i:i+2]
            if many:
                reslist.append(arg)
            else:
                return arg
            continue
        i += 1
    if many:
        return reslist

def parse_flag(argv, flagname, longname=""):
    return bool(parse_args(argv, flagname, longname=longname, want_arg=False))



class RegistersBase(object):
    _immutable_fields_ = []
    _attrs_ = ['have_exception', 'throw_location', 'current_exception', 'g', '_reg_zfloat_fflags', '_reg_zfloat_result']

    have_exception = False
    throw_location = None
    current_exception = None

    def __init__(self):
        pass

class ObjectBase(W_Root):
    _attrs_ = []

class LetsBase(object):
    def _freeze_(self):
        return True

class Globals(object):
    _immutable_fields_ = ['mem']
    _pydrofoil_enum_read_ifetch_value = -1

    def __init__(self):
        from pydrofoil import mem as mem_mod
        self.mem = mem_mod.BlockMemory()

class RegRef(object):
    pass

class SailError(Exception):
    def __init__(self, msg):
        self.msg = msg


# some helper functions for interfacing with PyPy, completely optional for
# almost everything except the plugin

@objectmodel.specialize.argtype(1)
def convert_to_pypy_error(space, val):
    raise ValueError

def convert_from_pypy_error(space, w_val):
    raise ValueError

def cache1(func):
    cache = {}
    @objectmodel.specialize.memo()
    def cached_func(arg):
        if arg in cache:
            return cache[arg]
        res = func(arg)
        cache[arg] = res
        return res
    return cached_func

def cache2(func):
    cache = {}
    @objectmodel.specialize.memo()
    def cached_func(arg, arg2):
        if (arg, arg2) in cache:
            return cache[arg, arg2]
        res = func(arg, arg2)
        cache[arg, arg2] = res
        return res
    return cached_func

@cache1
def generate_convert_to_pypy_error(typname):
    def convert_to_pypy_error(space, val):
        raise ValueError
    return convert_to_pypy_error

@cache1
def generate_convert_from_pypy_error(typname):
    def convert_from_pypy_error(space, val):
        raise ValueError
    return convert_from_pypy_error

@cache1
def generate_convert_to_pypy_bitvector_ruint(width):

    def c(space, val):
        return bitvector.from_ruint(width, val)
    c.func_name = "convert_to_pypy_bitvector_ruint_%s" % width
    return c

@cache1
def generate_convert_from_pypy_bitvector_ruint(width):
    from pypy.interpreter.error import oefmt
    def c(space, w_val):
        if isinstance(w_val, bitvector.BitVector):
            if w_val.size() != width:
                raise oefmt(space.w_ValueError, "expected bitvector of size %d, got size %d", width, w_val.size())
            return w_val.touint(width)
        return _mask(width, space.uint_w(w_val))
    c.func_name = "convert_from_pypy_bitvector_ruint_%s" % width
    return c

@cache1
def generate_convert_to_pypy_big_fixed_bitvector(width):
    def c(space, val):
        assert val.size() == width
        return val
    c.func_name = "convert_to_pypy_big_fixed_bitvector_%s" % width
    return c

@cache1
def generate_convert_from_pypy_big_fixed_bitvector(width):
    from pypy.interpreter.error import oefmt
    def c(space, w_val):
        if isinstance(w_val, bitvector.BitVector):
            if w_val.size() != width:
                raise oefmt(space.w_ValueError, "expected bitvector of size %d, got size %d", width, w_val.size())
            return w_val
        return bitvector.from_ruint(width, space.uint_w(w_val))
    c.func_name = "convert_from_pypy_big_fixed_bitvector_%s" % width
    return c

@cache2
def generate_convert_to_pypy_enum(cls, name):
    from pypy.interpreter.error import oefmt
    def c(space, val):
        try:
            res = cls.convert_value_to_name(val)
        except ValueError:
            raise oefmt(space.w_ValueError, "unknown value %d for enum %s", val, name)
        return space.newtext(res)
    c.func_name = "convert_to_pypy_enum_" + name
    return c

@cache2
def generate_convert_from_pypy_enum(cls, name):
    from pypy.interpreter.error import oefmt
    def c(space, w_val):
        try:
            return cls.convert_name_to_value(space.text_w(w_val))
        except ValueError:
            raise oefmt(space.w_ValueError, "unknown enum value %R for enum %s", w_val, name)
    c.func_name = "convert_from_pypy_enum_" + name
    return c

def convert_to_pypy_bool(space, val):
    return space.newbool(val)

def convert_from_pypy_bool(space, w_val):
    return space.is_true(w_val)

def convert_to_pypy_string(space, val):
    return space.newtext(val)

def convert_from_pypy_string(space, w_val):
    return space.text_w(w_val)

def convert_to_pypy_unit(space, val):
    return space.newtuple([])

def convert_from_pypy_unit(space, w_val):
    # just accept everything
    return ()

def convert_from_pypy_machineint(space, w_val):
    return space.int_w(w_val)

def convert_to_pypy_machineint(space, val):
    return space.newint(val)

def convert_from_pypy_int(space, w_val):
    from pypy.interpreter.error import OperationError
    try:
        return Integer.fromint(space.int_w(w_val))
    except OperationError as e:
        if not e.match(space, space.w_TypeError):
            raise
    return Integer.from_bigint(space.bigint_w(w_val))

def convert_to_pypy_int(space, val):
    if isinstance(val, bitvector.SmallInteger):
        return space.newint(val.val)
    return space.newlong_from_rbigint(val.tobigint())

def convert_from_pypy_bitvector(space, w_val):
    return space.interp_w(bitvector.BitVector, w_val)

def convert_to_pypy_bitvector(space, val):
    return val

@cache1
def generate_convert_from_pypy_vec(func):
    def convert_from_pypy_vec(space, w_val):
        list_w = space.listview(w_val)
        return [func(space, w_el) for w_el in list_w][:]
    convert_from_pypy_vec.__name__ += "_" + func.__name__
    return convert_from_pypy_vec

@cache1
def generate_convert_to_pypy_vec(func):
    def convert_to_pypy_vec(space, val):
        return space.newlist([func(space, el) for el in val])
    convert_to_pypy_vec.__name__ += "_" + func.__name__
    return convert_to_pypy_vec

@cache2
def generate_convert_from_pypy_fvec(size, func):
    from pypy.interpreter.error import oefmt
    def convert_from_pypy_fvec(space, w_val):
        list_w = space.listview(w_val)
        if len(list_w) != size:
            raise oefmt(space.w_ValueError, 'expected list of length %d, got %d', size, len(list_w))
        return [func(space, w_el) for w_el in list_w][:]
    convert_from_pypy_fvec.__name__ += "_" + func.__name__
    return convert_from_pypy_fvec

@cache2
def generate_convert_to_pypy_fvec(size, func):
    def convert_to_pypy_fvec(space, val):
        return space.newlist([func(space, el) for el in val])
    convert_to_pypy_fvec.__name__ += "_" + func.__name__
    return convert_to_pypy_fvec
