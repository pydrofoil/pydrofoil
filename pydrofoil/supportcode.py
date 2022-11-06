from rpython.rlib import objectmodel
from rpython.rlib.rbigint import rbigint
from rpython.rlib.rarithmetic import r_uint, intmask
from pydrofoil import bitvector
from pydrofoil.bitvector import Integer

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

def zero_extend(machine, a, b):
    return a

def add_bits_int(machine, a, b):
    return a.add_int(b)

def sub_bits_int(machine, a, b):
    return a.sub_int(b)

def length(machine, gbv):
    return Integer.fromint(gbv.size)

def fast_signed(machine, op, n):
    if n == 64:
        return intmask(op)
    assert n > 0
    u1 = r_uint(1)
    m = u1 << (n - 1)
    op = op & ((u1 << n) - 1) # mask off higher bits to be sure
    return intmask((op ^ m) - m)

def sign_extend(machine, gbv, lint):
    size = lint.toint()
    return gbv.sign_extend(size)

def raise_type_error():
    raise TypeError

def eq_int(machine, a, b):
    assert isinstance(a, Integer)
    return a.eq(b)

def eq_bit(machine, a, b):
    return a == b

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

def safe_rshift(machine, n, shift):
    assert shift >= 0
    if shift >= 64:
        return r_uint(0)
    return n >> shift

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

def sub_int(machine, ia, ib):
    return ia.sub(ib)

def mult_int(machine, ia, ib):
    return ia.mul(ib)

def tdiv_int(machine, ia, ib):
    return ia.tdiv(ib)

def tmod_int(machine, ia, ib):
    return ia.tmod(ib)

def emod_int(machine, ia, ib):
    a = ia.toint()
    b = ib.toint()
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

def print_endline(machine, s):
    print s
    return ()

def print_bits(machine, s, b):
    print s + b.string_of_bits()
    return ()

def print_int(machine, s, i):
    print s + i.str()
    return ()

@objectmodel.specialize.argtype(1)
def reg_deref(machine, s):
    return s

def not_(machine, b):
    return not b

def sail_assert(machine, *args):
    pass

def eq_bool(machine, a, b):
    return a == b

def shiftl(machine, gbv, i):
    return gbv.lshift(i.toint())

def shiftr(machine, gbv, i):
    return gbv.rshift(i.toint())

def shift_bits_left(machine, gbv, gbva):
    return gbv.lshift_bits(gbva)

def shift_bits_right(machine, gbv, gbva):
    return gbv.rshift_bits(gbva)

def sail_unsigned(machine, gbv):
    return gbv.unsigned()

def sail_signed(machine, gbv):
    return gbv.signed()

def append_64(machine, bv, v):
    return bv.append_64(v)

# vector stuff

@objectmodel.specialize.argtype(1, 2, 4)
def vector_update_inplace(machine, res, l, index, element):
    # super weird, the C backend does the same
    if res is not l:
        l = l[:]
    l[index] = element
    return l

def vector_update(machine, bv, index, element):
    return bv.update_bit(index.toint(), element)

def vector_access(machine, bv, index):
    return bv.read_bit(index.toint())

def update_fbits(fb, index, element):
    assert 0 <= index < 64
    if element:
        return fb | (r_uint(1) << index)
    else:
        return fb & ~(r_uint(1) << index)

def vector_update_subrange(machine, bv, n, m, s):
    return bv.update_subrange(n.toint(), m.toint(), s)

def vector_subrange(machine, bv, n, m):
    return bv.subrange(n.toint(), m.toint())


def elf_tohost(machine, _):
    return Integer.fromint(0)

def get_slice_int(machine, len, n, start):
    return n.slice(len.toint(), start.toint())

def platform_barrier(machine, _):
    return ()

def platform_write_mem_ea(machine, write_kind, addr_size, addr, n):
    return ()


# strings

def concat_str(machine, a, b):
    return a + b


def string_of_bits(machine, gbv):
    return gbv.string_of_bits()

def decimal_string_of_bits(machine, sbits):
    return str(sbits)
    
def string_of_int(machine, r):
    return r.str()


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
    def __init__(self):
        self.have_exception = False
        self.throw_location = None
        self.current_exception = None
