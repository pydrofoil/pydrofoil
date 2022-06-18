from rpython.rlib.rbigint import rbigint
from rpython.rlib.rarithmetic import r_uint, intmask

class SmallBitVector(object):
    def __init__(self, size, val):
        self.size = size # number of bits
        self.val = val # r_uint

class GenericBitVector(object):
    def __init__(self, size, rval):
        self.size = size
        self.rval = rval # rbigint

    def add_int(self, i):
        return GenericBitVector(self.size, self.rval.add(i).and_(rbigint.fromint(1).lshift(self.size).int_sub(1)))

    def print_bits(self):
        print "GenericBitVector<%s, %s>" % (self.size, self.rval.hex())
