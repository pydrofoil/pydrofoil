import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong

class Real(object):
    def __init__(self, num, den):
        self.num = num
        self.den = den

    @staticmethod
    def fromint(num, den=1):
        num = rbigint.fromint(num)
        den = rbigint.fromint(den)
        # assert den.int_ne(0)
        assert not den.int_eq(0), "denominator cannot be 0"
        return Real(num.div(num.gcd(den)), den.div(num.gcd(den)))
    
    def add(self, other):
        num_new_1 = self.num.mul(other.den)
        num_new_2 = other.num.mul(self.den)
        self.den = self.den.mul(other.den)
        self.num = num_new_1.add(num_new_2)
        # return Real(self.num.add(other.num), self.den)
        return Real(self.num.div(self.num.gcd(self.den)), self.den.div(self.num.gcd(self.den)))
    
    # def sub(self, other):
    #     num_new_1 = self.num.mul(other.den)
    #     num_new_2 = other.num.mul(self.den)
    #     self.den = self.den.mul(other.den)
    #     self.num = num_new_1.sub(num_new_2)
    #     # return Real(self.num.add(other.num), self.den)
    #     return Real(self.num.div(self.num.gcd(self.den)), self.den.div(self.num.gcd(self.den)))
    
    def toint(self):
        assert self.den.abs().int_eq(1)
        return self.num.mul(self.den).toint()
