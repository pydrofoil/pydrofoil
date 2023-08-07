import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong

class Real(object):
    def __init__(self, num, den):
        gcd_val = num.gcd(den)
        self.num = num.div(gcd_val)
        self.den = den.div(gcd_val)

    @staticmethod
    def fromint(num, den=1):
        sign = num/abs(num)*den/abs(den)
        num = abs(num)*sign
        den = abs(den)
        num = rbigint.fromint(num)
        den = rbigint.fromint(den)
        assert not den.int_eq(0), "denominator cannot be 0"
        return Real(num, den)
    
    def add(self, other):
        num_new_1 = self.num.mul(other.den)
        num_new_2 = other.num.mul(self.den)
        den_new = self.den.mul(other.den)
        num_new = num_new_1.add(num_new_2)
        return Real(num_new, den_new)
    
    def sub(self, other):
        num_new_1 = self.num.mul(other.den)
        num_new_2 = other.num.mul(self.den)
        den_new = self.den.mul(other.den)
        num_new = num_new_1.sub(num_new_2)
        return Real(num_new, den_new)
    
    def mul(self, other):
        num_new = self.num.mul(other.num)
        den_new = self.den.mul(other.den)
        return Real(num_new, den_new)
    
    def div(self, other):
        num_new = self.num.mul(other.den)
        den_new = self.den.mul(other.num)
        return Real(num_new, den_new)
    
    def neg(self):
        return Real(self.num, self.den.neg())
    
    def abs(self):
        return Real(self.num.abs(), self.den)

    def ceil(self):
        diff = self.num.divmod(self.den)
        num_new = self.num if diff[1].int_eq(0) else self.num.add(self.den.sub(diff[1]))
        return Real(num_new, self.den)

    def floor(self):
        diff = self.num.divmod(self.den)
        num_new = self.num if diff[1].int_eq(0) else self.num.sub(diff[1])
        return Real(num_new, self.den)
    
    def eq(self, other):
        return self.num.eq(other.num) and self.den.eq(other.den)
    
    def lt(self, other):
        if (self.den.int_gt(0) and other.den.int_gt(0)) or (not self.den.int_gt(0) and not other.den.int_gt(0)):
            return self.num.mul(other.den).lt(self.den.mul(other.num))
        elif self.den.int_gt(0):
            return False
        else:
            return True
    
    def gt(self, other):
        return other.lt(self)
    
    def le(self, other):
        return not self.gt(other)
    
    def ge(self, other):
        return not self.lt(other)

    def toint(self):
        assert self.den.abs().int_eq(1)
        return self.num.mul(self.den).toint()
    
    def toreal(self):
        return self.num.toint(), self.den.toint()