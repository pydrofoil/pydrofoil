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
        sign = num/abs(num)*den/abs(den)
        num = rbigint.fromint(abs(num))
        den = rbigint.fromint(abs(den)*sign)
        # assert den.int_ne(0)
        assert not den.int_eq(0), "denominator cannot be 0"
        return Real(num.div(num.gcd(den)), den.div(num.gcd(den)))
    
    def add(self, other):
        num_new_1 = self.num.mul(other.den)
        num_new_2 = other.num.mul(self.den)
        self.den = self.den.mul(other.den)
        self.num = num_new_1.add(num_new_2)
        sign = self.num.div(self.num.abs()).mul(self.den.div(self.den.abs()))
        self.num = self.num.abs()
        self.den = self.den.abs().mul(sign)
        # return Real(self.num.add(other.num), self.den)
        return Real(self.num.div(self.num.gcd(self.den)), self.den.div(self.num.gcd(self.den)))
    
    def sub(self, other):
        num_new_1 = self.num.mul(other.den)
        num_new_2 = other.num.mul(self.den)
        self.den = self.den.mul(other.den)
        self.num = num_new_1.sub(num_new_2)
        sign = self.num.div(self.num.abs()).mul(self.den.div(self.den.abs()))
        self.num = self.num.abs()
        self.den = self.den.abs().mul(sign)
        # return Real(self.num.add(other.num), self.den)
        return Real(self.num.div(self.num.gcd(self.den)), self.den.div(self.num.gcd(self.den)))
    
    def mul(self, other):
        self.num = self.num.mul(other.num)
        self.den = self.den.mul(other.den)
        sign = self.num.div(self.num.abs()).mul(self.den.div(self.den.abs()))
        self.num = self.num.abs()
        self.den = self.den.abs().mul(sign)
        return Real(self.num.div(self.num.gcd(self.den)), self.den.div(self.num.gcd(self.den)))
    
    def div(self, other):
        self.num = self.num.mul(other.den)
        self.den = self.den.mul(other.num)
        sign = self.num.div(self.num.abs()).mul(self.den.div(self.den.abs()))
        self.num = self.num.abs()
        self.den = self.den.abs().mul(sign)
        return Real(self.num.div(self.num.gcd(self.den)), self.den.div(self.num.gcd(self.den)))
    
    def neg(self):
        return Real(self.num, self.den.neg())
    
    def abs(self):
        return Real(self.num, self.den.abs())

    def ceil(self):
        diff = self.num.divmod(self.den)
        self.num = self.num if diff[1].int_eq(0) else self.num.add(self.den.sub(diff[1]))
        return Real(self.num.div(self.num.gcd(self.den)), self.den.div(self.num.gcd(self.den)))

    def floor(self):
        diff = self.num.divmod(self.den)
        self.num = self.num if diff[1].int_eq(0) else self.num.sub(diff[1])
        return Real(self.num.div(self.num.gcd(self.den)), self.den.div(self.num.gcd(self.den)))
    
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
