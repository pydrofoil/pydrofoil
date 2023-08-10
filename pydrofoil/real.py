import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong

MAXINT = 2**63-1
MININT = -2**63

class Real(object):
    def __init__(self, num, den, Normalize = True):
        if Normalize:
            self.num = num
            self.den = den
        else:
            gcd_val = num.gcd(den)
            self.num = num.div(gcd_val)
            self.den = den.div(gcd_val)
        

    @staticmethod
    def fromint(num, den=1):
        assert not den==0, "denominator cannot be 0"
        if num == MININT or den == MININT:
            num = rbigint.fromint(num)
            den = rbigint.fromint(den)
            sign = num.sign * den.sign
            num = num.abs().int_mul(sign)
            den = den.abs()
        elif num < MININT or num > MAXINT or den < MININT or den > MAXINT:
            assert False, "input is out of range of INT"
        else:
            sign = num/abs(num)*den/abs(den)
            num = rbigint.fromint(abs(num)*sign)
            den = rbigint.fromint(abs(den))
        return Real(num, den, False)
    
    @staticmethod
    def fromstr(str):
        from rpython.rlib.rstring import strip_spaces
        s = strip_spaces(str)
        decimalpos = s.find(".")
        num = rbigint.fromstr(s[:decimalpos]+s[decimalpos+1:], 10) if decimalpos != -1 else rbigint.fromstr(s, 10)
        den = rbigint.fromint(10).int_pow(len(s)-1 - decimalpos) if decimalpos != -1 else rbigint.fromint(1)
        return Real(num, den, False)


    def add(self, other):
        g = self.den.gcd(other.den)
        if g.int_eq(1):
            num_new_1 = self.num.mul(other.den)
            num_new_2 = other.num.mul(self.den)
            den_new = self.den.mul(other.den)
            num_new = num_new_1.add(num_new_2)
            return Real(num_new, den_new)
        s = self.den.div(g)
        t = self.num.mul(other.den.div(g)).add(other.num.mul(s))
        g2 = t.gcd(g)
        if g2.int_eq(1):
            return Real(t, s.mul(other.den))
        return Real(t.div(g2), s.mul(other.den.div(g2)))

    
    def sub(self, other):
        g = self.den.gcd(other.den)
        if g.int_eq(1):
            num_new_1 = self.num.mul(other.den)
            num_new_2 = other.num.mul(self.den)
            den_new = self.den.mul(other.den)
            num_new = num_new_1.sub(num_new_2)
            return Real(num_new, den_new)
        s = self.den.div(g)
        t = self.num.mul(other.den.div(g)).sub(other.num.mul(s))
        g2 = t.gcd(g)
        if g2.int_eq(1):
            return Real(t, s.mul(other.den))
        return Real(t.div(g2), s.mul(other.den.div(g2)))
    
    def mul(self, other):
        g1 = self.num.gcd(other.den)
        g2 = other.num.gcd(self.den)
        if (g1.int_eq(1) and g2.int_eq(1)):
            return Real(self.num.mul(other.num), self.den.mul(other.den))
        num1_new = self.num.div(g1) if g1.int_gt(1) else self.num
        den2_new = other.den.div(g1) if g1.int_gt(1) else other.den
        num2_new = other.num.div(g2) if g2.int_gt(1) else other.num
        den1_new = self.den.div(g2) if g2.int_gt(1) else self.den
        return Real(num1_new.mul(num2_new), den1_new.mul(den2_new))
        
    
    def div(self, other):
        if other.num.int_eq(0):
            assert False, "ZerodivideError: denominator cannot be 0"
        else:
            g1 = self.num.gcd(other.num)
            g2 = self.den.gcd(other.den)
            if g1.int_eq(1) and g2.int_eq(1):
                num_new = self.num.mul(other.den)
                den_new = self.den.mul(other.num)
            else:
                num1_new = self.num.div(g1) if g1.int_gt(1) else self.num
                num2_new = other.num.div(g1) if g1.int_gt(1) else other.num
                den1_new = self.den.div(g2) if g2.int_gt(1) else self.den
                den2_new = other.den.div(g2) if g2.int_gt(1) else other.den
                num_new, den_new = num1_new.mul(den2_new), num2_new.mul(den1_new)
        if den_new.int_lt(0):
            num_new = num_new.neg()
            den_new = den_new.neg()
        return Real(num_new, den_new)

    def pow(self, n):
        if n == 0:
            return Real(rbigint.fromint(1), rbigint.fromint(1))
        elif n < MININT or n > MAXINT:
            assert False, "exponent is out of range of INT"
        else:
            num_new = self.num.int_pow(n)
            den_new = self.den.int_pow(n)
            return Real(num_new, den_new, True)       
    
    def neg(self):
        return Real(self.num.neg(), self.den)
    
    def abs(self):
        return Real(self.num.abs(), self.den)

    def ceil(self):
        return self.num if self.den.int_eq(1) else self.num.floordiv(self.den).int_add(1)
    
    def floor(self):
        return self.num if self.den.int_eq(1) else self.num.floordiv(self.den)

    def eq(self, other):
        return self.num.eq(other.num) and self.den.eq(other.den)
    
    def lt(self, other):
        return self.num.mul(other.den).lt(self.den.mul(other.num))
    
    def gt(self, other):
        return other.lt(self)
    
    def le(self, other):
        return not self.gt(other)
    
    def ge(self, other):
        return not self.lt(other)

    def toint(self):
        assert self.den.abs().int_eq(1)
        return self.num.mul(self.den).toint()
    
    def totuple(self):
        return self.num.toint(), self.den.toint()
    
    def sqrt(self):
        return Real(self.num, self.den)
