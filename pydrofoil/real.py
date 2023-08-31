import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong

MAXINT = 2**63-1
MININT = -2**63
NULLRBIGINT = rbigint.fromint(0)
ONERBIGINT = rbigint.fromint(1)
SQRTPRECISION = 30
DEN_CONVERGE = rbigint.fromint(10).int_pow(SQRTPRECISION)


class Real(object):
    def __init__(self, num, den, normalized=False):
        if normalized:
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
        return Real(num, den)

    @staticmethod
    def fromstr(str):
        from rpython.rlib.rstring import strip_spaces
        s = strip_spaces(str)
        decimalpos = s.find(".")
        num = rbigint.fromstr(s[:decimalpos]+s[decimalpos+1:], 10) if decimalpos >= 0 else rbigint.fromstr(s, 10)
        den = rbigint.fromint(10).int_pow(len(s)-1 - decimalpos) if decimalpos >= 0 else rbigint.fromint(1)
        return Real(num, den)


    def add(self, other):
        g = self.den.gcd(other.den)
        if g.int_eq(1):
            num_new_1 = self.num.mul(other.den)
            num_new_2 = other.num.mul(self.den)
            den_new = self.den.mul(other.den)
            num_new = num_new_1.add(num_new_2)
            return Real(num_new, den_new, True)
        s = self.den.div(g)
        t = self.num.mul(other.den.div(g)).add(other.num.mul(s))
        g2 = t.gcd(g)
        if g2.int_eq(1):
            return Real(t, s.mul(other.den), True)
        return Real(t.div(g2), s.mul(other.den.div(g2)), True)


    def sub(self, other):
        g = self.den.gcd(other.den)
        if g.int_eq(1):
            num_new_1 = self.num.mul(other.den)
            num_new_2 = other.num.mul(self.den)
            den_new = self.den.mul(other.den)
            num_new = num_new_1.sub(num_new_2)
            return Real(num_new, den_new, True)
        s = self.den.div(g)
        t = self.num.mul(other.den.div(g)).sub(other.num.mul(s))
        g2 = t.gcd(g)
        if g2.int_eq(1):
            return Real(t, s.mul(other.den), True)
        return Real(t.div(g2), s.mul(other.den.div(g2)), True)

    def mul(self, other):
        num1_new, den1_new = self.num, self.den
        num2_new, den2_new = other.num, other.den
        g1 = num1_new.gcd(den2_new)
        if g1.int_gt(1):
            num1_new = num1_new.div(g1)
            den2_new = den2_new.div(g1)
        g2 = num2_new.gcd(den1_new)
        if g2.int_gt(1):
            num2_new = num2_new.div(g2)
            den1_new = den1_new.div(g2)
        return Real(num1_new.mul(num2_new), den1_new.mul(den2_new), True)


    def div(self, other):
        num2_new, den2_new = other.num, other.den
        if num2_new.int_eq(0):
            raise ZeroDivisionError(den2_new.str()+"/0")
        num1_new, den1_new = self.num, self.den
        g1 = num1_new.gcd(num2_new)
        if g1.int_gt(1):
            num1_new = num1_new.div(g1)
            num2_new = num2_new.div(g1)
        g2 = den1_new.gcd(den2_new)
        if g2.int_gt(1):
            den1_new = den1_new.div(g2)
            den2_new = den2_new.div(g2)
        num_new = num1_new.mul(den2_new)
        den_new = num2_new.mul(den1_new)
        if den_new.int_lt(0):
            num_new = num_new.neg()
            den_new = den_new.neg()
        return Real(num_new, den_new, True)

    def pow(self, n):
        if n == 0:
            return Real(rbigint.fromint(1), rbigint.fromint(1))
        elif n < MININT or n > MAXINT:
            assert False, "exponent is out of range of INT"
        else:
            if n > 0:
                num_new = self.num.int_pow(n)
                den_new = self.den.int_pow(n)
            else:
                if self.num.int_eq(0):
                    raise ZeroDivisionError("0 doesn't have negative power")
                else:
                    num_new = self.den.int_pow(-n)
                    den_new = self.num.int_pow(-n)
                if den_new.int_lt(0):
                    num_new, den_new = num_new.neg(), den_new.neg()
            return Real(num_new, den_new, True)

    def neg(self):
        return Real(self.num.neg(), self.den, True)

    def abs(self):
        return Real(self.num.abs(), self.den, True)

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
        if self.num.int_lt(0):
            assert False, "sqrt(x), x cannot be negative"
        if self.num.int_eq(0):
            return Real(NULLRBIGINT, ONERBIGINT)
        current = Real(self.num.isqrt(), self.den.isqrt())
        if current.mul(current).eq(self):
            return current
        convergence = Real(ONERBIGINT, DEN_CONVERGE, True).mul(self)
        while True:
            # next = (current + self/current)/2
            next = current.add(self.div(current)).div(Real(rbigint.fromint(2), ONERBIGINT))
            epsilon = next.sub(current).abs()
            if epsilon.le(convergence):
                break
            current = next
        return next

