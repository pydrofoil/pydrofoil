import sys
from rpython.rlib.rbigint import rbigint, _divrem as bigint_divrem
from rpython.rlib.rarithmetic import r_uint, intmask, string_to_int, ovfcheck, \
        int_c_div, int_c_mod, r_ulonglong

MAXINT = 2**63-1
MININT = -2**63

class Real(object):
    def __init__(self, num, den):
        gcd_val = num.gcd(den)
        self.num = num.div(gcd_val)
        self.den = den.div(gcd_val)

    @staticmethod
    def fromint(num, den=1):
        assert not den==0, "denominator cannot be 0"
        # if ((num <= -2**63 or num >= 2**63) and den > 0) or (den >= 2**63):
        #     num = rbigint.fromlong(num)
        #     den = rbigint.fromlong(den)
        # elif ((num <= -2**63 or num >= 2**63) and den <0) or (den <= -2**63):
        #     num = rbigint.fromlong(-num)
        #     den = rbigint.fromlong(-den)
        # else:
        # if ((num == MININT or num == MAXINT) and (den > 0 and den <= MAXINT)) or ((den == MAXINT) and ((num > 0 and num <= MAXINT) or (num < 0 and num >= MININT))):
        #     num = rbigint.fromint(num)
        #     den = rbigint.fromint(den)
        # elif ((num == MININT or num == MAXINT) and (den < 0 and den >= MININT)) or ((den == MININT) and ((num > 0 and num <= MAXINT) or (num < 0 and num >= MININT))):
        #     if (num == MININT and den == MININT):
        #         num = rbigint.fromint(1)
        #         den = rbigint.fromint(1)
        #     elif num == MININT:
        #         num = rbigint.fromint(MAXINT).add(rbigint.fromint(1))
        #         den = rbigint.fromint(-den)
        #     elif den == MININT:
        #         num = rbigint.fromint(-num)
        #         den = rbigint.fromint(MAXINT).add(rbigint.fromint(1))
        #     else:                
        #         num = rbigint.fromint(-num)
        #         den = rbigint.fromint(-den)
        # elif ((num > MININT and num < MAXINT) and (den > MININT and den < MAXINT)):
        #     sign = num/abs(num)*den/abs(den)
        #     num = rbigint.fromint(abs(num)*sign)
        #     den = rbigint.fromint(abs(den))
        # else:
        #     assert False, "input is out of range of INT"
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
        # assert not den.int_eq(0), "denominator cannot be 0"
        return Real(num, den)
    
    # @staticmethod
    # def fromstr(str):
    #     from rpython.rlib.rstring import strip_spaces
    #     s = strip_spaces(str)
    #     j = -1
    #     lead_zero_count = 0
    #     ZERO_COUNT_END = False
    #     for i in range(0, len(s)):
    #         if s[i].isdigit() and s[i] != "0":
    #             ZERO_COUNT_END = True
    #         if (not ZERO_COUNT_END) and s[i] == "0":
    #             lead_zero_count += 1 
    #         if not s[i].isdigit() and s[i] != "+" and s[i] != "-":
    #             if i == 1 or (i == 2 and (s[0] == "+" or s[0] == "-")):
    #                 for j in range(len(s)-1, i, -1):
    #                     if (s[j] == "+" or s[j] == "-") and s[j-1] == "e":
    #                         break
    #             for k in range(i+1, len(s)):
    #                 if (not ZERO_COUNT_END) and s[k] == "0":
    #                     lead_zero_count += 1
    #                 else:
    #                     break
    #             break
    #     # return i, s[:i]+s[i+1:]
    #     if j == -1 or (j == 2 and (s[0] != "+" and s[0] != "-")) or (j == 3 and (s[0] == "+" or s[0] == "-")):
    #         if lead_zero_count == len(s)-1:
    #             return Real(rbigint.fromint(0), rbigint.fromint(1))
    #         num = rbigint.fromstr((s[:i] + s[i+1:])[lead_zero_count:] if (s[0] != "+" and s[0] != "-") else s[0]+(s[1:i] + s[i+1:])[lead_zero_count:]) if i < len(s)-1 else rbigint.fromstr(s)
    #         dif = len(s)-1-i
    #         if dif < 19:
    #             den = rbigint.fromint(10**dif)
    #         else:
    #             den = den_of_fromstr(dif)
    #         return Real(num, den)
    #     else:
    #         if s[j] == "+":
    #             shift = int(s[j+1:])
    #             if shift >= j-i-2:
    #                 num = rbigint.fromstr(s[:i]+s[i+1:j-1]+"0"*(shift-(j-i-2)))
    #                 den = rbigint.fromint(1)
    #                 return Real(num, den)
    #             else:
    #                 return Real.fromstr(s[:i]+s[i+1:i+1+shift]+s[i]+s[i+1+shift:j-1])
    #             # 1.222e+5
    #             # 1.222222e+3
    #         elif s[j] == "-":
    #             shift = int(s[j+1:])
    #             num = rbigint.fromstr(s[:i]+s[i+1:j-1])
    #             dif = j-i-2+shift
    #             if dif < 19:
    #                 den = rbigint.fromint(10**dif)
    #             else:
    #                 den = den_of_fromstr(dif)
    #             return Real(num, den)

    # string to real without considering about input as x.xxxxe+xxx or x.xxxxe-xxxx
    # @staticmethod
    # def fromstr(str):
    #     from rpython.rlib.rstring import strip_spaces
    #     s = strip_spaces(str)
    #     lead_zero_count = 0
    #     ZERO_COUNT_END = False
    #     for i in range(0, len(s)):
    #         if s[i].isdigit() and s[i] != "0":
    #             ZERO_COUNT_END = True
    #         if (not ZERO_COUNT_END) and s[i] == "0":
    #             lead_zero_count += 1 
    #         if not s[i].isdigit() and s[i] != "+" and s[i] != "-":
    #             for j in range(i+1, len(s)):
    #                 if (not ZERO_COUNT_END) and s[j] == "0":
    #                     lead_zero_count += 1
    #                 else:
    #                     break
    #             break
    #     # return i, s[:i]+s[i+1:]
    #     if lead_zero_count == len(s)-1:
    #         return Real(rbigint.fromint(0), rbigint.fromint(1))
    #     num = rbigint.fromstr((s[:i] + s[i+1:])[lead_zero_count:] if (s[0] != "+" and s[0] != "-") else s[0]+(s[1:i] + s[i+1:])[lead_zero_count:]) if i < len(s)-1 else rbigint.fromstr(s)
    #     dif = len(s)-1-i
    #     if dif < 19:
    #         den = rbigint.fromint(10**dif)
    #     else:
    #         den = den_of_fromstr(dif)
    #     return Real(num, den)
    #     # num = ((s[:i] + s[i+1:])[lead_zero_count:] if (s[0] != "+" and s[0] != "-") else s[0]+(s[1:i] + s[i+1:])[lead_zero_count:]) if i < len(s)-1 else (s)
    #     # dif = len(s)-1-i
    #     # if dif < 19:
    #     #     den = rbigint.fromint(10**dif)
    #     # else:
    #     #     den = den_of_fromstr(dif)
    #     # # return Real(num, den)
    #     # return lead_zero_count, num, den.str()

    # Simplest implementation of fromstr with input format only as xxx.xxxx, leading zero issue resolved by setting base = 10 for rbigint.fromstr()
    @staticmethod
    def fromstr(str):
        from rpython.rlib.rstring import strip_spaces
        s = strip_spaces(str)
        decimalpos = s.find(".")
        num = rbigint.fromstr(s[:decimalpos]+s[decimalpos+1:], 10) if decimalpos < len(s)-1 else rbigint.fromstr(s, 10)
        den = rbigint.fromint(10).int_pow(len(s)-1 - decimalpos)
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
        if self.num.int_eq(0) and not other.num.int_eq(0):
            num_new = rbigint.fromint(0)
            den_new = rbigint.fromint(1)
        elif other.num.int_eq(0):
            assert False, "ZerodivideError: denominator cannot be 0"
        else:
            num_new = self.num.mul(other.den)
            den_new = self.den.mul(other.num)
        if den_new.int_lt(0):
            num_new = num_new.neg()
            den_new = den_new.neg()
        return Real(num_new, den_new)

    # def pow(self, n):
    #     if isinstance(n, int):
    #         if n == 0:
    #             return Real(rbigint.fromint(1), rbigint.fromint(1))
    #         elif n < MININT or n > MAXINT:
    #             assert False, "exponent is out of range of INT"
    #         else:
    #             n = rbigint.fromint(n)
    #             num_new = self.num.pow(n)
    #             den_new = self.den.pow(n)
    #             return Real(num_new, den_new)
    #     elif isinstance(n, rbigint):
    #         if n.int_eq(0):
    #             return Real(rbigint.fromint(1), rbigint.fromint(1))
    #         else:
    #             n = rbigint.fromint(n)
    #             num_new = self.num.pow(n)
    #             den_new = self.den.pow(n)
    #             return Real(num_new, den_new)
    #     elif isinstance(n, Real):
    #         if n.num.int_eq(0):
    #             return Real(rbigint.fromint(1), rbigint.fromint(1))
    #         else:
    #             if n.den.int_eq(1):
    #                 num_new = self.num.pow(n.num)
    #                 den_new = self.den.pow(n.num)
    #                 return Real(num_new, den_new)
    #             else:
    #                 assert False, "exponent cannot be fraction"
    #     else:
    #         raise TypeError("exponent doesn't support this type")
    def pow(self, n):
        if n == 0:
            return Real(rbigint.fromint(1), rbigint.fromint(1))
        elif n < MININT or n > MAXINT:
            assert False, "exponent is out of range of INT"
        else:
            n = rbigint.fromint(n)
            num_new = self.num.pow(n)
            den_new = self.den.pow(n)
            return Real(num_new, den_new)
        
        
            
    
    def neg(self):
        return Real(self.num.neg(), self.den)
    
    def abs(self):
        return Real(self.num.abs(), self.den)

    # def ceil(self):
    #     diff = self.num.divmod(self.den)
    #     num_new = self.num if diff[1].int_eq(0) else self.num.add(self.den.sub(diff[1]))
    #     return Real(num_new, self.den)

    # def floor(self):
    #     diff = self.num.divmod(self.den)
    #     num_new = self.num if diff[1].int_eq(0) else self.num.sub(diff[1])
    #     return Real(num_new, self.den)
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
    

# Helper function for fromstr()
def den_of_fromstr(dif):
    if dif < 19:
        quo = dif // 2
        rem = dif % 2
        return rbigint.fromint(10**(2*quo)*10**(rem))
    else:
        return rbigint.fromint(10**18).mul(den_of_fromstr(dif-18))
