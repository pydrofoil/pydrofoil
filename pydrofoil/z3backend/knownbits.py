# many methods copied/adapted from https://pypy.org/posts/2024/08/toy-knownbits.html

class KnownBits(object):

    def __init__(self, ones=0, unknowns=-1):
        self.ones = ones # one if we know its a one, else 0
        self.unknowns = unknowns # 1 if we dont know the digit
        # if a digit is neither in ones nor unknowns its zero
        self._check_well_formed()
    
    @classmethod
    def from_constant(self, constant):
        """ create KnownBits instance from constant, where everything is known """
        return KnownBits(constant, 0)
    
    def _check_well_formed(self):
        """ Checks if any digit is both unkown and known one """
        assert self.ones & self.unknowns == 0, "illegal KnownBits instance"

    def contains(self, value):
        """ check if concrete value fits into this KnownBits instance """
        # value & self.knowns only leaves the one bits set; thus must match with self.ones
        return value & self.knowns() == self.ones
    
    def is_constant(self):
        """ check if nothing is unknown """
        return self.unknowns == 0 # if nothing is unkown, we have a constant
    
    def knowns(self):
        """ known digit where a bit is set """
        return ~self.unknowns # we know everything that is not unkown

    def zeros(self):
        """ known zero where a bit is set """
        return self.knowns() & ~self.ones
    
    def __repr__(self):
        return self.__str__()

    def __str__(self):
        res = []
        ones, unknowns = self.ones, self.unknowns
        # construct the string representation right to left
        while 1:
            if not ones and not unknowns:
                break # we leave off the leading known 0s
            if ones == -1 and not unknowns:
                # -1 has all bits set in two's complement, so the leading
                # bits are all 1
                res.append('1')
                res.append("...")
                break
            if unknowns == -1:
                # -1 has all bits set in two's complement, so the leading bits
                # are all ?
                assert not ones
                res.append("?")
                res.append("...")
                break
            if unknowns & 1:
                res.append('?')
            elif ones & 1:
                res.append('1')
            else:
                res.append('0')
            ones >>= 1
            unknowns >>= 1
        if not res:
            res.append('0')
        res.reverse()
        return "".join(res)

## methods needed for z3backend ##
    
    def know_same(self, other):
        return (self.ones == other.ones) & (self.unknowns == other.unknowns)
    
    def copy(self):
        return KnownBits(self.ones, self.unknowns)
        
##      transfer functions      ##

# TODO;