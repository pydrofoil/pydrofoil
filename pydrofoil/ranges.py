import sys
from typing import Iterable

from pydrofoil import ir, makecode, types
from pydrofoil.bitvector import Integer

MININT = -sys.maxint - 1
MAXINT = sys.maxint

MAX_CONSIDERED_NUMBER_OF_BITS = 128

_RANGE_SET_MAX = 16


def int_c_div(x, y):
    r = x // y
    if x ^ y < 0 and x % y != 0:
        r += 1
    return r


class Range(object):
    def __new__(cls, low=None, high=None):
        # type: (type, int | None, int | None) -> Range
        if high is not None and low is not None:
            number_of_elements = high - low + 1
            if number_of_elements <= _RANGE_SET_MAX:
                return RangeSet(values=set(range(low, high + 1)))
        return object.__new__(cls)

    def __init__(self, low=None, high=None):
        # both can be None
        self.low = low  # type: int | None
        self.high = high  # type: int | None
        if low is not None and high is not None:
            assert low <= high

    @staticmethod
    def fromconst(value):
        return Range(value, value)

    @staticmethod
    def fromset(values):
        # type: (set[int]) -> Range
        if len(values) <= _RANGE_SET_MAX:
            return RangeSet(values)
        return Range(min(values), max(values))

    def is_bounded(self):
        return self.low is not None and self.high is not None

    def __repr__(self):
        return "Range(%r, %r)" % (self.low, self.high)

    def __eq__(self, other):
        return self.low == other.low and self.high == other.high

    def __ne__(self, other):
        return not self == other

    def contains(self, number):
        if self.low is not None and not self.low <= number:
            return False
        if self.high is not None and not number <= self.high:
            return False
        return True

    def contains_range(self, other):
        # type: (Range) -> bool
        if self.low is not None:
            if other.low is None:
                return False
            if other.low < self.low:
                return False
        if self.high is not None:
            if other.high is None:
                return False
            if other.high > self.high:
                return False
        return True

    def isconstant(self):
        return self.low is not None and self.low == self.high

    def fits_machineint(self):
        return self.is_bounded() and self.low >= MININT and self.high <= MAXINT

    def add(self, other):
        low = high = None
        if self.low is not None and other.low is not None:
            low = self.low + other.low
        if self.high is not None and other.high is not None:
            high = self.high + other.high
        return Range(low, high)

    def neg(self):
        low = high = None
        if self.low is not None:
            high = -self.low
        if self.high is not None:
            low = -self.high
        return Range(low, high)

    def abs(self):
        if self.low is None:
            if self.high is None:
                # ------ 0 -------
                return Range(0, None)
            if self.high < 0:
                # ---]   0
                return Range(-self.high, None)
            else:
                # ------ 0 --]
                return Range(0, None)
        elif self.high is None:
            if self.low < 0:
                #    [-- 0 -------
                return Range(0, None)
            else:
                #        0   [----
                return self
        else:
            if self.high < 0:
                # [---]  0
                return Range(-self.high, -self.low)
            if self.low >= 0:
                #        0   [----]
                # ------ 0 -------
                return self
            #       [--- 0 ------]
            return Range(0, max(-self.low, self.high))

    def sub(self, other):
        return self.add(other.neg())

    def mul(self, other):
        if self.is_bounded() and other.is_bounded():
            values = [
                self.low * other.low,
                self.high * other.low,
                self.low * other.high,
                self.high * other.high,
            ]
            return Range(min(values), max(values))
        if self.low is not None and other.low is not None:
            if self.low >= 0 and other.low >= 0:
                return Range(self.low * other.low, None)
        if self.high is not None and other.high is not None:
            if self.high < 0 and other.high < 0:
                return Range(self.high * other.high, None)
        return UNBOUNDED

    def tdiv(self, other):
        # very minimal for now
        if other.low is not None and other.low >= 1:
            if other.high is not None and self.is_bounded():
                values = [
                    int_c_div(self.low, other.low),
                    int_c_div(self.high, other.low),
                    int_c_div(self.low, other.high),
                    int_c_div(self.high, other.high),
                ]
                return Range(min(values), max(values))
            # division by positive number cannot change the sign
            if self.low is not None and self.low >= 0:
                return Range(0, self.high)
            if self.high is not None and self.high <= 0:
                return Range(self.low, 0)
        return UNBOUNDED

    def ediv(self, other):
        # very minimal for now
        if other.low is not None and other.low >= 1:
            # division by positive number cannot change the sign
            if self.low is not None and self.low >= 0:
                return Range(0, self.high)
        return UNBOUNDED

    def emod(self, other):
        # type: (Range) -> Range
        other = other.abs()
        if other.high is not None and other.high <= 0:
            return Range(None, None)
        high = (other.high - 1) if other.high is not None else None
        low = 0
        return Range(low, high)

    def lshift(self, other):
        # we check for an upper bound of 64 to not compute impossibly huge numbers
        if (
            self.is_bounded()
            and other.is_bounded()
            and 0 <= other.low
            and other.high <= 64
        ):
            values = [
                self.low << other.low,
                self.high << other.low,
                self.low << other.high,
                self.high << other.high,
            ]
            return Range(min(values), max(values))
        if self.low is not None and self.low >= 0 and other.low is not None:
            if 0 <= other.low <= 64:
                return Range(self.low << other.low, None)
            return Range(self.low, None)
        return UNBOUNDED

    def rshift(self, other):
        if (
            self.is_bounded()
            and other.is_bounded()
            and 0 <= other.low
            and other.high <= MAXINT
        ):
            values = [
                self.low >> other.low,
                self.high >> other.low,
                self.low >> other.high,
                self.high >> other.high,
            ]
            return Range(min(values), max(values))
        return UNBOUNDED

    def max(self, other):
        if self.low is None:
            low = other.low
        elif other.low is None:
            low = self.low
        else:
            low = max(self.low, other.low)
        if self.high is None or other.high is None:
            high = None
        else:
            high = max(self.high, other.high)
        return Range(low, high)

    def min(self, other):
        if self.low is None or other.low is None:
            low = None
        else:
            low = min(self.low, other.low)
        if self.high is None:
            high = other.high
        elif other.high is None:
            high = self.high
        else:
            high = min(self.high, other.high)
        return Range(low, high)

    def union(self, other):
        # type: (Range) -> Range
        low = high = None
        if self.low is not None and other.low is not None:
            low = min(self.low, other.low)
        if self.high is not None and other.high is not None:
            high = max(self.high, other.high)
        return Range(low, high)

    @staticmethod
    def union_many(ranges):
        # type: (Iterable[Range]) -> Range
        ranges_iter = iter(ranges)
        try:
            res = next(ranges_iter)
        except StopIteration:
            raise ValueError("No ranges given")
        for range in ranges_iter:
            res = res.union(range)
        return res

    def intersect(self, other):
        # type: (Range) -> Range | None
        if isinstance(other, RangeSet):
            return other.intersect(self)
        low = high = None
        if self.low is not None and other.low is not None:
            low = max(self.low, other.low)
        elif self.low is None:
            low = other.low
        elif other.low is None:
            low = self.low

        if self.high is not None and other.high is not None:
            high = min(self.high, other.high)
        elif self.high is None:
            high = other.high
        elif other.high is None:
            high = self.high

        if low is not None and high is not None and low > high:
            return None

        return Range(low, high)

    def eq(self, other):
        # type: (Range) -> Range
        intersection = self.intersect(other)
        if intersection is None:
            return FALSE
        if self.isconstant() and other.isconstant():
            assert self.low == other.low
            return TRUE
        return BOOL

    def le(self, other):
        if self.high is not None and other.low is not None:
            if self.high <= other.low:
                return TRUE
        if self.low is not None and other.high is not None:
            if other.high < self.low:
                return FALSE
        return BOOL

    def lt(self, other):
        if self.high is not None and other.low is not None:
            if self.high < other.low:
                return TRUE
        if self.low is not None and other.high is not None:
            if other.high <= self.low:
                return FALSE
        return BOOL

    def ge(self, other):
        if self.low is not None and other.high is not None:
            if self.low >= other.high:
                return TRUE
        if self.high is not None and other.low is not None:
            if other.low > self.high:
                return FALSE
        return BOOL

    def gt(self, other):
        if self.low is not None and other.high is not None:
            if self.low > other.high:
                return TRUE
        if self.high is not None and other.low is not None:
            if other.low >= self.high:
                return FALSE
        return BOOL

    def make_le(self, other):
        if other.high is not None:
            return self.make_le_const(other.high)
        return self

    def make_le_const(self, const):
        if self.high is None or const < self.high:
            return Range(self.low, const)
        return self

    def make_lt(self, other):
        if other.high is not None:
            return self.make_lt_const(other.high)
        return self

    def make_lt_const(self, const):
        return self.make_le_const(const - 1)

    def make_ge(self, other):
        if other.low is not None:
            return self.make_ge_const(other.low)
        return self

    def make_ge_const(self, const):
        if self.low is None or const > self.low:
            return Range(const, self.high)
        return self

    def make_gt(self, other):
        if other.low is not None:
            return self.make_gt_const(other.low)
        return self

    def make_gt_const(self, const):
        return self.make_ge_const(const + 1)

    @classmethod
    def for_int_with_bits(cls, number_of_bits, is_signed):
        # type: (int, bool) -> Range
        assert number_of_bits > 0
        if is_signed:
            # For high numbers of bits, calculating the power of 2 is too
            # costly, so we just use None
            if number_of_bits > MAX_CONSIDERED_NUMBER_OF_BITS:
                low, high = None, None
            else:
                power = 2 ** (number_of_bits - 1)
                low = -power
                high = power - 1
        else:
            low = 0
            if number_of_bits > MAX_CONSIDERED_NUMBER_OF_BITS:
                high = None
            else:
                high = 2 ** (number_of_bits) - 1
        return cls(low, high)


class RangeSet(Range):
    def __new__(cls, values):  # Override to use default implementation
        # type: (set[int]) -> RangeSet
        return object.__new__(cls)

    def __init__(self, values, high=None):
        # type: (set[int] | int, int | None) -> None
        if not isinstance(values, set):
            assert high is not None
            assert high == max(self._values)
            assert values == min(self._values)
            return
        else:
            self._values = values
            Range.__init__(self, min(values), max(values))

    def __repr__(self):
        return "Range.fromset(%r)" % self._values

    def __eq__(self, other):
        if not isinstance(other, RangeSet):
            return False
        return self._values == other._values

    def is_dense(self):
        """ returns True if there are no holes in the range """
        # type: () -> bool
        as_range = set(range(self.low, self.high + 1))
        return self._values == as_range

    def contains(self, number):
        # type: (int) -> bool
        return number in self._values

    def add(self, other):
        # type: (Range) -> Range
        if not isinstance(other, RangeSet):
            return super(RangeSet, self).add(other)
        values = {x + y for x in self._values for y in other._values}
        return Range.fromset(values)

    def neg(self):
        # type: () -> Range
        return Range.fromset({-x for x in self._values})

    def abs(self):
        # type: () -> Range
        return Range.fromset({abs(x) for x in self._values})

    def sub(self, other):
        # type: (Range) -> Range
        if not isinstance(other, RangeSet):
            return super(RangeSet, self).sub(other)
        values = {x - y for x in self._values for y in other._values}
        return Range.fromset(values)

    def mul(self, other):
        # type: (Range) -> Range
        if not isinstance(other, RangeSet):
            return super(RangeSet, self).mul(other)
        values = {x * y for x in self._values for y in other._values}
        return Range.fromset(values)

    def tdiv(self, other):
        # type: (Range) -> Range
        if not isinstance(other, RangeSet) or 0 in other._values:
            return super(RangeSet, self).tdiv(other)
        values = {int_c_div(x, y) for x in self._values for y in other._values}
        return Range.fromset(values)

    def ediv(self, other):
        # type: (Range) -> Range
        if not isinstance(other, RangeSet) or 0 in other._values:
            return super(RangeSet, self).ediv(other)
        values = {
            Integer.fromlong(x).ediv(Integer.fromlong(y)).tolong()
            for x in self._values
            for y in other._values
        }
        return Range.fromset(values)

    def emod(self, other):
        # type: (Range) -> Range
        if not isinstance(other, RangeSet) or 0 in other._values:
            return super(RangeSet, self).emod(other)
        values = {
            Integer.fromlong(x).emod(Integer.fromlong(y)).tolong()
            for x in self._values
            for y in other._values
        }
        return Range.fromset(values)

    def lshift(self, other):
        # type: (Range) -> Range
        if (
            isinstance(other, RangeSet)
            and other.low is not None
            and other.high is not None
            and 0 <= other.low
            and other.high <= 64
        ):
            return Range.fromset(
                {x << y for x in self._values for y in other._values}
            )
        return super(RangeSet, self).lshift(other)

    def rshift(self, other):
        # type: (Range) -> Range
        if (
            isinstance(other, RangeSet)
            and other.low is not None
            and 0 <= other.low
            and other.high is not None
            and other.high <= MAXINT
        ):
            return Range.fromset(
                {x >> y for x in self._values for y in other._values}
            )
        return super(RangeSet, self).rshift(other)

    def max(self, other):
        # type: (Range) -> Range
        if isinstance(other, RangeSet):
            return Range.fromset(
                {max(x, y) for x in self._values for y in other._values}
            )
        return super(RangeSet, self).max(other)

    def min(self, other):
        # type: (Range) -> Range
        if isinstance(other, RangeSet):
            return Range.fromset(
                {min(x, y) for x in self._values for y in other._values}
            )
        return super(RangeSet, self).min(other)

    def union(self, other):
        # type: (Range) -> Range
        if isinstance(other, RangeSet):
            return Range.fromset(self._values | other._values)
        return super(RangeSet, self).union(other)

    def intersect(self, other):
        # type: (Range) -> Range | None
        intersection = {x for x in self._values if other.contains(x)}
        if intersection:
            return Range.fromset(intersection)
        return None

    def make_le_const(self, const):
        # type: (int) -> Range
        return Range.fromset({val for val in self._values if val <= const})

    def make_ge_const(self, const):
        # type: (int) -> Range
        return Range.fromset({val for val in self._values if val >= const})


UNBOUNDED = Range(None, None)
MACHINEINT = Range(MININT, MAXINT)
BOOL = Range(0, 1)
TRUE = Range(1, 1)
FALSE = Range(0, 0)
BIT_VECTOR = Range(0, MAXINT)
