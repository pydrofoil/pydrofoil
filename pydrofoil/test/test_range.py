import sys

from pydrofoil.absinterp import Range, UNBOUNDED, TRUE, FALSE, BOOL

from rpython.rlib.rarithmetic import LONG_BIT

from hypothesis import given, strategies


special_values = (
    range(100) + range(-1, -100, -1) +
    [2 ** i for i in range(1, LONG_BIT)] +
    [-2 ** i for i in range(1, LONG_BIT)] +
    [2 ** i - 1 for i in range(1, LONG_BIT)] +
    [-2 ** i - 1 for i in range(1, LONG_BIT)] +
    [2 ** i + 1 for i in range(1, LONG_BIT)] +
    [-2 ** i + 1 for i in range(1, LONG_BIT)] +
    [sys.maxint, -sys.maxint-1])

special_values = strategies.sampled_from(
    [int(v) for v in special_values if type(int(v)) is int])

ints = strategies.builds(
    int, # strategies.integers sometimes returns a long?
    special_values | strategies.integers(
    min_value=int(-sys.maxint-1), max_value=sys.maxint) |
    strategies.integers())

def build_bound_with_contained_number(a, b, c):
    a, b, c = sorted([a, b, c])
    r = Range(a, c)
    assert r.contains(b)
    return r, b

unbounded = strategies.builds(
    lambda x: (Range(None, None), int(x)),
    ints
)

lower_bounded = strategies.builds(
    lambda x, y: (Range(min(x, y), None), max(x, y)),
    ints,
    ints
)

upper_bounded = strategies.builds(
    lambda x, y: (Range(None, max(x, y)), min(x, y)),
    ints,
    ints
)

bounded = strategies.builds(
    build_bound_with_contained_number,
    ints, ints, ints
)

constant = strategies.builds(
    lambda x: (Range(x, x), x),
    ints
)

bound_with_contained_number = strategies.one_of(
    unbounded, lower_bounded, upper_bounded, constant, bounded)

smallbounds = strategies.builds(
    lambda start, width: Range(start, start + width),
    ints,
    strategies.integers(min_value=1, max_value=50)
)

def test_add_example():
    assert Range(None, None).add(Range(1, None)) == Range(None, None)
    assert Range(5, None).add(Range(1, None)) == Range(6, None)
    assert Range(-12, None).add(Range(1, None)) == Range(-11, None)
    assert Range(-12, 0).add(Range(1, 1)) == Range(-11, 1)
    assert Range(None, 0).add(Range(1, 10)) == Range(None, 10)

@given(bound_with_contained_number, bound_with_contained_number)
def test_add_hypothesis(ta, tb):
    ra, a = ta
    rb, b = tb
    r = ra.add(rb)
    assert r.contains(a + b)

@given(smallbounds, smallbounds)
def test_add_hypothesis_enum(ra, rb):
    r = ra.add(rb)
    for a in range(ra.low, ra.high + 1):
        for b in range(rb.low, rb.high + 1):
            assert r.contains(a + b)
    # check precision, somewhat
    assert not r.contains(ra.low - 1 + rb.low)
    assert not r.contains(ra.high + 1 + rb.high)

def test_neg_example():
    assert Range(None, None).neg() == Range(None, None)
    assert Range(1, None).neg() == Range(None, -1)
    assert Range(None, 10).neg() == Range(-10, None)
    assert Range(-2**100, 2**1000).neg() == Range(-2**1000, 2**100)

@given(bound_with_contained_number)
def test_neg_hypothesis(ta):
    ra, a = ta
    r = ra.neg()
    assert r.contains(-a)

@given(smallbounds)
def test_neg_hypothesis_enum(ra):
    r = ra.neg()
    for a in range(ra.low, ra.high + 1):
        assert r.contains(-a)
    assert not r.contains(-(ra.low - 1))
    assert not r.contains(-(ra.high + 1))

def test_sub_example():
    assert Range(None, None).sub(Range(1, None)) == Range(None, None)
    assert Range(5, None).sub(Range(1, None)) == Range(None, None)
    assert Range(5, None).sub(Range(None, 1)) == Range(4, None)
    assert Range(-12, None).sub(Range(1, None)) == Range(None, None)
    assert Range(None, -12).sub(Range(1, None)) == Range(None, -13)
    assert Range(-12, 0).sub(Range(1, 1)) == Range(-13, -1)
    assert Range(None, 0).sub(Range(1, 10)) == Range(None, -1)

@given(bound_with_contained_number, bound_with_contained_number)
def test_sub_hypothesis(ta, tb):
    ra, a = ta
    rb, b = tb
    r = ra.sub(rb)
    assert r.contains(a - b)

@given(smallbounds, smallbounds)
def test_sub_hypothesis_enum(ra, rb):
    r = ra.sub(rb)
    for a in range(ra.low, ra.high + 1):
        for b in range(rb.low, rb.high + 1):
            assert r.contains(a - b)

def test_union_example():
    assert Range(None, None).union(Range(1, None)) == Range(None, None)
    assert Range(5, None).union(Range(1, None)) == Range(1, None)
    assert Range(5, None).union(Range(None, 1)) == Range(None, None)
    assert Range(-12, None).union(Range(1, None)) == Range(-12, None)
    assert Range(None, -12).union(Range(1, None)) == Range(None, None)
    assert Range(-12, 0).union(Range(1, 1)) == Range(-12, 1)
    assert Range(None, 0).union(Range(1, 10)) == Range(None, 10)

@given(bound_with_contained_number, bound_with_contained_number)
def test_union_hypothesis(ta, tb):
    ra, a = ta
    rb, b = tb
    r = ra.union(rb)
    assert r.contains(a)
    assert r.contains(b)

@given(smallbounds, smallbounds)
def test_union_hypothesis_enum(ra, rb):
    r = ra.union(rb)
    for a in range(ra.low, ra.high + 1):
        assert r.contains(a)
    for b in range(rb.low, rb.high + 1):
        assert r.contains(b)
    assert not r.contains(min(ra.low, rb.low) - 1)
    assert not r.contains(max(ra.high, rb.high) + 1)

def test_le_example():
    assert Range(None, None).le(Range(1, None)) == BOOL
    assert Range(5, None).le(Range(1, None)) == BOOL
    assert Range(None, 1).le(Range(5, None)) == TRUE
    assert Range(5, None).le(Range(None, 1)) == FALSE
    assert Range(5, None).le(Range(None, 4)) == FALSE
    assert Range(5, None).le(Range(None, 5)) == BOOL
    assert Range(5, 100).le(Range(-100, 1)) == FALSE
    assert Range(-12, None).le(Range(1, None)) == BOOL
    assert Range(None, -12).le(Range(1, None)) == TRUE
    assert Range(-12, 0).le(Range(1, 1)) == TRUE
    assert Range(None, 0).le(Range(1, 10)) == TRUE
    assert Range(10, 100).le(Range(99, 10000)) == BOOL

@given(bound_with_contained_number, bound_with_contained_number)
def test_le_hypothesis(ta, tb):
    ra, a = ta
    rb, b = tb
    r = ra.le(rb)
    assert r.contains(a <= b)

@given(smallbounds, smallbounds)
def test_le_hypothesis_enum(ra, rb):
    r = ra.le(rb)
    for a in range(ra.low, ra.high + 1):
        for b in range(rb.low, rb.high + 1):
            assert r.contains(a <= b)

@given(bound_with_contained_number, bound_with_contained_number)
def test_ge_hypothesis(ta, tb):
    ra, a = ta
    rb, b = tb
    r = ra.ge(rb)
    assert r.contains(a >= b)

@given(smallbounds, smallbounds)
def test_ge_hypothesis_enum(ra, rb):
    r = ra.ge(rb)
    for a in range(ra.low, ra.high + 1):
        for b in range(rb.low, rb.high + 1):
            assert r.contains(a >= b)

