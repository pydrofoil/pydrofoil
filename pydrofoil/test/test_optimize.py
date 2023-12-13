import pytest

from pydrofoil.optimize import (
    _compute_dominators,
    immediate_dominators,
)

# dominators


def test_compute_dominators():
    G = {0: {2}, 2: {3, 4, 6}, 3: {5}, 4: {5}, 5: {2}, 6: {}}
    assert _compute_dominators(G) == {
        0: {0},
        2: {0, 2},
        3: {0, 2, 3},
        4: {0, 2, 4},
        5: {0, 2, 5},
        6: {0, 2, 6},
    }
    assert immediate_dominators(G) == {2: 0, 3: 2, 4: 2, 5: 2, 6: 2}
