from pydrofoil.effectinfo import compute_all_effects, local_effects
from pydrofoil.test.examples import *


def test_local_effects_write():
    graph = get_example_00()
    effects = local_effects(graph)
    assert not effects.register_reads
    assert effects.register_writes == {"zx%s" % i for i in range(1, 32)}


def test_local_effects_read():
    graph = get_example_01()
    effects = local_effects(graph)
    assert not effects.register_writes
    assert effects.register_reads == {"zx%s" % i for i in range(1, 32)}

def test_all_effects():
    d = get_example_nand()
    all_effects = compute_all_effects(d)
    assert set(all_effects.keys()) == set(d.keys())
    assert all_effects["zcompute_value"] == local_effects(d["zcompute_value"])
    assert all_effects["zexecute_zCINST"] == local_effects(d["zexecute_zCINST"]).extend(local_effects(d["zcompute_value"]))
