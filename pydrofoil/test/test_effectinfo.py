from pydrofoil.effectinfo import compute_all_effects, local_effects, EffectInfo
from pydrofoil import (
    operations,
)  # Need to import this for __extend__ definitions
from pydrofoil.test.test_ir import compare
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


def test_local_effects_builtins():
    graph = get_example_builtins()
    effects = local_effects(graph)
    assert effects.called_builtins == {"@ones_i", "@zeros_i"}


def test_all_effects():
    d = get_example_nand()
    all_effects = compute_all_effects(d)
    assert set(all_effects.keys()) == set(d.keys())
    assert all_effects["zcompute_value"] == local_effects(d["zcompute_value"])
    assert all_effects["zexecute_zCINST"] == local_effects(
        d["zexecute_zCINST"]
    ).extend(local_effects(d["zcompute_value"]))


def _get_example_cse_global_with_effect_info():
    # a function f that does the following:
    # x = reg_a # global read
    # y = reg_b
    # call function g
    # x2 = reg_a # global read, should be optimized to x
    # y2 = reg_b # must not be optimized away

    # function g
    # write reg_b
    block_f = Block()
    x = block_f.emit(GlobalRead, "reg_a", [], Bool())
    y = block_f.emit(GlobalRead, "reg_b", [], Bool())
    block_f.emit(Operation, "g", [], Unit())
    x2 = block_f.emit(GlobalRead, "reg_a", [], Bool())
    y2 = block_f.emit(GlobalRead, "reg_b", [], Bool())
    block_f.emit(Operation, "@dummy", [x, y, x2, y2], Unit())
    block_f.next = Return(UnitConstant.UNIT)
    graph_f = Graph("f", [], block_f)

    block_g = Block()
    block_g.emit(GlobalWrite, "reg_b", [BooleanConstant.TRUE], Unit())
    block_g.next = Return(UnitConstant.UNIT)

    graph_g = Graph("g", [], block_g)
    return {"f": graph_f, "g": graph_g}


class MockCodegen(object):
    def __init__(self, graphs):
        self.all_graph_by_name = graphs
        self._effect_infos = None
        self.builtin_names = {}

    def get_effects(self, function_name):
        # type: (str) -> EffectInfo | None
        # TODO copy this to regular code gen
        if self._effect_infos is None:
            self._effect_infos = compute_all_effects(self.all_graph_by_name)
        return self._effect_infos.get(function_name)


def test_cse_global():
    graphs = _get_example_cse_global_with_effect_info()
    effect_info = compute_all_effects(graphs)
    assert effect_info["g"] == EffectInfo(register_writes=frozenset({"reg_b"}))
    assert effect_info["f"] == EffectInfo(
        register_writes=frozenset({"reg_b"}),
        register_reads=frozenset({"reg_a", "reg_b"}),
        called_builtins=frozenset({"@dummy"}),
    )

    codegen = MockCodegen(graphs)
    cse_global_reads(graphs["f"], codegen)
    compare(
        graphs["f"],
        """
block0 = Block()
i0 = block0.emit(GlobalRead, 'reg_a', [], Bool(), None, None)
i1 = block0.emit(GlobalRead, 'reg_b', [], Bool(), None, None)
i2 = block0.emit(Operation, 'g', [], Unit(), None, None)
i3 = block0.emit(GlobalRead, 'reg_b', [], Bool(), None, None)
i4 = block0.emit(Operation, '@dummy', [i0, i1, i0, i3], Unit(), None, None)
block0.next = Return(UnitConstant.UNIT, None)
graph = Graph('f', [], block0)""",
    )


def _get_example_cse_field_with_effect_info():
    # 2 struct types: S and T with fields x and y
    # function f(s, t):
    # a = s.x
    # b = s.y
    # c = t.x
    # d = t.y
    # call function g  # Modifies S.x and T.y
    # a2 = s.x  # Must be re-read
    # b2 = s.y  # Should be optimized
    # c2 = t.x  # Should be optimized
    # d2 = t.y  # Must be re-read

    # function g(s, t)
    # write s.x
    # write t.y
    s = Argument("s", Struct("S", ("x", "y"), (Bool(), Bool())))
    t = Argument("t", Struct("T", ("x", "y"), (Bool(), Bool())))
    u = Argument("u", Struct("U", ("x", "y"), (Bool(), Bool())))

    block_f = Block()
    a = block_f.emit(FieldAccess, "x", [s], Bool())
    b = block_f.emit(FieldAccess, "y", [s], Bool())
    c = block_f.emit(FieldAccess, "x", [t], Bool())
    d = block_f.emit(FieldAccess, "y", [t], Bool())
    block_f.emit(Operation, "g", [s, t], Unit())
    a2 = block_f.emit(FieldAccess, "x", [s], Bool())
    b2 = block_f.emit(FieldAccess, "y", [s], Bool())
    c2 = block_f.emit(FieldAccess, "x", [t], Bool())
    d2 = block_f.emit(FieldAccess, "y", [t], Bool())
    block_f.emit(Operation, "@dummy", [a, b, c, d, a2, b2, c2, d2], Unit())
    block_f.next = Return(UnitConstant.UNIT)
    graph_f = Graph("f", [s, t], block_f)

    block_g = Block()
    block_g.emit(FieldWrite, "x", [s, BooleanConstant.TRUE], Unit())
    block_g.emit(FieldWrite, "y", [t, BooleanConstant.TRUE], Unit())
    block_g.emit(FieldWrite, "x", [u, BooleanConstant.TRUE], Unit())
    block_g.next = Return(UnitConstant.UNIT)
    graph_g = Graph("g", [s, t, u], block_g)

    return {"f": graph_f, "g": graph_g}


def test_cse_field():
    graphs = _get_example_cse_field_with_effect_info()
    s = Struct("S", ("x", "y"), (Bool(), Bool()))
    t = Struct("T", ("x", "y"), (Bool(), Bool()))
    u = Struct("U", ("x", "y"), (Bool(), Bool()))
    effect_info = compute_all_effects(graphs)
    assert effect_info["g"] == EffectInfo(
        struct_writes=frozenset({(s, "x"), (t, "y"), (u, "x")})
    )
    assert effect_info["f"] == EffectInfo(
        struct_writes=frozenset({(s, "x"), (t, "y"), (u, "x")}),
        struct_reads=frozenset({(s, "x"), (s, "y"), (t, "x"), (t, "y")}),
        called_builtins=frozenset({"@dummy"}),
    )

    codegen = MockCodegen(graphs)
    cse_field_reads(graphs["f"], codegen)
    compare(
        graphs["f"],
        """
S = Struct('S', ('x', 'y'), (Bool(), Bool()))
T = Struct('T', ('x', 'y'), (Bool(), Bool()))
s = Argument('s', S)
t = Argument('t', T)
block0 = Block()
i2 = block0.emit(FieldAccess, 'x', [s], Bool(), None, None)
i3 = block0.emit(FieldAccess, 'y', [s], Bool(), None, None)
i4 = block0.emit(FieldAccess, 'x', [t], Bool(), None, None)
i5 = block0.emit(FieldAccess, 'y', [t], Bool(), None, None)
i6 = block0.emit(Operation, 'g', [s, t], Unit(), None, None)
i7 = block0.emit(FieldAccess, 'x', [s], Bool(), None, None)
i8 = block0.emit(FieldAccess, 'y', [t], Bool(), None, None)
i9 = block0.emit(Operation, '@dummy', [i2, i3, i4, i5, i7, i3, i4, i8], Unit(), None, None)
block0.next = Return(UnitConstant.UNIT, None)
graph = Graph('f', [s, t], block0)""",
    )


def test_effectinfo_methods():
    graphs = get_method_example()
    methods = {
        "execute": {
            "execute_first": graphs["execute_first"],
            "execute_second": graphs["execute_second"],
        }
    }
    effect_info = compute_all_effects(graphs, methods)
    assert effect_info["c1"] == EffectInfo(
        register_writes=frozenset(["zx1", "zx2"])
    )
