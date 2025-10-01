import pytest

from pydrofoil import ir, types
from pydrofoil.ir.purify import purify, purify_all_graphs
from pydrofoil.test.test_ir import compare
from pydrofoil.test.util import MockCodegen


def _get_example_simple():
    a = ir.Argument("a", types.MachineInt())
    block1 = ir.Block()
    block2 = ir.Block()
    block3 = ir.Block()
    block4 = ir.Block()

    i2 = block1.emit(ir.GlobalRead, "flag", [], types.Bool(), None, None)
    block1.next = ir.ConditionalGoto(i2, block2, block3)
    block2.next = ir.Goto(block4)
    block3.next = ir.Goto(block4)
    i3 = block4.emit_phi(
        [block2, block3],
        [ir.MachineIntConstant(4), ir.MachineIntConstant(5)],
        types.MachineInt(),
    )
    block4.next = ir.Return(i3)
    graph = ir.Graph("zalmost_pure", [a], block1)
    purified_str = """
a = Argument('a', MachineInt())
block0 = Block()
i1 = block0.emit(GlobalRead, 'flag', [], Bool(), None, None)
i2 = block0.emit(Operation, 'almost_pure_pure_core', [a, i1], MachineInt(), None, None)
block0.next = Return(i2, None)
graph = Graph('zalmost_pure', [a], block0)
"""
    pure_core_str = """
a = Argument('a', MachineInt())
flag = Argument('flag', Bool())
block0 = Block()
block1 = Block()
block2 = Block()
block3 = Block()
block0.next = ConditionalGoto(flag, block1, block3, None)
block1.next = Goto(block2, None)
i2 = block2.emit_phi([block1, block3], [MachineIntConstant(4), MachineIntConstant(5)], MachineInt())
block2.next = Return(i2, None)
block3.next = Goto(block2, None)
graph = Graph('almost_pure_pure_core', [a, flag], block0)
"""
    return graph, purified_str, pure_core_str


def test_simple():
    graph, purified_str, pure_core_str = _get_example_simple()
    mockcodegen = MockCodegen({"zalmost_pure": graph})
    purify(mockcodegen, graph)

    compare(graph, purified_str)
    compare(
        mockcodegen.all_graph_by_name["almost_pure_pure_core"],
        pure_core_str,
    )


def _get_example_pure():
    block1 = ir.Block()
    block1.next = ir.Return(ir.IntConstant(42))
    graph_str = """
block0 = Block()
block0.next = Return(IntConstant(42), None)
graph = Graph('zalready_pure', [], block0)"""
    return ir.Graph("zalready_pure", [], block1), graph_str


def test_purify_all_graphs():
    purifiable_graph, purified_str, pure_core_str = _get_example_simple()
    pure_graph, pure_str = _get_example_pure()

    codegen = MockCodegen({g.name: g for g in (purifiable_graph, pure_graph)})
    purify_all_graphs(codegen)

    compare(purifiable_graph, purified_str)
    compare(
        codegen.all_graph_by_name["almost_pure_pure_core"],
        pure_core_str,
    )
    compare(pure_graph, pure_str)


def _get_example_calls_simple():
    # This example calls the example graph from '_get_example_simple'
    block = ir.Block()
    a = ir.Argument("a", types.MachineInt())

    i0 = block.emit(ir.Operation, "zalmost_pure", [a], types.MachineInt())
    i1 = block.emit(
        ir.Operation,
        "add_i_i_must_fit",
        [a, ir.MachineIntConstant(9)],
        types.MachineInt(),
    )
    block.next = ir.Return(i1)

    graph = ir.Graph("zpurifiable_after_inline", [a], block)

    purified_str = """
a = Argument('a', MachineInt())
block0 = Block()
i1 = block0.emit(GlobalRead, 'flag', [], Bool(), None, None)
i2 = block0.emit(Operation, 'purifiable_after_inline_pure_core', [a, i1], MachineInt(), None, None)
block0.next = Return(i2, None)
graph = Graph('zpurifiable_after_inline', [a], block0)"""
    pure_core_str = """
a = Argument('a', MachineInt())
flag = Argument('flag', Bool())
block0 = Block()
i2 = block0.emit(Comment, 'inlined zalmost_pure', [], Unit(), None, None)
i3 = block0.emit(Operation, 'almost_pure_pure_core', [a, flag], MachineInt(), None, None)
i4 = block0.emit(Operation, 'add_i_i_must_fit', [a, MachineIntConstant(9)], MachineInt(), None, None)
block0.next = Return(i4, None)
graph = Graph('purifiable_after_inline_pure_core', [a, flag], block0)"""

    return graph, purified_str, pure_core_str


def test_inline_in_callers():
    callee_graph, _, _ = _get_example_simple()
    caller_graph, purifed_str, pure_core_str = _get_example_calls_simple()

    codegen = MockCodegen({g.name: g for g in (callee_graph, caller_graph)})
    purify_all_graphs(codegen)

    compare(caller_graph, purifed_str)
    compare(
        codegen.all_graph_by_name["purifiable_after_inline_pure_core"],
        pure_core_str,
    )
