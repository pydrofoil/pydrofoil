import pytest

from pydrofoil import ir, types
from pydrofoil.ir.purify import purify
from pydrofoil.test.test_ir import compare
from pydrofoil.test.util import MockCodegen


def test_simple():
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
    mockcodegen = MockCodegen({"zalmost_pure": graph})
    purify(mockcodegen, graph)
    compare(
        graph,
        """
a = Argument('a', MachineInt())
block0 = Block()
i1 = block0.emit(GlobalRead, 'flag', [], Bool(), None, None)
i2 = block0.emit(Operation, 'almost_pure_pure_core', [a, i1], MachineInt(), None, None)
block0.next = Return(i2, None)
graph = Graph('zalmost_pure', [a], block0)
""",
    )
    compare(
        mockcodegen.all_graph_by_name["almost_pure_pure_core"],
        """
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
""",
    )
