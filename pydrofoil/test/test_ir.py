from pydrofoil.parse import *
from pydrofoil.types import *
from pydrofoil.ir import *

class FakeCodeGen:
    builtin_names = {}

fakecodegen = FakeCodeGen()

def make_bits_to_bool():
    zb = Argument('zb', SmallFixedBitVector(1))
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    block4 = Block()
    block5 = Block()
    i1 = block0.emit(Cast, '$cast', [zb], GenericBitVector(), '`1 14:2-14:5', 'zz43')
    i2 = block0.emit(Cast, '$cast', [AstConstant(BitVectorConstant(constant='0b1', resolved_type=SmallFixedBitVector(1)), SmallFixedBitVector(1))], GenericBitVector(), '`1 14:2-14:5', 'zz44')
    i3 = block0.emit(Operation, 'zeq_bits', [i1, i2], Bool(), '`1 14:2-14:5', 'zz42')
    i4 = block0.emit(Operation, '@not', [i3], Bool(), '`1 13:27-16:1', None)
    block0.next = ConditionalGoto(i4, block4, block1, '`1 13:27-16:1')
    block1.next = Goto(block2, None)
    block2.next = Goto(block3, None)
    i5 = block3.emit_phi([block2, block5], [BooleanConstant.TRUE, BooleanConstant.FALSE], Bool())
    block3.next = Return(i5, None)
    block4.next = Goto(block5, None)
    block5.next = Goto(block3, None)
    return Graph('zbits1_to_bool', [zb], block0)

def test_swap_not():
    graph = make_bits_to_bool()

    swap_not(graph, fakecodegen)
    res = print_graph_construction(graph)
    assert "\n".join(res) == """\
zb = Argument('zb', SmallFixedBitVector(1))
block0 = Block()
block1 = Block()
block2 = Block()
block3 = Block()
block4 = Block()
block5 = Block()
i1 = block0.emit(Cast, '$cast', [zb], GenericBitVector(), '`1 14:2-14:5', 'zz43')
i2 = block0.emit(Cast, '$cast', [AstConstant(BitVectorConstant(constant='0b1', resolved_type=SmallFixedBitVector(1)), SmallFixedBitVector(1))], GenericBitVector(), '`1 14:2-14:5', 'zz44')
i3 = block0.emit(Operation, 'zeq_bits', [i1, i2], Bool(), '`1 14:2-14:5', 'zz42')
block0.next = ConditionalGoto(i3, block1, block4, '`1 13:27-16:1')
block1.next = Goto(block2, None)
block2.next = Goto(block3, None)
i4 = block3.emit_phi([block2, block5], [BooleanConstant.TRUE, BooleanConstant.FALSE], Bool())
block3.next = Return(i4, None)
block4.next = Goto(block5, None)
block5.next = Goto(block3, None)
graph = Graph('zbits1_to_bool', [zb], block0)"""

def test_remove_empty_blocks():
    graph = make_bits_to_bool()
    remove_empty_blocks(graph)
    res = print_graph_construction(graph)
    assert "\n".join(res) == """\
zb = Argument('zb', SmallFixedBitVector(1))
block0 = Block()
block1 = Block()
block2 = Block()
block3 = Block()
i1 = block0.emit(Cast, '$cast', [zb], GenericBitVector(), '`1 14:2-14:5', 'zz43')
i2 = block0.emit(Cast, '$cast', [AstConstant(BitVectorConstant(constant='0b1', resolved_type=SmallFixedBitVector(1)), SmallFixedBitVector(1))], GenericBitVector(), '`1 14:2-14:5', 'zz44')
i3 = block0.emit(Operation, 'zeq_bits', [i1, i2], Bool(), '`1 14:2-14:5', 'zz42')
i4 = block0.emit(Operation, '@not', [i3], Bool(), '`1 13:27-16:1', None)
block0.next = ConditionalGoto(i4, block1, block3, '`1 13:27-16:1')
block1.next = Goto(block2, None)
i5 = block2.emit_phi([block3, block1], [BooleanConstant.TRUE, BooleanConstant.FALSE], Bool())
block2.next = Return(i5, None)
block3.next = Goto(block2, None)
graph = Graph('zbits1_to_bool', [zb], block0)"""


def test_remove_empty_blocks_2():
    zx = Argument('zx', Bool())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    block0.next = ConditionalGoto(zx, block1, block3, '`1 204:26-204:48')
    block1.next = Goto(block2, None)
    i1 = block2.emit_phi([block3, block1], [AstConstant(BitVectorConstant(constant='0b0', resolved_type=SmallFixedBitVector(1)), SmallFixedBitVector(1)), AstConstant(BitVectorConstant(constant='0b1', resolved_type=SmallFixedBitVector(1)), SmallFixedBitVector(1))], SmallFixedBitVector(1))
    block2.next = Return(i1, None)
    block3.next = Goto(block2, None)
    graph = Graph('zbool_to_bits', [zx], block0)
    assert not remove_empty_blocks(graph)

def test_if_true_false():
    zargz3 = Argument('zargz3', SmallFixedBitVector(32))
    block1 = Block()
    block2 = Block()
    block3 = Block()
    block4 = Block()
    block1.next = ConditionalGoto(BooleanConstant.FALSE, block2, block3, '')
    block2.next = Goto(block4)
    block3.next = Goto(block4)
    v0 = block4.emit_phi([block2, block3], [MachineIntConstant(12), MachineIntConstant(13)], Int())
    v1 = block4.emit(Operation, 'foo', [MachineIntConstant(-12), v0], Int(), '', None)
    block4.next = Return(v0, '')

    g = Graph("execute", [zargz3], block1)
    res = remove_if_true_false(g)
    res = print_graph_construction(g)
    assert "\n".join(res) == """\
zargz3 = Argument('zargz3', SmallFixedBitVector(32))
block0 = Block()
block1 = Block()
block2 = Block()
block0.next = Goto(block1, None)
block1.next = Goto(block2, None)
i1 = block2.emit(Operation, 'foo', [MachineIntConstant(-12), MachineIntConstant(13)], Int(), '', None)
block2.next = Return(MachineIntConstant(13), '')
graph = Graph('execute', [zargz3], block0)"""

def test_cast():
    zb = Argument('zb', SmallFixedBitVector(1))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [zb], GenericBitVector(), '`1 14:2-14:5', 'zz43')
    i2 = block0.emit(Cast, '$cast', [i1], SmallFixedBitVector(1), '`1 14:2-14:5', 'zz43')
    block0.next = Return(i2, '')
    graph = Graph('f', [zb], block0)
    res = simplify(graph, fakecodegen)
    assert res
    res = print_graph_construction(graph)
    assert "\n".join(res) == """\
zb = Argument('zb', SmallFixedBitVector(1))
block0 = Block()
block0.next = Return(zb, '')
graph = Graph('f', [zb], block0)"""

def test_eq_bits():
    za = Argument('za', SmallFixedBitVector(2))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [za], GenericBitVector(), '`5 120:4-120:8', 'zz411')
    i2 = block0.emit(Cast, '$cast', [SmallBitVectorConstant(0b01, SmallFixedBitVector(2))], GenericBitVector(), '`5 120:4-120:8', 'zz412')
    i3 = block0.emit(Operation, 'eq_bits', [i1, i2], Bool(), '`5 120:4-120:8', 'zz410')
    block0.next = Return(i3, None)
    graph = Graph("f", [za], block0)
    simplify(graph, fakecodegen)
    res = print_graph_construction(graph)
    assert "\n".join(res) == """\
za = Argument('za', SmallFixedBitVector(2))
block0 = Block()
i1 = block0.emit(Operation, '@eq_bits_bv_bv', [za, SmallBitVectorConstant(1, SmallFixedBitVector(2))], Bool(), '`5 120:4-120:8', 'zz410')
block0.next = Return(i1, None)
graph = Graph('f', [za], block0)"""

def test_int_and_back():
    block0 = Block()
    i1 = block0.emit(Operation, 'int64_to_int', [MachineIntConstant(15)], Int(), '`5 295:30-295:32', 'zz42')
    i2 = block0.emit(Operation, 'int_to_int64', [i1], MachineInt(), '`5 295:30-295:32', 'zz40')
    block0.next = Return(i2)
    graph = Graph("f", [], block0)
    simplify(graph, fakecodegen)
    res = print_graph_construction(graph)
    assert "\n".join(res) == """\
block0 = Block()
block0.next = Return(MachineIntConstant(15), None)
graph = Graph('f', [], block0)"""
    
