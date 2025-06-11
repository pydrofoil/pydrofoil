from pydrofoil import graphalgorithms
from pydrofoil.types import *
from pydrofoil.ir import *

def example_graph():
    i = Argument('i', MachineInt())
    block1 = Block()
    block2 = Block()
    block3 = Block()
    block4 = Block()
    i34 = block1.emit(Operation, '@eq', [i, MachineIntConstant(32)], Bool(), '`94009', 'zz424')
    block1.next = ConditionalGoto(i34, block2, block3, '`10 150234:22-150234:43')
    i35 = block2.emit(Operation, 'usetheint', [i], Bool(), '`10 150235:4-150235:142', 'zz417')
    block2.next = Return(i35)
    i38 = block3.emit(Operation, '@eq', [i, MachineIntConstant(64)], Bool(), '`94020', 'zz425')
    block3.next = ConditionalGoto(i38, block2, block4, '`10 150217:4-150235:142')
    block4.next = Raise(StringConstant('src/instrs64.sail:150234.44-150234.45'), None)
    return block1, block2, block3, block4, Graph("g", [i], block1)

def test_dfs_labeled_edges():
    block1, block2, block3, block4, g = example_graph()

    edges = list(graphalgorithms.dfs_labeled_edges(g))
    assert edges == [
        (block1, block1, "forward"),
        (block1, block3, "forward"),
        (block3, block4, "forward"),
        (block3, block4, "reverse"),
        (block3, block2, "forward"),
        (block3, block2, "reverse"),
        (block1, block3, "reverse"),
        (block1, block2, "nontree"),
        (block1, block1, "reverse"),
    ]

def test_dfs_postorder():
    block1, block2, block3, block4, g = example_graph()

    nodes = list(graphalgorithms.dfs_postorder_nodes(g))
    assert nodes == [block4, block2, block3, block1]
    nodes = list(graphalgorithms.dfs_postorder_nodes(g, block1))
    assert nodes == [block4, block2, block3, block1]
    nodes = list(graphalgorithms.dfs_postorder_nodes(g, block3))
    assert nodes == [block4, block2, block3]

def test_idom():
    block1, block2, block3, block4, g = example_graph()
    idoms = graphalgorithms.immediate_dominators(g, block1, g.make_entrymap())
    assert idoms[block4] == block3
    assert idoms[block2] == block1
    assert idoms[block3] == block1

def get_double_return_graph():
    za = Argument('za', SmallFixedBitVector(1))
    block0 = Block()
    block1 = Block()
    block2 = Block()
    i2 = block0.emit(Operation, '@eq_bits_bv_bv', [za, SmallBitVectorConstant(0b0, SmallFixedBitVector(1))], Bool())
    block0.next = ConditionalGoto(i2, block1, block2, '`1 124:10-124:45')
    i3 = block1.emit(GlobalRead, 'zA', [], SmallFixedBitVector(16), None, None)
    block1.next = Return(i3)
    i4 = block2.emit(GlobalRead, 'zC', [], SmallFixedBitVector(16), None, None)
    block2.next = Return(i4)
    graph = Graph('f', [za], block0)
    return block0, block1, block2, graph


def test_compute_single_return_graph():
    _, _, _, graph = get_double_return_graph()
    
    new_graph = graphalgorithms.compute_single_return_graph(graph)

    startblock = new_graph.startblock
    true_block = startblock.next.truetarget
    false_block = startblock.next.falsetarget
    phi_block = true_block.next.target
    phi_op = phi_block.operations[0]

    assert true_block.next.target == false_block.next.target
    assert isinstance(true_block.next, Goto)
    assert false_block.next.target == phi_block

    assert phi_op.prevblocks == [true_block, false_block]
    assert isinstance(phi_block.next, Return)
    assert phi_block.next.value == phi_op 


def test_compute_max_phi_indeg_two_graph():
    pass
    #_, _, _, graph = get_double_return_graph()
    
    #new_graph = graphalgorithms.compute_max_phi_indeg_two_graph(graph)

    #assert False