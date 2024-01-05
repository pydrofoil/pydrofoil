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


