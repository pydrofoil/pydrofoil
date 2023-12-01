from pydrofoil.parse import *
from pydrofoil.types import *
from pydrofoil.ir import *

class FakeCodeGen:
    builtin_names = {"zz5izDzKz5i64": "int_to_int64", "zz5i64zDzKz5i": "int64_to_int"}
    inlinable_functions = {}

fakecodegen = FakeCodeGen()

def check_simplify(graph, expected):
    res = simplify(graph, fakecodegen)
    assert res
    res = print_graph_construction(graph)
    got = "\n".join(res)
    if got != expected:
        print "EXPECTED:"
        print "_" * 60
        print expected
        print "GOT:"
        print "_" * 60
        print got
    assert got == expected


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
    check_simplify(graph, """\
zb = Argument('zb', SmallFixedBitVector(1))
block0 = Block()
block0.next = Return(zb, '')
graph = Graph('f', [zb], block0)""")

def test_eq_bits():
    za = Argument('za', SmallFixedBitVector(2))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [za], GenericBitVector(), '`5 120:4-120:8', 'zz411')
    i2 = block0.emit(Cast, '$cast', [SmallBitVectorConstant(0b01, SmallFixedBitVector(2))], GenericBitVector(), '`5 120:4-120:8', 'zz412')
    i3 = block0.emit(Operation, 'eq_bits', [i1, i2], Bool(), '`5 120:4-120:8', 'zz410')
    block0.next = Return(i3, None)
    graph = Graph("f", [za], block0)
    check_simplify(graph, """\
za = Argument('za', SmallFixedBitVector(2))
block0 = Block()
i1 = block0.emit(Operation, '@eq_bits_bv_bv', [za, SmallBitVectorConstant(1, SmallFixedBitVector(2))], Bool(), '`5 120:4-120:8', 'zz410')
block0.next = Return(i1, None)
graph = Graph('f', [za], block0)""")

def test_neq_bits():
    za = Argument('za', SmallFixedBitVector(2))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [za], GenericBitVector(), '`5 120:4-120:8', 'zz411')
    i2 = block0.emit(Cast, '$cast', [SmallBitVectorConstant(0b01, SmallFixedBitVector(2))], GenericBitVector(), '`5 120:4-120:8', 'zz412')
    i3 = block0.emit(Operation, 'neq_bits', [i1, i2], Bool(), '`5 120:4-120:8', 'zz410')
    block0.next = Return(i3, None)
    graph = Graph("f", [za], block0)
    check_simplify(graph, """\
za = Argument('za', SmallFixedBitVector(2))
block0 = Block()
i1 = block0.emit(Operation, '@eq_bits_bv_bv', [za, SmallBitVectorConstant(1, SmallFixedBitVector(2))], Bool(), '`5 120:4-120:8', 'zz410')
i2 = block0.emit(Operation, '@not', [i1], Bool(), None, None)
block0.next = Return(i2, None)
graph = Graph('f', [za], block0)""")

def test_int_and_back():
    block0 = Block()
    i1 = block0.emit(Operation, 'int64_to_int', [MachineIntConstant(15)], Int(), '`5 295:30-295:32', 'zz42')
    i2 = block0.emit(Operation, 'int_to_int64', [i1], MachineInt(), '`5 295:30-295:32', 'zz40')
    block0.next = Return(i2)
    graph = Graph("f", [], block0)
    check_simplify(graph, """\
block0 = Block()
block0.next = Return(MachineIntConstant(15), None)
graph = Graph('f', [], block0)""")

def test_eq_int():
    zr = Argument('zr', MachineInt())
    block0 = Block()
    i1 = block0.emit(Operation, 'int64_to_int', [MachineIntConstant(0)], Int(), '`80', 'zz4128')
    i2 = block0.emit(Operation, 'int64_to_int', [zr], Int(), '`82', 'zz4130')
    i3 = block0.emit(Operation, 'eq_int', [i2, i1], Bool(), '`83', 'zz4129')
    block0.next = Return(i3)
    graph = Graph("f", [zr], block0)
    check_simplify(graph, """\
zr = Argument('zr', MachineInt())
block0 = Block()
i1 = block0.emit(Operation, '@eq', [zr, MachineIntConstant(0)], Bool(), '`83', 'zz4129')
block0.next = Return(i1, None)
graph = Graph('f', [zr], block0)""")

def test_vector_subrange():
    zargz3 = Argument('zargz3', SmallFixedBitVector(64))
    block0 = Block()
    i1 = block0.emit(Operation, 'int64_to_int', [MachineIntConstant(6)], Int(), '`36 84:17-84:31', 'zz412137')
    i2 = block0.emit(Operation, 'int64_to_int', [MachineIntConstant(0)], Int(), '`36 84:17-84:31', 'zz412138')
    i3 = block0.emit(Cast, '$cast', [zargz3], GenericBitVector(), '`36 84:17-84:31', 'zz412139')
    i4 = block0.emit(Operation, 'vector_subrange', [i3, i1, i2], GenericBitVector(), '`36 84:17-84:31', 'zz412140')
    i5 = block0.emit(Cast, '$cast', [i4], SmallFixedBitVector(7), '`36 84:17-84:31', 'zz412111')
    block0.next = Return(i5)
    graph = Graph("f", [zargz3], block0)
    check_simplify(graph, """\
zargz3 = Argument('zargz3', SmallFixedBitVector(64))
block0 = Block()
i1 = block0.emit(Operation, '@vector_subrange_fixed_bv_i_i', [zargz3, MachineIntConstant(6), MachineIntConstant(0)], SmallFixedBitVector(7), '`36 84:17-84:31', 'zz412140')
block0.next = Return(i1, None)
graph = Graph('f', [zargz3], block0)""")

def test_vector_update_subrange():
    zv = Argument('zv', SmallFixedBitVector(64))
    zx = Argument('zx', SmallFixedBitVector(1))
    block0 = Block()
    i3 = block0.emit(Cast, '$cast', [zv], GenericBitVector(), '`509', 'zz45')
    i4 = block0.emit(Cast, '$cast', [zx], GenericBitVector(), '`511', 'zz46')
    i5 = block0.emit(Operation, '@vector_update_subrange_o_i_i_o', [i3, MachineIntConstant(0), MachineIntConstant(0), i4], GenericBitVector(), '`513', 'zz47')
    i6 = block0.emit(Cast, '$cast', [i5], SmallFixedBitVector(64), '`514', 'zz40')
    block0.next = Return(i6, None)
    graph = Graph('update', [zv, zx], block0)
    check_simplify(graph, """\
zv = Argument('zv', SmallFixedBitVector(64))
zx = Argument('zx', SmallFixedBitVector(1))
block0 = Block()
i2 = block0.emit(Operation, '@vector_update_subrange_fixed_bv_i_i_bv', [zv, MachineIntConstant(0), MachineIntConstant(0), zx], SmallFixedBitVector(64), '`513', 'zz47')
block0.next = Return(i2, None)
graph = Graph('update', [zv, zx], block0)""")

def test_vector_access():
    zx = Argument('zx', SmallFixedBitVector(8))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [zx], GenericBitVector(), '`35 86:29-86:33', 'zz48')
    i2 = block0.emit(Operation, '@vector_access_o_i', [i1, MachineIntConstant(7)], Bit(), '`35 86:29-86:33', 'zz46')
    block0.next = Return(i2)
    graph = Graph('update', [zx], block0)
    check_simplify(graph, """\
zx = Argument('zx', SmallFixedBitVector(8))
block0 = Block()
i1 = block0.emit(Operation, '@vector_access_bv_i', [zx, MachineIntConstant(7)], Bit(), '`35 86:29-86:33', 'zz46')
block0.next = Return(i1, None)
graph = Graph('update', [zx], block0)""")

def test_and_not_bits():
    zx = Argument('zx', SmallFixedBitVector(64))
    zy = Argument('zy', SmallFixedBitVector(64))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [zx], GenericBitVector(), '`25 286:37-286:63', 'zz420')
    i2 = block0.emit(Operation, 'not_bits', [i1], GenericBitVector(), '`25 286:51-286:62', 'zz424')
    i3 = block0.emit(Cast, '$cast', [zy], GenericBitVector(), '`25 286:37-286:63', 'zz420')
    i4 = block0.emit(Operation, 'and_bits', [i3, i2], GenericBitVector(), '`25 286:37-286:63', 'zz422')
    i8 = block0.emit(Cast, '$cast', [i4], SmallFixedBitVector(64), '`25 286:37-286:63', 'zz420')
    block0.next = Return(i8)
    graph = Graph('update', [zx, zy], block0)
    check_simplify(graph, """\
zx = Argument('zx', SmallFixedBitVector(64))
zy = Argument('zy', SmallFixedBitVector(64))
block0 = Block()
i2 = block0.emit(Operation, '@not_vec_bv', [zx, MachineIntConstant(64)], SmallFixedBitVector(64), '`25 286:51-286:62', None)
i3 = block0.emit(Operation, '@and_vec_bv_bv', [zy, i2], SmallFixedBitVector(64), '`25 286:37-286:63', 'zz422')
block0.next = Return(i3, None)
graph = Graph('update', [zx, zy], block0)""")

def test_add_bits():
    zx = Argument('zx', SmallFixedBitVector(64))
    zy = Argument('zy', SmallFixedBitVector(64))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [zx], GenericBitVector(), '`25 286:37-286:63', 'zz420')
    i3 = block0.emit(Cast, '$cast', [zy], GenericBitVector(), '`25 286:37-286:63', 'zz420')
    i4 = block0.emit(Operation, 'add_bits', [i1, i3], GenericBitVector(), '`25 286:37-286:63', 'zz422')
    i8 = block0.emit(Cast, '$cast', [i4], SmallFixedBitVector(64), '`25 286:37-286:63', 'zz420')
    block0.next = Return(i8)
    graph = Graph('update', [zx, zy], block0)
    check_simplify(graph, """\
zx = Argument('zx', SmallFixedBitVector(64))
zy = Argument('zy', SmallFixedBitVector(64))
block0 = Block()
i2 = block0.emit(Operation, '@add_bits_bv_bv', [zx, zy, MachineIntConstant(64)], SmallFixedBitVector(64), '`25 286:37-286:63', 'zz422')
block0.next = Return(i2, None)
graph = Graph('update', [zx, zy], block0)""")

def test_append():
    zcreg = Argument('zcreg', SmallFixedBitVector(3))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [SmallBitVectorConstant(0b01, SmallFixedBitVector(2))], GenericBitVector(), '`5 100:30-100:41', 'zz40')
    i2 = block0.emit(Cast, '$cast', [zcreg], GenericBitVector(), '`5 100:30-100:41', 'zz41')
    i3 = block0.emit(Operation, 'append', [i1, i2], GenericBitVector(), '`5 100:30-100:41', 'zz42')
    i4 = block0.emit(Cast, '$cast', [i3], SmallFixedBitVector(5), '`5 100:30-100:41', 'return')
    block0.next = Return(i4, None)
    graph = Graph('zcreg2reg_idx', [zcreg], block0)
    check_simplify(graph, """\
zcreg = Argument('zcreg', SmallFixedBitVector(3))
block0 = Block()
i1 = block0.emit(Operation, '@bitvector_concat_bv_bv', [SmallBitVectorConstant(1, SmallFixedBitVector(2)), MachineIntConstant(3), zcreg], SmallFixedBitVector(5), '`5 100:30-100:41', 'zz42')
block0.next = Return(i1, None)
graph = Graph('zcreg2reg_idx', [zcreg], block0)""")

def test_shiftr():
    for kind in "@shiftr_o_i", "@arith_shiftr_o_i":
        arg = Argument('arg', SmallFixedBitVector(64))
        block0 = Block()
        i1 = block0.emit(Operation, '@vector_subrange_fixed_bv_i_i', [arg, MachineIntConstant(47), MachineIntConstant(0)], SmallFixedBitVector(48), '`3484', 'zz44')
        i2 = block0.emit(Operation, '@zero_extend_bv_i_i', [i1, MachineIntConstant(48), MachineIntConstant(64)], SmallFixedBitVector(64), '`26 426:31-426:66', 'zz449')
        i2 = block0.emit(Cast, '$cast', [i2], GenericBitVector(), None, None)
        i3 = block0.emit(Operation, kind, [i2, MachineIntConstant(1)], GenericBitVector(), '`26 426:31-426:71', 'zz445')
        i4 = block0.emit(Cast, '$cast', [i3], SmallFixedBitVector(64), '`26 426:31-426:71', 'zhtif_exit_code')
        block0.next = Return(i4, None)
        graph = Graph('zcreg2reg_idx', [arg], block0)
        check_simplify(graph, """\
arg = Argument('arg', SmallFixedBitVector(64))
block0 = Block()
i1 = block0.emit(Operation, '@vector_subrange_fixed_bv_i_i', [arg, MachineIntConstant(47), MachineIntConstant(0)], SmallFixedBitVector(48), '`3484', 'zz44')
i2 = block0.emit(Operation, '@zero_extend_bv_i_i', [i1, MachineIntConstant(48), MachineIntConstant(64)], SmallFixedBitVector(64), '`26 426:31-426:66', 'zz449')
i3 = block0.emit(Operation, '%s_bv_i', [i2, MachineIntConstant(64), MachineIntConstant(1)], SmallFixedBitVector(64), '`26 426:31-426:71', 'zz445')
block0.next = Return(i3, None)
graph = Graph('zcreg2reg_idx', [arg], block0)""" % (kind[:-4], ))

def test_int_cmp():
    a1 = Argument('i', SmallFixedBitVector(52))
    a2 = Argument('i', SmallFixedBitVector(52))
    block0 = Block()
    i1 = block0.emit(Operation, '@unsigned_bv', [a1, MachineIntConstant(52)], MachineInt(), '`41 263:11-263:24', 'zz429')
    i2 = block0.emit(Operation, '@unsigned_bv', [a2, MachineIntConstant(52)], MachineInt(), '`41 263:29-263:42', 'zz427')
    i3 = block0.emit(Operation, 'zz5i64zDzKz5i', [i1], Int(), '`41 263:11-263:42', 'zz424')
    i4 = block0.emit(Operation, 'zz5i64zDzKz5i', [i2], Int(), '`41 263:11-263:42', 'zz425')
    i5 = block0.emit(Operation, 'lt', [i3, i4], Bool(), '`41 263:11-263:42', 'zz412')
    block0.next = Return(i5, None)
    graph = Graph('f', [a1, a2], block0)
    check_simplify(graph, """\
i = Argument('i', SmallFixedBitVector(52))
i = Argument('i', SmallFixedBitVector(52))
block0 = Block()
i2 = block0.emit(Operation, '@unsigned_bv', [i, MachineIntConstant(52)], MachineInt(), '`41 263:11-263:24', 'zz429')
i3 = block0.emit(Operation, '@unsigned_bv', [i, MachineIntConstant(52)], MachineInt(), '`41 263:29-263:42', 'zz427')
i4 = block0.emit(Operation, '@lt', [i2, i3], Bool(), '`41 263:11-263:42', 'zz412')
block0.next = Return(i4, None)
graph = Graph('f', [i, i], block0)""")


def test_set_slice():
    zval_name = Argument('zval_name', SmallFixedBitVector(64))
    block0 = Block()
    i1 = block0.emit(Cast, '$cast', [zval_name], GenericBitVector(), '`7 47:10-47:38', 'zz419')
    i2 = block0.emit(Cast, '$cast', [SmallBitVectorConstant(0b00000, SmallFixedBitVector(5))], GenericBitVector(), '`7 47:10-47:38', 'zz420')
    i3 = block0.emit(Operation, '@set_slice_i_i_o_i_o', [MachineIntConstant(64), MachineIntConstant(5), i1, MachineIntConstant(3), i2], GenericBitVector(), '`7 47:10-47:38', 'zz421')
    i4 = block0.emit(Cast, '$cast', [SmallBitVectorConstant(0b0, SmallFixedBitVector(1))], GenericBitVector(), '`7 48:10-48:35', 'zz413')
    i5 = block0.emit(Operation, '@set_slice_i_i_o_i_o', [MachineIntConstant(64), MachineIntConstant(1), i3, MachineIntConstant(14), i4], GenericBitVector(), '`7 48:10-48:35', 'zz414')
    i6 = block0.emit(Cast, '$cast', [SmallBitVectorConstant(0b0000000000000000000000000000000000000, SmallFixedBitVector(37))], GenericBitVector(), '`7 49:10-49:72', 'zz46')
    i7 = block0.emit(Operation, '@set_slice_i_i_o_i_o', [MachineIntConstant(64), MachineIntConstant(37), i5, MachineIntConstant(27), i6], GenericBitVector(), '`7 49:10-49:72', 'zz47')
    i8 = block0.emit(Cast, '$cast', [i7], SmallFixedBitVector(64), '`7 49:10-49:72', 'zz40')
    block0.next = Return(i8, None)
    graph = Graph('z__get_FPCR', [zval_name], block0)
    check_simplify(graph, """\
zval_name = Argument('zval_name', SmallFixedBitVector(64))
block0 = Block()
i1 = block0.emit(Operation, '@vector_update_subrange_fixed_bv_i_i_bv', [zval_name, MachineIntConstant(7), MachineIntConstant(3), SmallBitVectorConstant(0, SmallFixedBitVector(5))], SmallFixedBitVector(64), '`7 47:10-47:38', 'zz421')
i2 = block0.emit(Operation, '@vector_update_subrange_fixed_bv_i_i_bv', [i1, MachineIntConstant(14), MachineIntConstant(14), SmallBitVectorConstant(0, SmallFixedBitVector(1))], SmallFixedBitVector(64), '`7 48:10-48:35', 'zz414')
i3 = block0.emit(Operation, '@vector_update_subrange_fixed_bv_i_i_bv', [i2, MachineIntConstant(63), MachineIntConstant(27), SmallBitVectorConstant(0, SmallFixedBitVector(37))], SmallFixedBitVector(64), '`7 49:10-49:72', 'zz47')
block0.next = Return(i3, None)
graph = Graph('z__get_FPCR', [zval_name], block0)""")

def test_zero_extend_unwrapped_res():
    value = Argument('value', GenericBitVector())
    block0 = Block()
    i0 = block0.emit(Operation, '@zero_extend_o_i', [value, MachineIntConstant(64)], GenericBitVector(), '`5 234:29-234:46', 'return')
    i1 = block0.emit(Cast, '$cast', [i0], SmallFixedBitVector(64), '`7 3419:16-3419:38', 'zz42')
    block0.next = Return(i1, None)
    graph = Graph('f', [value], block0)
    check_simplify(graph, """\
value = Argument('value', GenericBitVector())
block0 = Block()
i1 = block0.emit(Operation, '@zero_extend_o_i_unwrapped_res', [value, MachineIntConstant(64)], SmallFixedBitVector(64), '`5 234:29-234:46', 'return')
block0.next = Return(i1, None)
graph = Graph('f', [value], block0)""")

def test_sign_extend_unwrapped_res():
    value = Argument('value', GenericBitVector())
    block0 = Block()
    i0 = block0.emit(Operation, '@sign_extend_o_i', [value, MachineIntConstant(64)], GenericBitVector(), '`5 234:29-234:46', 'return')
    i1 = block0.emit(Cast, '$cast', [i0], SmallFixedBitVector(64), '`7 3419:16-3419:38', 'zz42')
    block0.next = Return(i1, None)
    graph = Graph('f', [value], block0)
    check_simplify(graph, """\
value = Argument('value', GenericBitVector())
block0 = Block()
i1 = block0.emit(Operation, '@sign_extend_o_i_unwrapped_res', [value, MachineIntConstant(64)], SmallFixedBitVector(64), '`5 234:29-234:46', 'return')
block0.next = Return(i1, None)
graph = Graph('f', [value], block0)""")

def test_vector_update_list():
    index = Argument('index', MachineInt())
    block0 = Block()
    i6 = block0.emit(GlobalRead, 'z_R', [], FVec(31, SmallFixedBitVector(64)), None, None)
    i7 = block0.emit(Cast, '$cast', [i6], Vec(SmallFixedBitVector(64)), '`7 1087:12-1087:17', 'zz416')
    i8 = block0.emit(Operation, '@vector_update_o_i_o', [i7, index, SmallBitVectorConstant(0b01, SmallFixedBitVector(2))], Vec(SmallFixedBitVector(64)), '`7 1087:12-1087:17', 'zz418')
    i9 = block0.emit(Cast, '$cast', [i8], FVec(31, SmallFixedBitVector(64)), '`7 1087:12-1087:17', 'z_R')
    block0.emit(GlobalWrite, 'z_R', [i9], FVec(31, SmallFixedBitVector(64)), None, None)
    block0.next = Return(None, None)
    graph = Graph('f', [index], block0)
    check_simplify(graph, """\
index = Argument('index', MachineInt())
block0 = Block()
i1 = block0.emit(GlobalRead, 'z_R', [], FVec(31, SmallFixedBitVector(64)), None, None)
i2 = block0.emit(Cast, '$cast', [i1], Vec(SmallFixedBitVector(64)), '`7 1087:12-1087:17', 'zz416')
i3 = block0.emit(Operation, '@helper_vector_update_inplace_o_i_o', [i2, index, SmallBitVectorConstant(1, SmallFixedBitVector(2))], Unit(), '`7 1087:12-1087:17', 'zz418')
block0.next = Return(None, None)
graph = Graph('f', [index], block0)""")

def test_fill_fresh_vector():
    block0 = Block()
    i1 = block0.emit(VectorInit, '$zinternal_vector_init', [MachineIntConstant(3)], Vec(MachineInt()), '`41 765:95-765:126', None)
    i2 = block0.emit(VectorUpdate, '$zinternal_vector_update', [i1, MachineIntConstant(0), MachineIntConstant(5)], Vec(MachineInt()), None, None)
    i3 = block0.emit(VectorUpdate, '$zinternal_vector_update', [i2, MachineIntConstant(1), MachineIntConstant(7)], Vec(MachineInt()), None, None)
    i4 = block0.emit(VectorUpdate, '$zinternal_vector_update', [i3, MachineIntConstant(2), MachineIntConstant(9)], Vec(MachineInt()), None, None)
    i5 = block0.emit(Operation, 'zvalidDoubleRegs', [IntConstant(3), i4], Bool(), '`41 765:95-765:126', 'zz46820')
    block0.next = Return(i5, None)
    graph = Graph('f', [], block0)
    check_simplify(graph, """\
block0 = Block()
i0 = block0.emit(VectorInit, '$zinternal_vector_init', [MachineIntConstant(3)], Vec(MachineInt()), '`41 765:95-765:126', None)
i1 = block0.emit(Operation, '@helper_vector_update_inplace_o_i_o', [i0, MachineIntConstant(0), MachineIntConstant(5)], Unit(), None, None)
i2 = block0.emit(Operation, '@helper_vector_update_inplace_o_i_o', [i0, MachineIntConstant(1), MachineIntConstant(7)], Unit(), None, None)
i3 = block0.emit(Operation, '@helper_vector_update_inplace_o_i_o', [i0, MachineIntConstant(2), MachineIntConstant(9)], Unit(), None, None)
i4 = block0.emit(Operation, 'zvalidDoubleRegs', [IntConstant(3), i0], Bool(), '`41 765:95-765:126', 'zz46820')
block0.next = Return(i4, None)
graph = Graph('f', [], block0)""")

def test_mult_1():
    index = Argument('index', Int())
    block0 = Block()
    i1 = block0.emit(Operation, 'mult_int', [index, IntConstant(1)], Int(), '`7 14894:55-14894:60', 'zz422')
    block0.next = Return(i1, None)
    graph = Graph('f', [index], block0)
    check_simplify(graph, """\
index = Argument('index', Int())
block0 = Block()
block0.next = Return(index, None)
graph = Graph('f', [index], block0)""")

def test_mult_to_shift():
    index = Argument('index', Int())
    block0 = Block()
    i1 = block0.emit(Operation, 'mult_int', [IntConstant(8), index], Int(), '`7 14894:55-14894:60', 'zz422')
    block0.next = Return(i1, None)
    graph = Graph('f', [index], block0)
    check_simplify(graph, """\
index = Argument('index', Int())
block0 = Block()
i1 = block0.emit(Operation, '@shl_int_o_i', [index, MachineIntConstant(3)], Int(), '`7 14894:55-14894:60', 'zz422')
block0.next = Return(i1, None)
graph = Graph('f', [index], block0)""")

def test_mult_constfold():
    index = Argument('index', Int())
    block0 = Block()
    i1 = block0.emit(Operation, 'mult_int', [IntConstant(12), IntConstant(2)], Int(), '`7 14894:55-14894:60', 'zz422')
    block0.next = Return(i1, None)
    graph = Graph('f', [index], block0)
    check_simplify(graph, """\
index = Argument('index', Int())
block0 = Block()
block0.next = Return(IntConstant(24), None)
graph = Graph('f', [index], block0)""")

def test_neg_constfold():
    index = Argument('index', Int())
    block0 = Block()
    i1 = block0.emit(Operation, 'neg_int', [IntConstant(12)], Int(), '`7 14894:55-14894:60', 'zz422')
    block0.next = Return(i1, None)
    graph = Graph('f', [index], block0)
    check_simplify(graph, """\
index = Argument('index', Int())
block0 = Block()
block0.next = Return(IntConstant(-12), None)
graph = Graph('f', [index], block0)""")

def test_ediv_constfold():
    block0 = Block()
    i1 = block0.emit(Operation, 'ediv_int', [IntConstant(128), IntConstant(2)], Int(), '`7 11526:20-11526:32', 'zz4179')
    block0.next = Return(i1, None)
    graph = Graph('f', [], block0)
    check_simplify(graph, """\
block0 = Block()
block0.next = Return(IntConstant(64), None)
graph = Graph('f', [], block0)""")

def test_pow_i():
    block0 = Block()
    i1 = block0.emit(Operation, '@pow2_i', [MachineIntConstant(32)], Int(), '`7 150231:75-150231:81', 'zz492')
    block0.next = Return(i1, None)
    graph = Graph('f', [], block0)
    check_simplify(graph, """\
block0 = Block()
block0.next = Return(IntConstant(4294967296), None)
graph = Graph('f', [], block0)""")

def test_simplify_loop_phi():
    zxs = Argument('zxs', SmallFixedBitVector(8))
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    block0.next = Goto(block1, None)
    i1 = block1.emit_phi([block0, block3], [zxs, None], SmallFixedBitVector(8))
    i1.prevvalues[1] = i1
    i2 = block1.emit_phi([block0, block3], [SmallBitVectorConstant(0x00, SmallFixedBitVector(8)), None], SmallFixedBitVector(8))
    i4 = block1.emit_phi([block0, block3], [MachineIntConstant(7), None], MachineInt())
    i4.prevvalues[1] = i4
    i5 = block1.emit_phi([block0, block3], [MachineIntConstant(1), None], MachineInt())
    i5.prevvalues[1] = i5
    i6 = block1.emit_phi([block0, block3], [MachineIntConstant(0), None], MachineInt())
    i8 = block1.emit(Operation, '@gt', [i6, i4], Bool(), '`1 279:2-280:19', None)
    block1.next = ConditionalGoto(i8, block2, block3, '`1 279:2-280:19')
    block2.next = Return(i2, None)
    i9 = block3.emit(Operation, '@sub_i_i_wrapped_res', [MachineIntConstant(7), i6], Int(), '`1 280:15-280:18', 'zz416')
    i10 = block3.emit(Operation, 'zz5izDzKz5i64', [i9], MachineInt(), None, None)
    i11 = block3.emit(Operation, '@vector_access_bv_i', [i1, i10], Bit(), '`1 280:12-280:19', 'zz47')
    i12 = block3.emit(Cast, '$cast', [i2], GenericBitVector(), '`1 280:4-280:9', 'zz48')
    i13 = block3.emit(Operation, '@vector_update_o_i_o', [i12, i6, i11], GenericBitVector(), '`1 280:4-280:9', 'zz410')
    i3 = block3.emit(Cast, '$cast', [i13], SmallFixedBitVector(8), '`1 280:4-280:9', 'zz40')
    i2.prevvalues[1] = i3
    i7 = block3.emit(Operation, '@iadd', [i6, i5], MachineInt(), '`1 279:2-280:19', 'zz45')
    i6.prevvalues[1] = i7
    block3.next = Goto(block1, None)
    graph = Graph('zreverse_bits_in_byte', [zxs], block0, True)
    check_simplify(graph, """\
zxs = Argument('zxs', SmallFixedBitVector(8))
block0 = Block()
block1 = Block()
block2 = Block()
block3 = Block()
block0.next = Goto(block1, None)
i1 = block1.emit_phi([block0, block3], [SmallBitVectorConstant(0, SmallFixedBitVector(8)), None], SmallFixedBitVector(8))
i2 = block1.emit_phi([block0, block3], [MachineIntConstant(0), None], MachineInt())
i3 = block1.emit(Operation, '@gt', [i2, MachineIntConstant(7)], Bool(), '`1 279:2-280:19', None)
block1.next = ConditionalGoto(i3, block2, block3, '`1 279:2-280:19')
block2.next = Return(i1, None)
i4 = block3.emit(Operation, '@sub_i_i_wrapped_res', [MachineIntConstant(7), i2], Int(), '`1 280:15-280:18', 'zz416')
i5 = block3.emit(Operation, 'zz5izDzKz5i64', [i4], MachineInt(), None, None)
i6 = block3.emit(Operation, '@vector_access_bv_i', [zxs, i5], Bit(), '`1 280:12-280:19', 'zz47')
i7 = block3.emit(Cast, '$cast', [i1], GenericBitVector(), '`1 280:4-280:9', 'zz48')
i8 = block3.emit(Operation, '@vector_update_o_i_o', [i7, i2, i6], GenericBitVector(), '`1 280:4-280:9', 'zz410')
i9 = block3.emit(Cast, '$cast', [i8], SmallFixedBitVector(8), '`1 280:4-280:9', 'zz40')
i1.prevvalues[1] = i9
i10 = block3.emit(Operation, '@iadd', [i2, MachineIntConstant(1)], MachineInt(), '`1 279:2-280:19', 'zz45')
i2.prevvalues[1] = i10
block3.next = Goto(block1, None)
graph = Graph('zreverse_bits_in_byte', [zxs], block0)""")


def test_complicated_inlining():
    codegen = FakeCodeGen()
    zlen = Argument('zlen', Int())
    zv = Argument('zv', GenericBitVector())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    i2 = block0.emit(Operation, '@length_unwrapped_res', [zv], MachineInt(), '`2 141:39-141:48', 'zz41')
    i3 = block0.emit(Operation, 'zz5i64zDzKz5i', [i2], Int(), '`2 141:39-141:48', None)
    i4 = block0.emit(Operation, 'zlteq_int', [zlen, i3], Bool(), '`2 141:32-141:48', 'zz40')
    block0.next = ConditionalGoto(i4, block1, block3, '`2 141:29-141:100')
    i5 = block1.emit(Operation, 'zz5izDzKz5i64', [zlen], MachineInt(), None, None)
    i6 = block1.emit(Operation, '@sail_truncate_o_i', [zv, i5], GenericBitVector(), '`2 141:54-141:70', 'return')
    block1.next = Goto(block2, None)
    i7 = block2.emit_phi([block3, block1], [None, i6], GenericBitVector())
    block2.next = Return(i7, None)
    i8 = block3.emit(Operation, 'zz5izDzKz5i64', [zlen], MachineInt(), None, None)
    i9 = block3.emit(Operation, '@zero_extend_o_i', [zv, i8], GenericBitVector(), '`2 141:76-141:100', 'return')
    i7.prevvalues[0] = i9
    block3.next = Goto(block2, None)
    graph1 = Graph('zsail_mask', [zlen, zv], block0)
    
    zn = Argument('zn', Int())
    zi = Argument('zi', Int())
    zl = Argument('zl', Int())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    i3 = block0.emit(Operation, 'zgteq_int', [zl, zn], Bool(), '`2 336:5-336:11', 'zz40')
    block0.next = ConditionalGoto(i3, block1, block3, '`2 336:2-341:3')
    i4 = block1.emit(Comment, 'inlined zsail_ones', [], Unit(), None, None)
    i5 = block1.emit(Operation, 'zz5izDzKz5i64', [zn], MachineInt(), None, None)
    i6 = block1.emit(Operation, '@zeros_i', [i5], GenericBitVector(), '`2 320:32-320:45', 'zz40')
    i7 = block1.emit(Operation, 'znot_vec', [i6], GenericBitVector(), '`2 320:24-320:46', 'return')
    i8 = block1.emit(Operation, 'zz5izDzKz5i64', [zi], MachineInt(), None, None)
    i9 = block1.emit(Operation, '@shiftl_o_i', [i7, i8], GenericBitVector(), '`2 337:4-337:35', 'return')
    block1.next = Goto(block2, None)
    i10 = block2.emit_phi([block3, block1], [None, i9], GenericBitVector())
    block2.next = Return(i10, None)
    i11 = block3.emit(Cast, '$cast', [SmallBitVectorConstant(0b1, SmallFixedBitVector(1))], GenericBitVector(), '`2 339:25-339:57', 'zz46')
    i12 = block3.emit(Operation, 'zsail_mask', [zn, i11], GenericBitVector(), '`2 339:25-339:57', 'zz42')
    i13 = block3.emit(Operation, 'zz5izDzKz5i64', [zl], MachineInt(), None, None)
    i14 = block3.emit(Operation, '@shiftl_o_i', [i12, i13], GenericBitVector(), '`2 340:28-340:50', 'zz44')
    i15 = block3.emit(Operation, 'zsub_bits', [i14, i12], GenericBitVector(), '`2 340:19-340:56', 'zz43')
    i16 = block3.emit(Operation, 'zz5izDzKz5i64', [zi], MachineInt(), None, None)
    i17 = block3.emit(Operation, '@shiftl_o_i', [i15, i16], GenericBitVector(), '`2 340:4-340:60', 'return')
    i10.prevvalues[0] = i17
    block3.next = Goto(block2, None)
    graph = Graph('zslice_mask', [zn, zi, zl], block0)
    codegen.inlinable_functions['zsail_mask'] = graph1
    inline(graph, codegen)
    res = print_graph_construction(graph)
    got = "\n".join(res)
    assert got == '''\
zn = Argument('zn', Int())
zi = Argument('zi', Int())
zl = Argument('zl', Int())
block0 = Block()
block1 = Block()
block2 = Block()
block3 = Block()
block4 = Block()
block5 = Block()
block6 = Block()
i3 = block0.emit(Operation, 'zgteq_int', [zl, zn], Bool(), '`2 336:5-336:11', 'zz40')
block0.next = ConditionalGoto(i3, block1, block3, '`2 336:2-341:3')
i4 = block1.emit(Comment, 'inlined zsail_ones', [], Unit(), None, None)
i5 = block1.emit(Operation, 'zz5izDzKz5i64', [zn], MachineInt(), None, None)
i6 = block1.emit(Operation, '@zeros_i', [i5], GenericBitVector(), '`2 320:32-320:45', 'zz40')
i7 = block1.emit(Operation, 'znot_vec', [i6], GenericBitVector(), '`2 320:24-320:46', 'return')
i8 = block1.emit(Operation, 'zz5izDzKz5i64', [zi], MachineInt(), None, None)
i9 = block1.emit(Operation, '@shiftl_o_i', [i7, i8], GenericBitVector(), '`2 337:4-337:35', 'return')
block1.next = Goto(block2, None)
i10 = block2.emit_phi([block5, block1], [None, i9], GenericBitVector())
block2.next = Return(i10, None)
i11 = block3.emit(Cast, '$cast', [SmallBitVectorConstant(1, SmallFixedBitVector(1))], GenericBitVector(), '`2 339:25-339:57', 'zz46')
i12 = block3.emit(Comment, 'inlined zsail_mask', [], Unit(), None, None)
i13 = block3.emit(Operation, '@length_unwrapped_res', [i11], MachineInt(), '`2 141:39-141:48', 'zz41')
i14 = block3.emit(Operation, 'zz5i64zDzKz5i', [i13], Int(), '`2 141:39-141:48', None)
i15 = block3.emit(Operation, 'zlteq_int', [zn, i14], Bool(), '`2 141:32-141:48', 'zz40')
block3.next = ConditionalGoto(i15, block4, block6, '`2 141:29-141:100')
i16 = block4.emit(Operation, 'zz5izDzKz5i64', [zn], MachineInt(), None, None)
i17 = block4.emit(Operation, '@sail_truncate_o_i', [i11, i16], GenericBitVector(), '`2 141:54-141:70', 'return')
block4.next = Goto(block5, None)
i18 = block5.emit_phi([block6, block4], [None, i17], GenericBitVector())
i19 = block5.emit(Operation, 'zz5izDzKz5i64', [zl], MachineInt(), None, None)
i20 = block5.emit(Operation, '@shiftl_o_i', [i18, i19], GenericBitVector(), '`2 340:28-340:50', 'zz44')
i21 = block5.emit(Operation, 'zsub_bits', [i20, i18], GenericBitVector(), '`2 340:19-340:56', 'zz43')
i22 = block5.emit(Operation, 'zz5izDzKz5i64', [zi], MachineInt(), None, None)
i23 = block5.emit(Operation, '@shiftl_o_i', [i21, i22], GenericBitVector(), '`2 340:4-340:60', 'return')
i10.prevvalues[0] = i23
block5.next = Goto(block2, None)
i24 = block6.emit(Operation, 'zz5izDzKz5i64', [zn], MachineInt(), None, None)
i25 = block6.emit(Operation, '@zero_extend_o_i', [i11, i24], GenericBitVector(), '`2 141:76-141:100', 'return')
i18.prevvalues[0] = i25
block6.next = Goto(block5, None)
graph = Graph('zslice_mask', [zn, zi, zl], block0)'''


def test_toposort():
    zp = Argument('zp', SmallFixedBitVector(2))
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    block4 = Block()
    block5 = Block()
    block6 = Block()
    block7 = Block()
    i1 = block0.emit(Operation, '@eq_bits_bv_bv', [zp, SmallBitVectorConstant(0b00, SmallFixedBitVector(2))], Bool(), '`5 170:4-170:8', 'zz414')
    block0.next = ConditionalGoto(i1, block1, block3, '`5 169:2-174:3')
    i2 = block1.emit(GlobalRead, 'zUser', [], Int(), None, None)
    block1.next = Goto(block2, None)
    i4 = block2.emit_phi([block1, block4, block6, block7], [i2, None, None, None], Int())
    block2.next = Return(i4, None)
    i5 = block3.emit(Operation, '@eq_bits_bv_bv', [zp, SmallBitVectorConstant(0b01, SmallFixedBitVector(2))], Bool(), '`5 171:4-171:8', 'zz410')
    block3.next = ConditionalGoto(i5, block4, block5, '`5 169:2-174:3')
    i6 = block4.emit(GlobalRead, 'zSupervisor', [], Int(), None, None)
    i4.prevvalues[1] = i6
    block4.next = Goto(block2, None)
    i8 = block5.emit(Operation, '@eq_bits_bv_bv', [zp, SmallBitVectorConstant(0b11, SmallFixedBitVector(2))], Bool(), '`5 172:4-172:8', 'zz46')
    block5.next = ConditionalGoto(i8, block6, block7, '`5 169:2-174:3')
    i9 = block6.emit(GlobalRead, 'zMachine', [], Int(), None, None)
    i4.prevvalues[2] = i9
    block6.next = Goto(block2, None)
    i11 = block7.emit(Cast, '$cast', [zp], GenericBitVector(), '`5 173:77-173:86', 'zz44')
    i12 = block7.emit(Operation, 'zstring_of_bits', [i11], String(), '`5 173:77-173:86', 'zz43')
    i14 = block7.emit(Operation, 'zinternal_errorzIEPrivilegez5zK', [], Int(), '`5 173:12-173:87', 'zz40')
    i4.prevvalues[3] = i14
    block7.next = Goto(block2, None)
    graph = Graph('zprivLevel_of_bits', [zp], block0)

    assert set(topo_order(graph)) == set(graph.iterblocks())
