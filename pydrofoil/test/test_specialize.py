from pydrofoil.types import *
from pydrofoil.ir import *
from pydrofoil.specialize import usefully_specializable, Specializer
from pydrofoil.specialize import SpecializingOptimizer

class FakeCodeGen:
    def __init__(self):
        self.builtin_names = {"zz5izDzKz5i64": "int_to_int64", "zz5i64zDzKz5i": "int64_to_int"}
        self.inlinable_functions = {}
        self.specialization_functions = {}

def test_specialize():
    fakecodegen = FakeCodeGen()
    zxs = Argument('zxs', GenericBitVector())
    zi = Argument('zi', Int())
    zj = Argument('zj', Int())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    block4 = Block()
    block5 = Block()
    block6 = Block()
    block7 = Block()
    block8 = Block()
    block9 = Block()
    i3 = block0.emit(Operation, '@length_unwrapped_res', [zxs], MachineInt(), '`1', 'zz46')
    i4 = block0.emit(Operation, 'zz5i64zDzKz5i', [i3], Int(), '`1', None)
    i5 = block0.emit(Operation, 'zz5izDzKz5i64', [zj], MachineInt(), None, None)
    i6 = block0.emit(Operation, '@sub_o_i_wrapped_res', [zi, i5], Int(), '`4 102:22-102:25', 'zz48')
    i7 = block0.emit(Operation, '@add_o_i_wrapped_res', [i6, MachineIntConstant(1)], Int(), '`4 102:22-102:27', 'zz47')
    i8 = block0.emit(Comment, 'inlined zslice_mask', [], Unit(), None, None)
    i9 = block0.emit(Operation, 'zgteq_int', [i7, i4], Bool(), '`2 336:5-336:11', 'zz40')
    block0.next = ConditionalGoto(i9, block1, block6, '`2 336:2-341:3')
    i10 = block1.emit(Comment, 'inlined zsail_ones', [], Unit(), None, None)
    i11 = block1.emit(Operation, '@zeros_i', [i3], GenericBitVector(), '`2 320:32-320:45', 'zz40')
    i12 = block1.emit(Operation, 'znot_vec', [i11], GenericBitVector(), '`2 320:24-320:46', 'return')
    i13 = block1.emit(Operation, '@shiftl_o_i', [i12, i5], GenericBitVector(), '`2 337:4-337:35', 'return')
    block1.next = Goto(block2, None)
    i14 = block2.emit_phi([block8, block1], [None, i13], GenericBitVector())
    i15 = block2.emit(Operation, 'zand_vec', [zxs, i14], GenericBitVector(), '`4 102:3-102:28', 'zz40')
    i16 = block2.emit(Cast, '$cast', [SmallBitVectorConstant('0b0', SmallFixedBitVector(1))], GenericBitVector(), '`4 102:33-102:59', 'zz44')
    i17 = block2.emit(Comment, 'inlined zextzzv', [], Unit(), None, None)
    i18 = block2.emit(Operation, '@lt', [i3, MachineIntConstant(1)], Bool(), '`4 80:5-80:11', 'zz40')
    block2.next = ConditionalGoto(i18, block3, block5, '`4 80:2-80:59')
    i19 = block3.emit(Operation, '@sail_truncate_o_i', [i16, i3], GenericBitVector(), '`4 80:17-80:31', 'return')
    block3.next = Goto(block4, None)
    i20 = block4.emit_phi([block5, block3], [None, i19], GenericBitVector())
    i21 = block4.emit(Operation, 'zeq_bits', [i15, i20], Bool(), '`4 102:2-102:59', 'return')
    block4.next = Return(i21, None)
    i22 = block5.emit(Operation, '@zero_extend_o_i', [i16, i3], GenericBitVector(), '`4 80:37-80:59', 'return')
    i20.prevvalues[0] = i22
    block5.next = Goto(block4, None)
    i23 = block6.emit(Cast, '$cast', [SmallBitVectorConstant('0b1', SmallFixedBitVector(1))], GenericBitVector(), '`2 339:25-339:57', 'zz46')
    i24 = block6.emit(Comment, 'inlined zsail_mask', [], Unit(), None, None)
    i25 = block6.emit(Operation, '@lteq', [i3, MachineIntConstant(1)], Bool(), '`2 141:32-141:48', 'zz40')
    block6.next = ConditionalGoto(i25, block7, block9, '`2 141:29-141:100')
    i26 = block7.emit(Operation, '@sail_truncate_o_i', [i23, i3], GenericBitVector(), '`2 141:54-141:70', 'return')
    block7.next = Goto(block8, None)
    i27 = block8.emit_phi([block9, block7], [None, i26], GenericBitVector())
    i28 = block8.emit(Operation, 'zz5izDzKz5i64', [i7], MachineInt(), None, None)
    i29 = block8.emit(Operation, '@shiftl_o_i', [i27, i28], GenericBitVector(), '`2 340:28-340:50', 'zz44')
    i30 = block8.emit(Operation, 'zsub_bits', [i29, i27], GenericBitVector(), '`2 340:19-340:56', 'zz43')
    i31 = block8.emit(Operation, '@shiftl_o_i', [i30, i5], GenericBitVector(), '`2 340:4-340:60', 'return')
    i14.prevvalues[0] = i31
    block8.next = Goto(block2, None)
    i32 = block9.emit(Operation, '@zero_extend_o_i', [i23, i3], GenericBitVector(), '`2 141:76-141:100', 'return')
    i27.prevvalues[0] = i32
    block9.next = Goto(block8, None)
    graph = Graph('zis_zzero_subrange', [zxs, zi, zj], block0)
    assert usefully_specializable(graph)

    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions['zis_zzero_subrange'] = spec

    # construct the calling graph
    block = Block()
    bv = Argument('bv', SmallFixedBitVector(52))
    i = Argument('i', Int())
    i2 = block.emit(Cast, '$cast', [bv], GenericBitVector(), None, None)
    i3 = block.emit(Operation, 'zis_zzero_subrange', [i2, IntConstant(51), i], Bool(), None, None)
    block.next = Return(i3)
    calling_graph = Graph("zf", [bv, i], block)
    opt = SpecializingOptimizer(calling_graph, fakecodegen)
    opt.optimize()
    simplify(calling_graph, fakecodegen)

    op = block.operations[0]
    assert op.name == 'zis_zzero_subrange_specialized_bv52_i_o'
    assert op.args[0] == bv
    assert type(op.args[1]) is MachineIntConstant
    assert op.args[1].number == 51
    assert op.args[2] == i