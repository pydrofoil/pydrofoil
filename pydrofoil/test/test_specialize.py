from pydrofoil.types import *
from pydrofoil.ir import *
from pydrofoil.specialize import usefully_specializable, Specializer
from pydrofoil.specialize import SpecializingOptimizer

class FakeCodeGen:
    def __init__(self):
        self.builtin_names = {"zz5izDzKz5i64": "int_to_int64", "zz5i64zDzKz5i": "int64_to_int"}
        self.inlinable_functions = {}
        self.specialization_functions = {}

    def emit_extra_graph(self, graph, typ):
        pass

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
    optimize(calling_graph, fakecodegen)

    op = block.operations[1]
    assert op.name == 'zis_zzero_subrange_specialized_bv52_51_i'
    assert op.args[0] == bv
    assert type(op.args[1]) is MachineIntConstant
    assert op.args[1].number == 51
    assert op.args[2].args[0] == i

def test_specialize_bool_value():
    zcond = Argument('zcond', Bool())
    block6 = Block()
    block8 = Block()
    block9 = Block()
    block10 = Block()
    block8.next = ConditionalGoto(zcond, block9, block10, '`7 2013:10-2017:11')
    i14 = block6.emit_phi([block9, block10], [None, None], Bool())
    block6.next = Return(i14, None)
    i21 = block9.emit(GlobalRead, 'zBRBFCR_EL1', [], SmallFixedBitVector(64), None, None)
    i22 = block9.emit(Operation, '@slice_fixed_bv_i_i', [i21, MachineIntConstant(22), MachineIntConstant(1)], SmallFixedBitVector(1), '`7 2014:21-2014:45', 'zz427')
    i23 = block9.emit(GlobalRead, 'zBRBFCR_EL1', [], SmallFixedBitVector(64), None, None)
    i24 = block9.emit(Operation, '@slice_fixed_bv_i_i', [i23, MachineIntConstant(16), MachineIntConstant(1)], SmallFixedBitVector(1), '`7 2014:49-2014:73', 'zz423')
    i25 = block9.emit(Operation, '@eq_bits_bv_bv', [i22, i24], Bool(), '`7 2014:21-2014:73', 'zz415')
    i26 = block9.emit(Operation, '@not', [i25], Bool(), None, None)
    i14.prevvalues[0] = i26
    block9.next = Goto(block6, None)
    i27 = block10.emit(GlobalRead, 'zBRBFCR_EL1', [], SmallFixedBitVector(64), None, None)
    i28 = block10.emit(Operation, '@slice_fixed_bv_i_i', [i27, MachineIntConstant(17), MachineIntConstant(1)], SmallFixedBitVector(1), '`7 2016:21-2016:45', 'zz440')
    i29 = block10.emit(GlobalRead, 'zBRBFCR_EL1', [], SmallFixedBitVector(64), None, None)
    i30 = block10.emit(Operation, '@slice_fixed_bv_i_i', [i29, MachineIntConstant(16), MachineIntConstant(1)], SmallFixedBitVector(1), '`7 2016:49-2016:73', 'zz436')
    i31 = block10.emit(Operation, '@eq_bits_bv_bv', [i28, i30], Bool(), '`7 2016:21-2016:73', 'zz428')
    i32 = block10.emit(Operation, '@not', [i31], Bool(), None, None)
    i14.prevvalues[1] = i32
    block10.next = Goto(block6, None)
    graph = Graph('filter', [zcond], block8)

    assert usefully_specializable(graph)

    fakecodegen = FakeCodeGen()
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions['filter'] = spec

    block = Block()
    i3 = block.emit(Operation, 'filter', [BooleanConstant.TRUE], Bool(), None, None)
    block.next = Return(i3)
    calling_graph = Graph("call_filter", [], block)
    opt = SpecializingOptimizer(calling_graph, fakecodegen)
    opt.optimize()
    (specialized_graph, _), = spec.cache.values()
    assert len(list(specialized_graph.iterblocks())) == 1


def test_specialize_on_result():
    zx = Argument('zx', GenericBitVector())
    zshift = Argument('zshift', Int())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    i2 = block0.emit(Operation, '@eq_int_o_i', [zshift, MachineIntConstant(0)], Bool(), '`7 433:7-433:17', 'zz40')
    block0.next = ConditionalGoto(i2, block1, block3, '`7 433:4-434:59')
    block1.next = Goto(block2, None)
    i3 = block2.emit_phi([block3, block1], [None, zx], GenericBitVector())
    block2.next = Return(i3, None)
    i4 = block3.emit(Operation, '@length_unwrapped_res', [zx], MachineInt(), '`7 434:26-434:28', 'zz48')
    i5 = block3.emit(Operation, 'zz5i64zDzKz5i', [i4], Int(), '`7 434:26-434:28', None)
    i6 = block3.emit(Operation, 'emod_int', [zshift, i5], Int(), '`7 434:15-434:29', 'zz41')
    i7 = block3.emit(Operation, 'zz5izDzKz5i64', [i6], MachineInt(), None, None)
    i8 = block3.emit(Operation, '@shiftr_o_i', [zx, i7], GenericBitVector(), '`7 434:33-434:42', 'zz44')
    i9 = block3.emit(Operation, '@sub_i_i_wrapped_res', [i4, i7], Int(), '`7 434:52-434:58', 'zz46')
    i10 = block3.emit(Operation, 'zz5izDzKz5i64', [i9], MachineInt(), None, None)
    i11 = block3.emit(Operation, '@shiftl_o_i', [zx, i10], GenericBitVector(), '`7 434:45-434:59', 'zz45')
    i12 = block3.emit(Operation, 'or_bits', [i8, i11], GenericBitVector(), '`7 434:33-434:59', 'zz42')
    i3.prevvalues[0] = i12
    block3.next = Goto(block2, None)
    graph = Graph('zROR', [zx, zshift], block0)

    fakecodegen = FakeCodeGen()
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions['zROR'] = spec

    zx = Argument('zx', SmallFixedBitVector(32))
    block0 = Block()
    i0 = block0.emit(Cast, '$cast', [zx], GenericBitVector(), None, None)
    i1 = block0.emit(Operation, 'zROR', [i0, IntConstant(2)], GenericBitVector(), '`7 456:19-456:28', 'zz419')
    i2 = block0.emit(Cast, '$cast', [i1], SmallFixedBitVector(32), '`7 456:19-456:28', 'zz419')
    block0.next = Return(i2, None)
    calling_graph = Graph('f', [zx], block0)
    opt = SpecializingOptimizer(calling_graph, fakecodegen)
    opt.optimize()
    optimize(calling_graph, fakecodegen)
    op = calling_graph.startblock.operations[0]
    assert op.name == "zROR_specialized_bv32_2__bv32"
    assert calling_graph.startblock.next.value is op
    (specialized_graph, _), = spec.cache.values()


def test_argument_demand_casts():
    zlen = Argument('zlen', Int())
    zv = Argument('zv', GenericBitVector())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    i2 = block0.emit(Operation, '@length_unwrapped_res', [zv], MachineInt(), '`2 141:39-141:48', 'zz41')
    i3 = block0.emit(Operation, 'zz5izDzKz5i64', [zlen], MachineInt(), None, None)
    i4 = block0.emit(Operation, '@lteq', [i3, i2], Bool(), '`2 141:32-141:48', 'zz40')
    block0.next = ConditionalGoto(i4, block1, block3, '`2 141:29-141:100')
    i5 = block1.emit(Operation, '@sail_truncate_o_i', [zv, i3], GenericBitVector(), '`2 141:54-141:70', 'return')
    block1.next = Goto(block2, None)
    i6 = block2.emit_phi([block3, block1], [None, i5], GenericBitVector())
    block2.next = Return(i6, None)
    i7 = block3.emit(Operation, '@zero_extend_o_i', [zv, i3], GenericBitVector(), '`2 141:76-141:100', 'return')
    i6.prevvalues[0] = i7
    block3.next = Goto(block2, None)
    graph = Graph('mask', [zlen, zv], block0)

    fakecodegen = FakeCodeGen()
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions['mask'] = spec

    a = Argument('a', Int())
    bv = Argument('bv', GenericBitVector())
    block0 = Block()
    i1 = block0.emit(Operation, 'mask', [a, bv], GenericBitVector(), '`7 456:19-456:28', 'zz419')
    block0.next = Return(i1, None)
    calling_graph = Graph('f', [a, bv], block0)

    optimize(calling_graph, fakecodegen)
    assert calling_graph.startblock.operations[1].name == 'mask_specialized_i_o'

def test_AddrTop_bug():
    zaddress = Argument('zaddress', SmallFixedBitVector(64))
    zIsInstr = Argument('zIsInstr', Bool())
    zel = Argument('zel', SmallFixedBitVector(2))
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
    i3 = block0.emit(Operation, 'zHaveEL', [zel], Bool(), '`7 1932:11-1932:21', 'zz49')
    i4 = block0.emit(Operation, 'zsail_assert', [i3], Unit(), '`7 1931:42-1943:1', 'zz410')
    i5 = block0.emit(Operation, 'zS1TranslationRegime', [zel], SmallFixedBitVector(2), '`7 1933:27-1933:50', 'zz40')
    i6 = block0.emit(GlobalRead, 'have_exception', [], Bool(), None, None)
    block0.next = ConditionalGoto(i6, block1, block2, '`7 1933:27-1933:50')
    block1.next = Return(DefaultValue(Int()), None)
    i7 = block2.emit(Operation, 'zELUsingAArch32', [i5], Bool(), '`7 1934:7-1934:29', 'zz41')
    i8 = block2.emit(GlobalRead, 'have_exception', [], Bool(), None, None)
    block2.next = ConditionalGoto(i8, block1, block3, '`7 1934:7-1934:29')
    block3.next = ConditionalGoto(i7, block4, block6, '`7 1934:4-1942:5')
    block4.next = Goto(block5, None)
    i9 = block5.emit_phi([block9, block8, block4], [IntConstant(63), IntConstant(55), IntConstant(31)], Int())
    block5.next = Return(i9, None)
    i10 = block6.emit(Operation, 'zEffectiveTBI', [zaddress, zIsInstr, zel], SmallFixedBitVector(1), '`7 1937:11-1937:45', 'zz46')
    i11 = block6.emit(GlobalRead, 'have_exception', [], Bool(), None, None)
    block6.next = ConditionalGoto(i11, block1, block7, '`7 1937:11-1937:45')
    i12 = block7.emit(Operation, '@eq_bits_bv_bv', [i10, SmallBitVectorConstant('0b1', SmallFixedBitVector(1))], Bool(), '`7 1937:11-1937:52', 'zz43')
    block7.next = ConditionalGoto(i12, block8, block9, '`7 1937:8-1941:9')
    block8.next = Goto(block5, None)
    block9.next = Goto(block5, None)
    graph = Graph('zAddrTop', [zaddress, zIsInstr, zel], block0)

    fakecodegen = FakeCodeGen()
    optimize(graph, fakecodegen)
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions['zAddrTop'] = spec

    zaddress = Argument('zaddress', SmallFixedBitVector(64))
    zel = Argument('zel', SmallFixedBitVector(2))
    block0 = Block()
    i1 = block0.emit(Operation, 'zAddrTop', [zaddress, BooleanConstant.TRUE, zel], Int(), '`7 456:19-456:28', 'zz419')
    block0.next = Return(i1, None)
    calling_graph = Graph('f', [zaddress, zel], block0)

    optimize(calling_graph, fakecodegen)
    assert calling_graph.startblock.operations[0].name == 'zAddrTop_specialized_o_True_o__i'
