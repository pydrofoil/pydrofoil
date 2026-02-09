from pydrofoil.types import *
from pydrofoil.ir import *
from pydrofoil.specialize import usefully_specializable, Specializer
from pydrofoil.specialize import SpecializingOptimizer, FixpointSpecializer
from pydrofoil.specialize import split_for_arg_constness
from pydrofoil import makecode


class FakeCodeGen(FixpointSpecializer):
    def __init__(self):
        FixpointSpecializer.__init__(self)
        self.builtin_names = {
            "zz5izDzKz5i64": "int_to_int64",
            "zz5i64zDzKz5i": "int64_to_int",
        }
        self._all_graphs = []
        self.all_registers = {}

    def add_struct_type(self, *args):
        pass

    def get_effects(self, name):
        return None


def test_specialize():
    fakecodegen = FakeCodeGen()
    zxs = Argument("zxs", GenericBitVector())
    zi = Argument("zi", Int())
    zj = Argument("zj", Int())
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
    i3 = block0.emit(
        Operation, "@length_unwrapped_res", [zxs], MachineInt(), "`1", "zz46"
    )
    i4 = block0.emit(Operation, "zz5i64zDzKz5i", [i3], Int(), "`1", None)
    i5 = block0.emit(
        Operation, "zz5izDzKz5i64", [zj], MachineInt(), None, None
    )
    i6 = block0.emit(
        Operation,
        "@sub_o_i_wrapped_res",
        [zi, i5],
        Int(),
        "`4 102:22-102:25",
        "zz48",
    )
    i7 = block0.emit(
        Operation,
        "@add_o_i_wrapped_res",
        [i6, MachineIntConstant(1)],
        Int(),
        "`4 102:22-102:27",
        "zz47",
    )
    i8 = block0.emit(Comment, "inlined zslice_mask", [], Unit(), None, None)
    i9 = block0.emit(
        Operation, "zgteq_int", [i7, i4], Bool(), "`2 336:5-336:11", "zz40"
    )
    block0.next = ConditionalGoto(i9, block1, block6, "`2 336:2-341:3")
    i10 = block1.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i11 = block1.emit(
        Operation,
        "@zeros_i",
        [i3],
        GenericBitVector(),
        "`2 320:32-320:45",
        "zz40",
    )
    i12 = block1.emit(
        Operation,
        "znot_vec",
        [i11],
        GenericBitVector(),
        "`2 320:24-320:46",
        "return",
    )
    i13 = block1.emit(
        Operation,
        "@shiftl_o_i",
        [i12, i5],
        GenericBitVector(),
        "`2 337:4-337:35",
        "return",
    )
    block1.next = Goto(block2, None)
    i14 = block2.emit_phi([block8, block1], [None, i13], GenericBitVector())
    i15 = block2.emit(
        Operation,
        "zand_vec",
        [zxs, i14],
        GenericBitVector(),
        "`4 102:3-102:28",
        "zz40",
    )
    i16 = block2.emit(
        Cast,
        "$cast",
        [SmallBitVectorConstant(0, SmallFixedBitVector(1))],
        GenericBitVector(),
        "`4 102:33-102:59",
        "zz44",
    )
    i17 = block2.emit(Comment, "inlined zextzzv", [], Unit(), None, None)
    i18 = block2.emit(
        Operation,
        "@lt",
        [i3, MachineIntConstant(1)],
        Bool(),
        "`4 80:5-80:11",
        "zz40",
    )
    block2.next = ConditionalGoto(i18, block3, block5, "`4 80:2-80:59")
    i19 = block3.emit(
        Operation,
        "@sail_truncate_o_i",
        [i16, i3],
        GenericBitVector(),
        "`4 80:17-80:31",
        "return",
    )
    block3.next = Goto(block4, None)
    i20 = block4.emit_phi([block5, block3], [None, i19], GenericBitVector())
    i21 = block4.emit(
        Operation, "zeq_bits", [i15, i20], Bool(), "`4 102:2-102:59", "return"
    )
    block4.next = Return(i21, None)
    i22 = block5.emit(
        Operation,
        "@zero_extend_o_i",
        [i16, i3],
        GenericBitVector(),
        "`4 80:37-80:59",
        "return",
    )
    i20.prevvalues[0] = i22
    block5.next = Goto(block4, None)
    i23 = block6.emit(
        Cast,
        "$cast",
        [SmallBitVectorConstant(0b1, SmallFixedBitVector(1))],
        GenericBitVector(),
        "`2 339:25-339:57",
        "zz46",
    )
    i24 = block6.emit(Comment, "inlined zsail_mask", [], Unit(), None, None)
    i25 = block6.emit(
        Operation,
        "@lteq",
        [i3, MachineIntConstant(1)],
        Bool(),
        "`2 141:32-141:48",
        "zz40",
    )
    block6.next = ConditionalGoto(i25, block7, block9, "`2 141:29-141:100")
    i26 = block7.emit(
        Operation,
        "@sail_truncate_o_i",
        [i23, i3],
        GenericBitVector(),
        "`2 141:54-141:70",
        "return",
    )
    block7.next = Goto(block8, None)
    i27 = block8.emit_phi([block9, block7], [None, i26], GenericBitVector())
    i28 = block8.emit(
        Operation, "zz5izDzKz5i64", [i7], MachineInt(), None, None
    )
    i29 = block8.emit(
        Operation,
        "@shiftl_o_i",
        [i27, i28],
        GenericBitVector(),
        "`2 340:28-340:50",
        "zz44",
    )
    i30 = block8.emit(
        Operation,
        "zsub_bits",
        [i29, i27],
        GenericBitVector(),
        "`2 340:19-340:56",
        "zz43",
    )
    i31 = block8.emit(
        Operation,
        "@shiftl_o_i",
        [i30, i5],
        GenericBitVector(),
        "`2 340:4-340:60",
        "return",
    )
    i14.prevvalues[0] = i31
    block8.next = Goto(block2, None)
    i32 = block9.emit(
        Operation,
        "@zero_extend_o_i",
        [i23, i3],
        GenericBitVector(),
        "`2 141:76-141:100",
        "return",
    )
    i27.prevvalues[0] = i32
    block9.next = Goto(block8, None)
    graph = Graph("zis_zzero_subrange", [zxs, zi, zj], block0)
    fakecodegen.should_inline = lambda x: False
    assert usefully_specializable(graph)

    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions["zis_zzero_subrange"] = spec

    # construct the calling graph
    block = Block()
    bv = Argument("bv", SmallFixedBitVector(52))
    i = Argument("i", Int())
    i2 = block.emit(Cast, "$cast", [bv], GenericBitVector(), None, None)
    i3 = block.emit(
        Operation,
        "zis_zzero_subrange",
        [i2, IntConstant(51), i],
        Bool(),
        None,
        None,
    )
    block.next = Return(i3)
    calling_graph = Graph("zf", [bv, i], block)
    opt = SpecializingOptimizer(calling_graph, fakecodegen)
    opt.optimize()
    optimize(calling_graph, fakecodegen)

    op = block.operations[1]
    assert op.name == "zis_zzero_subrange_specialized_bv52_51_i"
    assert op.args[0] == bv
    assert type(op.args[1]) is MachineIntConstant
    assert op.args[1].number == 51
    assert op.args[2].args[0] == i


def test_specialize_bool_value():
    zcond = Argument("zcond", Bool())
    block6 = Block()
    block8 = Block()
    block9 = Block()
    block10 = Block()
    block8.next = ConditionalGoto(zcond, block9, block10, "`7 2013:10-2017:11")
    i14 = block6.emit_phi([block9, block10], [None, None], Bool())
    block6.next = Return(i14, None)
    i21 = block9.emit(
        GlobalRead, "zBRBFCR_EL1", [], SmallFixedBitVector(64), None, None
    )
    i22 = block9.emit(
        Operation,
        "@slice_fixed_bv_i_i",
        [i21, MachineIntConstant(22), MachineIntConstant(1)],
        SmallFixedBitVector(1),
        "`7 2014:21-2014:45",
        "zz427",
    )
    i23 = block9.emit(
        GlobalRead, "zBRBFCR_EL1", [], SmallFixedBitVector(64), None, None
    )
    i24 = block9.emit(
        Operation,
        "@slice_fixed_bv_i_i",
        [i23, MachineIntConstant(16), MachineIntConstant(1)],
        SmallFixedBitVector(1),
        "`7 2014:49-2014:73",
        "zz423",
    )
    i25 = block9.emit(
        Operation,
        "@eq_bits_bv_bv",
        [i22, i24],
        Bool(),
        "`7 2014:21-2014:73",
        "zz415",
    )
    i26 = block9.emit(Operation, "@not", [i25], Bool(), None, None)
    i14.prevvalues[0] = i26
    block9.next = Goto(block6, None)
    i27 = block10.emit(
        GlobalRead, "zBRBFCR_EL1", [], SmallFixedBitVector(64), None, None
    )
    i28 = block10.emit(
        Operation,
        "@slice_fixed_bv_i_i",
        [i27, MachineIntConstant(17), MachineIntConstant(1)],
        SmallFixedBitVector(1),
        "`7 2016:21-2016:45",
        "zz440",
    )
    i29 = block10.emit(
        GlobalRead, "zBRBFCR_EL1", [], SmallFixedBitVector(64), None, None
    )
    i30 = block10.emit(
        Operation,
        "@slice_fixed_bv_i_i",
        [i29, MachineIntConstant(16), MachineIntConstant(1)],
        SmallFixedBitVector(1),
        "`7 2016:49-2016:73",
        "zz436",
    )
    i31 = block10.emit(
        Operation,
        "@eq_bits_bv_bv",
        [i28, i30],
        Bool(),
        "`7 2016:21-2016:73",
        "zz428",
    )
    i32 = block10.emit(Operation, "@not", [i31], Bool(), None, None)
    i14.prevvalues[1] = i32
    block10.next = Goto(block6, None)
    graph = Graph("filter", [zcond], block8)

    assert usefully_specializable(graph)

    fakecodegen = FakeCodeGen()
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions["filter"] = spec

    block = Block()
    i3 = block.emit(
        Operation, "filter", [BooleanConstant.TRUE], Bool(), None, None
    )
    block.next = Return(i3)
    calling_graph = Graph("call_filter", [], block)
    opt = SpecializingOptimizer(calling_graph, fakecodegen)
    opt.optimize()
    ((specialized_graph, _),) = spec.cache.values()
    assert len(list(specialized_graph.iterblocks())) == 1


def test_specialize_on_result():
    zx = Argument("zx", GenericBitVector())
    zshift = Argument("zshift", Int())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    i2 = block0.emit(
        Operation,
        "@eq_int_o_i",
        [zshift, MachineIntConstant(0)],
        Bool(),
        "`7 433:7-433:17",
        "zz40",
    )
    block0.next = ConditionalGoto(i2, block1, block3, "`7 433:4-434:59")
    block1.next = Goto(block2, None)
    i3 = block2.emit_phi([block3, block1], [None, zx], GenericBitVector())
    block2.next = Return(i3, None)
    i4 = block3.emit(
        Operation,
        "@length_unwrapped_res",
        [zx],
        MachineInt(),
        "`7 434:26-434:28",
        "zz48",
    )
    i5 = block3.emit(
        Operation, "zz5i64zDzKz5i", [i4], Int(), "`7 434:26-434:28", None
    )
    i6 = block3.emit(
        Operation, "emod_int", [zshift, i5], Int(), "`7 434:15-434:29", "zz41"
    )
    i7 = block3.emit(
        Operation, "zz5izDzKz5i64", [i6], MachineInt(), None, None
    )
    i8 = block3.emit(
        Operation,
        "@shiftr_o_i",
        [zx, i7],
        GenericBitVector(),
        "`7 434:33-434:42",
        "zz44",
    )
    i9 = block3.emit(
        Operation,
        "@sub_i_i_wrapped_res",
        [i4, i7],
        Int(),
        "`7 434:52-434:58",
        "zz46",
    )
    i10 = block3.emit(
        Operation, "zz5izDzKz5i64", [i9], MachineInt(), None, None
    )
    i11 = block3.emit(
        Operation,
        "@shiftl_o_i",
        [zx, i10],
        GenericBitVector(),
        "`7 434:45-434:59",
        "zz45",
    )
    i12 = block3.emit(
        Operation,
        "or_bits",
        [i8, i11],
        GenericBitVector(),
        "`7 434:33-434:59",
        "zz42",
    )
    i3.prevvalues[0] = i12
    block3.next = Goto(block2, None)
    graph = Graph("zROR", [zx, zshift], block0)

    fakecodegen = FakeCodeGen()
    fakecodegen.should_inline = lambda x: False
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions["zROR"] = spec

    zx = Argument("zx", SmallFixedBitVector(32))
    block0 = Block()
    i0 = block0.emit(Cast, "$cast", [zx], GenericBitVector(), None, None)
    i1 = block0.emit(
        Operation,
        "zROR",
        [i0, IntConstant(2)],
        GenericBitVector(),
        "`7 456:19-456:28",
        "zz419",
    )
    i2 = block0.emit(
        Cast,
        "$cast",
        [i1],
        SmallFixedBitVector(32),
        "`7 456:19-456:28",
        "zz419",
    )
    block0.next = Return(i2, None)
    calling_graph = Graph("f", [zx], block0)
    opt = SpecializingOptimizer(calling_graph, fakecodegen)
    opt.optimize()
    optimize(calling_graph, fakecodegen)
    op = calling_graph.startblock.operations[0]
    assert op.name == "zROR_specialized_bv32_2__bv32"
    assert calling_graph.startblock.next.value is op
    ((specialized_graph, _),) = spec.cache.values()


def test_argument_demand_casts():
    zlen = Argument("zlen", Int())
    zv = Argument("zv", GenericBitVector())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    block3 = Block()
    i2 = block0.emit(
        Operation,
        "@length_unwrapped_res",
        [zv],
        MachineInt(),
        "`2 141:39-141:48",
        "zz41",
    )
    i3 = block0.emit(
        Operation, "zz5izDzKz5i64", [zlen], MachineInt(), None, None
    )
    i4 = block0.emit(
        Operation, "@lteq", [i3, i2], Bool(), "`2 141:32-141:48", "zz40"
    )
    block0.next = ConditionalGoto(i4, block1, block3, "`2 141:29-141:100")
    i5 = block1.emit(
        Operation,
        "@sail_truncate_o_i",
        [zv, i3],
        GenericBitVector(),
        "`2 141:54-141:70",
        "return",
    )
    block1.next = Goto(block2, None)
    i6 = block2.emit_phi([block3, block1], [None, i5], GenericBitVector())
    block2.next = Return(i6, None)
    i7 = block3.emit(
        Operation,
        "@zero_extend_o_i",
        [zv, i3],
        GenericBitVector(),
        "`2 141:76-141:100",
        "return",
    )
    i6.prevvalues[0] = i7
    block3.next = Goto(block2, None)
    graph = Graph("mask", [zlen, zv], block0)

    fakecodegen = FakeCodeGen()
    fakecodegen.should_inline = lambda x: False
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions["mask"] = spec

    a = Argument("a", Int())
    bv = Argument("bv", GenericBitVector())
    block0 = Block()
    i1 = block0.emit(
        Operation,
        "mask",
        [a, bv],
        GenericBitVector(),
        "`7 456:19-456:28",
        "zz419",
    )
    block0.next = Return(i1, None)
    calling_graph = Graph("f", [a, bv], block0)

    optimize(calling_graph, fakecodegen)
    assert (
        calling_graph.startblock.operations[1].name == "mask_specialized_i_o"
    )


def test_AddrTop_bug():
    zaddress = Argument("zaddress", SmallFixedBitVector(64))
    zIsInstr = Argument("zIsInstr", Bool())
    zel = Argument("zel", SmallFixedBitVector(2))
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
    i3 = block0.emit(
        Operation, "zHaveEL", [zel], Bool(), "`7 1932:11-1932:21", "zz49"
    )
    i4 = block0.emit(
        Operation,
        "zsail_assert",
        [i3, StringConstant("")],
        Unit(),
        "`7 1931:42-1943:1",
        "zz410",
    )
    i5 = block0.emit(
        Operation,
        "zS1TranslationRegime",
        [zel],
        SmallFixedBitVector(2),
        "`7 1933:27-1933:50",
        "zz40",
    )
    i6 = block0.emit(GlobalRead, "have_exception", [], Bool(), None, None)
    block0.next = ConditionalGoto(i6, block1, block2, "`7 1933:27-1933:50")
    block1.next = Return(DefaultValue(Int()), None)
    i7 = block2.emit(
        Operation, "zELUsingAArch32", [i5], Bool(), "`7 1934:7-1934:29", "zz41"
    )
    i8 = block2.emit(GlobalRead, "have_exception", [], Bool(), None, None)
    block2.next = ConditionalGoto(i8, block1, block3, "`7 1934:7-1934:29")
    block3.next = ConditionalGoto(i7, block4, block6, "`7 1934:4-1942:5")
    block4.next = Goto(block5, None)
    i9 = block5.emit_phi(
        [block9, block8, block4],
        [IntConstant(63), IntConstant(55), IntConstant(31)],
        Int(),
    )
    block5.next = Return(i9, None)
    i10 = block6.emit(
        Operation,
        "zEffectiveTBI",
        [zaddress, zIsInstr, zel],
        SmallFixedBitVector(1),
        "`7 1937:11-1937:45",
        "zz46",
    )
    i11 = block6.emit(GlobalRead, "have_exception", [], Bool(), None, None)
    block6.next = ConditionalGoto(i11, block1, block7, "`7 1937:11-1937:45")
    i12 = block7.emit(
        Operation,
        "@eq_bits_bv_bv",
        [i10, SmallBitVectorConstant(0b1, SmallFixedBitVector(1))],
        Bool(),
        "`7 1937:11-1937:52",
        "zz43",
    )
    block7.next = ConditionalGoto(i12, block8, block9, "`7 1937:8-1941:9")
    block8.next = Goto(block5, None)
    block9.next = Goto(block5, None)
    graph = Graph("zAddrTop", [zaddress, zIsInstr, zel], block0)

    fakecodegen = FakeCodeGen()
    optimize(graph, fakecodegen)
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions["zAddrTop"] = spec

    zaddress = Argument("zaddress", SmallFixedBitVector(64))
    zel = Argument("zel", SmallFixedBitVector(2))
    block0 = Block()
    i1 = block0.emit(
        Operation,
        "zAddrTop",
        [zaddress, BooleanConstant.TRUE, zel],
        Int(),
        "`7 456:19-456:28",
        "zz419",
    )
    block0.next = Return(i1, None)
    calling_graph = Graph("f", [zaddress, zel], block0)

    optimize(calling_graph, fakecodegen)
    assert (
        calling_graph.startblock.operations[0].name
        == "zAddrTop_specialized_o_True_o__i"
    )


def test_specialize_on_result_tuple():
    tupletyp = Struct(
        "tup",
        ("bv", "i", "b"),
        (types.GenericBitVector(), types.Int(), types.Bool()),
        True,
    )
    bv = Argument("bv", GenericBitVector())
    i = Argument("i", Int())
    b = Argument("b", Bool())
    block0 = Block()
    i0 = block0.emit(
        PackPackedField, "$pack", [bv], Packed(GenericBitVector()), None, None
    )
    i1 = block0.emit(PackPackedField, "$pack", [i], Packed(Int()), None, None)
    i2 = block0.emit(StructConstruction, "tup", [i0, i1, b], tupletyp, None)
    block0.next = Return(i2, None)
    graph = Graph("tuplify", [bv, i, b], block0)

    fakecodegen = FakeCodeGen()
    fakecodegen.should_inline = lambda x: False
    spec = Specializer(graph, fakecodegen)
    fakecodegen.specialization_functions["tuplify"] = spec

    b = Argument("b", Bool())
    zx = Argument("zx", SmallFixedBitVector(32))
    block0 = Block()
    i0 = block0.emit(Cast, "$cast", [zx], GenericBitVector(), None, None)
    i1 = block0.emit(
        Operation,
        "tuplify",
        [i0, IntConstant(2), b],
        tupletyp,
        "`7 456:19-456:28",
        "zz419",
    )
    i2 = block0.emit(FieldAccess, "bv", [i1], Packed(GenericBitVector()), None)
    i3 = block0.emit(
        UnpackPackedField, "$unpack", [i2], GenericBitVector(), None, None
    )
    i4 = block0.emit(
        Cast,
        "$cast",
        [i3],
        SmallFixedBitVector(32),
        "`7 456:19-456:28",
        "zz419",
    )
    block0.next = Return(i4, None)
    calling_graph = Graph("f", [b, zx], block0)
    opt = SpecializingOptimizer(calling_graph, fakecodegen)
    opt.optimize()
    optimize(calling_graph, fakecodegen)
    assert (
        "\n".join(print_graph_construction(calling_graph))
        == """\
tup_tup_bv32_i_o = Struct('tup_tup_bv32_i_o', ('bv32_0', 'i_1', 'o_2'), (SmallFixedBitVector(32), MachineInt(), Bool()), True)
b = Argument('b', Bool())
zx = Argument('zx', SmallFixedBitVector(32))
block0 = Block()
i2 = block0.emit(Operation, 'tuplify_specialized_bv32_2_o__tup_bv32_i_o_put', [zx, MachineIntConstant(2), b], tup_tup_bv32_i_o, '`7 456:19-456:28', 'zz419')
i3 = block0.emit(FieldAccess, 'bv32_0', [i2], SmallFixedBitVector(32), None, None)
block0.next = Return(i3, None)
graph = Graph('f', [b, zx], block0)\
"""
    )


def test_results_bubble_up_problem():
    # f -> g(32) -> h(32) returns bv32
    fa = Argument("fa", SmallFixedBitVector(32))
    block0 = Block()
    i0 = block0.emit(Cast, "$cast", [fa], GenericBitVector())
    i1 = block0.emit(Operation, "g", [i0], GenericBitVector())
    i2 = block0.emit(Cast, "$cast", [i1], SmallFixedBitVector(32))
    block0.next = Return(i2, None)
    fgraph = Graph("f", [fa], block0)

    ga = Argument("ga", GenericBitVector())
    block0 = Block()
    i0 = block0.emit(Operation, "h", [ga], GenericBitVector())
    block0.next = Return(i0, None)
    ggraph = Graph("g", [ga], block0)

    ha = Argument("ha", GenericBitVector())
    block0 = Block()
    block0.next = Return(ha, None)
    hgraph = Graph("h", [ha], block0)
    codegen = FakeCodeGen()
    codegen.should_inline = lambda x: False
    gspec = Specializer(ggraph, codegen)
    codegen.specialization_functions["g"] = gspec
    hspec = Specializer(hgraph, codegen)
    codegen.specialization_functions["h"] = hspec
    codegen.schedule_graph_specialization(fgraph)
    codegen.schedule_graph_specialization(ggraph)
    codegen.schedule_graph_specialization(hgraph)
    codegen.specialize_all()
    (op,) = fgraph.startblock.operations
    assert op.name == "g_specialized_bv32__bv32"
    graphs = codegen.extract_needed_extra_graphs([fgraph])
    assert {g.name for g, _ in graphs} == {
        "g_specialized_bv32__bv32",
        "h_specialized_bv32__bv32",
    }


def test_inlinability_changes():
    ha = Argument("ha", Int())
    block0 = Block()
    i0 = block0.emit(Operation, "f", [ha], Int())
    block0.next = Return(i0, None)
    hgraph = Graph("h", [ha], block0)

    fa = Argument("a", Int())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    i0 = block0.emit(Operation, "g", [], Bool())
    block0.next = ConditionalGoto(i0, block1, block2)
    curr = fa
    for i in range(100):
        curr = block2.emit(Operation, "add_int", [curr, curr], Int())
    block2.next = Return(curr)
    block1.next = Return(IntConstant(12), None)
    fgraph = Graph("f", [fa], block0)

    block0 = Block()
    block0.next = Return(BooleanConstant.TRUE, None)
    ggraph = Graph("g", [], block0)

    codegen = FakeCodeGen()
    light_simplify(hgraph, codegen)
    codegen.inlinable_functions[hgraph.name] = hgraph
    light_simplify(fgraph, codegen)
    light_simplify(ggraph, codegen)
    codegen.inlinable_functions[ggraph.name] = ggraph
    codegen.schedule_graph_specialization(hgraph)
    codegen.schedule_graph_specialization(fgraph)
    codegen.schedule_graph_specialization(ggraph)
    codegen.specialize_all()
    # check that f got inlined into h
    assert hgraph.startblock.next.value.number == 12


def test_split_for_phi_arguments():
    zb = Argument("zb", Bool())
    zi = Argument("zi", MachineInt())
    block0 = Block()
    block1 = Block()
    block3 = Block()
    block4 = Block()
    block0.next = ConditionalGoto(zb, block1, block4, "`1 13:27-16:1")
    block1.next = Goto(block3, None)
    i4 = block3.emit_phi(
        [block1, block4],
        [MachineIntConstant(64), MachineIntConstant(32)],
        MachineInt(),
    )
    i8 = block3.emit(Operation, "f", [i4], GenericBitVector())
    i9 = block3.emit(Operation, "@length_unwrapped_res", [i8], MachineInt())
    block3.next = Return(i9, None)
    block4.next = Goto(block3, None)
    graph = Graph("g", [zb, zi], block0)

    fa = Argument("a", MachineInt())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    i0 = block0.emit(Operation, "@zeros_i", [fa], GenericBitVector())
    block0.next = Return(i0)
    fgraph = Graph("f", [fa], block0)

    codegen = FakeCodeGen()
    fspec = Specializer(fgraph, codegen)
    codegen.specialization_functions["f"] = fspec

    codegen.schedule_graph_specialization(graph)
    codegen.schedule_graph_specialization(fgraph)
    codegen.specialize_all()
    assert len(fspec.cache) == 2


def test_bug():
    zM = Argument("zM", MachineInt())
    zimmN = Argument("zimmN", SmallFixedBitVector(1))
    zimms = Argument("zimms", SmallFixedBitVector(6))
    zimmr = Argument("zimmr", SmallFixedBitVector(6))
    zimmediate = Argument("zimmediate", Bool())
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
    block10 = Block()
    block11 = Block()
    block12 = Block()
    block13 = Block()
    i5 = block0.emit(
        Operation,
        "@not_vec_bv",
        [zimms, MachineIntConstant(6)],
        SmallFixedBitVector(6),
        "`7 154376:36-154376:49",
        None,
    )
    i6 = block0.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [zimmN, MachineIntConstant(6), i5],
        SmallFixedBitVector(7),
        "`7 154376:29-154376:49",
        "zz4704",
    )
    i7 = block0.emit(
        Operation,
        "zHighestSetBit_specialized_bv7__i",
        [i6],
        MachineInt(),
        "`7 154376:15-154376:50",
        "zz40",
    )
    i8 = block0.emit(
        Operation,
        "@lt",
        [i7, MachineIntConstant(1)],
        Bool(),
        "`7 154377:7-154377:14",
        "zz4695",
    )
    block0.next = ConditionalGoto(i8, block1, block3, "`7 154377:4-154379:5")
    i11 = block1.emit(
        GlobalWrite,
        "have_exception",
        [BooleanConstant.TRUE],
        Bool(),
        None,
        None,
    )
    i12 = block1.emit(
        GlobalWrite,
        "throw_location",
        [StringConstant("src/v8_base.sail:154378.8-154378.32")],
        String(),
        None,
        None,
    )
    block1.next = Goto(block2, None)
    block2.next = Return(
        DefaultValue(
            Struct(
                "ztuplez3z5bv_z5bv",
                ("ztuplez3z5bv_z5bv0", "ztuplez3z5bv_z5bv1"),
                (GenericBitVector(), GenericBitVector()),
                True,
            )
        ),
        None,
    )
    i13 = block3.emit(
        Operation,
        "@shl_int_i_i_wrapped_res",
        [MachineIntConstant(1), i7],
        Int(),
        "`7 154380:17-154380:25",
        "zz4692",
    )
    i14 = block3.emit(
        Operation,
        "zz5i64zDzKz5i",
        [zM],
        Int(),
        "`7 154380:11-154380:26",
        "zz4693",
    )
    i15 = block3.emit(
        Operation,
        "zgteq_int",
        [i14, i13],
        Bool(),
        "`7 154380:11-154380:26",
        "zz4690",
    )
    i16 = block3.emit(
        Comment,
        "sail_assert src/v8_base.sail:154380.26-154380.27",
        [],
        Unit(),
        None,
        None,
    )
    block3.next = ConditionalGoto(
        i15, block4, block13, "`7 154377:4-154412:50"
    )
    i17 = block4.emit(Comment, "inlined z__id", [], Unit(), None, None)
    i18 = block4.emit(
        Operation,
        "@gteq",
        [MachineIntConstant(6), i7],
        Bool(),
        "`7 154381:22-154381:31",
        "zz4686",
    )
    i19 = block4.emit(
        Comment,
        "sail_assert src/v8_base.sail:154381.32-154381.33",
        [],
        Unit(),
        None,
        None,
    )
    block4.next = ConditionalGoto(
        i18, block5, block12, "`7 154377:4-154412:50"
    )
    i20 = block5.emit(Comment, "inlined zzzext_ones", [], Unit(), None, None)
    i21 = block5.emit(Comment, "inlined z__id", [], Unit(), None, None)
    i22 = block5.emit(Comment, "inlined zextsv", [], Unit(), None, None)
    i23 = block5.emit(
        Operation,
        "@sign_extend_bv_i_i",
        [
            SmallBitVectorConstant(0b1, SmallFixedBitVector(1)),
            MachineIntConstant(1),
            MachineIntConstant(6),
        ],
        SmallFixedBitVector(6),
        "`4 85:37-85:59",
        "return",
    )
    i24 = block5.emit(
        Operation,
        "@sub_i_i_must_fit",
        [MachineIntConstant(6), i7],
        MachineInt(),
        "`4 289:21-289:26",
        "zz41",
    )
    i25 = block5.emit(
        Operation,
        "@shiftr_bv_i",
        [i23, MachineIntConstant(6), i24],
        SmallFixedBitVector(6),
        "`4 289:2-289:27",
        "return",
    )
    block5.next = ConditionalGoto(
        zimmediate, block6, block8, "`7 154383:7-154383:44"
    )
    i26 = block6.emit(
        Operation,
        "@and_vec_bv_bv",
        [zimms, i25],
        SmallFixedBitVector(6),
        "`7 154383:20-154383:33",
        "zz4683",
    )
    i27 = block6.emit(
        Operation,
        "@eq_bits_bv_bv",
        [i26, i25],
        Bool(),
        "`7 154383:19-154383:44",
        "zz4677",
    )
    block6.next = ConditionalGoto(i27, block7, block8, "`7 154383:4-154385:5")
    i30 = block7.emit(
        GlobalWrite,
        "have_exception",
        [BooleanConstant.TRUE],
        Bool(),
        None,
        None,
    )
    i31 = block7.emit(
        GlobalWrite,
        "throw_location",
        [StringConstant("src/v8_base.sail:154384.8-154384.32")],
        String(),
        None,
        None,
    )
    block7.next = Goto(block2, None)
    i32 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [zimms, i25],
        SmallFixedBitVector(6),
        "`7 154386:18-154386:31",
        "zz4673",
    )
    i33 = block8.emit(
        Operation,
        "@unsigned_bv",
        [i32, MachineIntConstant(6)],
        MachineInt(),
        "`7 154386:13-154386:32",
        "zz4670",
    )
    i34 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [zimmr, i25],
        SmallFixedBitVector(6),
        "`7 154387:18-154387:31",
        "zz4667",
    )
    i35 = block8.emit(
        Operation,
        "@unsigned_bv",
        [i34, MachineIntConstant(6)],
        MachineInt(),
        "`7 154387:13-154387:32",
        "zz4664",
    )
    i36 = block8.emit(
        Operation,
        "@sub_i_i_must_fit",
        [i33, i35],
        MachineInt(),
        "`7 154388:16-154388:21",
        "zz4661",
    )
    i37 = block8.emit(
        Comment, "inlined zinteger_subrange", [], Unit(), None, None
    )
    i38 = block8.emit(
        Operation,
        "@get_slice_int_i_i_i",
        [MachineIntConstant(6), i36, MachineIntConstant(0)],
        SmallFixedBitVector(6),
        "`5 176:39-176:72",
        "return",
    )
    i39 = block8.emit(
        Operation,
        "@not_vec_bv",
        [i25, MachineIntConstant(6)],
        SmallFixedBitVector(6),
        "`7 154389:45-154389:60",
        None,
    )
    i40 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i38, i39],
        SmallFixedBitVector(6),
        "`7 154389:30-154389:60",
        "zz4652",
    )
    i41 = block8.emit(
        Comment, "inlined zinteger_subrange", [], Unit(), None, None
    )
    i42 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i38, i25],
        SmallFixedBitVector(6),
        "`7 154390:29-154390:50",
        "zz4643",
    )
    i43 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i44 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i45 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i40, MachineIntConstant(0)],
        SmallFixedBitVector(1),
        "`7 154392:52-154392:64",
        "zz4634",
    )
    i46 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i47 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i48 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i45,
            MachineIntConstant(1),
            SmallBitVectorConstant(0b1, SmallFixedBitVector(1)),
        ],
        SmallFixedBitVector(2),
        "`7 154392:41-154392:79",
        "zz4627",
    )
    i49 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i48, MachineIntConstant(2), MachineIntConstant(32)],
        SmallFixedBitVector(64),
        "`7 154392:31-154392:84",
        "zz4622",
    )
    i50 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [
            SmallBitVectorConstant(
                r_uint(0xFFFFFFFFFFFFFFFFL), SmallFixedBitVector(64)
            ),
            i49,
        ],
        SmallFixedBitVector(64),
        "`7 154392:23-154392:84",
        "zz4618",
    )
    i51 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i52 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i42, MachineIntConstant(0)],
        SmallFixedBitVector(1),
        "`7 154392:119-154392:130",
        "zz4609",
    )
    i53 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0b0, SmallFixedBitVector(1)),
            MachineIntConstant(1),
            i52,
        ],
        SmallFixedBitVector(2),
        "`7 154392:97-154392:135",
        "zz4604",
    )
    i54 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i53, MachineIntConstant(2), MachineIntConstant(32)],
        SmallFixedBitVector(64),
        "`7 154392:87-154392:140",
        "zz4599",
    )
    i55 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i50, i54],
        SmallFixedBitVector(64),
        "`7 154392:23-154392:140",
        "zz4595",
    )
    i56 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i40, MachineIntConstant(1)],
        SmallFixedBitVector(1),
        "`7 154393:52-154393:64",
        "zz4586",
    )
    i57 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i56, MachineIntConstant(1), MachineIntConstant(2)],
        SmallFixedBitVector(2),
        "`7 154393:41-154393:69",
        "zz4585",
    )
    i58 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i59 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i60 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i57,
            MachineIntConstant(2),
            SmallBitVectorConstant(0b11, SmallFixedBitVector(2)),
        ],
        SmallFixedBitVector(4),
        "`7 154393:41-154393:79",
        "zz4579",
    )
    i61 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i60, MachineIntConstant(4), MachineIntConstant(16)],
        SmallFixedBitVector(64),
        "`7 154393:31-154393:84",
        "zz4574",
    )
    i62 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i55, i61],
        SmallFixedBitVector(64),
        "`7 154393:23-154393:84",
        "zz4570",
    )
    i63 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i64 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i42, MachineIntConstant(1)],
        SmallFixedBitVector(1),
        "`7 154393:119-154393:130",
        "zz4561",
    )
    i65 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i64, MachineIntConstant(1), MachineIntConstant(2)],
        SmallFixedBitVector(2),
        "`7 154393:108-154393:135",
        "zz4560",
    )
    i66 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0b0, SmallFixedBitVector(2)),
            MachineIntConstant(2),
            i65,
        ],
        SmallFixedBitVector(4),
        "`7 154393:97-154393:135",
        "zz4556",
    )
    i67 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i66, MachineIntConstant(4), MachineIntConstant(16)],
        SmallFixedBitVector(64),
        "`7 154393:87-154393:140",
        "zz4551",
    )
    i68 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i62, i67],
        SmallFixedBitVector(64),
        "`7 154393:23-154393:140",
        "zz4547",
    )
    i69 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i40, MachineIntConstant(2)],
        SmallFixedBitVector(1),
        "`7 154394:52-154394:64",
        "zz4538",
    )
    i70 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i69, MachineIntConstant(1), MachineIntConstant(4)],
        SmallFixedBitVector(4),
        "`7 154394:41-154394:69",
        "zz4537",
    )
    i71 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i72 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i73 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i70,
            MachineIntConstant(4),
            SmallBitVectorConstant(0xF, SmallFixedBitVector(4)),
        ],
        SmallFixedBitVector(8),
        "`7 154394:41-154394:79",
        "zz4531",
    )
    i74 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i73, MachineIntConstant(8), MachineIntConstant(8)],
        SmallFixedBitVector(64),
        "`7 154394:31-154394:83",
        "zz4526",
    )
    i75 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i68, i74],
        SmallFixedBitVector(64),
        "`7 154394:23-154394:83",
        "zz4522",
    )
    i76 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i77 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i42, MachineIntConstant(2)],
        SmallFixedBitVector(1),
        "`7 154394:118-154394:129",
        "zz4513",
    )
    i78 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i77, MachineIntConstant(1), MachineIntConstant(4)],
        SmallFixedBitVector(4),
        "`7 154394:107-154394:134",
        "zz4512",
    )
    i79 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0x0, SmallFixedBitVector(4)),
            MachineIntConstant(4),
            i78,
        ],
        SmallFixedBitVector(8),
        "`7 154394:96-154394:134",
        "zz4508",
    )
    i80 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i79, MachineIntConstant(8), MachineIntConstant(8)],
        SmallFixedBitVector(64),
        "`7 154394:86-154394:138",
        "zz4503",
    )
    i81 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i75, i80],
        SmallFixedBitVector(64),
        "`7 154394:23-154394:138",
        "zz4499",
    )
    i82 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i40, MachineIntConstant(3)],
        SmallFixedBitVector(1),
        "`7 154395:52-154395:64",
        "zz4490",
    )
    i83 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i82, MachineIntConstant(1), MachineIntConstant(8)],
        SmallFixedBitVector(8),
        "`7 154395:41-154395:69",
        "zz4489",
    )
    i84 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i85 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i86 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i83,
            MachineIntConstant(8),
            SmallBitVectorConstant(0xFF, SmallFixedBitVector(8)),
        ],
        SmallFixedBitVector(16),
        "`7 154395:41-154395:79",
        "zz4483",
    )
    i87 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i86, MachineIntConstant(16), MachineIntConstant(4)],
        SmallFixedBitVector(64),
        "`7 154395:31-154395:83",
        "zz4478",
    )
    i88 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i81, i87],
        SmallFixedBitVector(64),
        "`7 154395:23-154395:83",
        "zz4474",
    )
    i89 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i90 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i42, MachineIntConstant(3)],
        SmallFixedBitVector(1),
        "`7 154395:118-154395:129",
        "zz4465",
    )
    i91 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i90, MachineIntConstant(1), MachineIntConstant(8)],
        SmallFixedBitVector(8),
        "`7 154395:107-154395:134",
        "zz4464",
    )
    i92 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0x0, SmallFixedBitVector(8)),
            MachineIntConstant(8),
            i91,
        ],
        SmallFixedBitVector(16),
        "`7 154395:96-154395:134",
        "zz4460",
    )
    i93 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i92, MachineIntConstant(16), MachineIntConstant(4)],
        SmallFixedBitVector(64),
        "`7 154395:86-154395:138",
        "zz4455",
    )
    i94 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i88, i93],
        SmallFixedBitVector(64),
        "`7 154395:23-154395:138",
        "zz4451",
    )
    i95 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i40, MachineIntConstant(4)],
        SmallFixedBitVector(1),
        "`7 154396:52-154396:64",
        "zz4442",
    )
    i96 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i95, MachineIntConstant(1), MachineIntConstant(16)],
        SmallFixedBitVector(16),
        "`7 154396:41-154396:70",
        "zz4441",
    )
    i97 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i98 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i99 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i96,
            MachineIntConstant(16),
            SmallBitVectorConstant(0xFFFF, SmallFixedBitVector(16)),
        ],
        SmallFixedBitVector(32),
        "`7 154396:41-154396:81",
        "zz4435",
    )
    i100 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i99, MachineIntConstant(32), MachineIntConstant(2)],
        SmallFixedBitVector(64),
        "`7 154396:31-154396:85",
        "zz4430",
    )
    i101 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i94, i100],
        SmallFixedBitVector(64),
        "`7 154396:23-154396:85",
        "zz4426",
    )
    i102 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i103 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i42, MachineIntConstant(4)],
        SmallFixedBitVector(1),
        "`7 154396:121-154396:132",
        "zz4417",
    )
    i104 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i103, MachineIntConstant(1), MachineIntConstant(16)],
        SmallFixedBitVector(16),
        "`7 154396:110-154396:138",
        "zz4416",
    )
    i105 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0x0, SmallFixedBitVector(16)),
            MachineIntConstant(16),
            i104,
        ],
        SmallFixedBitVector(32),
        "`7 154396:98-154396:138",
        "zz4412",
    )
    i106 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i105, MachineIntConstant(32), MachineIntConstant(2)],
        SmallFixedBitVector(64),
        "`7 154396:88-154396:142",
        "zz4407",
    )
    i107 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i101, i106],
        SmallFixedBitVector(64),
        "`7 154396:23-154396:142",
        "zz4403",
    )
    i108 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i40, MachineIntConstant(5)],
        SmallFixedBitVector(1),
        "`7 154397:56-154397:68",
        "zz4394",
    )
    i109 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i108, MachineIntConstant(1), MachineIntConstant(32)],
        SmallFixedBitVector(32),
        "`7 154397:45-154397:74",
        "zz4393",
    )
    i110 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i111 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i112 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i109,
            MachineIntConstant(32),
            SmallBitVectorConstant(0xFFFFFFFF, SmallFixedBitVector(32)),
        ],
        SmallFixedBitVector(64),
        "`7 154397:45-154397:85",
        "zz4387",
    )
    i113 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i107, i112],
        SmallFixedBitVector(64),
        "`7 154397:27-154397:89",
        "zz4378",
    )
    i114 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i115 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i42, MachineIntConstant(5)],
        SmallFixedBitVector(1),
        "`7 154397:125-154397:136",
        "zz4369",
    )
    i116 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i115, MachineIntConstant(1), MachineIntConstant(32)],
        SmallFixedBitVector(32),
        "`7 154397:114-154397:142",
        "zz4368",
    )
    i117 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0x0, SmallFixedBitVector(32)),
            MachineIntConstant(32),
            i116,
        ],
        SmallFixedBitVector(64),
        "`7 154397:102-154397:142",
        "zz4364",
    )
    i118 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i113, i117],
        SmallFixedBitVector(64),
        "`7 154397:27-154397:146",
        "zz4355",
    )
    i119 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [zimmr, i39],
        SmallFixedBitVector(6),
        "`7 154398:30-154398:52",
        "zz4348",
    )
    i120 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [zimmr, i25],
        SmallFixedBitVector(6),
        "`7 154399:29-154399:42",
        "zz4344",
    )
    i121 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i122 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i123 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i124 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i119, MachineIntConstant(0)],
        SmallFixedBitVector(1),
        "`7 154401:62-154401:74",
        "zz4334",
    )
    i125 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0b1, SmallFixedBitVector(1)),
            MachineIntConstant(1),
            i124,
        ],
        SmallFixedBitVector(2),
        "`7 154401:41-154401:79",
        "zz4329",
    )
    i126 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i125, MachineIntConstant(2), MachineIntConstant(32)],
        SmallFixedBitVector(64),
        "`7 154401:31-154401:84",
        "zz4324",
    )
    i127 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [SmallBitVectorConstant(0x0, SmallFixedBitVector(64)), i126],
        SmallFixedBitVector(64),
        "`7 154401:23-154401:84",
        "zz4320",
    )
    i128 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i120, MachineIntConstant(0)],
        SmallFixedBitVector(1),
        "`7 154401:108-154401:119",
        "zz4313",
    )
    i129 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i130 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i128,
            MachineIntConstant(1),
            SmallBitVectorConstant(0b0, SmallFixedBitVector(1)),
        ],
        SmallFixedBitVector(2),
        "`7 154401:97-154401:135",
        "zz4306",
    )
    i131 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i130, MachineIntConstant(2), MachineIntConstant(32)],
        SmallFixedBitVector(64),
        "`7 154401:87-154401:140",
        "zz4301",
    )
    i132 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i127, i131],
        SmallFixedBitVector(64),
        "`7 154401:23-154401:140",
        "zz4297",
    )
    i133 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i134 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i135 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i119, MachineIntConstant(1)],
        SmallFixedBitVector(1),
        "`7 154402:62-154402:74",
        "zz4286",
    )
    i136 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i135, MachineIntConstant(1), MachineIntConstant(2)],
        SmallFixedBitVector(2),
        "`7 154402:51-154402:79",
        "zz4285",
    )
    i137 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0b11, SmallFixedBitVector(2)),
            MachineIntConstant(2),
            i136,
        ],
        SmallFixedBitVector(4),
        "`7 154402:41-154402:79",
        "zz4281",
    )
    i138 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i137, MachineIntConstant(4), MachineIntConstant(16)],
        SmallFixedBitVector(64),
        "`7 154402:31-154402:84",
        "zz4276",
    )
    i139 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i132, i138],
        SmallFixedBitVector(64),
        "`7 154402:23-154402:84",
        "zz4272",
    )
    i140 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i120, MachineIntConstant(1)],
        SmallFixedBitVector(1),
        "`7 154402:108-154402:119",
        "zz4265",
    )
    i141 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i140, MachineIntConstant(1), MachineIntConstant(2)],
        SmallFixedBitVector(2),
        "`7 154402:97-154402:124",
        "zz4264",
    )
    i142 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i143 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i141,
            MachineIntConstant(2),
            SmallBitVectorConstant(0b0, SmallFixedBitVector(2)),
        ],
        SmallFixedBitVector(4),
        "`7 154402:97-154402:135",
        "zz4258",
    )
    i144 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i143, MachineIntConstant(4), MachineIntConstant(16)],
        SmallFixedBitVector(64),
        "`7 154402:87-154402:140",
        "zz4253",
    )
    i145 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i139, i144],
        SmallFixedBitVector(64),
        "`7 154402:23-154402:140",
        "zz4249",
    )
    i146 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i147 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i148 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i119, MachineIntConstant(2)],
        SmallFixedBitVector(1),
        "`7 154403:62-154403:74",
        "zz4238",
    )
    i149 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i148, MachineIntConstant(1), MachineIntConstant(4)],
        SmallFixedBitVector(4),
        "`7 154403:51-154403:79",
        "zz4237",
    )
    i150 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0xF, SmallFixedBitVector(4)),
            MachineIntConstant(4),
            i149,
        ],
        SmallFixedBitVector(8),
        "`7 154403:41-154403:79",
        "zz4233",
    )
    i151 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i150, MachineIntConstant(8), MachineIntConstant(8)],
        SmallFixedBitVector(64),
        "`7 154403:31-154403:83",
        "zz4228",
    )
    i152 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i145, i151],
        SmallFixedBitVector(64),
        "`7 154403:23-154403:83",
        "zz4224",
    )
    i153 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i120, MachineIntConstant(2)],
        SmallFixedBitVector(1),
        "`7 154403:107-154403:118",
        "zz4217",
    )
    i154 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i153, MachineIntConstant(1), MachineIntConstant(4)],
        SmallFixedBitVector(4),
        "`7 154403:96-154403:123",
        "zz4216",
    )
    i155 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i156 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i154,
            MachineIntConstant(4),
            SmallBitVectorConstant(0x0, SmallFixedBitVector(4)),
        ],
        SmallFixedBitVector(8),
        "`7 154403:96-154403:134",
        "zz4210",
    )
    i157 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i156, MachineIntConstant(8), MachineIntConstant(8)],
        SmallFixedBitVector(64),
        "`7 154403:86-154403:138",
        "zz4205",
    )
    i158 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i152, i157],
        SmallFixedBitVector(64),
        "`7 154403:23-154403:138",
        "zz4201",
    )
    i159 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i160 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i161 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i119, MachineIntConstant(3)],
        SmallFixedBitVector(1),
        "`7 154404:62-154404:74",
        "zz4190",
    )
    i162 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i161, MachineIntConstant(1), MachineIntConstant(8)],
        SmallFixedBitVector(8),
        "`7 154404:51-154404:79",
        "zz4189",
    )
    i163 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0xFF, SmallFixedBitVector(8)),
            MachineIntConstant(8),
            i162,
        ],
        SmallFixedBitVector(16),
        "`7 154404:41-154404:79",
        "zz4185",
    )
    i164 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i163, MachineIntConstant(16), MachineIntConstant(4)],
        SmallFixedBitVector(64),
        "`7 154404:31-154404:83",
        "zz4180",
    )
    i165 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i158, i164],
        SmallFixedBitVector(64),
        "`7 154404:23-154404:83",
        "zz4176",
    )
    i166 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i120, MachineIntConstant(3)],
        SmallFixedBitVector(1),
        "`7 154404:107-154404:118",
        "zz4169",
    )
    i167 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i166, MachineIntConstant(1), MachineIntConstant(8)],
        SmallFixedBitVector(8),
        "`7 154404:96-154404:123",
        "zz4168",
    )
    i168 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i169 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i167,
            MachineIntConstant(8),
            SmallBitVectorConstant(0x0, SmallFixedBitVector(8)),
        ],
        SmallFixedBitVector(16),
        "`7 154404:96-154404:134",
        "zz4162",
    )
    i170 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i169, MachineIntConstant(16), MachineIntConstant(4)],
        SmallFixedBitVector(64),
        "`7 154404:86-154404:138",
        "zz4157",
    )
    i171 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i165, i170],
        SmallFixedBitVector(64),
        "`7 154404:23-154404:138",
        "zz4153",
    )
    i172 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i173 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i174 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i119, MachineIntConstant(4)],
        SmallFixedBitVector(1),
        "`7 154405:63-154405:75",
        "zz4142",
    )
    i175 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i174, MachineIntConstant(1), MachineIntConstant(16)],
        SmallFixedBitVector(16),
        "`7 154405:52-154405:81",
        "zz4141",
    )
    i176 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0xFFFF, SmallFixedBitVector(16)),
            MachineIntConstant(16),
            i175,
        ],
        SmallFixedBitVector(32),
        "`7 154405:41-154405:81",
        "zz4137",
    )
    i177 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i176, MachineIntConstant(32), MachineIntConstant(2)],
        SmallFixedBitVector(64),
        "`7 154405:31-154405:85",
        "zz4132",
    )
    i178 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i171, i177],
        SmallFixedBitVector(64),
        "`7 154405:23-154405:85",
        "zz4128",
    )
    i179 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i120, MachineIntConstant(4)],
        SmallFixedBitVector(1),
        "`7 154405:109-154405:120",
        "zz4121",
    )
    i180 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i179, MachineIntConstant(1), MachineIntConstant(16)],
        SmallFixedBitVector(16),
        "`7 154405:98-154405:126",
        "zz4120",
    )
    i181 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i182 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i180,
            MachineIntConstant(16),
            SmallBitVectorConstant(0x0, SmallFixedBitVector(16)),
        ],
        SmallFixedBitVector(32),
        "`7 154405:98-154405:138",
        "zz4114",
    )
    i183 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i182, MachineIntConstant(32), MachineIntConstant(2)],
        SmallFixedBitVector(64),
        "`7 154405:88-154405:142",
        "zz4109",
    )
    i184 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i178, i183],
        SmallFixedBitVector(64),
        "`7 154405:23-154405:142",
        "zz4105",
    )
    i185 = block8.emit(Comment, "inlined zOnes", [], Unit(), None, None)
    i186 = block8.emit(Comment, "inlined zsail_ones", [], Unit(), None, None)
    i187 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i119, MachineIntConstant(5)],
        SmallFixedBitVector(1),
        "`7 154406:63-154406:75",
        "zz494",
    )
    i188 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i187, MachineIntConstant(1), MachineIntConstant(32)],
        SmallFixedBitVector(32),
        "`7 154406:52-154406:81",
        "zz493",
    )
    i189 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            SmallBitVectorConstant(0xFFFFFFFF, SmallFixedBitVector(32)),
            MachineIntConstant(32),
            i188,
        ],
        SmallFixedBitVector(64),
        "`7 154406:41-154406:81",
        "zz489",
    )
    i190 = block8.emit(
        Operation,
        "@and_vec_bv_bv",
        [i184, i189],
        SmallFixedBitVector(64),
        "`7 154406:23-154406:85",
        "zz480",
    )
    i191 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i120, MachineIntConstant(5)],
        SmallFixedBitVector(1),
        "`7 154406:109-154406:120",
        "zz473",
    )
    i192 = block8.emit(
        Operation,
        "@replicate_bv_i_i",
        [i191, MachineIntConstant(1), MachineIntConstant(32)],
        SmallFixedBitVector(32),
        "`7 154406:98-154406:126",
        "zz472",
    )
    i193 = block8.emit(Comment, "inlined zZeros", [], Unit(), None, None)
    i194 = block8.emit(
        Operation,
        "@bitvector_concat_bv_bv",
        [
            i192,
            MachineIntConstant(32),
            SmallBitVectorConstant(0x0, SmallFixedBitVector(32)),
        ],
        SmallFixedBitVector(64),
        "`7 154406:98-154406:138",
        "zz466",
    )
    i195 = block8.emit(
        Operation,
        "@or_vec_bv_bv",
        [i190, i194],
        SmallFixedBitVector(64),
        "`7 154406:23-154406:142",
        "zz457",
    )
    i196 = block8.emit(
        Comment, "inlined zinteger_access", [], Unit(), None, None
    )
    i197 = block8.emit(
        Comment, "inlined zinteger_subrange", [], Unit(), None, None
    )
    i198 = block8.emit(
        Operation,
        "@get_slice_int_i_i_i",
        [MachineIntConstant(1), i36, MachineIntConstant(6)],
        SmallFixedBitVector(1),
        "`5 176:39-176:72",
        "return",
    )
    i199 = block8.emit(
        Operation,
        "@vector_access_bv_i",
        [i198, MachineIntConstant(0)],
        SmallFixedBitVector(1),
        "`5 181:32-181:62",
        "return",
    )
    i200 = block8.emit(
        Operation,
        "@eq_bits_bv_bv",
        [i199, SmallBitVectorConstant(0b0, SmallFixedBitVector(1))],
        Bool(),
        "`7 154407:7-154407:23",
        "zz437",
    )
    block8.next = ConditionalGoto(
        i200, block9, block11, "`7 154407:4-154411:5"
    )
    i201 = block9.emit(
        Operation,
        "@or_vec_bv_bv",
        [i195, i118],
        SmallFixedBitVector(64),
        "`7 154410:16-154410:29",
        "zz444",
    )
    block9.next = Goto(block10, None)
    i202 = block10.emit_phi(
        [block9, block11], [i201, None], SmallFixedBitVector(64)
    )
    i203 = block10.emit(
        Operation,
        "@sub_i_i_must_fit",
        [zM, MachineIntConstant(1)],
        MachineInt(),
        "`7 154412:18-154412:23",
        "zz436",
    )
    i204 = block10.emit(
        Cast,
        "$cast",
        [i202],
        GenericBitVector(),
        "`7 154412:12-154412:29",
        "zz432",
    )
    i205 = block10.emit(
        Operation,
        "@vector_subrange_o_i_i",
        [i204, i203, MachineIntConstant(0)],
        GenericBitVector(),
        "`7 154412:12-154412:29",
        "zz421",
    )
    i206 = block10.emit(
        Cast,
        "$cast",
        [i118],
        GenericBitVector(),
        "`7 154412:31-154412:48",
        "zz425",
    )
    i207 = block10.emit(
        Operation,
        "@vector_subrange_o_i_i",
        [i206, i203, MachineIntConstant(0)],
        GenericBitVector(),
        "`7 154412:31-154412:48",
        "zz422",
    )
    i208 = block10.emit(
        PackPackedField,
        "$pack",
        [i205],
        Packed(GenericBitVector()),
        None,
        None,
    )
    i209 = block10.emit(
        PackPackedField,
        "$pack",
        [i207],
        Packed(GenericBitVector()),
        None,
        None,
    )
    i210 = block10.emit(
        StructConstruction,
        "ztuplez3z5bv_z5bv",
        [i208, i209],
        Struct(
            "ztuplez3z5bv_z5bv",
            ("ztuplez3z5bv_z5bv0", "ztuplez3z5bv_z5bv1"),
            (GenericBitVector(), GenericBitVector()),
            True,
        ),
        None,
        None,
    )
    block10.next = Return(i210, None)
    i211 = block11.emit(
        Operation,
        "@and_vec_bv_bv",
        [i195, i118],
        SmallFixedBitVector(64),
        "`7 154408:16-154408:29",
        "zz441",
    )
    i202.prevvalues[1] = i211
    block11.next = Goto(block10, None)
    block12.next = Raise(
        StringConstant("src/v8_base.sail:154381.32-154381.33"), None
    )
    block13.next = Raise(
        StringConstant("src/v8_base.sail:154380.26-154380.27"), None
    )
    graph = Graph(
        "zDecodeBitMasks", [zM, zimmN, zimms, zimmr, zimmediate], block0
    )
    codegen = FakeCodeGen()
    spec = Specializer(graph, codegen)
    key = (
        (MachineInt(), 32),
        (SmallFixedBitVector(1), None),
        (SmallFixedBitVector(6), None),
        (SmallFixedBitVector(6), None),
        (Bool(), False),
    )
    spec._make_stub(key)  # used to crash


def test_split_several():
    zb = Argument("zb", Bool())
    zi = Argument("zi", MachineInt())
    block0 = Block()
    block1 = Block()
    block3 = Block()
    block4 = Block()
    block0.next = ConditionalGoto(zb, block1, block4, "`1 13:27-16:1")
    block1.next = Goto(block3, None)
    i4 = block3.emit_phi(
        [block1, block4],
        [MachineIntConstant(64), MachineIntConstant(32)],
        MachineInt(),
    )
    i8 = block3.emit(Operation, "f", [i4], GenericBitVector())
    i9 = block3.emit(Operation, "h", [i8], MachineInt())
    block3.next = Return(i9, None)
    block4.next = Goto(block3, None)
    graph = Graph("g", [zb, zi], block0)

    fa = Argument("a", MachineInt())
    block0 = Block()
    i0 = block0.emit(Operation, "@zeros_i", [fa], GenericBitVector())
    block0.next = Return(i0)
    fgraph = Graph("f", [fa], block0)

    ha = Argument("a", GenericBitVector())
    block0 = Block()
    i0 = block0.emit(Operation, "@length_unwrapped_res", [ha], MachineInt())
    block0.next = Return(i0)
    hgraph = Graph("h", [ha], block0)

    codegen = FakeCodeGen()
    fspec = Specializer(fgraph, codegen)
    codegen.specialization_functions["f"] = fspec
    hspec = Specializer(hgraph, codegen)
    codegen.specialization_functions["h"] = hspec

    codegen.schedule_graph_specialization(graph)
    codegen.schedule_graph_specialization(fgraph)
    codegen.schedule_graph_specialization(hgraph)
    codegen.specialize_all()
    for block in graph.iterblocks():
        if isinstance(block.next, Return):
            assert isinstance(block.next.value, Phi)
            assert [
                isinstance(prev, MachineIntConstant)
                for prev in block.next.value.prevvalues
            ]


def test_spec_bug():
    # this turned out to really be a bug in _remove_unreachable_phi_prevvalues,
    # but this was a simple way to reproduce it
    zwidth = Argument("zwidth", MachineInt())
    zn = Argument("zn", Int())
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
    i2 = block0.emit(
        Operation, "zz5izDzKz5i64", [zn], MachineInt(), None, None
    )
    i3 = block0.emit(
        Operation,
        "@gteq",
        [i2, MachineIntConstant(0)],
        Bool(),
        "`7 151878:11-151878:17",
        "zz432",
    )
    block0.next = ConditionalGoto(i3, block1, block9, "`7 151878:11-151878:27")
    i4 = block1.emit(
        Operation,
        "@lteq",
        [i2, MachineIntConstant(31)],
        Bool(),
        "`7 151878:20-151878:27",
        "zz433",
    )
    i5 = block1.emit(
        Comment,
        "sail_assert src/v8_base.sail:151878.27-151878.28",
        [],
        Unit(),
        None,
        None,
    )
    block1.next = ConditionalGoto(i4, block2, block9, "`7 151877:29-151881:1")
    i6 = block2.emit(
        Operation,
        "@eq",
        [zwidth, MachineIntConstant(8)],
        Bool(),
        "`7 151879:11-151879:21",
        "zz412",
    )
    block2.next = ConditionalGoto(i6, block3, block4, "`7 151879:11-151879:78")
    i7 = block3.emit_phi(
        [block2, block4, block5, block6, block7],
        [
            MachineIntConstant(7),
            MachineIntConstant(15),
            MachineIntConstant(31),
            MachineIntConstant(63),
            MachineIntConstant(127),
        ],
        MachineInt(),
    )
    i8 = block3.emit(
        GlobalRead, "z_Z", [], FVec(32, BigFixedBitVector(2048)), None, None
    )
    i9 = block3.emit(
        Cast,
        "$cast",
        [i8],
        Vec(BigFixedBitVector(2048)),
        "`7 151880:11-151880:16",
        "zz49",
    )
    i10 = block3.emit(
        Operation,
        "@vector_access_o_i",
        [i9, i2],
        BigFixedBitVector(2048),
        "`7 151880:11-151880:16",
        "zz41",
    )
    i11 = block3.emit(
        Cast,
        "$cast",
        [i10],
        GenericBitVector(),
        "`7 151880:11-151880:32",
        "zz44",
    )
    i12 = block3.emit(
        Operation,
        "@vector_subrange_o_i_i",
        [i11, i7, MachineIntConstant(0)],
        GenericBitVector(),
        "`7 151880:11-151880:32",
        "zz40",
    )
    block3.next = Return(i12, None)
    i13 = block4.emit(
        Operation,
        "@eq",
        [zwidth, MachineIntConstant(16)],
        Bool(),
        "`7 151879:24-151879:35",
        "zz414",
    )
    block4.next = ConditionalGoto(
        i13, block3, block5, "`7 151879:24-151879:78"
    )
    i14 = block5.emit(
        Operation,
        "@eq",
        [zwidth, MachineIntConstant(32)],
        Bool(),
        "`7 151879:38-151879:49",
        "zz416",
    )
    block5.next = ConditionalGoto(
        i14, block3, block6, "`7 151879:38-151879:78"
    )
    i15 = block6.emit(
        Operation,
        "@eq",
        [zwidth, MachineIntConstant(64)],
        Bool(),
        "`7 151879:52-151879:63",
        "zz418",
    )
    block6.next = ConditionalGoto(
        i15, block3, block7, "`7 151879:52-151879:78"
    )
    i16 = block7.emit(
        Operation,
        "@eq",
        [zwidth, MachineIntConstant(128)],
        Bool(),
        "`7 151879:66-151879:78",
        "zz419",
    )
    i17 = block7.emit(
        Comment,
        "sail_assert src/v8_base.sail:151879.78-151879.79",
        [],
        Unit(),
        None,
        None,
    )
    block7.next = ConditionalGoto(i16, block3, block8, "`7 151877:29-151881:1")
    block8.next = Raise(
        StringConstant("src/v8_base.sail:151879.78-151879.79"), None
    )
    block9.next = Raise(
        StringConstant("src/v8_base.sail:151878.27-151878.28"), None
    )
    graph = Graph("zV_read", [zwidth, zn], block0)

    codegen = FakeCodeGen()
    spec = Specializer(graph, codegen)
    key = ((MachineInt(), 64), (MachineInt(), None))
    res = spec._make_stub(key)  # used to crash


def test_split_by_rangeset():
    zb = Argument("zb", Bool())
    zi = Argument("zi", MachineInt())
    block0 = Block()
    block1 = Block()
    block3 = Block()
    block4 = Block()
    block0.next = ConditionalGoto(zb, block1, block4, "`1 13:27-16:1")
    block1.next = Goto(block3, None)
    i4 = block3.emit_phi(
        [block1, block4],
        [MachineIntConstant(2), MachineIntConstant(4)],
        MachineInt(),
    )
    i5 = block3.emit_phi(
        [block1, block4],
        [MachineIntConstant(6), MachineIntConstant(8)],
        MachineInt(),
    )
    i6 = block3.emit(
        Operation,
        "@add_i_i_must_fit",
        [i4, i5],
        MachineInt(),
    )
    i8 = block3.emit(Operation, "f", [i6], GenericBitVector())
    i9 = block3.emit(Operation, "@length_unwrapped_res", [i8], MachineInt())
    block3.next = Return(i9, None)
    block4.next = Goto(block3, None)
    graph = Graph("g", [zb, zi], block0)

    fa = Argument("a", MachineInt())
    block0 = Block()
    block1 = Block()
    block2 = Block()
    i0 = block0.emit(Operation, "@zeros_i", [fa], GenericBitVector())
    block0.next = Return(i0)
    fgraph = Graph("f", [fa], block0)

    codegen = FakeCodeGen()
    fspec = Specializer(fgraph, codegen)
    codegen.specialization_functions["f"] = fspec

    codegen.schedule_graph_specialization(graph)
    codegen.schedule_graph_specialization(fgraph)
    codegen.specialize_all()
    assert len(fspec.cache) == 3

def test_graph_hangs():
    fakecodegen = FakeCodeGen()
    fakecodegen.specialization_functions['zsizze_bytes_backwards'] = True
    fakecodegen.specialization_functions['zinit_masked_result'] = True

    zword_width = Enum('zword_width', ('zBYTE', 'zHALF', 'zWORD', 'zDOUBLE'))
    ztuplez3z5vecz8z5bvz9_z5vecz8z5boolz9 = Struct('ztuplez3z5vecz8z5bvz9_z5vecz8z5boolz9', ('ztuplez3z5vecz8z5bvz9_z5vecz8z5boolz90', 'ztuplez3z5vecz8z5bvz9_z5vecz8z5boolz91'), (Vec(GenericBitVector()), Vec(Bool())), True)
    zRetired = Enum('zRetired', ('zRETIRE_SUCCESS', 'zRETIRE_FAIL'))
    zAccessTypezIuzK = Union('zAccessTypezIuzK', ('zExecutezIuzK', 'zReadzIuzK', 'zReadWritezIuzK', 'zWritezIuzK'), (Unit(), Unit(), Struct('ztuplez3z5unit_z5unit', ('ztuplez3z5unit_z5unit0', 'ztuplez3z5unit_z5unit1'), (Unit(), Unit()), True), Unit()))
    zTR_ResultzIUExceptionTypezIzKzCbzK = Union('zTR_ResultzIUExceptionTypezIzKzCbzK', ('zTR_AddresszIUExceptionTypezIzKzCbzK', 'zTR_FailurezIUExceptionTypezIzKzCbzK'), (Struct('ztuplez3z5bv_z5unit', ('ztuplez3z5bv_z5unit0', 'ztuplez3z5bv_z5unit1'), (GenericBitVector(), Unit()), True), Struct('ztuplez3z5unionz0zzExceptionType_z5unit', ('ztuplez3z5unionz0zzExceptionType_z5unit0', 'ztuplez3z5unionz0zzExceptionType_z5unit1'), (Union('zExceptionType', ('zE_Breakpoint', 'zE_Extension', 'zE_Fetch_Access_Fault', 'zE_Fetch_Addr_Align', 'zE_Fetch_Page_Fault', 'zE_Illegal_Instr', 'zE_Load_Access_Fault', 'zE_Load_Addr_Align', 'zE_Load_Page_Fault', 'zE_M_EnvCall', 'zE_Reserved_10', 'zE_Reserved_14', 'zE_SAMO_Access_Fault', 'zE_SAMO_Addr_Align', 'zE_SAMO_Page_Fault', 'zE_S_EnvCall', 'zE_U_EnvCall'), (Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit())), Unit()), True)))
    ztuplez3z5bv_z5unit = Struct('ztuplez3z5bv_z5unit', ('ztuplez3z5bv_z5unit0', 'ztuplez3z5bv_z5unit1'), (GenericBitVector(), Unit()), True)
    zMstatus = Struct('zMstatus', ('zbits',), (SmallFixedBitVector(64),))
    zPrivilege = Enum('zPrivilege', ('zUser', 'zSupervisor', 'zMachine'))
    zMemoryOpResultzIz8bzCuz9zK = Union('zMemoryOpResultzIz8bzCuz9zK', ('zMemExceptionzIz8bzCuz9zK', 'zMemValuezIz8bzCuz9zK'), (Union('zExceptionType', ('zE_Breakpoint', 'zE_Extension', 'zE_Fetch_Access_Fault', 'zE_Fetch_Addr_Align', 'zE_Fetch_Page_Fault', 'zE_Illegal_Instr', 'zE_Load_Access_Fault', 'zE_Load_Addr_Align', 'zE_Load_Page_Fault', 'zE_M_EnvCall', 'zE_Reserved_10', 'zE_Reserved_14', 'zE_SAMO_Access_Fault', 'zE_SAMO_Addr_Align', 'zE_SAMO_Page_Fault', 'zE_S_EnvCall', 'zE_U_EnvCall'), (Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit())), Struct('ztuplez3z5bv_z5unit', ('ztuplez3z5bv_z5unit0', 'ztuplez3z5bv_z5unit1'), (GenericBitVector(), Unit()), True)))
    zMemoryOpResultzIbzK = Union('zMemoryOpResultzIbzK', ('zMemExceptionzIbzK', 'zMemValuezIbzK'), (Union('zExceptionType', ('zE_Breakpoint', 'zE_Extension', 'zE_Fetch_Access_Fault', 'zE_Fetch_Addr_Align', 'zE_Fetch_Page_Fault', 'zE_Illegal_Instr', 'zE_Load_Access_Fault', 'zE_Load_Addr_Align', 'zE_Load_Page_Fault', 'zE_M_EnvCall', 'zE_Reserved_10', 'zE_Reserved_14', 'zE_SAMO_Access_Fault', 'zE_SAMO_Addr_Align', 'zE_SAMO_Page_Fault', 'zE_S_EnvCall', 'zE_U_EnvCall'), (Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit())), GenericBitVector()))
    zExceptionType = Union('zExceptionType', ('zE_Breakpoint', 'zE_Extension', 'zE_Fetch_Access_Fault', 'zE_Fetch_Addr_Align', 'zE_Fetch_Page_Fault', 'zE_Illegal_Instr', 'zE_Load_Access_Fault', 'zE_Load_Addr_Align', 'zE_Load_Page_Fault', 'zE_M_EnvCall', 'zE_Reserved_10', 'zE_Reserved_14', 'zE_SAMO_Access_Fault', 'zE_SAMO_Addr_Align', 'zE_SAMO_Page_Fault', 'zE_S_EnvCall', 'zE_U_EnvCall'), (Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit()))
    zoptionzIbzK = Union('zoptionzIbzK', ('zNonezIbzK', 'zSomezIbzK'), (Unit(), GenericBitVector()))
    zoptionzIuzK = Union('zoptionzIuzK', ('zNonezIuzK', 'zSomezIuzK'), (Unit(), Unit()))
    zsync_exception = Struct('zsync_exception', ('zexcinfo', 'zext', 'ztrap'), (Union('zoptionzIbzK', ('zNonezIbzK', 'zSomezIbzK'), (Unit(), GenericBitVector())), Union('zoptionzIuzK', ('zNonezIuzK', 'zSomezIuzK'), (Unit(), Unit())), Union('zExceptionType', ('zE_Breakpoint', 'zE_Extension', 'zE_Fetch_Access_Fault', 'zE_Fetch_Addr_Align', 'zE_Fetch_Page_Fault', 'zE_Illegal_Instr', 'zE_Load_Access_Fault', 'zE_Load_Addr_Align', 'zE_Load_Page_Fault', 'zE_M_EnvCall', 'zE_Reserved_10', 'zE_Reserved_14', 'zE_SAMO_Access_Fault', 'zE_SAMO_Addr_Align', 'zE_SAMO_Page_Fault', 'zE_S_EnvCall', 'zE_U_EnvCall'), (Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit()))))
    zctl_result = Union('zctl_result', ('zCTL_MRET', 'zCTL_SRET', 'zCTL_TRAP', 'zCTL_URET'), (Unit(), Unit(), Struct('zsync_exception', ('zexcinfo', 'zext', 'ztrap'), (Union('zoptionzIbzK', ('zNonezIbzK', 'zSomezIbzK'), (Unit(), GenericBitVector())), Union('zoptionzIuzK', ('zNonezIuzK', 'zSomezIuzK'), (Unit(), Unit())), Union('zExceptionType', ('zE_Breakpoint', 'zE_Extension', 'zE_Fetch_Access_Fault', 'zE_Fetch_Addr_Align', 'zE_Fetch_Page_Fault', 'zE_Illegal_Instr', 'zE_Load_Access_Fault', 'zE_Load_Addr_Align', 'zE_Load_Page_Fault', 'zE_M_EnvCall', 'zE_Reserved_10', 'zE_Reserved_14', 'zE_SAMO_Access_Fault', 'zE_SAMO_Addr_Align', 'zE_SAMO_Page_Fault', 'zE_S_EnvCall', 'zE_U_EnvCall'), (Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit())))), Unit()))
    ztuplez3z5unionz0zzExceptionType_z5unit = Struct('ztuplez3z5unionz0zzExceptionType_z5unit', ('ztuplez3z5unionz0zzExceptionType_z5unit0', 'ztuplez3z5unionz0zzExceptionType_z5unit1'), (Union('zExceptionType', ('zE_Breakpoint', 'zE_Extension', 'zE_Fetch_Access_Fault', 'zE_Fetch_Addr_Align', 'zE_Fetch_Page_Fault', 'zE_Illegal_Instr', 'zE_Load_Access_Fault', 'zE_Load_Addr_Align', 'zE_Load_Page_Fault', 'zE_M_EnvCall', 'zE_Reserved_10', 'zE_Reserved_14', 'zE_SAMO_Access_Fault', 'zE_SAMO_Addr_Align', 'zE_SAMO_Page_Fault', 'zE_S_EnvCall', 'zE_U_EnvCall'), (Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit(), Unit())), Unit()), True)
    znf = Argument('znf', MachineInt())
    zvm = Argument('zvm', SmallFixedBitVector(1))
    zvd = Argument('zvd', SmallFixedBitVector(5))
    zload_width_bytes = Argument('zload_width_bytes', MachineInt())
    zrs1 = Argument('zrs1', SmallFixedBitVector(5))
    zEMUL_pow = Argument('zEMUL_pow', Int())
    znum_elem = Argument('znum_elem', Int())
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
    block10 = Block()
    block11 = Block()
    block12 = Block()
    block13 = Block()
    block14 = Block()
    block15 = Block()
    block16 = Block()
    block17 = Block()
    block18 = Block()
    block19 = Block()
    block20 = Block()
    block21 = Block()
    block22 = Block()
    block23 = Block()
    block24 = Block()
    block25 = Block()
    block26 = Block()
    block27 = Block()
    block28 = Block()
    i7 = block0.emit(RangeCheck, '$rangecheck', [znum_elem, IntConstant(1), IntConstant(1180591620717411303360L), StringConstant("Argument 'znum_elem' of function 'zprocess_vlseg'")], Unit(), None, None)
    i8 = block0.emit(ValueSetCheck, '$valuesetcheck', [zEMUL_pow, StringConstant("Argument 'zEMUL_pow' of function 'zprocess_vlseg'"), IntConstant(-6), IntConstant(-5), IntConstant(-4), IntConstant(-3), IntConstant(-2), IntConstant(-1), IntConstant(0), IntConstant(1), IntConstant(2), IntConstant(3), IntConstant(4), IntConstant(5), IntConstant(6)], Unit(), None, None)
    i9 = block0.emit(ValueSetCheck, '$valuesetcheck', [zload_width_bytes, StringConstant("Argument 'zload_width_bytes' of function 'zprocess_vlseg'"), IntConstant(1), IntConstant(2), IntConstant(4), IntConstant(8)], Unit(), None, None)
    i10 = block0.emit(ValueSetCheck, '$valuesetcheck', [znf, StringConstant("Argument 'znf' of function 'zprocess_vlseg'"), IntConstant(1), IntConstant(2), IntConstant(3), IntConstant(4), IntConstant(5), IntConstant(6), IntConstant(7), IntConstant(8)], Unit(), None, None)
    i11 = block0.emit(Operation, 'zlteq_int', [zEMUL_pow, IntConstant(0)], Bool(), '`57 72:26-72:39', 'zz4142')
    block0.next = ConditionalGoto(i11, block1, block28, '`57 72:23-72:66')
    block1.next = Goto(block2, None)
    i12 = block2.emit_phi([block28, block1], [None, IntConstant(1)], Int())
    i13 = block2.emit(Operation, 'zsizze_bytes_backwards', [zload_width_bytes], zword_width, '`57 73:32-73:60', 'zz41')
    i14 = block2.emit(Operation, 'zread_vmask', [znum_elem, zvm, SmallBitVectorConstant(0b0, SmallFixedBitVector(5))], Vec(Bool()), '`57 74:34-74:67', 'zz42')
    i15 = block2.emit(Operation, '@shl_int_i_i_must_fit', [zload_width_bytes, MachineIntConstant(3)], MachineInt(), '`57 75:71-75:91', 'zz4141')
    i16 = block2.emit(Operation, 'zz5i64zDzKz5i', [i15], Int(), '`57 75:47-75:110', 'zz4137')
    i17 = block2.emit(Operation, 'zz5i64zDzKz5i', [znf], Int(), '`57 75:47-75:110', 'zz4138')
    i18 = block2.emit(Operation, 'zread_vreg_seg', [znum_elem, i16, zEMUL_pow, i17, zvd], Vec(GenericBitVector()), '`57 75:47-75:110', 'zz43')
    i19 = block2.emit(Operation, '@mult_i_i_must_fit', [znf, zload_width_bytes], MachineInt(), '`57 77:52-77:73', 'zz4135')
    i20 = block2.emit(Operation, '@shl_int_i_i_must_fit', [i19, MachineIntConstant(3)], MachineInt(), '`57 77:52-77:77', 'zz4132')
    i21 = block2.emit(Operation, 'zz5i64zDzKz5i', [i20], Int(), '`57 77:23-77:104', 'zz4128')
    i22 = block2.emit(Operation, 'zinit_masked_result', [znum_elem, i21, zEMUL_pow, i18, i14], ztuplez3z5vecz8z5bvz9_z5vecz8z5boolz9, '`57 77:23-77:104', 'zz44')
    i23 = block2.emit(FieldAccess, 'ztuplez3z5vecz8z5bvz9_z5vecz8z5boolz90', [i22], Vec(GenericBitVector()), None, None)
    i24 = block2.emit(FieldAccess, 'ztuplez3z5vecz8z5bvz9_z5vecz8z5boolz91', [i22], Vec(Bool()), None, None)
    i25 = block2.emit(Operation, '@sub_o_i_wrapped_res', [znum_elem, MachineIntConstant(1)], Int(), '`57 79:24-79:36', 'zz4125')
    i26 = block2.emit(Operation, 'zz5izDzKz5i64', [i25], MachineInt(), '`57 79:24-79:36', 'zz410')
    block2.next = Goto(block3, None)
    i27 = block3.emit_phi([block2, block9], [MachineIntConstant(0), None], MachineInt())
    i28 = block3.emit(Operation, '@gt', [i27, i26], Bool(), '`57 79:2-106:3', None)
    block3.next = ConditionalGoto(i28, block4, block6, '`57 79:2-106:3')
    i29 = block4.emit(GlobalWrite, 'zvstart', [SmallBitVectorConstant(0x0, SmallFixedBitVector(16))], SmallFixedBitVector(16), None, None)
    block4.next = Goto(block5, None)
    i30 = block5.emit_phi([block22, block20, block24, block4], [EnumConstant('zRETIRE_FAIL', Enum('zRetired', ('zRETIRE_SUCCESS', 'zRETIRE_FAIL'))), EnumConstant('zRETIRE_FAIL', Enum('zRetired', ('zRETIRE_SUCCESS', 'zRETIRE_FAIL'))), EnumConstant('zRETIRE_FAIL', Enum('zRetired', ('zRETIRE_SUCCESS', 'zRETIRE_FAIL'))), EnumConstant('zRETIRE_SUCCESS', Enum('zRetired', ('zRETIRE_SUCCESS', 'zRETIRE_FAIL')))], zRetired)
    block5.next = Return(i30, None)
    i31 = block6.emit(Operation, '@vector_access_o_i', [i24, i27], Bool(), '`57 80:7-80:14', 'zz415')
    block6.next = ConditionalGoto(i31, block7, block25, '`57 80:4-105:5')
    i32 = block7.emit(Comment, 'inlined zto_bits', [], Unit(), None, None)
    i33 = block7.emit(Operation, '@get_slice_int_i_i_i', [MachineIntConstant(16), i27, MachineIntConstant(0)], SmallFixedBitVector(16), '`5 119:26-119:48', 'return')
    i34 = block7.emit(GlobalWrite, 'zvstart', [i33], SmallFixedBitVector(16), None, None)
    i35 = block7.emit(Operation, '@sub_i_i_must_fit', [znf, MachineIntConstant(1)], MachineInt(), '`57 82:28-82:34', 'zz469')
    block7.next = Goto(block8, None)
    i36 = block8.emit_phi([block7, block21], [MachineIntConstant(0), None], MachineInt())
    i37 = block8.emit(Operation, '@gt', [i36, i35], Bool(), '`57 82:6-99:7', None)
    block8.next = ConditionalGoto(i37, block9, block10, '`57 82:6-99:7')
    i38 = block9.emit(Operation, '@iadd', [i27, MachineIntConstant(1)], MachineInt(), '`57 79:2-106:3', 'zz413')
    i27.prevvalues[1] = i38
    block9.next = Goto(block3, None)
    i39 = block10.emit(Operation, 'zz5i64zDzKz5i', [i27], Int(), '`57 83:27-83:33', 'zz464')
    i40 = block10.emit(Operation, '@mult_i_i_wrapped_res', [i27, znf], Int(), '`57 83:27-83:33', 'zz462')
    i41 = block10.emit(Operation, '@add_o_i_wrapped_res', [i40, i36], Int(), '`57 83:27-83:37', 'zz460')
    i42 = block10.emit(Operation, '@mult_o_i_wrapped_res', [i41, zload_width_bytes], Int(), '`57 83:26-83:57', 'zz421')
    i43 = block10.emit(Comment, 'inlined zto_bits', [], Unit(), None, None)
    i44 = block10.emit(Operation, '@get_slice_int_i_o_i_unwrapped_res', [MachineIntConstant(64), i42, MachineIntConstant(0)], SmallFixedBitVector(64), '`5 119:26-119:48', 'return')
    i45 = block10.emit(Comment, 'inlined zext_data_get_addr', [], Unit(), None, None)
    i46 = block10.emit(Comment, 'inlined zrX_bits', [], Unit(), None, None)
    i47 = block10.emit(Operation, '@unsigned_bv', [zrs1, MachineIntConstant(5)], MachineInt(), '`17 145:45-145:56', 'zz42')
    i48 = block10.emit(Operation, 'zrX', [i47], SmallFixedBitVector(64), '`17 145:42-145:57', 'return')
    i49 = block10.emit(Operation, '@add_bits_bv_bv', [i48, i44, MachineIntConstant(64)], SmallFixedBitVector(64), '`24 59:13-59:29', 'zz44')
    i50 = block10.emit(Comment, 'inlined zcheck_misaligned', [], Unit(), None, None)
    i51 = block10.emit(Operation, 'zplat_enable_misaligned_access', [UnitConstant.UNIT], Bool(), '`39 321:6-321:37', 'zz43')
    i52 = block10.emit(Comment, 'inlined znot', [], Unit(), None, None)
    block10.next = ConditionalGoto(i51, block11, block23, '`39 321:2-321:70')
    i53 = block11.emit(Operation, 'zReadzIuzK', [UnitConstant.UNIT], zAccessTypezIuzK, '`57 89:46-89:56', 'zz453')
    i54 = block11.emit(Operation, 'ztranslateAddr', [i49, i53], zTR_ResultzIUExceptionTypezIzKzCbzK, '`57 89:25-89:57', 'zz428')
    i55 = block11.emit(GlobalRead, 'have_exception', [], Bool(), None, None)
    block11.next = ConditionalGoto(i55, block12, block13, '`57 89:25-89:57')
    block12.next = Return(DefaultValue(Enum('zRetired', ('zRETIRE_SUCCESS', 'zRETIRE_FAIL'))), None)
    i56 = block13.emit(UnionVariantCheck, 'zTR_FailurezIUExceptionTypezIzKzCbzK', [i54], Bool(), '`57 90:16-90:32', None)
    block13.next = ConditionalGoto(i56, block14, block22, '`57 90:16-90:32')
    i57 = block14.emit(UnionVariantCheck, 'zTR_AddresszIUExceptionTypezIzKzCbzK', [i54], Bool(), '`57 91:16-91:36', None)
    block14.next = ConditionalGoto(i57, block15, block16, '`57 91:16-91:36')
    block15.next = Raise(StringConstant('match'), '`57 89:19-97:15')
    i58 = block16.emit(UnionCast, 'zTR_AddresszIUExceptionTypezIzKzCbzK', [i54], ztuplez3z5bv_z5unit, None, None)
    i59 = block16.emit(FieldAccess, 'ztuplez3z5bv_z5unit0', [i58], Packed(GenericBitVector()), None, None)
    i60 = block16.emit(RangeCheck, '$rangecheck', [i59, IntConstant(0), IntConstant(9223372036854775807), StringConstant("Access to field 'ztuplez3z5bv_z5unit0' of struct 'ztuplez3z5bv_z5unit'")], Unit(), None, None)
    i61 = block16.emit(Operation, '@packed_field_cast_smallfixedbitvector', [MachineIntConstant(64), i59], SmallFixedBitVector(64), '`57 91:27-91:32', None)
    i62 = block16.emit(Operation, 'zReadzIuzK', [UnitConstant.UNIT], zAccessTypezIuzK, '`57 92:33-92:43', 'zz450')
    i63 = block16.emit(Comment, 'inlined zmem_read', [], Unit(), None, None)
    i64 = block16.emit(GlobalRead, 'zmstatus', [], zMstatus, None, None)
    i65 = block16.emit(GlobalRead, 'zcur_privilege', [], zPrivilege, None, None)
    i66 = block16.emit(Operation, 'zeffectivePrivilege', [i62, i64, i65], zPrivilege, '`32 167:21-167:68', 'zz40')
    i67 = block16.emit(Comment, 'inlined zmem_read_priv', [], Unit(), None, None)
    i68 = block16.emit(Operation, 'zmem_read_priv_meta', [i62, i66, i61, zload_width_bytes, BooleanConstant.FALSE, BooleanConstant.FALSE, BooleanConstant.FALSE, BooleanConstant.FALSE], zMemoryOpResultzIz8bzCuz9zK, '`32 163:27-163:90', 'zz40')
    i69 = block16.emit(GlobalRead, 'have_exception', [], Bool(), None, None)
    block16.next = ConditionalGoto(i69, block12, block17, '`32 163:27-163:90')
    i70 = block17.emit(Operation, 'zMemoryOpResult_drop_metazIbzK', [i68], zMemoryOpResultzIbzK, '`32 163:2-163:91', 'return')
    i71 = block17.emit(UnionVariantCheck, 'zMemValuezIbzK', [i70], Bool(), '`57 93:20-93:34', None)
    block17.next = ConditionalGoto(i71, block18, block21, '`57 93:20-93:34')
    i72 = block18.emit(UnionVariantCheck, 'zMemExceptionzIbzK', [i70], Bool(), '`57 94:20-94:35', None)
    block18.next = ConditionalGoto(i72, block19, block20, '`57 94:20-94:35')
    block19.next = Raise(StringConstant('match'), '`57 92:18-95:19')
    i73 = block20.emit(UnionCast, 'zMemExceptionzIbzK', [i70], zExceptionType, None, None)
    i74 = block20.emit(Comment, 'inlined zhandle_mem_exception', [], Unit(), None, None)
    i75 = block20.emit(Cast, '$cast', [i49], GenericBitVector(), '`30 479:46-479:56', 'zz45')
    i76 = block20.emit(Operation, 'zSomezIbzK', [i75], zoptionzIbzK, '`30 479:46-479:56', 'zz43')
    i77 = block20.emit(Operation, 'zNonezIuzK', [UnitConstant.UNIT], zoptionzIuzK, '`30 480:46-480:52', 'zz44')
    i78 = block20.emit(StructConstruction, 'zsync_exception', [i76, i77, i73], zsync_exception, '`30 478:27-480:54', None)
    i79 = block20.emit(Operation, 'zCTL_TRAP', [i78], zctl_result, '`30 481:47-481:58', 'zz42')
    i80 = block20.emit(GlobalRead, 'zcur_privilege', [], zPrivilege, None, None)
    i81 = block20.emit(GlobalRead, 'zPC', [], SmallFixedBitVector(64), None, None)
    i82 = block20.emit(Operation, 'zexception_handler', [i80, i79, i81], SmallFixedBitVector(64), '`30 481:14-481:63', 'zz41')
    i83 = block20.emit(Comment, 'inlined zset_next_pc', [], Unit(), None, None)
    i84 = block20.emit(GlobalWrite, 'znextPC', [i82], SmallFixedBitVector(64), None, None)
    block20.next = Goto(block5, None)
    i85 = block21.emit(UnionCast, 'zMemValuezIbzK', [i70], GenericBitVector(), None, None)
    i86 = block21.emit(Operation, '@shl_int_i_i_must_fit', [zload_width_bytes, MachineIntConstant(3)], MachineInt(), '`57 93:61-93:81', 'zz449')
    i87 = block21.emit(Operation, '@mult_o_i_wrapped_res', [i12, i36], Int(), '`57 93:102-93:114', 'zz443')
    i88 = block21.emit(Comment, 'inlined zto_bits', [], Unit(), None, None)
    i89 = block21.emit(Operation, '@get_slice_int_i_o_i_unwrapped_res', [MachineIntConstant(5), i87, MachineIntConstant(0)], SmallFixedBitVector(5), '`5 119:26-119:48', 'return')
    i90 = block21.emit(Operation, '@add_bits_bv_bv', [zvd, i89, MachineIntConstant(5)], SmallFixedBitVector(5), '`57 93:86-93:115', 'zz442')
    i91 = block21.emit(Operation, 'zwrite_single_element', [i86, i39, i90, i85], Unit(), '`57 93:40-93:122', 'zz432')
    i92 = block21.emit(Operation, '@iadd', [i36, MachineIntConstant(1)], MachineInt(), '`57 82:6-99:7', 'zz419')
    i36.prevvalues[1] = i92
    block21.next = Goto(block8, None)
    i93 = block22.emit(UnionCast, 'zTR_FailurezIUExceptionTypezIzKzCbzK', [i54], ztuplez3z5unionz0zzExceptionType_z5unit, None, None)
    i94 = block22.emit(FieldAccess, 'ztuplez3z5unionz0zzExceptionType_z5unit0', [i93], zExceptionType, None, None)
    i95 = block22.emit(Comment, 'inlined zhandle_mem_exception', [], Unit(), None, None)
    i96 = block22.emit(Cast, '$cast', [i49], GenericBitVector(), '`30 479:46-479:56', 'zz45')
    i97 = block22.emit(Operation, 'zSomezIbzK', [i96], zoptionzIbzK, '`30 479:46-479:56', 'zz43')
    i98 = block22.emit(Operation, 'zNonezIuzK', [UnitConstant.UNIT], zoptionzIuzK, '`30 480:46-480:52', 'zz44')
    i99 = block22.emit(StructConstruction, 'zsync_exception', [i97, i98, i94], zsync_exception, '`30 478:27-480:54', None)
    i100 = block22.emit(Operation, 'zCTL_TRAP', [i99], zctl_result, '`30 481:47-481:58', 'zz42')
    i101 = block22.emit(GlobalRead, 'zcur_privilege', [], zPrivilege, None, None)
    i102 = block22.emit(GlobalRead, 'zPC', [], SmallFixedBitVector(64), None, None)
    i103 = block22.emit(Operation, 'zexception_handler', [i101, i100, i102], SmallFixedBitVector(64), '`30 481:14-481:63', 'zz41')
    i104 = block22.emit(Comment, 'inlined zset_next_pc', [], Unit(), None, None)
    i105 = block22.emit(GlobalWrite, 'znextPC', [i103], SmallFixedBitVector(64), None, None)
    block22.next = Goto(block5, None)
    i106 = block23.emit(Operation, 'zis_aligned', [i49, i13], Bool(), '`39 321:45-321:69', 'zz42')
    i107 = block23.emit(Comment, 'inlined znot', [], Unit(), None, None)
    block23.next = ConditionalGoto(i106, block11, block24, '`57 87:14-97:15')
    i108 = block24.emit(Operation, 'zE_Load_Addr_Align', [UnitConstant.UNIT], zExceptionType, '`57 88:49-88:68', 'zz426')
    i109 = block24.emit(Comment, 'inlined zhandle_mem_exception', [], Unit(), None, None)
    i110 = block24.emit(Cast, '$cast', [i49], GenericBitVector(), '`30 479:46-479:56', 'zz45')
    i111 = block24.emit(Operation, 'zSomezIbzK', [i110], zoptionzIbzK, '`30 479:46-479:56', 'zz43')
    i112 = block24.emit(Operation, 'zNonezIuzK', [UnitConstant.UNIT], zoptionzIuzK, '`30 480:46-480:52', 'zz44')
    i113 = block24.emit(StructConstruction, 'zsync_exception', [i111, i112, i108], zsync_exception, '`30 478:27-480:54', None)
    i114 = block24.emit(Operation, 'zCTL_TRAP', [i113], zctl_result, '`30 481:47-481:58', 'zz42')
    i115 = block24.emit(GlobalRead, 'zcur_privilege', [], zPrivilege, None, None)
    i116 = block24.emit(GlobalRead, 'zPC', [], SmallFixedBitVector(64), None, None)
    i117 = block24.emit(Operation, 'zexception_handler', [i115, i114, i116], SmallFixedBitVector(64), '`30 481:14-481:63', 'zz41')
    i118 = block24.emit(Comment, 'inlined zset_next_pc', [], Unit(), None, None)
    i119 = block24.emit(GlobalWrite, 'znextPC', [i117], SmallFixedBitVector(64), None, None)
    block24.next = Goto(block5, None)
    i120 = block25.emit(Operation, '@sub_i_i_must_fit', [znf, MachineIntConstant(1)], MachineInt(), '`57 101:28-101:34', 'zz4120')
    block25.next = Goto(block26, None)
    i121 = block26.emit_phi([block25, block27], [MachineIntConstant(0), None], MachineInt())
    i122 = block26.emit(Operation, '@gt', [i121, i120], Bool(), '`57 101:6-104:7', None)
    block26.next = ConditionalGoto(i122, block9, block27, '`57 101:6-104:7')
    i123 = block27.emit(Operation, 'zz5i64zDzKz5i', [i27], Int(), '`57 102:28-102:37', 'zz4116')
    i124 = block27.emit(Operation, '@vector_access_o_i', [i23, i27], GenericBitVector(), '`57 102:28-102:37', 'zz4106')
    i125 = block27.emit(Operation, '@mult_i_i_must_fit', [i121, zload_width_bytes], MachineInt(), '`57 102:42-102:62', 'zz4115')
    i126 = block27.emit(Operation, '@shl_int_i_i_must_fit', [i125, MachineIntConstant(3)], MachineInt(), '`57 102:42-102:66', 'zz4112')
    i127 = block27.emit(Operation, '@shiftr_o_i', [i124, i126], GenericBitVector(), '`57 102:28-102:67', 'zz495')
    i128 = block27.emit(Operation, '@shl_int_i_i_must_fit', [zload_width_bytes, MachineIntConstant(3)], MachineInt(), '`57 102:70-102:90', 'zz4105')
    i129 = block27.emit(Operation, '@sub_i_i_must_fit', [i128, MachineIntConstant(1)], MachineInt(), '`57 102:70-102:94', 'zz4102')
    i130 = block27.emit(Operation, '@vector_subrange_o_i_i', [i127, i129, MachineIntConstant(0)], GenericBitVector(), '`57 102:27-102:101', 'zz480')
    i131 = block27.emit(Operation, '@mult_o_i_wrapped_res', [i12, i121], Int(), '`57 103:70-103:82', 'zz488')
    i132 = block27.emit(Comment, 'inlined zto_bits', [], Unit(), None, None)
    i133 = block27.emit(Operation, '@get_slice_int_i_o_i_unwrapped_res', [MachineIntConstant(5), i131, MachineIntConstant(0)], SmallFixedBitVector(5), '`5 119:26-119:48', 'return')
    i134 = block27.emit(Operation, '@add_bits_bv_bv', [zvd, i133, MachineIntConstant(5)], SmallFixedBitVector(5), '`57 103:54-103:83', 'zz487')
    i135 = block27.emit(Operation, 'zwrite_single_element', [i128, i123, i134, i130], Unit(), '`57 103:8-103:98', 'zz479')
    i136 = block27.emit(Operation, '@iadd', [i121, MachineIntConstant(1)], MachineInt(), '`57 101:6-104:7', 'zz478')
    i121.prevvalues[1] = i136
    block27.next = Goto(block26, None)
    i137 = block28.emit(Operation, 'zz5izDzKz5i64', [zEMUL_pow], MachineInt(), None, None)
    i138 = block28.emit(Operation, '@pow2_i', [i137], Int(), '`57 72:52-72:66', 'zz40')
    i12.prevvalues[0] = i138
    block28.next = Goto(block2, None)
    graph = Graph('zprocess_vlseg', [znf, zvm, zvd, zload_width_bytes, zrs1, zEMUL_pow, znum_elem], block0, True)
    split_for_arg_constness(graph, fakecodegen)
    assert len(list(graph.iterblocks())) < 100 # should not explode the number of graphs

