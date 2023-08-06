import pytest

from pydrofoil import parse, types
from pydrofoil.parse import *
from pydrofoil.optimize import (
    find_decl_defs_uses,
    identify_replacements,
    do_replacements,
    specialize_ops,
)


class dummy_codegen:
    builtin_names = {}


dummy_codegen = dummy_codegen()


def test_find_used_vars_exprs():
    v = parse.Var("abc")
    assert v.find_used_vars() == {"abc"}
    n = parse.Number(123)
    assert n.find_used_vars() == set()
    f = parse.FieldAccess(v, "abc")
    assert v.find_used_vars() == {"abc"}
    c = parse.Cast(v, "abc")
    assert c.find_used_vars() == {"abc"}
    r = parse.Cast(v, "abc")
    assert r.find_used_vars() == {"abc"}

    v2 = parse.Var("def")
    s = parse.StructConstruction("S", ["x", "y"], [v, v2])
    assert s.find_used_vars() == {"abc", "def"}


def test_find_used_vars_statements():
    v = parse.Var("abc")
    l = parse.LocalVarDeclaration("x", "dummy", v)
    assert l.find_used_vars() == {"abc"}

    a = parse.Assignment("x", v)
    assert l.find_used_vars() == {"abc"}

    v2 = parse.Var("def")
    s = parse.Operation("x", "dummyop", [v, v2])
    assert s.find_used_vars() == {"abc", "def"}

    v2 = parse.Var("def")
    s = parse.StructElementAssignment(v, "field", v2)
    assert s.find_used_vars() == {"abc", "def"}


def test_find_used_vars_condition():
    v = parse.Var("abc")
    v2 = parse.Var("def")
    l = parse.ExprCondition(v)
    assert l.find_used_vars() == {"abc"}

    s = parse.Comparison("@eq", [v, v2])
    assert s.find_used_vars() == {"abc", "def"}

    u = parse.UnionVariantCheck(v, "X")
    assert u.find_used_vars() == {"abc"}


# __________________________________________________

vector_subrange_example = [
    LocalVarDeclaration(name="bv32", typ=NamedType("%bv32"), value=None),
    Assignment(result="bv32", value=Var(name="zargz3")),
    LocalVarDeclaration(name="subrange_result_bv7", typ=NamedType("%bv7"), value=None),
    LocalVarDeclaration(name="num6", typ=NamedType("%i"), value=None),
    Operation(
        args=[Number(number=6)],
        name="int64_to_int",
        resolved_type=types.Int(),
        result="num6",
        sourcepos="pos1",
    ),
    LocalVarDeclaration(name="num0", typ=NamedType("%i"), value=None),
    Operation(
        args=[Number(number=0)],
        name="int64_to_int",
        result="num0",
        resolved_type=types.Int(),
        sourcepos="pos2",
    ),
    LocalVarDeclaration(name="bvusedonce", typ=NamedType("%bv"), value=None),
    Assignment(
        result="bvusedonce",
        value=Var(name="bv32"),
        resolved_type=types.GenericBitVector(),
    ),
    LocalVarDeclaration(name="subrange_result", typ=NamedType("%bv"), value=None),
    Operation(
        args=[Var(name="bvusedonce"), Var(name="num6"), Var(name="num0")],
        name="vector_subrange",
        resolved_type=types.GenericBitVector(),
        result="subrange_result",
        sourcepos="pos3",
    ),
    Assignment(
        result="subrange_result_bv7",
        value=Var(name="subrange_result"),
        resolved_type=types.SmallFixedBitVector(7),
    ),
    LocalVarDeclaration(name="cond", typ=NamedType("%bool"), value=None),
    Operation(
        args=[Var(name="subrange_result_bv7")],
        name="zencdec_uop_backwards_matches",
        result="cond",
        resolved_type=types.Bool(),
        sourcepos="pos4",
    ),
    ConditionalJump(
        condition=Comparison(args=[Var(name="cond")], operation="@not"),
        target=17,
        sourcepos="pos5",
    ),
    End(),
]

targetjumpop = ConditionalJump(
    condition=Comparison(
        args=[
            OperationExpr(
                args=[
                    CastExpr(
                        expr=OperationExpr(
                            args=[
                                CastExpr(
                                    expr=Var(name="bv32"),
                                    resolved_type=types.GenericBitVector(),
                                ),
                                OperationExpr(
                                    args=[Number(number=6)],
                                    name="int64_to_int",
                                    resolved_type=types.Int(),
                                    sourcepos="pos1",
                                ),
                                OperationExpr(
                                    args=[Number(number=0)],
                                    name="int64_to_int",
                                    resolved_type=types.Int(),
                                    sourcepos="pos2",
                                ),
                            ],
                            name="vector_subrange",
                            resolved_type=types.GenericBitVector(),
                            sourcepos="pos3",
                        ),
                        resolved_type=types.SmallFixedBitVector(7),
                    )
                ],
                name="zencdec_uop_backwards_matches",
                resolved_type=types.Bool(),
                sourcepos="pos4",
            )
        ],
        operation="@not",
    ),
    sourcepos="pos5",
    target=17,
)


def test_find_defs_uses():
    block = vector_subrange_example
    decls, defs, uses = find_decl_defs_uses({0: block})
    assert uses["bv32"] == [(block, 8)]
    assert uses["subrange_result_bv7"] == [(block, 13)]
    assert defs["num6"] == [(block, 4)]
    assert defs["subrange_result_bv7"] == [(block, 11)]
    for var, uses in uses.iteritems():
        for bl, index in uses:
            assert bl is block
            assert var in block[index].find_used_vars()
            for i, op in enumerate(block):
                if i != index:
                    assert var not in block[i].find_used_vars()


def test_identify_replacements():
    replacements = identify_replacements({0: vector_subrange_example})
    assert replacements["bvusedonce"] == (vector_subrange_example, 7, 8, 10)


def test_do_replacements():
    block = vector_subrange_example[:]
    replacements = identify_replacements({0: block})
    do_replacements(replacements)
    assert block[2] == targetjumpop


def test_replacements_arguments():
    predefined = {
        "zx": NamedType("%bv"),
        "zy": NamedType("%bv"),
        "return": NamedType("%bool"),
    }
    blocks = {
        0: [
            LocalVarDeclaration(
                name="zz40",
                sourcepos="`3 227:32-227:53",
                typ=NamedType("%i"),
                value=None,
            ),
            Operation(
                args=[Var(name="zx")],
                name="zsigned",
                result="zz40",
                sourcepos="`1 227:32-227:41",
                resolved_type=types.Int(),
            ),
            LocalVarDeclaration(
                name="zz41",
                sourcepos="`1 227:32-227:53",
                typ=NamedType("%i"),
                value=None,
            ),
            Operation(
                args=[Var(name="zy")],
                name="zsigned",
                result="zz41",
                resolved_type=types.Int(),
                sourcepos="`1 227:44-227:53",
            ),
            Operation(
                args=[Var(name="zz40"), Var(name="zz41")],
                name="zlt_int",
                result="return",
                sourcepos="`1 227:32-227:53",
            ),
            End(),
        ]
    }
    do_replacements(identify_replacements(blocks, predefined))
    assert blocks[0][0] == Operation(
        args=[
            OperationExpr(
                args=[Var(name="zx")],
                name="zsigned",
                resolved_type=types.Int(),
                sourcepos="`1 227:32-227:41",
            ),
            OperationExpr(
                args=[Var(name="zy")],
                name="zsigned",
                resolved_type=types.Int(),
                sourcepos="`1 227:44-227:53",
            ),
        ],
        name="zlt_int",
        result="return",
        sourcepos="`1 227:32-227:53",
    )


def test_specialize_ops():
    lv = LocalVarDeclaration(
        name="zz40",
        sourcepos="`12 526:2-529:3",
        typ=NamedType(name="%bv64"),
        value=None,
    )
    op = Assignment(
        result="return",
        value=OperationExpr(
            args=[
                CastExpr(
                    expr=Var(name="zz40", resolved_type=types.SmallFixedBitVector(64)),
                    resolved_type=types.GenericBitVector(),
                ),
                OperationExpr(
                    args=[Number(number=31)],
                    name="int64_to_int",
                    resolved_type=types.Int(),
                ),
                OperationExpr(
                    args=[Number(number=0)],
                    name="int64_to_int",
                    resolved_type=types.Int(),
                ),
            ],
            name="vector_subrange",
            resolved_type=types.GenericBitVector(),
        ),
    )
    block = [lv, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[1].value == OperationExpr(
        args=[
            Var(name="zz40", resolved_type=types.SmallFixedBitVector(64)),
            Number(number=31),
            Number(number=0),
        ],
        name="@slice_fixed_bv_i_i",
        resolved_type=types.SmallFixedBitVector(32),
    )


@pytest.mark.xfail()
def test_specialize_eq_bits():
    op = ConditionalJump(
        condition=ExprCondition(
            expr=OperationExpr(
                args=[
                    CastExpr(
                        expr=OperationExpr(
                            args=[
                                Var(name="zz410160"),
                                Number(number=31),
                                Number(number=26),
                            ],
                            name="@slice_fixed_bv_i_i",
                            resolved_type=types.SmallFixedBitVector(6),
                        ),
                        resolved_type=types.GenericBitVector(),
                    ),
                    CastExpr(
                        expr=BitVectorConstant(constant="0b000000"),
                        resolved_type=types.GenericBitVector(),
                    ),
                ],
                name="eq_bits",
                resolved_type=types.Bool(),
            )
        ),
        sourcepos="`36 272:65-272:112",
        target=697,
    )
    block = [op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[0] == ConditionalJump(
        condition=ExprCondition(
            expr=OperationExpr(
                args=[
                    OperationExpr(
                        args=[
                            Var(name="zz410160"),
                            Number(number=31),
                            Number(number=26),
                        ],
                        name="@slice_fixed_bv_i_i",
                        resolved_type=types.SmallFixedBitVector(6),
                    ),
                    BitVectorConstant(constant="0b000000"),
                ],
                name="@eq_bits_bv_bv",
                resolved_type=types.Bool(),
            )
        ),
        sourcepos="`36 272:65-272:112",
        target=697,
    )


@pytest.mark.xfail()
def test_optimize_operation():
    lv = LocalVarDeclaration(
        name="zz410260",
        typ=NamedType(name="%bool"),
        value=None,
    )
    op = Operation(
        args=[
            CastExpr(
                expr=OperationExpr(
                    args=[Var(name="zz410258"), Number(number=6), Number(number=0)],
                    name="@slice_fixed_bv_i_i",
                    resolved_type=types.SmallFixedBitVector(7),
                ),
                resolved_type=types.GenericBitVector(),
            ),
            CastExpr(
                expr=BitVectorConstant(constant="0b0010011"),
                resolved_type=types.GenericBitVector(),
            ),
        ],
        name="eq_bits",
        result="zz410260",
        sourcepos=None,
        resolved_type=types.Bool(),
    )
    block = [lv, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[1] == Assignment(
        result="zz410260",
        sourcepos=None,
        value=OperationExpr(
            args=[
                OperationExpr(
                    args=[Var(name="zz410258"), Number(number=6), Number(number=0)],
                    name="@slice_fixed_bv_i_i",
                    typ=NamedType("%bv7"),
                ),
                BitVectorConstant(constant="0b0010011"),
            ],
            name="@eq_bits_bv_bv",
            typ=NamedType("%bool"),
        ),
    )


@pytest.mark.xfail()
def test_optimize_append():
    lv = LocalVarDeclaration(
        name="res",
        typ=NamedType(name="%bv21"),
        value=None,
    )
    op = Assignment(
        "res",
        CastExpr(
            expr=OperationExpr(
                args=[
                    CastExpr(
                        expr=BitVectorConstant("0b1"),
                        typ=NamedType("%bv"),
                    ),
                    CastExpr(
                        expr=OperationExpr(
                            args=[
                                CastExpr(
                                    expr=BitVectorConstant("0b10010111"),
                                    typ=NamedType("%bv"),
                                ),
                                CastExpr(
                                    expr=OperationExpr(
                                        args=[
                                            CastExpr(
                                                expr=BitVectorConstant("0b0"),
                                                typ=NamedType("%bv"),
                                            ),
                                            CastExpr(
                                                expr=OperationExpr(
                                                    args=[
                                                        CastExpr(
                                                            expr=BitVectorConstant(
                                                                "0b111011"
                                                            ),
                                                            typ=NamedType("%bv"),
                                                        ),
                                                        CastExpr(
                                                            expr=OperationExpr(
                                                                args=[
                                                                    CastExpr(
                                                                        expr=BitVectorConstant(
                                                                            "0b0111"
                                                                        ),
                                                                        typ=NamedType(
                                                                            "%bv"
                                                                        ),
                                                                    ),
                                                                    CastExpr(
                                                                        expr=BitVectorConstant(
                                                                            constant="0b0"
                                                                        ),
                                                                        typ=NamedType(
                                                                            "%bv"
                                                                        ),
                                                                    ),
                                                                ],
                                                                name="zbitvector_concat",
                                                                typ=NamedType("%bv"),
                                                            ),
                                                            typ=NamedType("%bv"),
                                                        ),
                                                    ],
                                                    name="zbitvector_concat",
                                                    typ=NamedType("%bv"),
                                                ),
                                                typ=NamedType("%bv"),
                                            ),
                                        ],
                                        name="zbitvector_concat",
                                        typ=NamedType("%bv"),
                                    ),
                                    typ=NamedType("%bv"),
                                ),
                            ],
                            name="zbitvector_concat",
                            typ=NamedType("%bv"),
                        ),
                        typ=NamedType("%bv"),
                    ),
                ],
                name="zbitvector_concat",
                typ=NamedType("%bv"),
            ),
            typ=NamedType("%bv21"),
        ),
    )
    block = [lv, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[1].value == OperationExpr(
        args=[
            BitVectorConstant(constant="0b1"),
            Number(number=20),
            OperationExpr(
                args=[
                    BitVectorConstant(constant="0b10010111"),
                    Number(number=12),
                    OperationExpr(
                        args=[
                            BitVectorConstant(constant="0b0"),
                            Number(number=11),
                            OperationExpr(
                                args=[
                                    BitVectorConstant(constant="0b111011"),
                                    Number(number=5),
                                    OperationExpr(
                                        args=[
                                            BitVectorConstant(constant="0b0111"),
                                            Number(number=1),
                                            BitVectorConstant(constant="0b0"),
                                        ],
                                        name="@bitvector_concat_bv_bv",
                                        typ=NamedType("%bv5"),
                                    ),
                                ],
                                name="@bitvector_concat_bv_bv",
                                typ=NamedType("%bv11"),
                            ),
                        ],
                        name="@bitvector_concat_bv_bv",
                        typ=NamedType("%bv12"),
                    ),
                ],
                name="@bitvector_concat_bv_bv",
                typ=NamedType("%bv20"),
            ),
        ],
        name="@bitvector_concat_bv_bv",
        typ=NamedType("%bv21"),
    )


@pytest.mark.xfail()
def test_eq_int():
    op = ConditionalJump(
        condition=Comparison(
            args=[
                OperationExpr(
                    args=[
                        OperationExpr(
                            args=[Var(name="zz4127")],
                            name="int64_to_int",
                            typ=NamedType("%i"),
                        ),
                        OperationExpr(
                            args=[Number(number=0)],
                            name="int64_to_int",
                            typ=NamedType("%i"),
                        ),
                    ],
                    name="zeq_int",
                    typ=NamedType("%bool"),
                )
            ],
            operation="@not",
        ),
        sourcepos="`9 116:4-150:5",
        target=12,
    )
    block = [op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[0].condition.args[0] == OperationExpr(
        args=[Var(name="zz4127"), Number(number=0)],
        name="@eq_int_i_i",
        typ=NamedType("%bool"),
    )


@pytest.mark.xfail()
def test_int64_to_int_and_back():
    op = OperationExpr(
        args=[
            OperationExpr(
                args=[
                    OperationExpr(
                        args=[CastExpr(expr=Var(name="zz44"), typ=NamedType("%bv"))],
                        name="foo",
                        typ=NamedType("%i"),
                    )
                ],
                name="zz5izDzKz5i64",
                typ=NamedType("%i64"),
            )
        ],
        name="int64_to_int",
        typ=NamedType("%i"),
    )
    block = [op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[0] == OperationExpr(
        args=[CastExpr(expr=Var(name="zz44"), typ=NamedType("%bv"))],
        name="foo",
        typ=NamedType("%i"),
    )


@pytest.mark.xfail()
def test_int_to_int64_and_back():
    op = OperationExpr(
        args=[
            OperationExpr(
                args=[Number(number=8)],
                name="int64_to_int",
                typ=NamedType("%i"),
            )
        ],
        name="zz5izDzKz5i64",
        typ=NamedType("%i64"),
    )
    block = [op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[0] == Number(8)


@pytest.mark.xfail()
def test_structconstruction_fieldread():
    lv = LocalVarDeclaration(
        name="var",
        typ=NamedType(name="%bv21"),
        value=None,
    )
    op = OperationExpr(
        args=[
            CastExpr(
                expr=FieldAccess(
                    element="ztuplez3z5bv4_z5bv40",
                    obj=StructConstruction(
                        fieldnames=["ztuplez3z5bv4_z5bv40", "ztuplez3z5bv4_z5bv41"],
                        fieldvalues=[Var(name="var"), Var(name="zz44751")],
                        name="ztuplez3z5bv4_z5bv4",
                    ),
                ),
                typ=NamedType("%bv"),
            ),
            OperationExpr(
                args=[Number(number=1)], name="int64_to_int", typ=NamedType("%i")
            ),
            OperationExpr(
                args=[Number(number=0)], name="int64_to_int", typ=NamedType("%i")
            ),
        ],
        name="vector_subrange",
        typ=NamedType("%bv"),
    )

    block = [lv, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[1] == CastExpr(
        expr=OperationExpr(
            args=[Var(name="var"), Number(number=1), Number(number=0)],
            name="@slice_fixed_bv_i_i",
            typ=NamedType("%bv2"),
        ),
        typ=NamedType("%bv"),
    )


@pytest.mark.xfail()
def test_xor_bits():
    lv1 = LocalVarDeclaration(
        name="var1",
        typ=NamedType(name="%bv21"),
        value=None,
    )
    lv2 = LocalVarDeclaration(
        name="var2",
        typ=NamedType(name="%bv21"),
        value=None,
    )
    op = OperationExpr(
        args=[
            CastExpr(expr=Var(name="var1"), typ=NamedType("%bv")),
            CastExpr(expr=Var(name="var2"), typ=NamedType("%bv")),
        ],
        name="zxor_vec",
        typ=NamedType("%bv"),
    )
    block = [lv1, lv2, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[2] == CastExpr(
        expr=OperationExpr(
            args=[Var(name="var1"), Var(name="var2")],
            name="@xor_vec_bv_bv",
            typ=NamedType("%bv21"),
        ),
        typ=NamedType("%bv"),
    )


@pytest.mark.xfail()
def test_and_not_bits():
    lv1 = LocalVarDeclaration(
        name="var1",
        typ=NamedType(name="%bv21"),
        value=None,
    )
    lv2 = LocalVarDeclaration(
        name="var2",
        typ=NamedType(name="%bv21"),
        value=None,
    )
    op = OperationExpr(
        args=[
            CastExpr(expr=Var(name="var1"), typ=NamedType("%bv")),
            CastExpr(
                expr=OperationExpr(
                    args=[CastExpr(expr=Var(name="var2"), typ=NamedType("%bv"))],
                    name="znot_vec",
                    typ=NamedType("%bv"),
                ),
                typ=NamedType("%bv"),
            ),
        ],
        name="zand_vec",
        typ=NamedType("%bv"),
    )
    block = [lv1, lv2, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[2] == CastExpr(
        expr=OperationExpr(
            args=[
                Var(name="var1"),
                OperationExpr(
                    args=[Var(name="var2"), Number(21)],
                    name="@not_vec_bv",
                    typ=NamedType("%bv21"),
                ),
            ],
            name="@and_vec_bv_bv",
            typ=NamedType("%bv21"),
        ),
        typ=NamedType("%bv"),
    )


@pytest.mark.skip("broken, fix with better types")
def test_fieldaccess_bug():
    op = Assignment(
        result="return",
        sourcepos="`11 1:34-1:48",
        value=OperationExpr(
            args=[
                CastExpr(
                    expr=FieldAccess(element="zbits", obj=Var(name="zv")),
                    typ=NamedType("%bv"),
                ),
                OperationExpr(
                    args=[Number(number=8)], name="int64_to_int", typ=NamedType("%i")
                ),
                OperationExpr(
                    args=[Number(number=8)], name="int64_to_int", typ=NamedType("%i")
                ),
            ],
            name="vector_subrange",
            typ=NamedType("%bv"),
        ),
    )
    block = [op]
    specialize_ops({0: block}, dummy_codegen)


@pytest.mark.xfail()
def test_signed():
    lv1 = LocalVarDeclaration(
        name="var1",
        typ=NamedType(name="%bv64"),
        value=None,
    )
    op = Assignment(
        result="zz40",
        sourcepos=None,
        value=OperationExpr(
            args=[CastExpr(expr=Var(name="var1"), typ=NamedType("%bv"))],
            name="zsigned",
            typ=NamedType("%i"),
        ),
    )
    block = [lv1, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[1] == Assignment(
        result="zz40",
        sourcepos=None,
        value=OperationExpr(
            args=[Var(name="var1"), Number(number=64)],
            name="@signed_bv",
            typ=NamedType("%i64"),
        ),
    )


@pytest.mark.xfail()
def test_vector_update_subrange():
    op = Assignment(
        result="zmtimecmp",
        sourcepos="`26 311:15-311:83",
        value=OperationExpr(
            args=[
                Var(name="zz462"),
                OperationExpr(
                    args=[Number(number=63)], name="int64_to_int", typ=NamedType("%i")
                ),
                OperationExpr(
                    args=[Number(number=32)], name="int64_to_int", typ=NamedType("%i")
                ),
                CastExpr(
                    expr=OperationExpr(
                        args=[
                            Var(name="zdata"),
                            OperationExpr(
                                args=[Number(number=32)],
                                name="int64_to_int",
                                typ=NamedType("%i"),
                            ),
                        ],
                        name="zsail_zzero_extend",
                        typ=NamedType("%bv"),
                    ),
                    typ=NamedType("%bv"),
                ),
            ],
            name="zupdate_subrange_bits",
            typ=NamedType("%bv"),
        ),
    )
    block = [op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[0].value == OperationExpr(
        args=[
            Var(name="zz462"),
            Number(number=63),
            Number(number=32),
            OperationExpr(
                args=[
                    Var(name="zdata"),
                    OperationExpr(
                        args=[Number(number=32)],
                        name="int64_to_int",
                        typ=NamedType("%i"),
                    ),
                ],
                name="zsail_zzero_extend",
                typ=NamedType("%bv"),
            ),
        ],
        name="@vector_update_subrange_o_i_i_o",
        typ=NamedType("%bv"),
    )


@pytest.mark.xfail()
def test_add_bits():
    lv1 = LocalVarDeclaration(
        name="zbase",
        typ=NamedType(name="%bv5"),
        value=None,
    )
    lv2 = LocalVarDeclaration(
        name="zoffset",
        typ=NamedType(name="%bv64"),
        value=None,
    )
    op = OperationExpr(
        args=[
            CastExpr(
                expr=OperationExpr(
                    args=[
                        CastExpr(
                            expr=OperationExpr(
                                args=[Var(name="zbase")],
                                name="zrX_bits",
                                typ=NamedType("%bv64"),
                            ),
                            typ=NamedType("%bv"),
                        ),
                        CastExpr(expr=Var(name="zoffset"), typ=NamedType("%bv")),
                    ],
                    name="zadd_bits",
                    typ=NamedType("%bv"),
                ),
                typ=NamedType("%bv64"),
            )
        ],
        name="zExt_DataAddr_OKzIuzK",
        typ=UnionType(name="zExt_DataAddr_CheckzIuzK"),
    )
    block = [lv1, lv2, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[2] == OperationExpr(
        args=[
            OperationExpr(
                args=[
                    OperationExpr(
                        args=[Var(name="zbase")],
                        name="zrX_bits",
                        typ=NamedType("%bv64"),
                    ),
                    Var(name="zoffset"),
                ],
                name="@add_bits_bv_bv",
                typ=NamedType("%bv64"),
            )
        ],
        name="zExt_DataAddr_OKzIuzK",
        typ=UnionType(name="zExt_DataAddr_CheckzIuzK"),
    )


@pytest.mark.xfail()
def test_vector_access():
    lv1 = LocalVarDeclaration(
        name="zv",
        typ=NamedType(name="%bv64"),
        value=None,
    )
    op = OperationExpr(
        args=[
            CastExpr(expr=Var(name="zv"), typ=NamedType("%bv")),
            OperationExpr(
                args=[Number(number=2)], name="int64_to_int", typ=NamedType("%i")
            ),
        ],
        name="zbitvector_access",
        typ=NamedType("%bit"),
    )
    block = [lv1, op]
    specialize_ops({0: block}, dummy_codegen)
    assert block[1] == OperationExpr(
        args=[Var(name="zv"), Number(number=2)],
        name="@vector_access_bv_i",
        typ=NamedType("%bit"),
    )
