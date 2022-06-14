from parse import *

def test_lex_full():
    with open("c.ir", "rb") as f:
        s = f.read()
    try:
        for tok in lexer.lex(s):
            print(tok)
    except LexingError as e:
        print s[e.getsourcepos().idx:e.getsourcepos().idx+20]
        assert 0

def test_lex_binary():
    tok, = lexer.lex("0b0100101")

def test_parse_enum():
    res = parser.parse(lexer.lex("""
enum zjump {
  zJDONT,
  zJGT,
  zJEQ,
  zJGE,
  zJLT,
  zJNE,
  zJLE,
  zJMP
}
"""))
    assert res.declarations[0] == Enum(
        'zjump', ['zJDONT', 'zJGT', 'zJEQ', 'zJGE', 'zJLT', 'zJNE', 'zJLE', 'zJMP'])

def test_union():
    res = parser.parse(lexer.lex("""
union zinstr {
  zAINST: %bv16,
  zCINST: (%bv1, %enum zarithmetic_op, (%bool, %bool, %bool), %enum zjump)
}
"""))
    assert res.declarations[0] == Union('zinstr',
            [('zAINST', NamedType('%bv16')),
             ('zCINST', TupleType([
                 NamedType('%bv1'), EnumType('zarithmetic_op'),
                 TupleType([NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]),
                 EnumType('zjump')])),
            ])

def test_globalval():
    res = parser.parse(lexer.lex("""
val zeq_bool = "eq_bool" : (%bool, %bool) ->  %bool
val zneq_int : (%i, %i) ->  %bool

"""))
    assert res.declarations == [
        GlobalVal('zeq_bool', '"eq_bool"', FunctionType(TupleType([NamedType('%bool')] * 2), NamedType('%bool'))),
        GlobalVal('zneq_int', None, FunctionType(TupleType([NamedType('%i')] * 2), NamedType('%bool'))),
    ]

def test_function():
    res = parser.parse(lexer.lex("""
fn zneq_int(zx, zy) {
  zgaz30_lz30 : %bool;
  zgaz30_lz30 = zeq_int(zx, zy);
  return = znot_bool(zgaz30_lz30);
  end;
}
"""))
    assert res.declarations[0] == Function(
        'zneq_int', ['zx', 'zy'],
        [
            LocalVarDeclaration('zgaz30_lz30', NamedType('%bool')),
            Operation('zgaz30_lz30', 'zeq_int', [Var('zx'), Var('zy')]),
            Operation('return', 'znot_bool', [Var('zgaz30_lz30')]),
            End(),
        ]
    )

def test_function2():
    res = parser.parse(lexer.lex("""
fn zsail_mask(zlen, zv) {
  zgaz32_lz30 : %bool;
  zgaz31_lz31 : %i;
  zgaz31_lz31 = zbitvector_length(zv);
  zgaz32_lz30 = zlteq_int(zlen, zgaz31_lz31);
  jump zgaz32_lz30 goto 7 ` "/home/cfbolz/.opam/default/share/sail/lib/vector_dec.sail 81:29 - 81:100";
  return = zsail_zzero_extend(zv, zlen);
  goto 8;
  return = ztruncate(zv, zlen);
  end;
}
"""))
    assert res.declarations[0] == Function(
        'zsail_mask', ['zlen', 'zv'],
        [
            LocalVarDeclaration('zgaz32_lz30', NamedType('%bool')),
            LocalVarDeclaration('zgaz31_lz31', NamedType('%i')),
            Operation('zgaz31_lz31', 'zbitvector_length', [Var('zv')]),
            Operation('zgaz32_lz30', 'zlteq_int', [Var('zlen'), Var('zgaz31_lz31')]),
            ConditionalJump('zgaz32_lz30', 7, '"/home/cfbolz/.opam/default/share/sail/lib/vector_dec.sail 81:29 - 81:100"'),
            Operation('return', 'zsail_zzero_extend', [Var('zv'), Var('zlen')]),
            Goto(8),
            Operation('return', 'ztruncate', [Var('zv'), Var('zlen')]),
            End(),
        ]
    )

def test_function3():
    res = parser.parse(lexer.lex("""
fn zbits1_to_bool(zb) {
  zgsz310_lz30 : %bool;
  zb__0_lz33 : %bv1;
  zb__0_lz33 = zb;
  zgsz311_lz34 : %bool;
  zgsz311_lz34 = @eq(zb__0_lz33, 0b1);
  jump @not(zgsz311_lz34) goto 7 ` "f.sail 13:27 - 16:1";
  goto 8;
  goto 10;
  zgsz310_lz30 = true;
  goto 20;
  zb__1_lz31 : %bv1;
  zb__1_lz31 = zb;
  zgsz312_lz32 : %bool;
  zgsz312_lz32 = @eq(zb__1_lz31, 0b0);
  jump @not(zgsz312_lz32) goto 16 ` "f.sail 13:27 - 16:1";
  goto 17;
  goto 19;
  zgsz310_lz30 = false;
  goto 20;
  failure;
  return = zgsz310_lz30;
  end;
}
    """))
    assert res.declarations[0].body[2] == Assignment('zb__0_lz33', 'zb')
    assert res.declarations[0].body[5] == ConditionalJumpComparison(
            '@not', [Var('zgsz311_lz34')], 7, '"f.sail 13:27 - 16:1"')

def test_function4():
    res = parser.parse(lexer.lex("""
fn zdecode(zmergez3var) {
  zgsz344_lz30 : %union zoption;
  zv__1_lz315 : %bv16;
  zv__1_lz315 = zmergez3var;
  zgaz317_lz316 : %bv1;
  zgaz317_lz316 = @slice::<1>(zv__1_lz315, 15);
  zgsz348_lz317 : %bool;
  zgsz348_lz317 = @eq(zgaz317_lz316, 0b0);
  jump @not(zgsz348_lz317) goto 9 ` "f.sail 97:16 - 98:39";
  end;
}"""))
