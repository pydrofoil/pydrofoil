from pydrofoil import parse

def test_find_used_vars_exprs():
    v = parse.Var("abc")
    assert v.find_used_vars() == {"abc"}
    n = parse.Number(123)
    assert n.find_used_vars() == set()
    f = parse.FieldAccess(v, 'abc')
    assert v.find_used_vars() == {"abc"}
    c = parse.Cast(v, 'abc')
    assert c.find_used_vars() == {"abc"}
    r = parse.Cast(v, 'abc')
    assert r.find_used_vars() == {"abc"}

    v2 = parse.Var("def")
    s = parse.StructConstruction("S", ['x', 'y'], [v, v2])
    assert s.find_used_vars() == {"abc", "def"}

def test_find_used_vars_statements():
    v = parse.Var("abc")
    l = parse.LocalVarDeclaration("x", "dummy", v)
    assert l.find_used_vars() == {'abc'}
    
    a = parse.Assignment("x", v)
    assert l.find_used_vars() == {'abc'}

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
    assert l.find_used_vars() == {'abc'}
    
    s = parse.Comparison("@eq", [v, v2])
    assert s.find_used_vars() == {"abc", "def"}

    u = parse.UnionVariantCheck("abc", "X")
    assert u.find_used_vars() == {"abc"}
