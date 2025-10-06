import z3
from pydrofoil.z3backend.z3btypes import BooleanConstant, Z3BoolValue, Z3BoolNotValue, Z3Value

### BooleanConstant ###

def test_booleanconstant_not_():
    """ Test negation of BooleanConstant """
    w_cond_true = BooleanConstant(True)

    w_cond_true_not = w_cond_true.not_().value

    assert w_cond_true_not == False


    w_cond_false = BooleanConstant(False)

    w_cond_false_not = w_cond_false.not_().value
    
    assert w_cond_false_not == True

def test_booleanconstant_if():
    """ Test if with BooleanConstant as condition """
    w_val_a = Z3Value(z3.BitVec("a", 32))
    w_val_b = Z3Value(z3.BitVec("b", 32))
    
    w_cond_true = BooleanConstant(True)
    w_if_true = w_cond_true._create_w_z3_if(w_val_a, w_val_b)

    assert w_if_true is w_val_a


    w_cond_false = BooleanConstant(False)
    w_if_false = w_cond_false._create_w_z3_if(w_val_a, w_val_b)

    assert w_if_false is w_val_b

def test_booleanconstant_or():
    """ Test or on BooleanConstant """
    w_true = BooleanConstant(True)
    w_val_a = Z3Value(z3.Bool("a"))
    
    w_or_res = w_true._create_w_z3_or(w_val_a)

    assert w_or_res is w_true


    w_false = BooleanConstant(False)
    w_or_res = w_false._create_w_z3_or(w_val_a)

    assert w_or_res is w_val_a

def test_booleanconstant_and():
    """ Test and on BooleanConstant """
    w_true = BooleanConstant(True)
    vals_w = []
    
    w_and_res = w_true._create_w_z3_and(*vals_w)

    assert w_and_res is w_true


    w_false = BooleanConstant(False)
    vals_w = [BooleanConstant(True)]
    w_and_res = w_false._create_w_z3_and(*vals_w)

    assert w_and_res is w_false


    vals_w = [BooleanConstant(True), BooleanConstant(True),  BooleanConstant(False)]
    w_and_res = w_false._create_w_z3_and(*vals_w)

    assert w_and_res.value == False


### Z3BoolValue ###

def test_z3boolvalue_not_():
    """ Test negation of Z3BoolValue """
    x = z3.Bool("x")
    w_cond = Z3BoolValue(x)

    w_cond_not = w_cond.not_()

    solver = z3.Solver()
    res = solver.check(z3.Not(w_cond_not.toz3() == z3.Not(x)))
    assert res == z3.unsat

def test_z3boolvalue_if():
    """ Test if with Z3BoolValue as condition """
    a = z3.BitVec("a", 32)
    b = z3.BitVec("b", 32)
    w_val_a = Z3Value(a)
    w_val_b = Z3Value(b)
    
    x = z3.Bool("x")
    w_cond = Z3BoolValue(x)
    w_if = w_cond._create_w_z3_if(w_val_a, w_val_b)

    solver = z3.Solver()
    res = solver.check(z3.Not(w_if.toz3() == z3.If(x, a, b)))
    assert res == z3.unsat

def test_z3boolvalue_or():
    """ Test or on Z3BoolValue """
    x = z3.Bool("x")
    a = z3.Bool("a")
    w_val = Z3BoolValue(x)
    w_val_other = Z3Value(a)
    
    w_or_res = w_val._create_w_z3_or(w_val_other)

    solver = z3.Solver()
    res = solver.check(z3.Not(w_or_res.toz3() == z3.Or(x, a)))
    assert res == z3.unsat

    w_true = BooleanConstant(True)
    w_or_res = w_val._create_w_z3_or(w_true)

    assert w_or_res == w_true

    w_false = BooleanConstant(False)
    w_or_res = w_val._create_w_z3_or(w_false)

    assert w_or_res == w_val

def test_z3boolvalue_and():
    """ Test and on Z3BoolValue """
    x = z3.Bool("x")
    w_val = Z3BoolValue(x)
    vals_w = []
    
    w_and_res = w_val._create_w_z3_and(*vals_w)

    assert w_and_res is w_val


    vals_w = [BooleanConstant(True)]
    w_and_res = w_val._create_w_z3_and(*vals_w)

    assert w_and_res is w_val


    vals_w = [BooleanConstant(True), BooleanConstant(True),  BooleanConstant(False)]
    w_and_res = w_val._create_w_z3_and(*vals_w)

    assert isinstance(w_and_res, BooleanConstant)
    assert w_and_res.value == False

    a = z3.Bool("a")
    b = z3.Bool("b")
    vals_w = [BooleanConstant(True), BooleanConstant(True),  Z3BoolValue(a), Z3BoolNotValue(b)]
    w_and_res = w_val._create_w_z3_and(*vals_w)
    
    solver = z3.Solver()
    res = solver.check(z3.Not(w_and_res.toz3() == z3.And(x, a, z3.Not(b))))
    assert res == z3.unsat


### Z3BoolNotValue ###

def test_z3boolnotvalue_not_():
    """ Test negation of Z3BoolNotValue """
    
    x = z3.Bool("x")
    w_cond = Z3BoolNotValue(x) # this means not(x)

    w_cond_not = w_cond.not_()

    solver = z3.Solver()
    res = solver.check(z3.Not(w_cond_not.toz3() == x))
    assert res == z3.unsat

def test_z3boolnotvalue_if():
    """ Test if with Z3BoolNotValue as condition """
    a = z3.BitVec("a", 32)
    b = z3.BitVec("b", 32)
    w_val_a = Z3Value(a)
    w_val_b = Z3Value(b)
    
    x = z3.Bool("x")
    w_cond = Z3BoolNotValue(x)
    w_if = w_cond._create_w_z3_if(w_val_a, w_val_b)

    solver = z3.Solver()
    res = solver.check(z3.Not(w_if.toz3() == z3.If(x, b, a)))
    assert res == z3.unsat


def test_z3boolnotvalue_or():
    """ Test or on Z3BoolNotValue """
    x = z3.Bool("x")
    a = z3.Bool("a")
    w_val = Z3BoolNotValue(x)
    w_val_other = Z3Value(a)
    
    w_or_res = w_val._create_w_z3_or(w_val_other)

    solver = z3.Solver()
    res = solver.check(z3.Not(w_or_res.toz3() == z3.Or(z3.Not(x), a)))
    assert res == z3.unsat

    w_true = BooleanConstant(True)
    w_or_res = w_val._create_w_z3_or(w_true)

    assert w_or_res == w_true

    w_false = BooleanConstant(False)
    w_or_res = w_val._create_w_z3_or(w_false)

    assert w_or_res == w_val

def test_z3boolnotvalue_and():
    """ Test and on Z3BoolNotValue """
    x = z3.Bool("x")
    w_val = Z3BoolNotValue(x)
    vals_w = []
    
    w_and_res = w_val._create_w_z3_and(*vals_w)

    assert w_and_res is w_val


    vals_w = [BooleanConstant(True)]
    w_and_res = w_val._create_w_z3_and(*vals_w)

    assert w_and_res is w_val


    vals_w = [BooleanConstant(True), BooleanConstant(True),  BooleanConstant(False)]
    w_and_res = w_val._create_w_z3_and(*vals_w)

    assert isinstance(w_and_res, BooleanConstant)
    assert w_and_res.value == False

    a = z3.Bool("a")
    b = z3.Bool("b")
    vals_w = [BooleanConstant(True), BooleanConstant(True),  Z3BoolValue(a), Z3BoolNotValue(b)]
    w_and_res = w_val._create_w_z3_and(*vals_w)
    
    solver = z3.Solver()
    res = solver.check(z3.Not(w_and_res.toz3() == z3.And(z3.Not(x), a, z3.Not(b))))
    assert res == z3.unsat


# TODO: test the toz3() method on every type
# bugs in toz3() are really annoying to find 