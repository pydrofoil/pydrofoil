import z3
from pydrofoil.z3backend import BooleanConstant, Z3BoolValue, Z3BoolNotValue, Z3Value

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


### Z3BoolNotValue ###

def test_z3boolnotvalue_not_():
    """ Test negation of Z3BoolNotValue """
    
    x = z3.Bool("x")
    w_cond = Z3BoolNotValue(x) # this means not(x)

    w_cond_not = w_cond.not_()

    solver = z3.Solver()
    res = solver.check(z3.Not(w_cond_not.toz3() == x))
    assert res == z3.unsat


