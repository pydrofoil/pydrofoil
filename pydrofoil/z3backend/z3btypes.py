import z3
from pydrofoil import types

class Value(object):

    def __init__(self):
        # TODO: Resolved_Type
        self.value = None
    
    def toz3(self):
        pass
    
    def __str__(self):
        return str(self.value)
    
    def __repr__(self):
        return self.__str__()
    
    def same_value(self, other):
        if not isinstance(other, Value):
            return False
        return self.value == other.value
    
class Vec(Value):
    """ Vector
        This is only a wrapper on the python side """

    def __init__(self, w_value):
        self.w_value = w_value# can types.Vec only hold one value
    
    def toz3(self):
        return self.w_value.toz3()
    
    def __str__(self):
        return str(self.w_value)
    
    def __repr__(self):
        return "Vec(%s)" % self.__str__()
    
    def same_value(self, other):
        return self.w_value.same_value(other)
    
class Packed(Value):
    """ this is only a wrapper on the python side
        Values are not packed on z3 level """

    def __init__(self, w_value):
        self.w_value = w_value
    
    def toz3(self):
        return self.w_value.toz3()
    
    def __str__(self):
        return str(self.w_value)
    
    def __repr__(self):
        return "Packed(%s)" % self.__str__()
    
    def same_value(self, other):
        return self.w_value.same_value(other)

class Enum(Value):# AbstractConstant
    
    def __init__(self, name, variant, z3value):
        self.enum_name = name
        self.variant = variant
        self.value = z3value

    def toz3(self):
        return self.value
    
    def __eq__(self, other):
        # So we can eval enums on Interpreter level
        if not isinstance(other, Enum): return False
        return self.enum_name == other.enum_name and self.variant == other.variant
    
    def same_value(self, other):
        if not isinstance(other, Enum):
            return False
        if self.value.eq(other.value):# syntactical equality
            return True
        return self == other

class AbstractConstant(Value):
    
    def same_value(self, other):
        import pdb; pdb.set_trace()
    

class StringConstant(AbstractConstant): 
    
    def __init__(self, val):
        self.value = val

    def toz3(self):
        return z3.StringVal(self.value)
    
    def __str__(self):
        return str(self.value)
    
    def same_value(self, other):
        if not isinstance(other, StringConstant):
            return False
        return self.value == other.value
    

class ConstantSmallBitVector(AbstractConstant):
    
    def __init__(self, val, width):
        self.value = val
        self.width = width

    def toz3(self):
        return z3.BitVecVal(self.value, self.width)
    
    def same_value(self, other):
        if isinstance(other,ConstantSmallBitVector) or isinstance(other, ConstantGenericBitVector):
            return self.value == other.value
        return False
    
class ConstantGenericBitVector(AbstractConstant):
    def __init__(self, val, width, z3type):
        self.value = val
        assert isinstance(width, int)
        self.width = width
        self.z3type = z3type

    def toz3(self):
        return self.z3type.constructor(0)(z3.IntVal(self.value), self.width)
    
    def toz3bv(self, width):
        """ extract the value as fixed size bv 
            needed for register comparison"""
        return z3.BitVecVal(self.value, width)
    
    def same_value(self, other):
        if not isinstance(other, ConstantGenericBitVector) or not isinstance(other, ConstantSmallBitVector):
            return False 
        return (self.value == other.value)

class ConstantInt(AbstractConstant): # TODO: renname to ConstantMachineInt
    def __init__(self, val):
        assert isinstance(val, int)
        self.value = val

    def toz3(self):
        return z3.IntVal(self.value)
    
    def same_value(self, other):
        if not isinstance(other, ConstantInt):
            return False
        return self.value == other.value
  

class ConstantGenericInt(AbstractConstant):
    def __init__(self, val):
        assert isinstance(val, (int, long))
        self.value = val

    def toz3(self):
        return z3.IntVal(self.value)
    
    def same_value(self, other):
        if not isinstance(other, ConstantGenericInt):
            return False
        return self.value == other.value


class BooleanConstant(AbstractConstant):
    
    def __init__(self, val):
        self.value = val

    def toz3(self):
        return z3.BoolVal(self.value)

    def same_value(self, other):
        if not isinstance(other, BooleanConstant): 
            return False
        return self.value == other.value
    
    def not_(self):
        return BooleanConstant(not self.value)

    def _create_w_z3_if(self, w_true, w_false):
        """ return w_true or w_false depending on self.value """
        if self.value:
            return w_true
        return w_false
    
    def _create_w_z3_or(self, w_other):
        """ return self or w_other depending on self.value """
        if self.value:
            return self
        return w_other

    def _create_w_z3_and(self, *args_w):
        """ create z3 and or return BooleanConstant depending on self.value and args_w """
        if (self.value and args_w in ((), [])) or not self.value:
            return self
        else:
            return args_w[0]._create_w_z3_and(*(args_w[1:]))


class UnitConstant(AbstractConstant):
    """ None """
    
    def __init__(self, z3_unit):
        self.z3_unit = z3_unit

    def toz3(self):
        return self.z3_unit
    
    def __str__(self):
        return "UNIT"
    
    def same_value(self, other):
        if isinstance(other, UnitConstant): return True
        return  False

    
class UnionConstant(AbstractConstant):

    def __init__(self, variant_name, w_val, resolved_type, z3type):
        self.variant_name = variant_name
        self.w_val = w_val
        self.resolved_type = resolved_type
        self.z3type = z3type
    
    def toz3(self):
        if isinstance(self.w_val, UnitConstant):
            return getattr(self.z3type, self.variant_name)
        z3val = self.w_val.toz3()
        return getattr(self.z3type, self.variant_name)(z3val)
    
    def __str__(self):
        return "%s(%s)" % (self.variant_name, self.w_val)
    
    def same_value(self, other):
        if not isinstance(other, UnionConstant): 
            return False
        if self.resolved_type != other.resolved_type:
            return False
        if self.z3type != other.z3type:
            return False
        if self.variant_name != other.variant_name:
            return False
        if self.toz3().eq(other.toz3()):
            return True
        return self.w_val == other.w_val
    
    
class StructConstant(AbstractConstant):

    def __init__(self, vals_w, resolved_type, z3type):
        self.vals_w = vals_w
        self.resolved_type = resolved_type
        self.z3type = z3type
    
    def toz3(self):
        z3vals = [w_val.toz3() for w_val in self.vals_w]
        return self.z3type.constructor(0)(*z3vals)
    
    def __str__(self):
        return "<StructConstant %s %s>" % (self.vals_w, self.resolved_type.name)
    
    def same_value(self, other):
        if not isinstance(other, StructConstant): 
            return False
        if self.resolved_type != other.resolved_type:
            return False
        if self.z3type != other.z3type:
            return False
        if len(self.vals_w) !=  len(other.vals_w):
            return False
        for self_w_val, other_w_val in zip(self.vals_w, other.vals_w):
            if not self_w_val.same_value(other_w_val):
                return False
        return True
    
    def copy(self):
        return StructConstant(self.vals_w, self.resolved_type, self.z3type)
        
class Z3Value(Value):
    
    def __init__(self, val):
        if "_generic_bv_val_width_tup" in  str(val.sort()): import pdb; pdb.set_trace()
        self.value = val

    def toz3(self):
        return self.value
    
    def same_value(self, other):
        if self.value.eq(other.toz3()): # syntactical equality
            return True
        return False
    
    def copy(self):
        return Z3Value(self.value)

    def not_(self):
        assert 0,  "ilegal"
    
class Z3CastedValue(Z3Value):
    
    def __init__(self, val, cast_func, cast_params):
        if "_generic_bv_val_width_tup" in  str(val.sort()): import pdb; pdb.set_trace()
        self.value = val
        # problem: often pydrofoil does this:
        # get bv from register, slice, extend, cast to int
        # then the int is used in an abstract operation e.g. some_bv >> some_int
        # but z3 does not allow shifting bvs with an integer shift amount; thus we must cast the int to a bv again
        # this results in formulas like `x >> int2bv(bv2int(zero_ext(y[5:0])))`
        # this can sometimes be avoided by saving the non casted value on casting `zero_ext(y[5:0])` into a int with bv2int
        # If the int really is needed as int we can just call to_z3() as usual
        # but if we need the non casted bv value we can use it without using `int2bv`
        # Problems: Maybe the width of the bv value is not the width needed for use => then we must extend or slice
        self.cast_func = cast_func
        self.cast_params = cast_params
    
    def toz3(self):
        params = [self.value]
        params.extend(self.cast_params)
        return self.cast_func(*params)
    
    def same_value(self, other):
        if self.value.eq(other.toz3()): # syntactical equality
            return True
        return False
    
    def copy(self):
        return Z3CastedValue(self.value, self.cast_func, self.cast_params)

    def not_(self):
        assert 0,  "ilegal"
    
class Z3StringValue(Z3Value): 
    
    def __init__(self, val):
        assert isinstance(val, z3.z3.SeqRef)
        self.value = val

    def toz3(self):
        return self.value
    
    def __str__(self):
        return str(self.value)
    
    def same_value(self, other):
        if not isinstance(other, StringConstant):
            return False
        return self.value == other.value

class Z3GenericBitVector(Z3Value):
    """ Z3 level Generic BV,value is a z3 fixedsize bv """
    
    def __init__(self, val, width, z3type):
        assert isinstance(width, int)
        self.value = val
        self.width = width
        self.z3type = z3type

    def toz3(self):
        return self.z3type.constructor(0)(z3.BV2Int(self.value, False), self.width)
    
    def same_value(self, other):
        if self.toz3().eq(other.toz3()): # syntactical equality
            return True
        return False
    
    def copy(self):
        return Z3GenericBitVector(self.value, self.width) 

class Z3DeferredIntGenericBitVector(Z3Value):
    def __init__(self, z3_bv_tuple):
        """ Idea: create this class instead of crashing on failing to get a width for a generic bv from z3
            and hope this class dies somewhere without being directly used """
        self.z3_bv_tuple = z3_bv_tuple
      
    def toz3(self):
        """ returns the z3 generic bitvec val width struct instance """
        return self.z3_bv_tuple
    
    def __str__(self):
        return "Z3DeferredIntGenericBitVector(%s)" % str(self.z3_bv_tuple)
    
    def same_value(self, other):
        assert 0
    
class Z3BoolValue(Z3Value):

    def __init__(self, val):
        assert val.sort() == z3.BoolSort(), "cannot put non Bools into Z3BoolValue/Z3BoolNotValue"
        self.value = val

    def toz3(self):
        return self.value
    
    def same_value(self, other):
        if self.toz3().eq(other.toz3()): # syntactical equality
            return True
        return False

    def not_(self):
        return Z3BoolNotValue(self.value)
    
    def _create_w_z3_if(self, w_true, w_false):
        """ create z3 if, but only if w_true and w_false are non Constant or unequal"""
        if w_true.same_value(w_false): return w_true
        if self.value.eq(z3.BoolVal(True)) or self.value.eq(z3.BoolVal(False)): import pdb; pdb.set_trace()
        if isinstance(w_true, ConstantInt) or isinstance(w_true, ConstantGenericInt):
            ## Handle this explicitly ## 
            cls = Z3Value
        elif w_true.toz3().sort() == z3.BoolSort():
            cls = Z3BoolValue
        else:
            cls = Z3Value
        if isinstance(self, Z3BoolNotValue):
            return cls(z3.If(self.value, w_false.toz3(), w_true.toz3()))
        return cls(z3.If(self.value, w_true.toz3(), w_false.toz3()))
    
    def _create_w_z3_or(self, w_other):
        """ create z3 if, but only if w_true and w_false are non Constant or unequal"""
        if isinstance(w_other, BooleanConstant):
            if w_other.value:
                return w_other
            return self
        if self.same_value(w_other): return self
        if isinstance(w_other, Z3BoolNotValue):
            ### This elimates cases like 'a or not(a)' which eval to True
            if self.not_().toz3().eq(w_other.toz3()): 
                return BooleanConstant(True)
        return Z3BoolValue(z3.Or(self.toz3(), w_other.toz3())) # use self.toz3() here as this method is inherited to Z3BoolNotValue

    def _create_w_z3_and(self, *args_w):
        if args_w in ((), []):
            return self
        n_args_w = [self]
        if self.toz3().eq(z3.BoolVal(True)) or self.toz3().eq(z3.BoolVal(False)): import pdb; pdb.set_trace()
        for w_arg in args_w:
            if isinstance(w_arg, Z3BoolValue) or isinstance(w_arg, Z3BoolNotValue):
                if w_arg.toz3().eq(z3.BoolVal(True)) or w_arg.toz3().eq(z3.BoolVal(False)): import pdb; pdb.set_trace()
            if isinstance(w_arg, BooleanConstant):
                # Return  false if encountering a single False
                # TODO: check for z3 False here
                if not w_arg.value: return BooleanConstant(False)
            else:
                # TODO: check for z3 True here
                # Skip True, because True in and is unnecessary
                n_args_w.append(w_arg)
        if len(n_args_w) == 1: return self
        return Z3BoolValue(z3.And(*[w_arg.toz3() for w_arg in n_args_w]))  

class Z3BoolNotValue(Z3BoolValue):

    def toz3(self):
        return z3.Not(self.value)
    
    def _create_w_z3_or(self, w_other):
        """ create z3 if, but only if w_true and w_false are non Constant or unequal"""
        if isinstance(w_other, BooleanConstant):
            if w_other.value:
                return w_other
            return self
        if self.same_value(w_other): return self
        if isinstance(w_other, Z3BoolValue):
            ### This elimates cases like 'a or not(a)' which eval to True
            if self.toz3().eq(w_other.not_().toz3()): 
                return BooleanConstant(True)
        return Z3BoolValue(z3.Or(self.toz3(), w_other.toz3()))

    def not_(self):
        return Z3BoolValue(self.value)
