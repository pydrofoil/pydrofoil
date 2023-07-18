from rpython.rlib import jit
from rpython.rlib.rbigint import rbigint
from rpython.rlib import objectmodel
from rpython.rlib.rarithmetic import r_uint, intmask
import operator
from pydrofoil.test.nand2tetris import supportcodenand as supportcode
from pydrofoil import bitvector
from pydrofoil.bitvector import Integer

class Lets(supportcode.LetsBase): pass

class Machine(supportcode.RegistersBase):
    def __init__(self): self.l = Lets(); model_init(self)
UninitInt = bitvector.Integer.fromint(-0xfefee)

class Tuple_1(supportcode.ObjectBase): # TupleType(elements=[NamedType('%i')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_1)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%i')
        return True

class Tuple_2(supportcode.ObjectBase): # TupleType(elements=[NamedType('%i64')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_2)
        if not ((self.utup0 == other.utup0)): return False # NamedType('%i64')
        return True

class Enum_zjump(supportcode.ObjectBase):
    zJDONT = 0
    zJGT = 1
    zJEQ = 2
    zJGE = 3
    zJLT = 4
    zJNE = 5
    zJLE = 6
    zJMP = 7

class Union_zexception(supportcode.ObjectBase):
    @objectmodel.always_inline
    def eq(self, other):
        return False
Union_zexception.singleton = Union_zexception()

class Union_zexception_z__dummy_exnz3(Union_zexception):
    def __init__(self, a):
        pass
    @objectmodel.always_inline
    def eq(self, other):
        if type(self) is not type(other): return False
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zexception_z__dummy_exnz3):
            return ()
        else:
            raise TypeError
Union_zexception_z__dummy_exnz3.singleton = Union_zexception_z__dummy_exnz3(())

class Enum_zarithmetic_op(supportcode.ObjectBase):
    zC_ZERO = 9
    zC_ONE = 10
    zC_MINUSONE = 11
    zC_D = 12
    zC_A = 13
    zC_NOT_D = 14
    zC_NOT_A = 15
    zC_NEG_D = 16
    zC_NEG_A = 17
    zC_D_ADD_1 = 18
    zC_A_ADD_1 = 19
    zC_D_SUB_1 = 20
    zC_A_SUB_1 = 21
    zC_D_ADD_A = 22
    zC_D_SUB_A = 23
    zC_A_SUB_D = 24
    zC_D_AND_A = 25
    zC_D_OR_A = 26

class Struct_ztuplez3z5bool_z5bool_z5bool(supportcode.ObjectBase):
    def __init__(self, ztuplez3z5bool_z5bool_z5bool0, ztuplez3z5bool_z5bool_z5bool1, ztuplez3z5bool_z5bool_z5bool2):
        self.ztuplez3z5bool_z5bool_z5bool0 = ztuplez3z5bool_z5bool_z5bool0 # NamedType('%bool')
        self.ztuplez3z5bool_z5bool_z5bool1 = ztuplez3z5bool_z5bool_z5bool1 # NamedType('%bool')
        self.ztuplez3z5bool_z5bool_z5bool2 = ztuplez3z5bool_z5bool_z5bool2 # NamedType('%bool')
    def copy_into(self, res=None):
        if res is None: res = type(self)()
        res.ztuplez3z5bool_z5bool_z5bool0 = self.ztuplez3z5bool_z5bool_z5bool0 # NamedType('%bool')
        res.ztuplez3z5bool_z5bool_z5bool1 = self.ztuplez3z5bool_z5bool_z5bool1 # NamedType('%bool')
        res.ztuplez3z5bool_z5bool_z5bool2 = self.ztuplez3z5bool_z5bool_z5bool2 # NamedType('%bool')
        return res
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Struct_ztuplez3z5bool_z5bool_z5bool)
        if not (self.ztuplez3z5bool_z5bool_z5bool0 == other.ztuplez3z5bool_z5bool_z5bool0): return False # NamedType('%bool')
        if not (self.ztuplez3z5bool_z5bool_z5bool1 == other.ztuplez3z5bool_z5bool_z5bool1): return False # NamedType('%bool')
        if not (self.ztuplez3z5bool_z5bool_z5bool2 == other.ztuplez3z5bool_z5bool_z5bool2): return False # NamedType('%bool')
        return True

class Struct_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump(supportcode.ObjectBase):
    def __init__(self, ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0, ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1, ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2, ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3):
        self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 = ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 # NamedType('%bv1')
        self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 = ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 # EnumType(name='zarithmetic_op')
        self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2 = ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2 # StructType(name='ztuplez3z5bool_z5bool_z5bool')
        self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 = ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 # EnumType(name='zjump')
    def copy_into(self, res=None):
        if res is None: res = type(self)()
        res.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 = self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 # NamedType('%bv1')
        res.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 = self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 # EnumType(name='zarithmetic_op')
        res.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2 = self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2 # StructType(name='ztuplez3z5bool_z5bool_z5bool')
        res.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 = self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 # EnumType(name='zjump')
        return res
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Struct_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump)
        if not (self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 == other.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0): return False # NamedType('%bv1')
        if not (self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 == other.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1): return False # EnumType(name='zarithmetic_op')
        if not (self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2.eq(other.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2)): return False # StructType(name='ztuplez3z5bool_z5bool_z5bool')
        if not (self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 == other.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3): return False # EnumType(name='zjump')
        return True

class Union_zinstr(supportcode.ObjectBase):
    @objectmodel.always_inline
    def eq(self, other):
        return False
Union_zinstr.singleton = Union_zinstr()

class Union_zinstr_zAINST(Union_zinstr):
    a = r_uint(0)
    def __init__(self, a):
        self.a = a # NamedType('%bv16')
    @objectmodel.always_inline
    def eq(self, other):
        if type(self) is not type(other): return False
        if not (self.a == other.a): return False # NamedType('%bv16')
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zinstr_zAINST):
            return inst.a
        else:
            raise TypeError

class Union_zinstr_zCINST(Union_zinstr):
    ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 = r_uint(0)
    ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 = -1
    ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2 = Struct_ztuplez3z5bool_z5bool_z5bool(False, False, False)
    ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 = -1
    def __init__(self, a):
        # StructType(name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump')
        self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 = a.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0
        self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 = a.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1
        self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2 = a.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2
        self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 = a.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3
    @objectmodel.always_inline
    def eq(self, other):
        if type(self) is not type(other): return False
        # StructType(name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump')
        if not (self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 == other.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0): return False
        if not (self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 == other.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1): return False
        if not (self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2.eq(other.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2)): return False
        if not (self.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 == other.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3): return False
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zinstr_zCINST):
            res = Struct_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump(r_uint(0), -1, Struct_ztuplez3z5bool_z5bool_z5bool(False, False, False), -1)
            res.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0 = inst.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0
            res.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1 = inst.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1
            res.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2 = inst.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2
            res.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3 = inst.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3
            return res
        else:
            raise TypeError
    @staticmethod
    def convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0(inst):
        if isinstance(inst, Union_zinstr_zCINST):
            return inst.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0
        else:
            raise TypeError
    @staticmethod
    def convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1(inst):
        if isinstance(inst, Union_zinstr_zCINST):
            return inst.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1
        else:
            raise TypeError
    @staticmethod
    def convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2(inst):
        if isinstance(inst, Union_zinstr_zCINST):
            return inst.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2
        else:
            raise TypeError
    @staticmethod
    def convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3(inst):
        if isinstance(inst, Union_zinstr_zCINST):
            return inst.ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3
        else:
            raise TypeError

class Union_zoptionzIUinstrzIzKzK(supportcode.ObjectBase):
    @objectmodel.always_inline
    def eq(self, other):
        return False
Union_zoptionzIUinstrzIzKzK.singleton = Union_zoptionzIUinstrzIzKzK()

class Union_zoptionzIUinstrzIzKzK_zNonezIUinstrzIzKzK(Union_zoptionzIUinstrzIzKzK):
    def __init__(self, a):
        pass
    @objectmodel.always_inline
    def eq(self, other):
        if type(self) is not type(other): return False
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zoptionzIUinstrzIzKzK_zNonezIUinstrzIzKzK):
            return ()
        else:
            raise TypeError
Union_zoptionzIUinstrzIzKzK_zNonezIUinstrzIzKzK.singleton = Union_zoptionzIUinstrzIzKzK_zNonezIUinstrzIzKzK(())

class Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK(Union_zoptionzIUinstrzIzKzK):
    a = Union_zinstr.singleton
    def __init__(self, a):
        self.a = a # UnionType(name='zinstr')
    @objectmodel.always_inline
    def eq(self, other):
        if type(self) is not type(other): return False
        if not (self.a.eq(other.a)): return False # UnionType(name='zinstr')
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK):
            return inst.a
        else:
            raise TypeError

class Tuple_3(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bool')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_3)
        if not (self.utup0 == other.utup0): return False # NamedType('%bool')
        return True

class Tuple_4(supportcode.ObjectBase): # TupleType(elements=[NamedType('%i'), NamedType('%i')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_4)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%i')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%i')
        return True

class Tuple_5(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv'), NamedType('%bv')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_5)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%bv')
        return True

class Tuple_6(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv'), NamedType('%i')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_6)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%i')
        return True

class Tuple_7(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv'), NamedType('%bv64')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_7)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        if not (self.utup1 == other.utup1): return False # NamedType('%bv64')
        return True

class Tuple_8(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_8)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        return True

class Tuple_9(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv'), NamedType('%i'), NamedType('%i')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_9)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%i')
        if not (self.utup2.eq(other.utup2)): return False # NamedType('%i')
        return True

class Tuple_10(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv1')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_10)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv1')
        return True
bitvectorconstant0b1_1 = bitvector.from_ruint(1, r_uint(0b1))

class Tuple_11(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv16'), NamedType('%bv16')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_11)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv16')
        if not (self.utup1 == other.utup1): return False # NamedType('%bv16')
        return True

class Tuple_12(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv16')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_12)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv16')
        return True

class Tuple_13(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv64'), NamedType('%bv16'), NamedType('%bv16'), NamedType('%bv16')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_13)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv64')
        if not (self.utup1 == other.utup1): return False # NamedType('%bv16')
        if not (self.utup2 == other.utup2): return False # NamedType('%bv16')
        if not (self.utup3 == other.utup3): return False # NamedType('%bv16')
        return True
# Register(name='zPC', pyname='_reg_zPC', typ=NamedType('%bv16'))
Machine._reg_zPC = r_uint(0)
# Register(name='zA', pyname='_reg_zA', typ=NamedType('%bv16'))
Machine._reg_zA = r_uint(0)
# Register(name='zD', pyname='_reg_zD', typ=NamedType('%bv16'))
Machine._reg_zD = r_uint(0)

class Tuple_14(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv6')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_14)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv6')
        return True
bitvectorconstant0b101010_1 = bitvector.from_ruint(6, r_uint(0b101010))
bitvectorconstant0b111111_1 = bitvector.from_ruint(6, r_uint(0b111111))
bitvectorconstant0b111010_1 = bitvector.from_ruint(6, r_uint(0b111010))
bitvectorconstant0b001100_1 = bitvector.from_ruint(6, r_uint(0b001100))
bitvectorconstant0b110000_1 = bitvector.from_ruint(6, r_uint(0b110000))
bitvectorconstant0b001101_1 = bitvector.from_ruint(6, r_uint(0b001101))
bitvectorconstant0b110001_1 = bitvector.from_ruint(6, r_uint(0b110001))
bitvectorconstant0b001111_1 = bitvector.from_ruint(6, r_uint(0b001111))
bitvectorconstant0b110011_1 = bitvector.from_ruint(6, r_uint(0b110011))
bitvectorconstant0b011111_1 = bitvector.from_ruint(6, r_uint(0b011111))
bitvectorconstant0b110111_1 = bitvector.from_ruint(6, r_uint(0b110111))
bitvectorconstant0b001110_1 = bitvector.from_ruint(6, r_uint(0b001110))
bitvectorconstant0b110010_1 = bitvector.from_ruint(6, r_uint(0b110010))
bitvectorconstant0b000010_1 = bitvector.from_ruint(6, r_uint(0b000010))
bitvectorconstant0b010011_1 = bitvector.from_ruint(6, r_uint(0b010011))
bitvectorconstant0b000111_1 = bitvector.from_ruint(6, r_uint(0b000111))
bitvectorconstant0b000000_1 = bitvector.from_ruint(6, r_uint(0b000000))
bitvectorconstant0b010101_1 = bitvector.from_ruint(6, r_uint(0b010101))

class Tuple_15(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv3')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_15)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv3')
        return True
bitvectorconstant0b000_1 = bitvector.from_ruint(3, r_uint(0b000))
bitvectorconstant0b001_1 = bitvector.from_ruint(3, r_uint(0b001))
bitvectorconstant0b010_1 = bitvector.from_ruint(3, r_uint(0b010))
bitvectorconstant0b011_1 = bitvector.from_ruint(3, r_uint(0b011))
bitvectorconstant0b100_1 = bitvector.from_ruint(3, r_uint(0b100))
bitvectorconstant0b101_1 = bitvector.from_ruint(3, r_uint(0b101))
bitvectorconstant0b110_1 = bitvector.from_ruint(3, r_uint(0b110))
bitvectorconstant0b111_1 = bitvector.from_ruint(3, r_uint(0b111))

class Tuple_16(supportcode.ObjectBase): # TupleType(elements=[UnionType(name='zinstr')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_16)
        if not (self.utup0.eq(other.utup0)): return False # UnionType(name='zinstr')
        return True
smallintconst2_1 = bitvector.SmallInteger(2)
smallintconst0_1 = bitvector.SmallInteger(0)
smallintconst1_1 = bitvector.SmallInteger(1)
smallintconst15_1 = bitvector.SmallInteger(15)
bitvectorconstant0b0_1 = bitvector.from_ruint(1, r_uint(0b0))
smallintconst14_1 = bitvector.SmallInteger(14)
smallintconst16_1 = bitvector.SmallInteger(16)
smallintconst13_1 = bitvector.SmallInteger(13)
smallintconst12_1 = bitvector.SmallInteger(12)
smallintconst11_1 = bitvector.SmallInteger(11)
smallintconst6_1 = bitvector.SmallInteger(6)
smallintconst5_1 = bitvector.SmallInteger(5)
smallintconst3_1 = bitvector.SmallInteger(3)

class Tuple_17(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_17)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv1')
        if not (self.utup1 == other.utup1): return False # EnumType(name='zarithmetic_op')
        return True
bitvectorconstant0x0001_1 = bitvector.from_ruint(16, r_uint(0x0001))
bitvectorconstant0x0000_1 = bitvector.from_ruint(16, r_uint(0x0000))

class Tuple_18(supportcode.ObjectBase): # TupleType(elements=[StructType(name='ztuplez3z5bool_z5bool_z5bool'), NamedType('%bv16')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_18)
        if not (self.utup0.eq(other.utup0)): return False # StructType(name='ztuplez3z5bool_z5bool_z5bool')
        if not (self.utup1 == other.utup1): return False # NamedType('%bv16')
        return True

class Tuple_19(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv16'), EnumType(name='zjump')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_19)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv16')
        if not (self.utup1 == other.utup1): return False # EnumType(name='zjump')
        return True

class Tuple_20(supportcode.ObjectBase): # TupleType(elements=[NamedType('%unit')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_20)
        if not (True): return False # NamedType('%unit')
        return True

class Tuple_21(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv64'), NamedType('%bool')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_21)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv64')
        if not (self.utup1 == other.utup1): return False # NamedType('%bool')
        return True
bitvectorconstant0x0000000000000001_1 = bitvector.from_ruint(64, r_uint(0x0000000000000001))


def model_init(machine):
    pass







# Pragma(content=['ztuplez3z5bool_z5bool_z5bool', 'ztuplez3z5bool_z5bool_z5bool0', 'ztuplez3z5bool_z5bool_z5bool1', 'ztuplez3z5bool_z5bool_z5bool2'], name='tuplestruct')


# Pragma(content=['ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3'], name='tuplestruct')




# Pragma(content=['zSome', 'zSomezIUinstrzIzKzK'], name='mangled')

# Pragma(content=['zNone', 'zNonezIUinstrzIzKzK'], name='mangled')

# Pragma(content=['zoption', 'zoptionzIUinstrzIzKzK'], name='mangled')





def func_zneq_int(machine, zx, zy):
    # zz40: NamedType('%bool')
    # Operation(args=[Var(name='zx'), Var(name='zy')], name='zeq_int', result='zz40', sourcepos='`0 100:35-100:47')
    zz40 = supportcode.eq_int(machine, zx, zy)
    # Operation(args=[Var(name='zz40')], name='znot_bool', result='return', sourcepos='`0 100:26-100:48')
    return_ = supportcode.not_(machine, zz40)
    # End()
    return return_



















def func_zbits1_to_bool(machine, zb):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zz40', sourcepos='`1 13:27-16:1', typ=NamedType('%bool'), value=None)
            # zz40: NamedType('%bool')
            zz40 = False
            # zz41: NamedType('%bv1')
            # Assignment(result='zz41', sourcepos='`1 14:2-14:5', value=Var(name='zb'))
            zz41 = zb
            if not supportcode.eq_bits(machine, bitvector.from_ruint(1, zz41), bitvectorconstant0b1_1):
                # inline pc=11
                pc = 14
                continue
            pc = 12
        if pc == 12:
            # Assignment(result='zz40', sourcepos='`1 14:10-14:14', value=Var(name='true'))
            zz40 = True
            pc = 15
        if pc == 14:
            # Assignment(result='zz40', sourcepos='`1 15:9-15:14', value=Var(name='false'))
            zz40 = False
            pc = 15
        if pc == 15:
            # Assignment(result='return', sourcepos='`1 13:27-16:1', value=Var(name='zz40'))
            return_ = zz40
            # End()
            return return_











def func_zdecode_compute_backwards(machine, zargz3):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zz40', sourcepos='`1', typ=EnumType(name='zarithmetic_op'), value=None)
            # zz40: EnumType(name='zarithmetic_op')
            zz40 = -1
            # zz469: NamedType('%bv6')
            # Assignment(result='zz469', sourcepos='`1 56:19-56:27', value=Var(name='zargz3'))
            zz469 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz469), bitvectorconstant0b101010_1):
                # inline pc=11
                pc = 14
                continue
            pc = 12
        if pc == 12:
            # Assignment(result='zz40', sourcepos='`1 56:2-56:8', value=Var(name='zC_ZERO'))
            zz40 = Enum_zarithmetic_op.zC_ZERO
            pc = 236
        if pc == 14:
            # zz465: NamedType('%bv6')
            # Assignment(result='zz465', sourcepos='`1 57:19-57:27', value=Var(name='zargz3'))
            zz465 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz465), bitvectorconstant0b111111_1):
                # inline pc=24
                pc = 27
                continue
            pc = 25
        if pc == 25:
            # Assignment(result='zz40', sourcepos='`1 57:2-57:7', value=Var(name='zC_ONE'))
            zz40 = Enum_zarithmetic_op.zC_ONE
            pc = 236
        if pc == 27:
            # zz461: NamedType('%bv6')
            # Assignment(result='zz461', sourcepos='`1 58:19-58:27', value=Var(name='zargz3'))
            zz461 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz461), bitvectorconstant0b111010_1):
                # inline pc=37
                pc = 40
                continue
            pc = 38
        if pc == 38:
            # Assignment(result='zz40', sourcepos='`1 58:2-58:12', value=Var(name='zC_MINUSONE'))
            zz40 = Enum_zarithmetic_op.zC_MINUSONE
            pc = 236
        if pc == 40:
            # zz457: NamedType('%bv6')
            # Assignment(result='zz457', sourcepos='`1 59:19-59:27', value=Var(name='zargz3'))
            zz457 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz457), bitvectorconstant0b001100_1):
                # inline pc=50
                pc = 53
                continue
            pc = 51
        if pc == 51:
            # Assignment(result='zz40', sourcepos='`1 59:2-59:5', value=Var(name='zC_D'))
            zz40 = Enum_zarithmetic_op.zC_D
            pc = 236
        if pc == 53:
            # zz453: NamedType('%bv6')
            # Assignment(result='zz453', sourcepos='`1 60:19-60:27', value=Var(name='zargz3'))
            zz453 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz453), bitvectorconstant0b110000_1):
                # inline pc=63
                pc = 66
                continue
            pc = 64
        if pc == 64:
            # Assignment(result='zz40', sourcepos='`1 60:2-60:5', value=Var(name='zC_A'))
            zz40 = Enum_zarithmetic_op.zC_A
            pc = 236
        if pc == 66:
            # zz449: NamedType('%bv6')
            # Assignment(result='zz449', sourcepos='`1 61:19-61:27', value=Var(name='zargz3'))
            zz449 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz449), bitvectorconstant0b001101_1):
                # inline pc=76
                pc = 79
                continue
            pc = 77
        if pc == 77:
            # Assignment(result='zz40', sourcepos='`1 61:2-61:9', value=Var(name='zC_NOT_D'))
            zz40 = Enum_zarithmetic_op.zC_NOT_D
            pc = 236
        if pc == 79:
            # zz445: NamedType('%bv6')
            # Assignment(result='zz445', sourcepos='`1 62:19-62:27', value=Var(name='zargz3'))
            zz445 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz445), bitvectorconstant0b110001_1):
                # inline pc=89
                pc = 92
                continue
            pc = 90
        if pc == 90:
            # Assignment(result='zz40', sourcepos='`1 62:2-62:9', value=Var(name='zC_NOT_A'))
            zz40 = Enum_zarithmetic_op.zC_NOT_A
            pc = 236
        if pc == 92:
            # zz441: NamedType('%bv6')
            # Assignment(result='zz441', sourcepos='`1 63:19-63:27', value=Var(name='zargz3'))
            zz441 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz441), bitvectorconstant0b001111_1):
                # inline pc=102
                pc = 105
                continue
            pc = 103
        if pc == 103:
            # Assignment(result='zz40', sourcepos='`1 63:2-63:9', value=Var(name='zC_NEG_D'))
            zz40 = Enum_zarithmetic_op.zC_NEG_D
            pc = 236
        if pc == 105:
            # zz437: NamedType('%bv6')
            # Assignment(result='zz437', sourcepos='`1 64:19-64:27', value=Var(name='zargz3'))
            zz437 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz437), bitvectorconstant0b110011_1):
                # inline pc=115
                pc = 118
                continue
            pc = 116
        if pc == 116:
            # Assignment(result='zz40', sourcepos='`1 64:2-64:9', value=Var(name='zC_NEG_A'))
            zz40 = Enum_zarithmetic_op.zC_NEG_A
            pc = 236
        if pc == 118:
            # zz433: NamedType('%bv6')
            # Assignment(result='zz433', sourcepos='`1 65:19-65:27', value=Var(name='zargz3'))
            zz433 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz433), bitvectorconstant0b011111_1):
                # inline pc=128
                pc = 131
                continue
            pc = 129
        if pc == 129:
            # Assignment(result='zz40', sourcepos='`1 65:2-65:11', value=Var(name='zC_D_ADD_1'))
            zz40 = Enum_zarithmetic_op.zC_D_ADD_1
            pc = 236
        if pc == 131:
            # zz429: NamedType('%bv6')
            # Assignment(result='zz429', sourcepos='`1 66:19-66:27', value=Var(name='zargz3'))
            zz429 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz429), bitvectorconstant0b110111_1):
                # inline pc=141
                pc = 144
                continue
            pc = 142
        if pc == 142:
            # Assignment(result='zz40', sourcepos='`1 66:2-66:11', value=Var(name='zC_A_ADD_1'))
            zz40 = Enum_zarithmetic_op.zC_A_ADD_1
            pc = 236
        if pc == 144:
            # zz425: NamedType('%bv6')
            # Assignment(result='zz425', sourcepos='`1 67:19-67:27', value=Var(name='zargz3'))
            zz425 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz425), bitvectorconstant0b001110_1):
                # inline pc=154
                pc = 157
                continue
            pc = 155
        if pc == 155:
            # Assignment(result='zz40', sourcepos='`1 67:2-67:11', value=Var(name='zC_D_SUB_1'))
            zz40 = Enum_zarithmetic_op.zC_D_SUB_1
            pc = 236
        if pc == 157:
            # zz421: NamedType('%bv6')
            # Assignment(result='zz421', sourcepos='`1 68:19-68:27', value=Var(name='zargz3'))
            zz421 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz421), bitvectorconstant0b110010_1):
                # inline pc=167
                pc = 170
                continue
            pc = 168
        if pc == 168:
            # Assignment(result='zz40', sourcepos='`1 68:2-68:11', value=Var(name='zC_A_SUB_1'))
            zz40 = Enum_zarithmetic_op.zC_A_SUB_1
            pc = 236
        if pc == 170:
            # zz417: NamedType('%bv6')
            # Assignment(result='zz417', sourcepos='`1 69:19-69:27', value=Var(name='zargz3'))
            zz417 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz417), bitvectorconstant0b000010_1):
                # inline pc=180
                pc = 183
                continue
            pc = 181
        if pc == 181:
            # Assignment(result='zz40', sourcepos='`1 69:2-69:11', value=Var(name='zC_D_ADD_A'))
            zz40 = Enum_zarithmetic_op.zC_D_ADD_A
            pc = 236
        if pc == 183:
            # zz413: NamedType('%bv6')
            # Assignment(result='zz413', sourcepos='`1 70:19-70:27', value=Var(name='zargz3'))
            zz413 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz413), bitvectorconstant0b010011_1):
                # inline pc=193
                pc = 196
                continue
            pc = 194
        if pc == 194:
            # Assignment(result='zz40', sourcepos='`1 70:2-70:11', value=Var(name='zC_D_SUB_A'))
            zz40 = Enum_zarithmetic_op.zC_D_SUB_A
            pc = 236
        if pc == 196:
            # zz49: NamedType('%bv6')
            # Assignment(result='zz49', sourcepos='`1 71:19-71:27', value=Var(name='zargz3'))
            zz49 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz49), bitvectorconstant0b000111_1):
                # inline pc=206
                pc = 209
                continue
            pc = 207
        if pc == 207:
            # Assignment(result='zz40', sourcepos='`1 71:2-71:11', value=Var(name='zC_A_SUB_D'))
            zz40 = Enum_zarithmetic_op.zC_A_SUB_D
            pc = 236
        if pc == 209:
            # zz45: NamedType('%bv6')
            # Assignment(result='zz45', sourcepos='`1 72:19-72:27', value=Var(name='zargz3'))
            zz45 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz45), bitvectorconstant0b000000_1):
                # inline pc=219
                pc = 222
                continue
            pc = 220
        if pc == 220:
            # Assignment(result='zz40', sourcepos='`1 72:2-72:11', value=Var(name='zC_D_AND_A'))
            zz40 = Enum_zarithmetic_op.zC_D_AND_A
            pc = 236
        if pc == 222:
            # zz41: NamedType('%bv6')
            # Assignment(result='zz41', sourcepos='`1 73:19-73:27', value=Var(name='zargz3'))
            zz41 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(6, zz41), bitvectorconstant0b010101_1):
                # inline pc=232
                pc = 235
                continue
            pc = 233
        if pc == 233:
            # Assignment(result='zz40', sourcepos='`1 73:2-73:10', value=Var(name='zC_D_OR_A'))
            zz40 = Enum_zarithmetic_op.zC_D_OR_A
            pc = 236
        if pc == 235:
            # Exit(kind='match', sourcepos='`38')
            raise TypeError
        if pc == 236:
            # Assignment(result='return', sourcepos='`39', value=Var(name='zz40'))
            return_ = zz40
            # End()
            return return_




def func_zdecode_jump_backwards(machine, zargz3):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zz40', sourcepos='`40', typ=EnumType(name='zjump'), value=None)
            # zz40: EnumType(name='zjump')
            zz40 = -1
            # zz429: NamedType('%bv3')
            # Assignment(result='zz429', sourcepos='`1 79:13-79:18', value=Var(name='zargz3'))
            zz429 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, zz429), bitvectorconstant0b000_1):
                # inline pc=11
                pc = 14
                continue
            pc = 12
        if pc == 12:
            # Assignment(result='zz40', sourcepos='`1 79:2-79:7', value=Var(name='zJDONT'))
            zz40 = Enum_zjump.zJDONT
            pc = 106
        if pc == 14:
            # zz425: NamedType('%bv3')
            # Assignment(result='zz425', sourcepos='`1 80:13-80:18', value=Var(name='zargz3'))
            zz425 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, zz425), bitvectorconstant0b001_1):
                # inline pc=24
                pc = 27
                continue
            pc = 25
        if pc == 25:
            # Assignment(result='zz40', sourcepos='`1 80:2-80:5', value=Var(name='zJGT'))
            zz40 = Enum_zjump.zJGT
            pc = 106
        if pc == 27:
            # zz421: NamedType('%bv3')
            # Assignment(result='zz421', sourcepos='`1 81:13-81:18', value=Var(name='zargz3'))
            zz421 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, zz421), bitvectorconstant0b010_1):
                # inline pc=37
                pc = 40
                continue
            pc = 38
        if pc == 38:
            # Assignment(result='zz40', sourcepos='`1 81:2-81:5', value=Var(name='zJEQ'))
            zz40 = Enum_zjump.zJEQ
            pc = 106
        if pc == 40:
            # zz417: NamedType('%bv3')
            # Assignment(result='zz417', sourcepos='`1 82:13-82:18', value=Var(name='zargz3'))
            zz417 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, zz417), bitvectorconstant0b011_1):
                # inline pc=50
                pc = 53
                continue
            pc = 51
        if pc == 51:
            # Assignment(result='zz40', sourcepos='`1 82:2-82:5', value=Var(name='zJGE'))
            zz40 = Enum_zjump.zJGE
            pc = 106
        if pc == 53:
            # zz413: NamedType('%bv3')
            # Assignment(result='zz413', sourcepos='`1 83:13-83:18', value=Var(name='zargz3'))
            zz413 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, zz413), bitvectorconstant0b100_1):
                # inline pc=63
                pc = 66
                continue
            pc = 64
        if pc == 64:
            # Assignment(result='zz40', sourcepos='`1 83:2-83:5', value=Var(name='zJLT'))
            zz40 = Enum_zjump.zJLT
            pc = 106
        if pc == 66:
            # zz49: NamedType('%bv3')
            # Assignment(result='zz49', sourcepos='`1 84:13-84:18', value=Var(name='zargz3'))
            zz49 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, zz49), bitvectorconstant0b101_1):
                # inline pc=76
                pc = 79
                continue
            pc = 77
        if pc == 77:
            # Assignment(result='zz40', sourcepos='`1 84:2-84:5', value=Var(name='zJNE'))
            zz40 = Enum_zjump.zJNE
            pc = 106
        if pc == 79:
            # zz45: NamedType('%bv3')
            # Assignment(result='zz45', sourcepos='`1 85:13-85:18', value=Var(name='zargz3'))
            zz45 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, zz45), bitvectorconstant0b110_1):
                # inline pc=89
                pc = 92
                continue
            pc = 90
        if pc == 90:
            # Assignment(result='zz40', sourcepos='`1 85:2-85:5', value=Var(name='zJLE'))
            zz40 = Enum_zjump.zJLE
            pc = 106
        if pc == 92:
            # zz41: NamedType('%bv3')
            # Assignment(result='zz41', sourcepos='`1 86:13-86:18', value=Var(name='zargz3'))
            zz41 = zargz3
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, zz41), bitvectorconstant0b111_1):
                # inline pc=102
                pc = 105
                continue
            pc = 103
        if pc == 103:
            # Assignment(result='zz40', sourcepos='`1 86:2-86:5', value=Var(name='zJMP'))
            zz40 = Enum_zjump.zJMP
            pc = 106
        if pc == 105:
            # Exit(kind='match', sourcepos='`57')
            raise TypeError
        if pc == 106:
            # Assignment(result='return', sourcepos='`58', value=Var(name='zz40'))
            return_ = zz40
            # End()
            return return_






def func_zdecode_destination(machine, zb):
    # LocalVarDeclaration(name='zz40', sourcepos='`1 111:4-113:5', typ=StructType(name='ztuplez3z5bool_z5bool_z5bool'), value=None)
    # zz40: StructType(name='ztuplez3z5bool_z5bool_z5bool')
    zz40 = Struct_ztuplez3z5bool_z5bool_z5bool(False, False, False)
    # zz41: NamedType('%bv3')
    # Assignment(result='zz41', sourcepos='`1 112:8-112:47', value=Var(name='zb'))
    zz41 = zb
    # LocalVarDeclaration(name='zz42', sourcepos='`1 112:51-112:105', typ=NamedType('%bv1'), value=None)
    # zz42: NamedType('%bv1')
    zz42 = r_uint(0)
    # zz421: NamedType('%i')
    # Operation(args=[Number(number=2)], name='zz5i64zDzKz5i', result='zz421', sourcepos='`1 112:8-112:9')
    zz421 = smallintconst2_1
    # zz422: NamedType('%i')
    # Operation(args=[Number(number=2)], name='zz5i64zDzKz5i', result='zz422', sourcepos='`1 112:8-112:9')
    zz422 = smallintconst2_1
    # zz423: NamedType('%bv')
    # Assignment(result='zz423', sourcepos='`1 112:8-112:9', value=Var(name='zz41'))
    zz423 = bitvector.from_ruint(3, zz41)
    # zz424: NamedType('%bv')
    # Operation(args=[Var(name='zz423'), Var(name='zz421'), Var(name='zz422')], name='zsubrange_bits', result='zz424', sourcepos='`1 112:8-112:9')
    zz424 = supportcode.vector_subrange(machine, zz423, zz421, zz422)
    # Assignment(result='zz42', sourcepos='`1 112:8-112:9', value=Var(name='zz424'))
    zz42 = zz424.touint()
    # LocalVarDeclaration(name='zz43', sourcepos='`1 112:36-112:37', typ=NamedType('%bv1'), value=None)
    # zz43: NamedType('%bv1')
    zz43 = r_uint(0)
    # zz417: NamedType('%i')
    # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz417', sourcepos='`1 112:36-112:37')
    zz417 = smallintconst0_1
    # zz418: NamedType('%i')
    # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz418', sourcepos='`1 112:36-112:37')
    zz418 = smallintconst0_1
    # zz419: NamedType('%bv')
    # Assignment(result='zz419', sourcepos='`1 112:36-112:37', value=Var(name='zz41'))
    zz419 = bitvector.from_ruint(3, zz41)
    # zz420: NamedType('%bv')
    # Operation(args=[Var(name='zz419'), Var(name='zz417'), Var(name='zz418')], name='zsubrange_bits', result='zz420', sourcepos='`1 112:36-112:37')
    zz420 = supportcode.vector_subrange(machine, zz419, zz417, zz418)
    # Assignment(result='zz43', sourcepos='`1 112:36-112:37', value=Var(name='zz420'))
    zz43 = zz420.touint()
    # LocalVarDeclaration(name='zz44', sourcepos='`1 112:22-112:23', typ=NamedType('%bv1'), value=None)
    # zz44: NamedType('%bv1')
    zz44 = r_uint(0)
    # zz413: NamedType('%i')
    # Operation(args=[Number(number=1)], name='zz5i64zDzKz5i', result='zz413', sourcepos='`1 112:22-112:23')
    zz413 = smallintconst1_1
    # zz414: NamedType('%i')
    # Operation(args=[Number(number=1)], name='zz5i64zDzKz5i', result='zz414', sourcepos='`1 112:22-112:23')
    zz414 = smallintconst1_1
    # zz415: NamedType('%bv')
    # Assignment(result='zz415', sourcepos='`1 112:22-112:23', value=Var(name='zz41'))
    zz415 = bitvector.from_ruint(3, zz41)
    # zz416: NamedType('%bv')
    # Operation(args=[Var(name='zz415'), Var(name='zz413'), Var(name='zz414')], name='zsubrange_bits', result='zz416', sourcepos='`1 112:22-112:23')
    zz416 = supportcode.vector_subrange(machine, zz415, zz413, zz414)
    # Assignment(result='zz44', sourcepos='`1 112:22-112:23', value=Var(name='zz416'))
    zz44 = zz416.touint()
    # LocalVarDeclaration(name='zz45', sourcepos='`1 112:8-112:9', typ=NamedType('%bv1'), value=None)
    # zz45: NamedType('%bv1')
    zz45 = r_uint(0)
    # zz49: NamedType('%i')
    # Operation(args=[Number(number=2)], name='zz5i64zDzKz5i', result='zz49', sourcepos='`1 112:8-112:9')
    zz49 = smallintconst2_1
    # zz410: NamedType('%i')
    # Operation(args=[Number(number=2)], name='zz5i64zDzKz5i', result='zz410', sourcepos='`1 112:8-112:9')
    zz410 = smallintconst2_1
    # zz411: NamedType('%bv')
    # Assignment(result='zz411', sourcepos='`1 112:8-112:9', value=Var(name='zz41'))
    zz411 = bitvector.from_ruint(3, zz41)
    # zz412: NamedType('%bv')
    # Operation(args=[Var(name='zz411'), Var(name='zz49'), Var(name='zz410')], name='zsubrange_bits', result='zz412', sourcepos='`1 112:8-112:9')
    zz412 = supportcode.vector_subrange(machine, zz411, zz49, zz410)
    # Assignment(result='zz45', sourcepos='`1 112:8-112:9', value=Var(name='zz412'))
    zz45 = zz412.touint()
    # zz46: NamedType('%bool')
    # Operation(args=[Var(name='zz45')], name='zbits1_to_bool', result='zz46', sourcepos='`1 112:52-112:68')
    zz46 = func_zbits1_to_bool(machine, zz45)
    # zz47: NamedType('%bool')
    # Operation(args=[Var(name='zz44')], name='zbits1_to_bool', result='zz47', sourcepos='`1 112:70-112:86')
    zz47 = func_zbits1_to_bool(machine, zz44)
    # zz48: NamedType('%bool')
    # Operation(args=[Var(name='zz43')], name='zbits1_to_bool', result='zz48', sourcepos='`1 112:88-112:104')
    zz48 = func_zbits1_to_bool(machine, zz43)
    # Assignment(result='zz40', sourcepos='`1 112:51-112:105', value=StructConstruction(fieldnames=['ztuplez3z5bool_z5bool_z5bool0', 'ztuplez3z5bool_z5bool_z5bool1', 'ztuplez3z5bool_z5bool_z5bool2'], fieldvalues=[Var(name='zz46'), Var(name='zz47'), Var(name='zz48')], name='ztuplez3z5bool_z5bool_z5bool'))
    zz40 = Struct_ztuplez3z5bool_z5bool_z5bool(zz46, zz47, zz48)
    # Assignment(result='return', sourcepos='`1 111:4-113:5', value=Var(name='zz40'))
    return_ = zz40
    # End()
    return return_



def func_zdecode(machine, zmergez3var):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zz40', sourcepos='`1 99:16-100:39', typ=UnionType(name='zoptionzIUinstrzIzKzK'), value=None)
            # zz40: UnionType(name='zoptionzIUinstrzIzKzK')
            zz40 = Union_zoptionzIUinstrzIzKzK.singleton
            # zz435: NamedType('%bv16')
            # Assignment(result='zz435', sourcepos='`1 99:23-99:41', value=Var(name='zmergez3var'))
            zz435 = zmergez3var
            if not supportcode.eq_bits(machine, bitvector.from_ruint(1, supportcode.vector_subrange(machine, bitvector.from_ruint(16, zz435), smallintconst15_1, smallintconst15_1).touint()), bitvectorconstant0b0_1):
                # inline pc=21
                pc = 44
                continue
            pc = 22
        if pc == 22:
            # Operation(args=[OperationExpr(args=[CastExpr(expr=OperationExpr(args=[CastExpr(expr=CastExpr(expr=OperationExpr(args=[CastExpr(expr=Var(name='zz435'), typ=NamedType('%bv')), OperationExpr(args=[Number(number=14)], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zsubrange_bits', typ=NamedType('%bv')), typ=NamedType('%bv15')), typ=NamedType('%bv')), OperationExpr(args=[Number(number=16)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zsail_zzero_extend', typ=NamedType('%bv')), typ=NamedType('%bv16'))], name='zAINST', typ=UnionType(name='zinstr'))], name='zSomezIUinstrzIzKzK', result='zz40', sourcepos=None)
            zz40 = Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK(Union_zinstr_zAINST(supportcode.zero_extend(machine, bitvector.from_ruint(15, supportcode.vector_subrange(machine, bitvector.from_ruint(16, zz435), smallintconst14_1, smallintconst0_1).touint()), smallintconst16_1).touint()))
            pc = 118
        if pc == 44:
            # zz41: NamedType('%bv16')
            # Assignment(result='zz41', sourcepos='`1 118:23-118:90', value=Var(name='zmergez3var'))
            zz41 = zmergez3var
            if not supportcode.eq_bits(machine, bitvector.from_ruint(3, supportcode.vector_subrange(machine, bitvector.from_ruint(16, zz41), smallintconst15_1, smallintconst13_1).touint()), bitvectorconstant0b111_1):
                # inline pc=64
                pc = 117
                continue
            pc = 65
        if pc == 65:
            # Operation(args=[OperationExpr(args=[CastExpr(expr=StructConstruction(fieldnames=['ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3'], fieldvalues=[CastExpr(expr=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), OperationExpr(args=[Number(number=12)], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=12)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zsubrange_bits', typ=NamedType('%bv')), typ=NamedType('%bv1')), OperationExpr(args=[CastExpr(expr=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), OperationExpr(args=[Number(number=11)], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=6)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zsubrange_bits', typ=NamedType('%bv')), typ=NamedType('%bv6'))], name='zdecode_compute_backwards', typ=EnumType(name='zarithmetic_op')), OperationExpr(args=[CastExpr(expr=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), OperationExpr(args=[Number(number=5)], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=3)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zsubrange_bits', typ=NamedType('%bv')), typ=NamedType('%bv3'))], name='zdecode_destination', typ=StructType(name='ztuplez3z5bool_z5bool_z5bool')), OperationExpr(args=[CastExpr(expr=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), OperationExpr(args=[Number(number=2)], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zsubrange_bits', typ=NamedType('%bv')), typ=NamedType('%bv3'))], name='zdecode_jump_backwards', typ=EnumType(name='zjump'))], name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump'), typ=StructType(name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump'))], name='zCINST', typ=UnionType(name='zinstr'))], name='zSomezIUinstrzIzKzK', result='zz40', sourcepos=None)
            zz40 = Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK(Union_zinstr_zCINST(Struct_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump(supportcode.vector_subrange(machine, bitvector.from_ruint(16, zz41), smallintconst12_1, smallintconst12_1).touint(), func_zdecode_compute_backwards(machine, supportcode.vector_subrange(machine, bitvector.from_ruint(16, zz41), smallintconst11_1, smallintconst6_1).touint()), func_zdecode_destination(machine, supportcode.vector_subrange(machine, bitvector.from_ruint(16, zz41), smallintconst5_1, smallintconst3_1).touint()), func_zdecode_jump_backwards(machine, supportcode.vector_subrange(machine, bitvector.from_ruint(16, zz41), smallintconst2_1, smallintconst0_1).touint()))))
            pc = 118
        if pc == 117:
            # Operation(args=[Unit()], name='zNonezIUinstrzIzKzK', result='zz40', sourcepos='`1 121:27-121:33')
            zz40 = Union_zoptionzIUinstrzIzKzK_zNonezIUinstrzIzKzK.singleton
            pc = 118
        if pc == 118:
            # Assignment(result='return', sourcepos='`1 99:16-100:39', value=Var(name='zz40'))
            return_ = zz40
            # End()
            return return_




def func_zcompute_value(machine, za, zop):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zz40', sourcepos='`1 124:2-146:8', typ=NamedType('%bv16'), value=None)
            # zz40: NamedType('%bv16')
            zz40 = r_uint(0)
            # zz442: NamedType('%bv')
            # Assignment(result='zz442', sourcepos='`1 124:13-124:21', value=Var(name='za'))
            zz442 = bitvector.from_ruint(1, za)
            if supportcode.eq_bits(machine, zz442, bitvectorconstant0b0_1):
                # inline pc=10
                # Assignment(result='zz40', sourcepos='`1 124:27-124:28', value=Var(name='zA'))
                zz40 = machine._reg_zA
                pc = 11
                continue
            # Operation(args=[Var(name='zA')], name='zread_mem', result='zz40', sourcepos='`1 124:34-124:45')
            zz40 = supportcode.my_read_mem(machine, machine._reg_zA)
            pc = 11
        if pc == 11:
            # zz41: NamedType('%bv16')
            # Assignment(result='zz41', sourcepos='`1 125:10-125:11', value=Var(name='zD'))
            zz41 = machine._reg_zD
            # LocalVarDeclaration(name='zz42', sourcepos='`1 126:2-146:8', typ=NamedType('%bv16'), value=None)
            # zz42: NamedType('%bv16')
            zz42 = r_uint(0)
            # LocalVarDeclaration(name='zz43', sourcepos='`1 126:26-145:3', typ=NamedType('%bv16'), value=None)
            # zz43: NamedType('%bv16')
            zz43 = r_uint(0)
            if not (Enum_zarithmetic_op.zC_ZERO == zop):
                # inline pc=18
                if not (Enum_zarithmetic_op.zC_ONE == zop):
                    # inline pc=21
                    if not (Enum_zarithmetic_op.zC_MINUSONE == zop):
                        # inline pc=24
                        if not (Enum_zarithmetic_op.zC_D == zop):
                            # inline pc=27
                            if not (Enum_zarithmetic_op.zC_A == zop):
                                # inline pc=30
                                if not (Enum_zarithmetic_op.zC_NOT_D == zop):
                                    # inline pc=37
                                    if not (Enum_zarithmetic_op.zC_NOT_A == zop):
                                        # inline pc=44
                                        if not (Enum_zarithmetic_op.zC_NEG_D == zop):
                                            # inline pc=53
                                            if not (Enum_zarithmetic_op.zC_NEG_A == zop):
                                                # inline pc=62
                                                if not (Enum_zarithmetic_op.zC_D_ADD_1 == zop):
                                                    # inline pc=71
                                                    if not (Enum_zarithmetic_op.zC_A_ADD_1 == zop):
                                                        # inline pc=80
                                                        if not (Enum_zarithmetic_op.zC_D_SUB_1 == zop):
                                                            # inline pc=89
                                                            if not (Enum_zarithmetic_op.zC_A_SUB_1 == zop):
                                                                # inline pc=98
                                                                if not (Enum_zarithmetic_op.zC_D_ADD_A == zop):
                                                                    # inline pc=107
                                                                    if not (Enum_zarithmetic_op.zC_D_SUB_A == zop):
                                                                        # inline pc=116
                                                                        if not (Enum_zarithmetic_op.zC_A_SUB_D == zop):
                                                                            # inline pc=125
                                                                            if not (Enum_zarithmetic_op.zC_D_AND_A == zop):
                                                                                # inline pc=134
                                                                                if not (Enum_zarithmetic_op.zC_D_OR_A == zop):
                                                                                    # inline pc=143
                                                                                    # Exit(kind='match', sourcepos='`1 126:26-145:3')
                                                                                    raise TypeError
                                                                                    continue
                                                                                # zz45: NamedType('%bv')
                                                                                # Assignment(result='zz45', sourcepos='`1 144:16-144:21', value=Var(name='zz40'))
                                                                                zz45 = bitvector.from_ruint(16, zz40)
                                                                                # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), Var(name='zz45')], name='zor_vec', typ=NamedType('%bv')))
                                                                                zz43 = supportcode.or_bits(machine, bitvector.from_ruint(16, zz41), zz45).touint()
                                                                                pc = 144
                                                                                continue
                                                                            # zz48: NamedType('%bv')
                                                                            # Assignment(result='zz48', sourcepos='`1 143:17-143:22', value=Var(name='zz40'))
                                                                            zz48 = bitvector.from_ruint(16, zz40)
                                                                            # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), Var(name='zz48')], name='zand_vec', typ=NamedType('%bv')))
                                                                            zz43 = supportcode.and_bits(machine, bitvector.from_ruint(16, zz41), zz48).touint()
                                                                            pc = 144
                                                                            continue
                                                                        # zz410: NamedType('%bv')
                                                                        # Assignment(result='zz410', sourcepos='`1 142:17-142:22', value=Var(name='zz40'))
                                                                        zz410 = bitvector.from_ruint(16, zz40)
                                                                        # Assignment(result='zz43', value=OperationExpr(args=[Var(name='zz410'), CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv'))], name='zsub_vec', typ=NamedType('%bv')))
                                                                        zz43 = supportcode.sub_bits(machine, zz410, bitvector.from_ruint(16, zz41)).touint()
                                                                        pc = 144
                                                                        continue
                                                                    # zz414: NamedType('%bv')
                                                                    # Assignment(result='zz414', sourcepos='`1 141:17-141:22', value=Var(name='zz40'))
                                                                    zz414 = bitvector.from_ruint(16, zz40)
                                                                    # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), Var(name='zz414')], name='zsub_vec', typ=NamedType('%bv')))
                                                                    zz43 = supportcode.sub_bits(machine, bitvector.from_ruint(16, zz41), zz414).touint()
                                                                    pc = 144
                                                                    continue
                                                                # zz417: NamedType('%bv')
                                                                # Assignment(result='zz417', sourcepos='`1 140:17-140:22', value=Var(name='zz40'))
                                                                zz417 = bitvector.from_ruint(16, zz40)
                                                                # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), Var(name='zz417')], name='zadd_bits', typ=NamedType('%bv')))
                                                                zz43 = supportcode.add_bits(machine, bitvector.from_ruint(16, zz41), zz417).touint()
                                                                pc = 144
                                                                continue
                                                            # zz419: NamedType('%bv')
                                                            # Assignment(result='zz419', sourcepos='`1 139:17-139:27', value=Var(name='zz40'))
                                                            zz419 = bitvector.from_ruint(16, zz40)
                                                            # Assignment(result='zz43', value=OperationExpr(args=[Var(name='zz419'), CastExpr(expr=BitVectorConstant(constant='0x0001'), typ=NamedType('%bv'))], name='zsub_vec', typ=NamedType('%bv')))
                                                            zz43 = supportcode.sub_bits(machine, zz419, bitvectorconstant0x0001_1).touint()
                                                            pc = 144
                                                            continue
                                                        # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), CastExpr(expr=BitVectorConstant(constant='0x0001'), typ=NamedType('%bv'))], name='zsub_vec', typ=NamedType('%bv')))
                                                        zz43 = supportcode.sub_bits(machine, bitvector.from_ruint(16, zz41), bitvectorconstant0x0001_1).touint()
                                                        pc = 144
                                                        continue
                                                    # zz425: NamedType('%bv')
                                                    # Assignment(result='zz425', sourcepos='`1 137:17-137:27', value=Var(name='zz40'))
                                                    zz425 = bitvector.from_ruint(16, zz40)
                                                    # Assignment(result='zz43', value=OperationExpr(args=[Var(name='zz425'), CastExpr(expr=BitVectorConstant(constant='0x0001'), typ=NamedType('%bv'))], name='zadd_bits', typ=NamedType('%bv')))
                                                    zz43 = supportcode.add_bits(machine, zz425, bitvectorconstant0x0001_1).touint()
                                                    pc = 144
                                                    continue
                                                # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), CastExpr(expr=BitVectorConstant(constant='0x0001'), typ=NamedType('%bv'))], name='zadd_bits', typ=NamedType('%bv')))
                                                zz43 = supportcode.add_bits(machine, bitvector.from_ruint(16, zz41), bitvectorconstant0x0001_1).touint()
                                                pc = 144
                                                continue
                                            # zz432: NamedType('%bv')
                                            # Assignment(result='zz432', sourcepos='`1 135:15-135:23', value=Var(name='zz40'))
                                            zz432 = bitvector.from_ruint(16, zz40)
                                            # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=BitVectorConstant(constant='0x0000'), typ=NamedType('%bv')), Var(name='zz432')], name='zsub_vec', typ=NamedType('%bv')))
                                            zz43 = supportcode.sub_bits(machine, bitvectorconstant0x0000_1, zz432).touint()
                                            pc = 144
                                            continue
                                        # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=BitVectorConstant(constant='0x0000'), typ=NamedType('%bv')), CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv'))], name='zsub_vec', typ=NamedType('%bv')))
                                        zz43 = supportcode.sub_bits(machine, bitvectorconstant0x0000_1, bitvector.from_ruint(16, zz41)).touint()
                                        pc = 144
                                        continue
                                    # zz437: NamedType('%bv')
                                    # Assignment(result='zz437', sourcepos='`1 133:15-133:25', value=Var(name='zz40'))
                                    zz437 = bitvector.from_ruint(16, zz40)
                                    # Assignment(result='zz43', value=OperationExpr(args=[Var(name='zz437')], name='znot_vec', typ=NamedType('%bv')))
                                    zz43 = supportcode.not_bits(machine, zz437).touint()
                                    pc = 144
                                    continue
                                # Assignment(result='zz43', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv'))], name='znot_vec', typ=NamedType('%bv')))
                                zz43 = supportcode.not_bits(machine, bitvector.from_ruint(16, zz41)).touint()
                                pc = 144
                                continue
                            # Assignment(result='zz43', sourcepos='`1 131:11-131:12', value=Var(name='zz40'))
                            zz43 = zz40
                            pc = 144
                            continue
                        # Assignment(result='zz43', sourcepos='`1 130:11-130:12', value=Var(name='zz41'))
                        zz43 = zz41
                        pc = 144
                        continue
                    # Assignment(result='zz43', sourcepos='`1 129:18-129:24', value=BitVectorConstant(constant='0xFFFF'))
                    zz43 = r_uint(0xFFFF)
                    pc = 144
                    continue
                # Assignment(result='zz43', sourcepos='`1 128:13-128:19', value=BitVectorConstant(constant='0x0001'))
                zz43 = r_uint(0x0001)
                pc = 144
                continue
            # Assignment(result='zz43', sourcepos='`1 127:14-127:20', value=BitVectorConstant(constant='0x0000'))
            zz43 = r_uint(0x0000)
            pc = 144
        if pc == 144:
            # Assignment(result='zz42', sourcepos='`1 126:26-145:3', value=Var(name='zz43'))
            zz42 = zz43
            # Assignment(result='return', sourcepos='`1 146:2-146:8', value=Var(name='zz42'))
            return_ = zz42
            # End()
            return return_




def func_zassign_dest(machine, zgsz381, zvalue):
    pc = 0
    while 1:
        if pc == 0:
            # zz40: NamedType('%bool')
            # Assignment(result='zz40', sourcepos='`1 149:22-149:23', value=FieldAccess(element='ztuplez3z5bool_z5bool_z5bool0', obj=Var(name='zgsz381')))
            zz40 = zgsz381.ztuplez3z5bool_z5bool_z5bool0
            # zz41: NamedType('%bool')
            # Assignment(result='zz41', sourcepos='`1 149:32-149:33', value=FieldAccess(element='ztuplez3z5bool_z5bool_z5bool1', obj=Var(name='zgsz381')))
            zz41 = zgsz381.ztuplez3z5bool_z5bool_z5bool1
            # zz42: NamedType('%bool')
            # Assignment(result='zz42', sourcepos='`1 149:42-149:43', value=FieldAccess(element='ztuplez3z5bool_z5bool_z5bool2', obj=Var(name='zgsz381')))
            zz42 = zgsz381.ztuplez3z5bool_z5bool_z5bool2
            # LocalVarDeclaration(name='zz44', sourcepos='`1 150:4-150:38', typ=NamedType('%unit'), value=None)
            # zz44: NamedType('%unit')
            zz44 = ()
            if zz42:
                # inline pc=10
                # Operation(args=[Var(name='zA'), Var(name='zvalue')], name='zwrite_mem', result='zz44', sourcepos='`1 150:16-150:35')
                zz44 = supportcode.my_write_mem(machine, machine._reg_zA, zvalue)
                pc = 11
                continue
            # Assignment(result='zz44', sourcepos='`1 150:38-150:38', value=Unit())
            zz44 = ()
            pc = 11
        if pc == 11:
            # LocalVarDeclaration(name='zz43', sourcepos='`1 151:4-151:28', typ=NamedType('%unit'), value=None)
            # zz43: NamedType('%unit')
            zz43 = ()
            if zz40:
                # inline pc=15
                # Assignment(result='zA', sourcepos='`1 151:20-151:25', value=Var(name='zvalue'))
                machine._reg_zA = zvalue
                # Assignment(result='zz43', sourcepos='`1 151:16-151:25', value=Unit())
                zz43 = ()
                pc = 17
                continue
            # Assignment(result='zz43', sourcepos='`1 151:28-151:28', value=Unit())
            zz43 = ()
            pc = 17
        if pc == 17:
            if zz41:
                # inline pc=20
                # Assignment(result='zD', sourcepos='`1 152:20-152:25', value=Var(name='zvalue'))
                machine._reg_zD = zvalue
                # Assignment(result='return', sourcepos='`1 152:16-152:25', value=Unit())
                return_ = ()
                pc = 22
                continue
            # Assignment(result='return', sourcepos='`1 152:28-152:28', value=Unit())
            return_ = ()
            pc = 22
        if pc == 22:
            # End()
            return return_




def func_zmaybe_jump(machine, zvalue, zj):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zz40', sourcepos='`1 155:58-167:1', typ=NamedType('%bool'), value=None)
            # zz40: NamedType('%bool')
            zz40 = False
            # LocalVarDeclaration(name='zz44', sourcepos='`1 156:18-165:5', typ=NamedType('%bool'), value=None)
            # zz44: NamedType('%bool')
            zz44 = False
            if not (Enum_zjump.zJDONT == zj):
                # inline pc=5
                if not (Enum_zjump.zJGT == zj):
                    # inline pc=18
                    if not (Enum_zjump.zJEQ == zj):
                        # inline pc=31
                        if not (Enum_zjump.zJGE == zj):
                            # inline pc=44
                            if not (Enum_zjump.zJLT == zj):
                                # inline pc=57
                                if not (Enum_zjump.zJNE == zj):
                                    # inline pc=70
                                    if not (Enum_zjump.zJLE == zj):
                                        # inline pc=83
                                        if not (Enum_zjump.zJMP == zj):
                                            # inline pc=86
                                            # Exit(kind='match', sourcepos='`1 156:18-165:5')
                                            raise TypeError
                                            continue
                                        # Assignment(result='zz44', sourcepos='`1 164:15-164:19', value=Var(name='true'))
                                        zz44 = True
                                        pc = 87
                                        continue
                                    # zz48: NamedType('%bv')
                                    # Assignment(result='zz48', sourcepos='`1 163:15-163:28', value=Var(name='zvalue'))
                                    zz48 = bitvector.from_ruint(16, zvalue)
                                    # Operation(args=[OperationExpr(args=[OperationExpr(args=[OperationExpr(args=[Var(name='zz48')], name='zsigned', typ=NamedType('%i'))], name='zz5izDzKz5i64', typ=NamedType('%i64'))], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zlteq_int', result='zz44', sourcepos=None)
                                    zz44 = supportcode.lteq(machine, supportcode.int64_to_int(machine, supportcode.int_to_int64(machine, supportcode.sail_signed(machine, zz48))), smallintconst0_1)
                                    pc = 87
                                    continue
                                # zz413: NamedType('%bv')
                                # Assignment(result='zz413', sourcepos='`1 162:15-162:28', value=Var(name='zvalue'))
                                zz413 = bitvector.from_ruint(16, zvalue)
                                # Operation(args=[OperationExpr(args=[OperationExpr(args=[OperationExpr(args=[Var(name='zz413')], name='zsigned', typ=NamedType('%i'))], name='zz5izDzKz5i64', typ=NamedType('%i64'))], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zneq_int', result='zz44', sourcepos=None)
                                zz44 = func_zneq_int(machine, supportcode.int64_to_int(machine, supportcode.int_to_int64(machine, supportcode.sail_signed(machine, zz413))), smallintconst0_1)
                                pc = 87
                                continue
                            # zz418: NamedType('%bv')
                            # Assignment(result='zz418', sourcepos='`1 161:15-161:28', value=Var(name='zvalue'))
                            zz418 = bitvector.from_ruint(16, zvalue)
                            # Operation(args=[OperationExpr(args=[OperationExpr(args=[OperationExpr(args=[Var(name='zz418')], name='zsigned', typ=NamedType('%i'))], name='zz5izDzKz5i64', typ=NamedType('%i64'))], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zlt_int', result='zz44', sourcepos=None)
                            zz44 = supportcode.lt(machine, supportcode.int64_to_int(machine, supportcode.int_to_int64(machine, supportcode.sail_signed(machine, zz418))), smallintconst0_1)
                            pc = 87
                            continue
                        # zz423: NamedType('%bv')
                        # Assignment(result='zz423', sourcepos='`1 160:15-160:28', value=Var(name='zvalue'))
                        zz423 = bitvector.from_ruint(16, zvalue)
                        # Operation(args=[OperationExpr(args=[OperationExpr(args=[OperationExpr(args=[Var(name='zz423')], name='zsigned', typ=NamedType('%i'))], name='zz5izDzKz5i64', typ=NamedType('%i64'))], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zgteq_int', result='zz44', sourcepos=None)
                        zz44 = supportcode.gteq(machine, supportcode.int64_to_int(machine, supportcode.int_to_int64(machine, supportcode.sail_signed(machine, zz423))), smallintconst0_1)
                        pc = 87
                        continue
                    # zz428: NamedType('%bv')
                    # Assignment(result='zz428', sourcepos='`1 159:15-159:28', value=Var(name='zvalue'))
                    zz428 = bitvector.from_ruint(16, zvalue)
                    # Operation(args=[OperationExpr(args=[OperationExpr(args=[OperationExpr(args=[Var(name='zz428')], name='zsigned', typ=NamedType('%i'))], name='zz5izDzKz5i64', typ=NamedType('%i64'))], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zeq_int', result='zz44', sourcepos=None)
                    zz44 = supportcode.eq_int(machine, supportcode.int64_to_int(machine, supportcode.int_to_int64(machine, supportcode.sail_signed(machine, zz428))), smallintconst0_1)
                    pc = 87
                    continue
                # zz433: NamedType('%bv')
                # Assignment(result='zz433', sourcepos='`1 158:15-158:28', value=Var(name='zvalue'))
                zz433 = bitvector.from_ruint(16, zvalue)
                # Operation(args=[OperationExpr(args=[OperationExpr(args=[OperationExpr(args=[Var(name='zz433')], name='zsigned', typ=NamedType('%i'))], name='zz5izDzKz5i64', typ=NamedType('%i64'))], name='zz5i64zDzKz5i', typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zgt_int', result='zz44', sourcepos=None)
                zz44 = supportcode.gt(machine, supportcode.int64_to_int(machine, supportcode.int_to_int64(machine, supportcode.sail_signed(machine, zz433))), smallintconst0_1)
                pc = 87
                continue
            # Assignment(result='zz44', sourcepos='`1 157:15-157:20', value=Var(name='false'))
            zz44 = False
            pc = 87
        if pc == 87:
            # Assignment(result='zz40', sourcepos='`1 156:18-165:5', value=Var(name='zz44'))
            zz40 = zz44
            if zz40:
                # inline pc=98
                # Assignment(result='zPC', sourcepos='`1 166:23-166:24', value=Var(name='zA'))
                machine._reg_zPC = machine._reg_zA
                # Assignment(result='return', sourcepos='`1 166:18-166:24', value=Unit())
                return_ = ()
                pc = 100
                continue
            # zz42: NamedType('%bv')
            # Assignment(result='zz42', sourcepos='`1 166:38-166:44', value=Var(name='zPC'))
            zz42 = bitvector.from_ruint(16, machine._reg_zPC)
            # Assignment(result='zPC', value=OperationExpr(args=[Var(name='zz42'), OperationExpr(args=[Number(number=1)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zadd_bits_int', typ=NamedType('%bv')))
            machine._reg_zPC = supportcode.add_bits_int(machine, zz42, smallintconst1_1).touint()
            # Assignment(result='return', sourcepos='`1 166:33-166:44', value=Unit())
            return_ = ()
            pc = 100
        if pc == 100:
            # End()
            return return_



def func_zexecute(machine, zmergez3var):
    return zmergez3var.meth_zexecute(machine, )

def zexecute_zAINST(zmergez3var, machine, ):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zz40', sourcepos='`1 102:16-104:1', typ=NamedType('%unit'), value=None)
            # zz40: NamedType('%unit')
            zz40 = ()
            # zz47: NamedType('%bv16')
            # Assignment(result='zz47', sourcepos='`1 102:30-102:31', value=Cast(expr=Var(name='zmergez3var'), variant='zAINST'))
            zz47 = Union_zinstr_zAINST.convert(zmergez3var)
            # Assignment(result='zA', sourcepos='`1 103:6-103:7', value=Var(name='zz47'))
            machine._reg_zA = zz47
            # zz411: NamedType('%unit')
            # Assignment(result='zz411', sourcepos='`1 103:2-103:7', value=Unit())
            zz411 = ()
            # Assignment(result='zPC', value=OperationExpr(args=[CastExpr(expr=Var(name='zPC'), typ=NamedType('%bv')), OperationExpr(args=[Number(number=1)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zadd_bits_int', typ=NamedType('%bv')))
            machine._reg_zPC = supportcode.add_bits_int(machine, bitvector.from_ruint(16, machine._reg_zPC), smallintconst1_1).touint()
            # Assignment(result='zz40', sourcepos='`1 103:9-103:20', value=Unit())
            zz40 = ()
            pc = 32
        if pc == 32:
            # Assignment(result='return', sourcepos='`1 102:16-104:1', value=Var(name='zz40'))
            return_ = zz40
            # End()
            return return_
Union_zinstr_zAINST.meth_zexecute = zexecute_zAINST

def zexecute_zCINST(zmergez3var, machine, ):
    pc = 16
    while 1:
        if pc == 16:
            # LocalVarDeclaration(name='zz40', sourcepos='`1 102:16-104:1', typ=NamedType('%unit'), value=None)
            # zz40: NamedType('%unit')
            zz40 = ()
            # zz41: NamedType('%bv1')
            # Assignment(result='zz41', sourcepos='`1 169:30-169:31', value=FieldAccess(element='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')))
            zz41 = Union_zinstr_zCINST.convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0(zmergez3var)
            # zz42: EnumType(name='zarithmetic_op')
            # Assignment(result='zz42', sourcepos='`1 169:33-169:35', value=FieldAccess(element='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')))
            zz42 = Union_zinstr_zCINST.convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1(zmergez3var)
            # zz43: StructType(name='ztuplez3z5bool_z5bool_z5bool')
            # Assignment(result='zz43', sourcepos='`1 169:37-169:41', value=FieldAccess(element='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')))
            zz43 = Union_zinstr_zCINST.convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2(zmergez3var)
            # zz44: EnumType(name='zjump')
            # Assignment(result='zz44', sourcepos='`1 169:43-169:47', value=FieldAccess(element='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')))
            zz44 = Union_zinstr_zCINST.convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3(zmergez3var)
            # zz45: NamedType('%bv16')
            # Operation(args=[Var(name='zz41'), Var(name='zz42')], name='zcompute_value', result='zz45', sourcepos='`1 170:14-170:34')
            zz45 = func_zcompute_value(machine, zz41, zz42)
            # zz46: NamedType('%unit')
            # Operation(args=[Var(name='zz43'), Var(name='zz45')], name='zassign_dest', result='zz46', sourcepos='`1 171:2-171:26')
            zz46 = func_zassign_dest(machine, zz43, zz45)
            # Operation(args=[Var(name='zz45'), Var(name='zz44')], name='zmaybe_jump', result='zz40', sourcepos='`1 172:2-172:25')
            zz40 = func_zmaybe_jump(machine, zz45, zz44)
            pc = 32
        if pc == 32:
            # Assignment(result='return', sourcepos='`1 102:16-104:1', value=Var(name='zz40'))
            return_ = zz40
            # End()
            return return_
Union_zinstr_zCINST.meth_zexecute = zexecute_zCINST

def zexecute_default(zmergez3var, machine, ):
    pc = 31
    while 1:
        if pc == 31:
            # LocalVarDeclaration(name='zz40', sourcepos='`1 102:16-104:1', typ=NamedType('%unit'), value=None)
            # zz40: NamedType('%unit')
            zz40 = ()
            # Exit(kind='match', sourcepos='`1 102:16-104:1')
            raise TypeError
Union_zinstr.meth_zexecute = zexecute_default



def func_zfetch_decode_execute(machine, zgsz3106):
    pc = 0
    while 1:
        if pc == 0:
            # zz40: NamedType('%bv16')
            # Operation(args=[Var(name='zPC')], name='zread_rom', result='zz40', sourcepos='`1 179:27-179:39')
            zz40 = supportcode.my_read_rom(machine, machine._reg_zPC)
            # zz41: UnionType(name='zoptionzIUinstrzIzKzK')
            # Operation(args=[Var(name='zz40')], name='zdecode', result='zz41', sourcepos='`1 180:12-180:25')
            zz41 = func_zdecode(machine, zz40)
            # zz42: NamedType('%bool')
            # Assignment(result='zz42', sourcepos='`1 181:18-181:23', value=Var(name='false'))
            zz42 = False
            # LocalVarDeclaration(name='zz43', sourcepos='`1 182:4-185:5', typ=NamedType('%unit'), value=None)
            # zz43: NamedType('%unit')
            zz43 = ()
            if not isinstance(zz41, Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK):
                # inline pc=15
                if not isinstance(zz41, Union_zoptionzIUinstrzIzKzK_zNonezIUinstrzIzKzK):
                    # inline pc=19
                    # Exit(kind='match', sourcepos='`1 182:4-185:5')
                    raise TypeError
                    continue
                # Assignment(result='zz42', sourcepos='`1 184:27-184:32', value=Var(name='false'))
                zz42 = False
                # Assignment(result='zz43', sourcepos='`1 184:20-184:32', value=Unit())
                zz43 = ()
                pc = 20
                continue
            # zz46: NamedType('%unit')
            # Operation(args=[CastExpr(expr=Cast(expr=Var(name='zz41'), variant='zSomezIUinstrzIzKzK'), typ=UnionType(name='zinstr'))], name='zexecute', result='zz46', sourcepos=None)
            zz46 = func_zexecute(machine, Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK.convert(zz41))
            # Assignment(result='zz42', sourcepos='`1 183:48-183:52', value=Var(name='true'))
            zz42 = True
            # Assignment(result='zz43', sourcepos='`1 183:41-183:52', value=Unit())
            zz43 = ()
            pc = 20
        if pc == 20:
            # zz44: NamedType('%unit')
            # Assignment(result='zz44', sourcepos='`1 182:4-185:5', value=Var(name='zz43'))
            zz44 = zz43
            # Assignment(result='return', sourcepos='`59', value=Var(name='zz42'))
            return_ = zz42
            # End()
            return return_




def func_zrun(machine, zlimit, zdebug):
    pc = 0
    while 1:
        if pc == 0:
            # zz40: NamedType('%bv64')
            # Assignment(result='zz40', sourcepos='`1 192:29-192:47', value=BitVectorConstant(constant='0x0000000000000000'))
            zz40 = r_uint(0x0000000000000000)
            # zz41: NamedType('%bool')
            # Assignment(result='zz41', sourcepos='`1 193:18-193:22', value=Var(name='true'))
            zz41 = True
            # LocalVarDeclaration(name='zz42', sourcepos='`1 194:4-205:5', typ=NamedType('%bool'), value=None)
            # zz42: NamedType('%bool')
            zz42 = False
            # LocalVarDeclaration(name='zz43', sourcepos='`1 194:4-205:5', typ=NamedType('%unit'), value=None)
            # zz43: NamedType('%unit')
            zz43 = ()
            pc = 6
        if pc == 6:
            # Assignment(result='zz42', sourcepos='`1 194:11-194:15', value=Var(name='zz41'))
            zz42 = zz41
            if not zz42:
                # inline pc=54
                # Assignment(result='return', sourcepos='`1 194:4-205:5', value=Unit())
                return_ = ()
                # End()
                return return_
                continue
            # Assignment(result='zz41', sourcepos='`1 195:15-195:20', value=Var(name='false'))
            zz41 = False
            # zz419: NamedType('%unit')
            # Assignment(result='zz419', sourcepos='`1 195:8-195:20', value=Unit())
            zz419 = ()
            # LocalVarDeclaration(name='zz418', sourcepos='`1 196:8-198:9', typ=NamedType('%unit'), value=None)
            # zz418: NamedType('%unit')
            zz418 = ()
            if zdebug:
                # inline pc=15
                # Operation(args=[Var(name='zz40'), Var(name='zPC'), Var(name='zA'), Var(name='zD')], name='zprint_debug', result='zz418', sourcepos='`1 197:12-197:46')
                zz418 = supportcode.my_print_debug(machine, zz40, machine._reg_zPC, machine._reg_zA, machine._reg_zD)
                pc = 16
                continue
            # Assignment(result='zz418', sourcepos='`1 198:9-198:9', value=Unit())
            zz418 = ()
            pc = 16
        if pc == 16:
            # LocalVarDeclaration(name='zz48', sourcepos='`1 199:8-203:9', typ=NamedType('%unit'), value=None)
            # zz48: NamedType('%unit')
            zz48 = ()
            if func_zfetch_decode_execute(machine, ()):
                # inline pc=22
                # zz416: NamedType('%bv')
                # Assignment(result='zz416', sourcepos='`1 200:15-200:34', value=Var(name='zz40'))
                zz416 = bitvector.from_ruint(64, zz40)
                # zz414: NamedType('%bv')
                # Assignment(result='zz414', sourcepos='`1 200:37-200:50', value=Var(name='zlimit'))
                zz414 = bitvector.from_ruint(64, zlimit)
                if supportcode.lt(machine, supportcode.int64_to_int(machine, supportcode.int_to_int64(machine, supportcode.sail_signed(machine, zz416))), supportcode.int64_to_int(machine, supportcode.int_to_int64(machine, supportcode.sail_signed(machine, zz414)))):
                    # inline pc=43
                    # Assignment(result='zz41', sourcepos='`1 201:23-201:27', value=Var(name='true'))
                    zz41 = True
                    # Assignment(result='zz48', sourcepos='`1 201:16-201:27', value=Unit())
                    zz48 = ()
                    pc = 45
                    continue
                # Assignment(result='zz48', sourcepos='`1 202:13-202:13', value=Unit())
                zz48 = ()
                pc = 45
                continue
            # Assignment(result='zz48', sourcepos='`1 203:9-203:9', value=Unit())
            zz48 = ()
            pc = 45
        if pc == 45:
            # zz44: NamedType('%bv')
            # Assignment(result='zz44', sourcepos='`1 204:22-204:54', value=Var(name='zz40'))
            zz44 = bitvector.from_ruint(64, zz40)
            # Assignment(result='zz40', value=OperationExpr(args=[Var(name='zz44'), CastExpr(expr=BitVectorConstant(constant='0x0000000000000001'), typ=NamedType('%bv'))], name='zadd_bits', typ=NamedType('%bv')))
            zz40 = supportcode.add_bits(machine, zz44, bitvectorconstant0x0000000000000001_1).touint()
            # Assignment(result='zz43', sourcepos='`1 204:8-204:54', value=Unit())
            zz43 = ()
            pc = 6




def func_zmymain(machine, zlimit, zdebug):
    # Assignment(result='zPC', sourcepos='`1 209:9-209:15', value=BitVectorConstant(constant='0x0000'))
    machine._reg_zPC = r_uint(0x0000)
    # zz42: NamedType('%unit')
    # Assignment(result='zz42', sourcepos='`1 209:4-209:15', value=Unit())
    zz42 = ()
    # Assignment(result='zA', sourcepos='`1 210:8-210:14', value=BitVectorConstant(constant='0x0000'))
    machine._reg_zA = r_uint(0x0000)
    # zz41: NamedType('%unit')
    # Assignment(result='zz41', sourcepos='`1 210:4-210:14', value=Unit())
    zz41 = ()
    # Assignment(result='zD', sourcepos='`1 211:8-211:14', value=BitVectorConstant(constant='0x0000'))
    machine._reg_zD = r_uint(0x0000)
    # zz40: NamedType('%unit')
    # Assignment(result='zz40', sourcepos='`1 211:4-211:14', value=Unit())
    zz40 = ()
    # Operation(args=[Var(name='zlimit'), Var(name='zdebug')], name='zrun', result='return', sourcepos='`1 212:4-212:21')
    return_ = func_zrun(machine, zlimit, zdebug)
    # End()
    return return_




def func_zmain(machine, zgsz3120):
    # zz40: NamedType('%unit')
    # Operation(args=[BitVectorConstant(constant='0x0000000000000010'), Var(name='false')], name='zmymain', result='zz40', sourcepos='`1 218:27-218:60')
    zz40 = func_zmymain(machine, r_uint(0x0000000000000010), False)
    # Assignment(result='return', sourcepos='`60', value=Var(name='zz40'))
    return_ = zz40
    # End()
    return return_




def func_zinitializze_registers(machine, zgsz3121):
    # Assignment(result='zPC', sourcepos='`61', value=BitVectorConstant(constant='0x0000'))
    machine._reg_zPC = r_uint(0x0000)
    # zz41: NamedType('%unit')
    # Assignment(result='zz41', sourcepos='`63', value=Unit())
    zz41 = ()
    # Assignment(result='zA', sourcepos='`64', value=BitVectorConstant(constant='0x0000'))
    machine._reg_zA = r_uint(0x0000)
    # zz40: NamedType('%unit')
    # Assignment(result='zz40', sourcepos='`66', value=Unit())
    zz40 = ()
    # Assignment(result='zD', sourcepos='`67', value=BitVectorConstant(constant='0x0000'))
    machine._reg_zD = r_uint(0x0000)
    # Assignment(result='return', sourcepos='`68', value=Unit())
    return_ = ()
    # End()
    return return_


# Files(filenames=['"/home/cfbolz/.opam/ocaml.4.13.1/share/sail/lib/flow.sail"', '"nand2tetris.sail"'])
