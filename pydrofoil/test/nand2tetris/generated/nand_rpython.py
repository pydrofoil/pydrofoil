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

class Tuple_15(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv3')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_15)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv3')
        return True

class Tuple_16(supportcode.ObjectBase): # TupleType(elements=[UnionType(name='zinstr')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_16)
        if not (self.utup0.eq(other.utup0)): return False # UnionType(name='zinstr')
        return True
smallintconst16_1 = bitvector.SmallInteger(16)

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
smallintconst0_1 = bitvector.SmallInteger(0)
smallintconst1_1 = bitvector.SmallInteger(1)

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
    # Assignment(result='return', sourcepos=None, value=OperationExpr(args=[OperationExpr(args=[Var(name='zx'), Var(name='zy')], name='zeq_int', typ=NamedType('%bool'))], name='znot_bool', typ=NamedType('%bool')))
    return_ = supportcode.not_(machine, supportcode.eq_int(machine, zx, zy))
    # End()
    return return_



















def func_zbits1_to_bool(machine, zb):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zz40', sourcepos='`1 13:27-16:1', typ=NamedType('%bool'), value=None)
            # zz40: NamedType('%bool')
            zz40 = False
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zb'), BitVectorConstant(constant='0b1')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`1 13:27-16:1', target=11)
            if not supportcode.eq_bits_bv_bv(zb, r_uint(0b1)):
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
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b101010')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`3', target=11)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b101010)):
                # inline pc=11
                pc = 14
                continue
            pc = 12
        if pc == 12:
            # Assignment(result='zz40', sourcepos='`1 56:2-56:8', value=Var(name='zC_ZERO'))
            zz40 = Enum_zarithmetic_op.zC_ZERO
            pc = 236
        if pc == 14:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b111111')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`5', target=24)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b111111)):
                # inline pc=24
                pc = 27
                continue
            pc = 25
        if pc == 25:
            # Assignment(result='zz40', sourcepos='`1 57:2-57:7', value=Var(name='zC_ONE'))
            zz40 = Enum_zarithmetic_op.zC_ONE
            pc = 236
        if pc == 27:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b111010')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`7', target=37)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b111010)):
                # inline pc=37
                pc = 40
                continue
            pc = 38
        if pc == 38:
            # Assignment(result='zz40', sourcepos='`1 58:2-58:12', value=Var(name='zC_MINUSONE'))
            zz40 = Enum_zarithmetic_op.zC_MINUSONE
            pc = 236
        if pc == 40:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b001100')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`9', target=50)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b001100)):
                # inline pc=50
                pc = 53
                continue
            pc = 51
        if pc == 51:
            # Assignment(result='zz40', sourcepos='`1 59:2-59:5', value=Var(name='zC_D'))
            zz40 = Enum_zarithmetic_op.zC_D
            pc = 236
        if pc == 53:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b110000')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`11', target=63)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b110000)):
                # inline pc=63
                pc = 66
                continue
            pc = 64
        if pc == 64:
            # Assignment(result='zz40', sourcepos='`1 60:2-60:5', value=Var(name='zC_A'))
            zz40 = Enum_zarithmetic_op.zC_A
            pc = 236
        if pc == 66:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b001101')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`13', target=76)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b001101)):
                # inline pc=76
                pc = 79
                continue
            pc = 77
        if pc == 77:
            # Assignment(result='zz40', sourcepos='`1 61:2-61:9', value=Var(name='zC_NOT_D'))
            zz40 = Enum_zarithmetic_op.zC_NOT_D
            pc = 236
        if pc == 79:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b110001')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`15', target=89)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b110001)):
                # inline pc=89
                pc = 92
                continue
            pc = 90
        if pc == 90:
            # Assignment(result='zz40', sourcepos='`1 62:2-62:9', value=Var(name='zC_NOT_A'))
            zz40 = Enum_zarithmetic_op.zC_NOT_A
            pc = 236
        if pc == 92:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b001111')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`17', target=102)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b001111)):
                # inline pc=102
                pc = 105
                continue
            pc = 103
        if pc == 103:
            # Assignment(result='zz40', sourcepos='`1 63:2-63:9', value=Var(name='zC_NEG_D'))
            zz40 = Enum_zarithmetic_op.zC_NEG_D
            pc = 236
        if pc == 105:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b110011')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`19', target=115)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b110011)):
                # inline pc=115
                pc = 118
                continue
            pc = 116
        if pc == 116:
            # Assignment(result='zz40', sourcepos='`1 64:2-64:9', value=Var(name='zC_NEG_A'))
            zz40 = Enum_zarithmetic_op.zC_NEG_A
            pc = 236
        if pc == 118:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b011111')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`21', target=128)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b011111)):
                # inline pc=128
                pc = 131
                continue
            pc = 129
        if pc == 129:
            # Assignment(result='zz40', sourcepos='`1 65:2-65:11', value=Var(name='zC_D_ADD_1'))
            zz40 = Enum_zarithmetic_op.zC_D_ADD_1
            pc = 236
        if pc == 131:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b110111')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`23', target=141)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b110111)):
                # inline pc=141
                pc = 144
                continue
            pc = 142
        if pc == 142:
            # Assignment(result='zz40', sourcepos='`1 66:2-66:11', value=Var(name='zC_A_ADD_1'))
            zz40 = Enum_zarithmetic_op.zC_A_ADD_1
            pc = 236
        if pc == 144:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b001110')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`25', target=154)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b001110)):
                # inline pc=154
                pc = 157
                continue
            pc = 155
        if pc == 155:
            # Assignment(result='zz40', sourcepos='`1 67:2-67:11', value=Var(name='zC_D_SUB_1'))
            zz40 = Enum_zarithmetic_op.zC_D_SUB_1
            pc = 236
        if pc == 157:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b110010')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`27', target=167)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b110010)):
                # inline pc=167
                pc = 170
                continue
            pc = 168
        if pc == 168:
            # Assignment(result='zz40', sourcepos='`1 68:2-68:11', value=Var(name='zC_A_SUB_1'))
            zz40 = Enum_zarithmetic_op.zC_A_SUB_1
            pc = 236
        if pc == 170:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b000010')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`29', target=180)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b000010)):
                # inline pc=180
                pc = 183
                continue
            pc = 181
        if pc == 181:
            # Assignment(result='zz40', sourcepos='`1 69:2-69:11', value=Var(name='zC_D_ADD_A'))
            zz40 = Enum_zarithmetic_op.zC_D_ADD_A
            pc = 236
        if pc == 183:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b010011')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`31', target=193)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b010011)):
                # inline pc=193
                pc = 196
                continue
            pc = 194
        if pc == 194:
            # Assignment(result='zz40', sourcepos='`1 70:2-70:11', value=Var(name='zC_D_SUB_A'))
            zz40 = Enum_zarithmetic_op.zC_D_SUB_A
            pc = 236
        if pc == 196:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b000111')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`33', target=206)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b000111)):
                # inline pc=206
                pc = 209
                continue
            pc = 207
        if pc == 207:
            # Assignment(result='zz40', sourcepos='`1 71:2-71:11', value=Var(name='zC_A_SUB_D'))
            zz40 = Enum_zarithmetic_op.zC_A_SUB_D
            pc = 236
        if pc == 209:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b000000')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`35', target=219)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b000000)):
                # inline pc=219
                pc = 222
                continue
            pc = 220
        if pc == 220:
            # Assignment(result='zz40', sourcepos='`1 72:2-72:11', value=Var(name='zC_D_AND_A'))
            zz40 = Enum_zarithmetic_op.zC_D_AND_A
            pc = 236
        if pc == 222:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b010101')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`37', target=232)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b010101)):
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
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b000')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`42', target=11)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b000)):
                # inline pc=11
                pc = 14
                continue
            pc = 12
        if pc == 12:
            # Assignment(result='zz40', sourcepos='`1 79:2-79:7', value=Var(name='zJDONT'))
            zz40 = Enum_zjump.zJDONT
            pc = 106
        if pc == 14:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b001')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`44', target=24)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b001)):
                # inline pc=24
                pc = 27
                continue
            pc = 25
        if pc == 25:
            # Assignment(result='zz40', sourcepos='`1 80:2-80:5', value=Var(name='zJGT'))
            zz40 = Enum_zjump.zJGT
            pc = 106
        if pc == 27:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b010')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`46', target=37)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b010)):
                # inline pc=37
                pc = 40
                continue
            pc = 38
        if pc == 38:
            # Assignment(result='zz40', sourcepos='`1 81:2-81:5', value=Var(name='zJEQ'))
            zz40 = Enum_zjump.zJEQ
            pc = 106
        if pc == 40:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b011')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`48', target=50)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b011)):
                # inline pc=50
                pc = 53
                continue
            pc = 51
        if pc == 51:
            # Assignment(result='zz40', sourcepos='`1 82:2-82:5', value=Var(name='zJGE'))
            zz40 = Enum_zjump.zJGE
            pc = 106
        if pc == 53:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b100')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`50', target=63)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b100)):
                # inline pc=63
                pc = 66
                continue
            pc = 64
        if pc == 64:
            # Assignment(result='zz40', sourcepos='`1 83:2-83:5', value=Var(name='zJLT'))
            zz40 = Enum_zjump.zJLT
            pc = 106
        if pc == 66:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b101')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`52', target=76)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b101)):
                # inline pc=76
                pc = 79
                continue
            pc = 77
        if pc == 77:
            # Assignment(result='zz40', sourcepos='`1 84:2-84:5', value=Var(name='zJNE'))
            zz40 = Enum_zjump.zJNE
            pc = 106
        if pc == 79:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b110')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`54', target=89)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b110)):
                # inline pc=89
                pc = 92
                continue
            pc = 90
        if pc == 90:
            # Assignment(result='zz40', sourcepos='`1 85:2-85:5', value=Var(name='zJLE'))
            zz40 = Enum_zjump.zJLE
            pc = 106
        if pc == 92:
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[Var(name='zargz3'), BitVectorConstant(constant='0b111')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`56', target=102)
            if not supportcode.eq_bits_bv_bv(zargz3, r_uint(0b111)):
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
    # zz41: NamedType('%bv3')
    # Assignment(result='zz41', sourcepos='`1 112:8-112:47', value=Var(name='zb'))
    zz41 = zb
    # zz42: NamedType('%bv1')
    # Assignment(result='zz42', sourcepos='`1 112:8-112:9', value=OperationExpr(args=[Var(name='zz41'), Number(number=2), Number(number=2)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv1')))
    zz42 = supportcode.slice_fixed_bv_i_i(zz41, 2, 2)
    # Assignment(result='return', sourcepos='`1 111:4-113:5', value=StructConstruction(fieldnames=['ztuplez3z5bool_z5bool_z5bool0', 'ztuplez3z5bool_z5bool_z5bool1', 'ztuplez3z5bool_z5bool_z5bool2'], fieldvalues=[OperationExpr(args=[OperationExpr(args=[Var(name='zz41'), Number(number=2), Number(number=2)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv1'))], name='zbits1_to_bool', typ=NamedType('%bool')), OperationExpr(args=[OperationExpr(args=[Var(name='zz41'), Number(number=1), Number(number=1)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv1'))], name='zbits1_to_bool', typ=NamedType('%bool')), OperationExpr(args=[OperationExpr(args=[Var(name='zz41'), Number(number=0), Number(number=0)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv1'))], name='zbits1_to_bool', typ=NamedType('%bool'))], name='ztuplez3z5bool_z5bool_z5bool'))
    return_ = Struct_ztuplez3z5bool_z5bool_z5bool(func_zbits1_to_bool(machine, supportcode.slice_fixed_bv_i_i(zz41, 2, 2)), func_zbits1_to_bool(machine, supportcode.slice_fixed_bv_i_i(zz41, 1, 1)), func_zbits1_to_bool(machine, supportcode.slice_fixed_bv_i_i(zz41, 0, 0)))
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
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[OperationExpr(args=[Var(name='zz435'), Number(number=15), Number(number=15)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv1')), BitVectorConstant(constant='0b0')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`1 99:16-100:39', target=21)
            if not supportcode.eq_bits_bv_bv(supportcode.slice_fixed_bv_i_i(zz435, 15, 15), r_uint(0b0)):
                # inline pc=21
                pc = 44
                continue
            pc = 22
        if pc == 22:
            # Assignment(result='zz40', sourcepos=None, value=OperationExpr(args=[OperationExpr(args=[CastExpr(expr=OperationExpr(args=[CastExpr(expr=OperationExpr(args=[Var(name='zz435'), Number(number=14), Number(number=0)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv15')), typ=NamedType('%bv')), OperationExpr(args=[Number(number=16)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zsail_zzero_extend', typ=NamedType('%bv')), typ=NamedType('%bv16'))], name='zAINST', typ=UnionType(name='zinstr'))], name='zSomezIUinstrzIzKzK', typ=UnionType(name='zoptionzIUinstrzIzKzK')))
            zz40 = Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK(Union_zinstr_zAINST(supportcode.zero_extend(machine, bitvector.from_ruint(15, supportcode.slice_fixed_bv_i_i(zz435, 14, 0)), smallintconst16_1).touint()))
            pc = 118
        if pc == 44:
            # zz41: NamedType('%bv16')
            # Assignment(result='zz41', sourcepos='`1 118:23-118:90', value=Var(name='zmergez3var'))
            zz41 = zmergez3var
            # ConditionalJump(condition=Comparison(args=[OperationExpr(args=[OperationExpr(args=[Var(name='zz41'), Number(number=15), Number(number=13)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv3')), BitVectorConstant(constant='0b111')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))], operation='@not'), sourcepos='`1 99:16-100:39', target=64)
            if not supportcode.eq_bits_bv_bv(supportcode.slice_fixed_bv_i_i(zz41, 15, 13), r_uint(0b111)):
                # inline pc=64
                pc = 117
                continue
            pc = 65
        if pc == 65:
            # Assignment(result='zz40', sourcepos=None, value=OperationExpr(args=[OperationExpr(args=[CastExpr(expr=StructConstruction(fieldnames=['ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3'], fieldvalues=[OperationExpr(args=[Var(name='zz41'), Number(number=12), Number(number=12)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv1')), OperationExpr(args=[OperationExpr(args=[Var(name='zz41'), Number(number=11), Number(number=6)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv6'))], name='zdecode_compute_backwards', typ=EnumType(name='zarithmetic_op')), OperationExpr(args=[OperationExpr(args=[Var(name='zz41'), Number(number=5), Number(number=3)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv3'))], name='zdecode_destination', typ=StructType(name='ztuplez3z5bool_z5bool_z5bool')), OperationExpr(args=[OperationExpr(args=[Var(name='zz41'), Number(number=2), Number(number=0)], name='@slice_fixed_bv_i_i', typ=NamedType('%bv3'))], name='zdecode_jump_backwards', typ=EnumType(name='zjump'))], name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump'), typ=StructType(name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump'))], name='zCINST', typ=UnionType(name='zinstr'))], name='zSomezIUinstrzIzKzK', typ=UnionType(name='zoptionzIUinstrzIzKzK')))
            zz40 = Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK(Union_zinstr_zCINST(Struct_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump(supportcode.slice_fixed_bv_i_i(zz41, 12, 12), func_zdecode_compute_backwards(machine, supportcode.slice_fixed_bv_i_i(zz41, 11, 6)), func_zdecode_destination(machine, supportcode.slice_fixed_bv_i_i(zz41, 5, 3)), func_zdecode_jump_backwards(machine, supportcode.slice_fixed_bv_i_i(zz41, 2, 0)))))
            pc = 118
        if pc == 117:
            # Assignment(result='zz40', sourcepos='`1 121:27-121:33', value=OperationExpr(args=[Unit()], name='zNonezIUinstrzIzKzK', typ=UnionType(name='zoptionzIUinstrzIzKzK')))
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
            # ConditionalJump(condition=ExprCondition(expr=OperationExpr(args=[Var(name='za'), BitVectorConstant(constant='0b0')], name='@eq_bits_bv_bv', typ=NamedType('%bool'))), sourcepos='`1 124:10-124:45', target=10)
            if supportcode.eq_bits_bv_bv(za, r_uint(0b0)):
                # inline pc=10
                # Assignment(result='zz40', sourcepos='`1 124:27-124:28', value=Var(name='zA'))
                zz40 = machine._reg_zA
                pc = 11
                continue
            # Assignment(result='zz40', sourcepos='`1 124:34-124:45', value=OperationExpr(args=[Var(name='zA')], name='zread_mem', typ=NamedType('%bv16')))
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
            # ConditionalJump(condition=Comparison(args=[Var(name='zC_ZERO'), Var(name='zop')], operation='@neq'), sourcepos='`1 127:4-127:10', target=18)
            if not (Enum_zarithmetic_op.zC_ZERO == zop):
                # inline pc=18
                # ConditionalJump(condition=Comparison(args=[Var(name='zC_ONE'), Var(name='zop')], operation='@neq'), sourcepos='`1 128:4-128:9', target=21)
                if not (Enum_zarithmetic_op.zC_ONE == zop):
                    # inline pc=21
                    # ConditionalJump(condition=Comparison(args=[Var(name='zC_MINUSONE'), Var(name='zop')], operation='@neq'), sourcepos='`1 129:4-129:14', target=24)
                    if not (Enum_zarithmetic_op.zC_MINUSONE == zop):
                        # inline pc=24
                        # ConditionalJump(condition=Comparison(args=[Var(name='zC_D'), Var(name='zop')], operation='@neq'), sourcepos='`1 130:4-130:7', target=27)
                        if not (Enum_zarithmetic_op.zC_D == zop):
                            # inline pc=27
                            # ConditionalJump(condition=Comparison(args=[Var(name='zC_A'), Var(name='zop')], operation='@neq'), sourcepos='`1 131:4-131:7', target=30)
                            if not (Enum_zarithmetic_op.zC_A == zop):
                                # inline pc=30
                                # ConditionalJump(condition=Comparison(args=[Var(name='zC_NOT_D'), Var(name='zop')], operation='@neq'), sourcepos='`1 132:4-132:11', target=37)
                                if not (Enum_zarithmetic_op.zC_NOT_D == zop):
                                    # inline pc=37
                                    # ConditionalJump(condition=Comparison(args=[Var(name='zC_NOT_A'), Var(name='zop')], operation='@neq'), sourcepos='`1 133:4-133:11', target=44)
                                    if not (Enum_zarithmetic_op.zC_NOT_A == zop):
                                        # inline pc=44
                                        # ConditionalJump(condition=Comparison(args=[Var(name='zC_NEG_D'), Var(name='zop')], operation='@neq'), sourcepos='`1 134:4-134:11', target=53)
                                        if not (Enum_zarithmetic_op.zC_NEG_D == zop):
                                            # inline pc=53
                                            # ConditionalJump(condition=Comparison(args=[Var(name='zC_NEG_A'), Var(name='zop')], operation='@neq'), sourcepos='`1 135:4-135:11', target=62)
                                            if not (Enum_zarithmetic_op.zC_NEG_A == zop):
                                                # inline pc=62
                                                # ConditionalJump(condition=Comparison(args=[Var(name='zC_D_ADD_1'), Var(name='zop')], operation='@neq'), sourcepos='`1 136:4-136:13', target=71)
                                                if not (Enum_zarithmetic_op.zC_D_ADD_1 == zop):
                                                    # inline pc=71
                                                    # ConditionalJump(condition=Comparison(args=[Var(name='zC_A_ADD_1'), Var(name='zop')], operation='@neq'), sourcepos='`1 137:4-137:13', target=80)
                                                    if not (Enum_zarithmetic_op.zC_A_ADD_1 == zop):
                                                        # inline pc=80
                                                        # ConditionalJump(condition=Comparison(args=[Var(name='zC_D_SUB_1'), Var(name='zop')], operation='@neq'), sourcepos='`1 138:4-138:13', target=89)
                                                        if not (Enum_zarithmetic_op.zC_D_SUB_1 == zop):
                                                            # inline pc=89
                                                            # ConditionalJump(condition=Comparison(args=[Var(name='zC_A_SUB_1'), Var(name='zop')], operation='@neq'), sourcepos='`1 139:4-139:13', target=98)
                                                            if not (Enum_zarithmetic_op.zC_A_SUB_1 == zop):
                                                                # inline pc=98
                                                                # ConditionalJump(condition=Comparison(args=[Var(name='zC_D_ADD_A'), Var(name='zop')], operation='@neq'), sourcepos='`1 140:4-140:13', target=107)
                                                                if not (Enum_zarithmetic_op.zC_D_ADD_A == zop):
                                                                    # inline pc=107
                                                                    # ConditionalJump(condition=Comparison(args=[Var(name='zC_D_SUB_A'), Var(name='zop')], operation='@neq'), sourcepos='`1 141:4-141:13', target=116)
                                                                    if not (Enum_zarithmetic_op.zC_D_SUB_A == zop):
                                                                        # inline pc=116
                                                                        # ConditionalJump(condition=Comparison(args=[Var(name='zC_A_SUB_D'), Var(name='zop')], operation='@neq'), sourcepos='`1 142:4-142:13', target=125)
                                                                        if not (Enum_zarithmetic_op.zC_A_SUB_D == zop):
                                                                            # inline pc=125
                                                                            # ConditionalJump(condition=Comparison(args=[Var(name='zC_D_AND_A'), Var(name='zop')], operation='@neq'), sourcepos='`1 143:4-143:13', target=134)
                                                                            if not (Enum_zarithmetic_op.zC_D_AND_A == zop):
                                                                                # inline pc=134
                                                                                # ConditionalJump(condition=Comparison(args=[Var(name='zC_D_OR_A'), Var(name='zop')], operation='@neq'), sourcepos='`1 144:4-144:12', target=143)
                                                                                if not (Enum_zarithmetic_op.zC_D_OR_A == zop):
                                                                                    # inline pc=143
                                                                                    # Exit(kind='match', sourcepos='`1 126:26-145:3')
                                                                                    raise TypeError
                                                                                    continue
                                                                                # zz45: NamedType('%bv')
                                                                                # Assignment(result='zz45', sourcepos='`1 144:16-144:21', value=Var(name='zz40'))
                                                                                zz45 = bitvector.from_ruint(16, zz40)
                                                                                # Assignment(result='zz43', sourcepos='`1 144:16-144:21', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), Var(name='zz45')], name='zor_vec', typ=NamedType('%bv')))
                                                                                zz43 = supportcode.or_bits(machine, bitvector.from_ruint(16, zz41), zz45).touint()
                                                                                pc = 144
                                                                                continue
                                                                            # zz48: NamedType('%bv')
                                                                            # Assignment(result='zz48', sourcepos='`1 143:17-143:22', value=Var(name='zz40'))
                                                                            zz48 = bitvector.from_ruint(16, zz40)
                                                                            # Assignment(result='zz43', sourcepos='`1 143:17-143:22', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), Var(name='zz48')], name='zand_vec', typ=NamedType('%bv')))
                                                                            zz43 = supportcode.and_bits(machine, bitvector.from_ruint(16, zz41), zz48).touint()
                                                                            pc = 144
                                                                            continue
                                                                        # zz410: NamedType('%bv')
                                                                        # Assignment(result='zz410', sourcepos='`1 142:17-142:22', value=Var(name='zz40'))
                                                                        zz410 = bitvector.from_ruint(16, zz40)
                                                                        # Assignment(result='zz43', sourcepos='`1 142:17-142:22', value=OperationExpr(args=[Var(name='zz410'), CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv'))], name='zsub_vec', typ=NamedType('%bv')))
                                                                        zz43 = supportcode.sub_bits(machine, zz410, bitvector.from_ruint(16, zz41)).touint()
                                                                        pc = 144
                                                                        continue
                                                                    # zz414: NamedType('%bv')
                                                                    # Assignment(result='zz414', sourcepos='`1 141:17-141:22', value=Var(name='zz40'))
                                                                    zz414 = bitvector.from_ruint(16, zz40)
                                                                    # Assignment(result='zz43', sourcepos='`1 141:17-141:22', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), Var(name='zz414')], name='zsub_vec', typ=NamedType('%bv')))
                                                                    zz43 = supportcode.sub_bits(machine, bitvector.from_ruint(16, zz41), zz414).touint()
                                                                    pc = 144
                                                                    continue
                                                                # zz417: NamedType('%bv')
                                                                # Assignment(result='zz417', sourcepos='`1 140:17-140:22', value=Var(name='zz40'))
                                                                zz417 = bitvector.from_ruint(16, zz40)
                                                                # Assignment(result='zz43', sourcepos='`1 140:17-140:22', value=OperationExpr(args=[CastExpr(expr=Var(name='zz41'), typ=NamedType('%bv')), Var(name='zz417')], name='zadd_bits', typ=NamedType('%bv')))
                                                                zz43 = supportcode.add_bits(machine, bitvector.from_ruint(16, zz41), zz417).touint()
                                                                pc = 144
                                                                continue
                                                            # zz419: NamedType('%bv')
                                                            # Assignment(result='zz419', sourcepos='`1 139:17-139:27', value=Var(name='zz40'))
                                                            zz419 = bitvector.from_ruint(16, zz40)
                                                            # Assignment(result='zz43', sourcepos='`1 139:17-139:27', value=OperationExpr(args=[Var(name='zz419'), CastExpr(expr=BitVectorConstant(constant='0x0001'), typ=NamedType('%bv'))], name='zsub_vec', typ=NamedType('%bv')))
                                                            zz43 = supportcode.sub_bits(machine, zz419, bitvectorconstant0x0001_1).touint()
                                                            pc = 144
                                                            continue
                                                        # Assignment(result='zz43', sourcepos='`1 138:17-138:27', value=OperationExpr(args=[Var(name='zz41'), BitVectorConstant(constant='0x0001')], name='@sub_bits_bv_bv', typ=NamedType('%bv16')))
                                                        zz43 = supportcode.sub_bits_bv_bv(zz41, r_uint(0x0001))
                                                        pc = 144
                                                        continue
                                                    # zz425: NamedType('%bv')
                                                    # Assignment(result='zz425', sourcepos='`1 137:17-137:27', value=Var(name='zz40'))
                                                    zz425 = bitvector.from_ruint(16, zz40)
                                                    # Assignment(result='zz43', sourcepos='`1 137:17-137:27', value=OperationExpr(args=[Var(name='zz425'), CastExpr(expr=BitVectorConstant(constant='0x0001'), typ=NamedType('%bv'))], name='zadd_bits', typ=NamedType('%bv')))
                                                    zz43 = supportcode.add_bits(machine, zz425, bitvectorconstant0x0001_1).touint()
                                                    pc = 144
                                                    continue
                                                # Assignment(result='zz43', sourcepos='`1 136:17-136:27', value=OperationExpr(args=[Var(name='zz41'), BitVectorConstant(constant='0x0001')], name='@add_bits_bv_bv', typ=NamedType('%bv16')))
                                                zz43 = supportcode.add_bits_bv_bv(zz41, r_uint(0x0001))
                                                pc = 144
                                                continue
                                            # zz432: NamedType('%bv')
                                            # Assignment(result='zz432', sourcepos='`1 135:15-135:23', value=Var(name='zz40'))
                                            zz432 = bitvector.from_ruint(16, zz40)
                                            # Assignment(result='zz43', sourcepos='`1 135:15-135:23', value=OperationExpr(args=[CastExpr(expr=BitVectorConstant(constant='0x0000'), typ=NamedType('%bv')), Var(name='zz432')], name='zsub_vec', typ=NamedType('%bv')))
                                            zz43 = supportcode.sub_bits(machine, bitvectorconstant0x0000_1, zz432).touint()
                                            pc = 144
                                            continue
                                        # Assignment(result='zz43', sourcepos='`1 134:15-134:23', value=OperationExpr(args=[BitVectorConstant(constant='0x0000'), Var(name='zz41')], name='@sub_bits_bv_bv', typ=NamedType('%bv16')))
                                        zz43 = supportcode.sub_bits_bv_bv(r_uint(0x0000), zz41)
                                        pc = 144
                                        continue
                                    # zz437: NamedType('%bv')
                                    # Assignment(result='zz437', sourcepos='`1 133:15-133:25', value=Var(name='zz40'))
                                    zz437 = bitvector.from_ruint(16, zz40)
                                    # Assignment(result='zz43', sourcepos='`1 133:15-133:25', value=OperationExpr(args=[Var(name='zz437')], name='znot_vec', typ=NamedType('%bv')))
                                    zz43 = supportcode.not_bits(machine, zz437).touint()
                                    pc = 144
                                    continue
                                # Assignment(result='zz43', sourcepos='`1 132:15-132:25', value=OperationExpr(args=[Var(name='zz41'), Number(number=16)], name='@not_vec_bv', typ=NamedType('%bv16')))
                                zz43 = supportcode.not_vec_bv(zz41, 16)
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
            # LocalVarDeclaration(name='zz44', sourcepos='`1 150:4-150:38', typ=NamedType('%unit'), value=None)
            # zz44: NamedType('%unit')
            zz44 = ()
            # ConditionalJump(condition=ExprCondition(expr=CastExpr(expr=FieldAccess(element='ztuplez3z5bool_z5bool_z5bool2', obj=Var(name='zgsz381')), typ=NamedType('%bool'))), sourcepos='`1 150:4-150:38', target=10)
            if zgsz381.ztuplez3z5bool_z5bool_z5bool2:
                # inline pc=10
                # Assignment(result='zz44', sourcepos='`1 150:16-150:35', value=OperationExpr(args=[Var(name='zA'), Var(name='zvalue')], name='zwrite_mem', typ=NamedType('%unit')))
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
            # ConditionalJump(condition=ExprCondition(expr=Var(name='zz40')), sourcepos='`1 151:4-151:28', target=15)
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
            # ConditionalJump(condition=ExprCondition(expr=Var(name='zz41')), sourcepos='`1 152:4-152:28', target=20)
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
            # ConditionalJump(condition=Comparison(args=[Var(name='zJDONT'), Var(name='zj')], operation='@neq'), sourcepos='`1 157:6-157:11', target=5)
            if not (Enum_zjump.zJDONT == zj):
                # inline pc=5
                # ConditionalJump(condition=Comparison(args=[Var(name='zJGT'), Var(name='zj')], operation='@neq'), sourcepos='`1 158:6-158:9', target=18)
                if not (Enum_zjump.zJGT == zj):
                    # inline pc=18
                    # ConditionalJump(condition=Comparison(args=[Var(name='zJEQ'), Var(name='zj')], operation='@neq'), sourcepos='`1 159:6-159:9', target=31)
                    if not (Enum_zjump.zJEQ == zj):
                        # inline pc=31
                        # ConditionalJump(condition=Comparison(args=[Var(name='zJGE'), Var(name='zj')], operation='@neq'), sourcepos='`1 160:6-160:9', target=44)
                        if not (Enum_zjump.zJGE == zj):
                            # inline pc=44
                            # ConditionalJump(condition=Comparison(args=[Var(name='zJLT'), Var(name='zj')], operation='@neq'), sourcepos='`1 161:6-161:9', target=57)
                            if not (Enum_zjump.zJLT == zj):
                                # inline pc=57
                                # ConditionalJump(condition=Comparison(args=[Var(name='zJNE'), Var(name='zj')], operation='@neq'), sourcepos='`1 162:6-162:9', target=70)
                                if not (Enum_zjump.zJNE == zj):
                                    # inline pc=70
                                    # ConditionalJump(condition=Comparison(args=[Var(name='zJLE'), Var(name='zj')], operation='@neq'), sourcepos='`1 163:6-163:9', target=83)
                                    if not (Enum_zjump.zJLE == zj):
                                        # inline pc=83
                                        # ConditionalJump(condition=Comparison(args=[Var(name='zJMP'), Var(name='zj')], operation='@neq'), sourcepos='`1 164:6-164:9', target=86)
                                        if not (Enum_zjump.zJMP == zj):
                                            # inline pc=86
                                            # Exit(kind='match', sourcepos='`1 156:18-165:5')
                                            raise TypeError
                                            continue
                                        # Assignment(result='zz44', sourcepos='`1 164:15-164:19', value=Var(name='true'))
                                        zz44 = True
                                        pc = 87
                                        continue
                                    # Assignment(result='zz44', sourcepos=None, value=OperationExpr(args=[CastExpr(expr=OperationExpr(args=[Var(name='zvalue'), Number(number=16)], name='@signed_bv', typ=NamedType('%i64')), typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zlteq_int', typ=NamedType('%bool')))
                                    zz44 = supportcode.lteq(machine, Integer.fromint(supportcode.signed_bv(zvalue, 16)), smallintconst0_1)
                                    pc = 87
                                    continue
                                # Assignment(result='zz44', sourcepos=None, value=OperationExpr(args=[CastExpr(expr=OperationExpr(args=[Var(name='zvalue'), Number(number=16)], name='@signed_bv', typ=NamedType('%i64')), typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zneq_int', typ=NamedType('%bool')))
                                zz44 = func_zneq_int(machine, Integer.fromint(supportcode.signed_bv(zvalue, 16)), smallintconst0_1)
                                pc = 87
                                continue
                            # Assignment(result='zz44', sourcepos=None, value=OperationExpr(args=[CastExpr(expr=OperationExpr(args=[Var(name='zvalue'), Number(number=16)], name='@signed_bv', typ=NamedType('%i64')), typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zlt_int', typ=NamedType('%bool')))
                            zz44 = supportcode.lt(machine, Integer.fromint(supportcode.signed_bv(zvalue, 16)), smallintconst0_1)
                            pc = 87
                            continue
                        # Assignment(result='zz44', sourcepos=None, value=OperationExpr(args=[CastExpr(expr=OperationExpr(args=[Var(name='zvalue'), Number(number=16)], name='@signed_bv', typ=NamedType('%i64')), typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zgteq_int', typ=NamedType('%bool')))
                        zz44 = supportcode.gteq(machine, Integer.fromint(supportcode.signed_bv(zvalue, 16)), smallintconst0_1)
                        pc = 87
                        continue
                    # Assignment(result='zz44', sourcepos=None, value=OperationExpr(args=[OperationExpr(args=[CastExpr(expr=OperationExpr(args=[Var(name='zvalue'), Number(number=16)], name='@signed_bv', typ=NamedType('%i64')), typ=NamedType('%i'))], name='zz5izDzKz5i64', typ=NamedType('%i64')), Number(number=0)], name='@eq_int_i_i', typ=NamedType('%bool')))
                    zz44 = supportcode.eq_int_i_i(supportcode.int_to_int64(machine, Integer.fromint(supportcode.signed_bv(zvalue, 16))), 0)
                    pc = 87
                    continue
                # Assignment(result='zz44', sourcepos=None, value=OperationExpr(args=[CastExpr(expr=OperationExpr(args=[Var(name='zvalue'), Number(number=16)], name='@signed_bv', typ=NamedType('%i64')), typ=NamedType('%i')), OperationExpr(args=[Number(number=0)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zgt_int', typ=NamedType('%bool')))
                zz44 = supportcode.gt(machine, Integer.fromint(supportcode.signed_bv(zvalue, 16)), smallintconst0_1)
                pc = 87
                continue
            # Assignment(result='zz44', sourcepos='`1 157:15-157:20', value=Var(name='false'))
            zz44 = False
            pc = 87
        if pc == 87:
            # Assignment(result='zz40', sourcepos='`1 156:18-165:5', value=Var(name='zz44'))
            zz40 = zz44
            # ConditionalJump(condition=ExprCondition(expr=Var(name='zz40')), sourcepos='`1 166:4-166:46', target=98)
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
            # Assignment(result='zPC', sourcepos='`1 166:38-166:44', value=OperationExpr(args=[Var(name='zz42'), OperationExpr(args=[Number(number=1)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zadd_bits_int', typ=NamedType('%bv')))
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
            # Assignment(result='zA', sourcepos='`1 103:6-103:7', value=Cast(expr=Var(name='zmergez3var'), variant='zAINST'))
            machine._reg_zA = Union_zinstr_zAINST.convert(zmergez3var)
            # zz411: NamedType('%unit')
            # Assignment(result='zz411', sourcepos='`1 103:2-103:7', value=Unit())
            zz411 = ()
            # Assignment(result='zPC', sourcepos='`1 103:14-103:20', value=OperationExpr(args=[CastExpr(expr=Var(name='zPC'), typ=NamedType('%bv')), OperationExpr(args=[Number(number=1)], name='zz5i64zDzKz5i', typ=NamedType('%i'))], name='zadd_bits_int', typ=NamedType('%bv')))
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
            # zz45: NamedType('%bv16')
            # Assignment(result='zz45', sourcepos=None, value=OperationExpr(args=[CastExpr(expr=FieldAccess(element='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')), typ=NamedType('%bv1')), CastExpr(expr=FieldAccess(element='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')), typ=EnumType(name='zarithmetic_op'))], name='zcompute_value', typ=NamedType('%bv16')))
            zz45 = func_zcompute_value(machine, Union_zinstr_zCINST.convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0(zmergez3var), Union_zinstr_zCINST.convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1(zmergez3var))
            # zz46: NamedType('%unit')
            # Assignment(result='zz46', sourcepos=None, value=OperationExpr(args=[CastExpr(expr=FieldAccess(element='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')), typ=StructType(name='ztuplez3z5bool_z5bool_z5bool')), Var(name='zz45')], name='zassign_dest', typ=NamedType('%unit')))
            zz46 = func_zassign_dest(machine, Union_zinstr_zCINST.convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2(zmergez3var), zz45)
            # Assignment(result='zz40', sourcepos=None, value=OperationExpr(args=[Var(name='zz45'), CastExpr(expr=FieldAccess(element='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')), typ=EnumType(name='zjump'))], name='zmaybe_jump', typ=NamedType('%unit')))
            zz40 = func_zmaybe_jump(machine, zz45, Union_zinstr_zCINST.convert_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3(zmergez3var))
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
            # Assignment(result='zz40', sourcepos='`1 179:27-179:39', value=OperationExpr(args=[Var(name='zPC')], name='zread_rom', typ=NamedType('%bv16')))
            zz40 = supportcode.my_read_rom(machine, machine._reg_zPC)
            # zz41: UnionType(name='zoptionzIUinstrzIzKzK')
            # Assignment(result='zz41', sourcepos='`1 180:12-180:25', value=OperationExpr(args=[Var(name='zz40')], name='zdecode', typ=UnionType(name='zoptionzIUinstrzIzKzK')))
            zz41 = func_zdecode(machine, zz40)
            # zz42: NamedType('%bool')
            # Assignment(result='zz42', sourcepos='`1 181:18-181:23', value=Var(name='false'))
            zz42 = False
            # LocalVarDeclaration(name='zz43', sourcepos='`1 182:4-185:5', typ=NamedType('%unit'), value=None)
            # zz43: NamedType('%unit')
            zz43 = ()
            # ConditionalJump(condition=UnionVariantCheck(var=Var(name='zz41'), variant='zSomezIUinstrzIzKzK'), sourcepos='`1 183:8-183:19', target=15)
            if not isinstance(zz41, Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK):
                # inline pc=15
                # ConditionalJump(condition=UnionVariantCheck(var=Var(name='zz41'), variant='zNonezIUinstrzIzKzK'), sourcepos='`1 184:8-184:14', target=19)
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
            # Assignment(result='zz46', sourcepos=None, value=OperationExpr(args=[CastExpr(expr=Cast(expr=Var(name='zz41'), variant='zSomezIUinstrzIzKzK'), typ=UnionType(name='zinstr'))], name='zexecute', typ=NamedType('%unit')))
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
            # ConditionalJump(condition=Comparison(args=[Var(name='zz42')], operation='@not'), sourcepos='`1 194:4-205:5', target=54)
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
            # ConditionalJump(condition=ExprCondition(expr=Var(name='zdebug')), sourcepos='`1 196:8-198:9', target=15)
            if zdebug:
                # inline pc=15
                # Assignment(result='zz418', sourcepos='`1 197:12-197:46', value=OperationExpr(args=[Var(name='zz40'), Var(name='zPC'), Var(name='zA'), Var(name='zD')], name='zprint_debug', typ=NamedType('%unit')))
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
            # ConditionalJump(condition=ExprCondition(expr=OperationExpr(args=[Unit()], name='zfetch_decode_execute', typ=NamedType('%bool'))), sourcepos='`1 199:8-203:9', target=22)
            if func_zfetch_decode_execute(machine, ()):
                # inline pc=22
                # zz416: NamedType('%bv')
                # Assignment(result='zz416', sourcepos='`1 200:15-200:34', value=Var(name='zz40'))
                zz416 = bitvector.from_ruint(64, zz40)
                # ConditionalJump(condition=ExprCondition(expr=OperationExpr(args=[OperationExpr(args=[Var(name='zz416')], name='zsigned', typ=NamedType('%i')), CastExpr(expr=OperationExpr(args=[Var(name='zlimit'), Number(number=64)], name='@signed_bv', typ=NamedType('%i64')), typ=NamedType('%i'))], name='zlt_int', typ=NamedType('%bool'))), sourcepos='`1 200:12-202:13', target=43)
                if supportcode.lt(machine, supportcode.sail_signed(machine, zz416), Integer.fromint(supportcode.signed_bv(zlimit, 64))):
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
            # Assignment(result='zz40', sourcepos='`1 204:22-204:54', value=OperationExpr(args=[Var(name='zz44'), CastExpr(expr=BitVectorConstant(constant='0x0000000000000001'), typ=NamedType('%bv'))], name='zadd_bits', typ=NamedType('%bv')))
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
    # Assignment(result='return', sourcepos='`1 212:4-212:21', value=OperationExpr(args=[Var(name='zlimit'), Var(name='zdebug')], name='zrun', typ=NamedType('%unit')))
    return_ = func_zrun(machine, zlimit, zdebug)
    # End()
    return return_




def func_zmain(machine, zgsz3120):
    # zz40: NamedType('%unit')
    # Assignment(result='zz40', sourcepos='`1 218:27-218:60', value=OperationExpr(args=[BitVectorConstant(constant='0x0000000000000010'), Var(name='false')], name='zmymain', typ=NamedType('%unit')))
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
