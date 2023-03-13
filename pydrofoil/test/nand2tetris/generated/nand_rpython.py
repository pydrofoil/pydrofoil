from rpython.rlib import jit
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
        if (self.utup0 != other.utup0): return False # NamedType('%i64')
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
    a = Struct_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump(r_uint(0), -1, Struct_ztuplez3z5bool_z5bool_z5bool(False, False, False), -1)
    def __init__(self, a):
        self.a = a # StructType(name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump')
    @objectmodel.always_inline
    def eq(self, other):
        if type(self) is not type(other): return False
        if not (self.a.eq(other.a)): return False # StructType(name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump')
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zinstr_zCINST):
            return inst.a
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

class Tuple_17(supportcode.ObjectBase): # TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op')])
    @objectmodel.always_inline
    def eq(self, other):
        assert isinstance(other, Tuple_17)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv1')
        if not (self.utup1 == other.utup1): return False # EnumType(name='zarithmetic_op')
        return True

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
            # LocalVarDeclaration(name='zz42', sourcepos='`1 13:27-16:1', typ=NamedType('%bool'), value=None)
            # zz42: NamedType('%bool')
            zz42 = False
            # zz43: NamedType('%bv')
            # Assignment(result='zz43', sourcepos='`1 14:2-14:5', value=Var(name='zz41'))
            zz43 = bitvector.from_ruint(1, zz41)
            # zz44: NamedType('%bv')
            # Assignment(result='zz44', sourcepos='`1 14:2-14:5', value=BitVectorConstant(constant='0b1'))
            zz44 = bitvector.from_ruint(1, r_uint(0b1))
            # Operation(args=[Var(name='zz43'), Var(name='zz44')], name='zeq_bits', result='zz42', sourcepos='`1 14:2-14:5')
            zz42 = supportcode.eq_bits(machine, zz43, zz44)
            if not zz42:
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
            # LocalVarDeclaration(name='zz470', sourcepos='`2', typ=NamedType('%bool'), value=None)
            # zz470: NamedType('%bool')
            zz470 = False
            # zz471: NamedType('%bv')
            # Assignment(result='zz471', sourcepos='`1 56:19-56:27', value=Var(name='zz469'))
            zz471 = bitvector.from_ruint(6, zz469)
            # zz472: NamedType('%bv')
            # Assignment(result='zz472', sourcepos='`1 56:19-56:27', value=BitVectorConstant(constant='0b101010'))
            zz472 = bitvector.from_ruint(6, r_uint(0b101010))
            # Operation(args=[Var(name='zz471'), Var(name='zz472')], name='zeq_bits', result='zz470', sourcepos='`1 56:19-56:27')
            zz470 = supportcode.eq_bits(machine, zz471, zz472)
            if not zz470:
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
            # LocalVarDeclaration(name='zz466', sourcepos='`4', typ=NamedType('%bool'), value=None)
            # zz466: NamedType('%bool')
            zz466 = False
            # zz467: NamedType('%bv')
            # Assignment(result='zz467', sourcepos='`1 57:19-57:27', value=Var(name='zz465'))
            zz467 = bitvector.from_ruint(6, zz465)
            # zz468: NamedType('%bv')
            # Assignment(result='zz468', sourcepos='`1 57:19-57:27', value=BitVectorConstant(constant='0b111111'))
            zz468 = bitvector.from_ruint(6, r_uint(0b111111))
            # Operation(args=[Var(name='zz467'), Var(name='zz468')], name='zeq_bits', result='zz466', sourcepos='`1 57:19-57:27')
            zz466 = supportcode.eq_bits(machine, zz467, zz468)
            if not zz466:
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
            # LocalVarDeclaration(name='zz462', sourcepos='`6', typ=NamedType('%bool'), value=None)
            # zz462: NamedType('%bool')
            zz462 = False
            # zz463: NamedType('%bv')
            # Assignment(result='zz463', sourcepos='`1 58:19-58:27', value=Var(name='zz461'))
            zz463 = bitvector.from_ruint(6, zz461)
            # zz464: NamedType('%bv')
            # Assignment(result='zz464', sourcepos='`1 58:19-58:27', value=BitVectorConstant(constant='0b111010'))
            zz464 = bitvector.from_ruint(6, r_uint(0b111010))
            # Operation(args=[Var(name='zz463'), Var(name='zz464')], name='zeq_bits', result='zz462', sourcepos='`1 58:19-58:27')
            zz462 = supportcode.eq_bits(machine, zz463, zz464)
            if not zz462:
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
            # LocalVarDeclaration(name='zz458', sourcepos='`8', typ=NamedType('%bool'), value=None)
            # zz458: NamedType('%bool')
            zz458 = False
            # zz459: NamedType('%bv')
            # Assignment(result='zz459', sourcepos='`1 59:19-59:27', value=Var(name='zz457'))
            zz459 = bitvector.from_ruint(6, zz457)
            # zz460: NamedType('%bv')
            # Assignment(result='zz460', sourcepos='`1 59:19-59:27', value=BitVectorConstant(constant='0b001100'))
            zz460 = bitvector.from_ruint(6, r_uint(0b001100))
            # Operation(args=[Var(name='zz459'), Var(name='zz460')], name='zeq_bits', result='zz458', sourcepos='`1 59:19-59:27')
            zz458 = supportcode.eq_bits(machine, zz459, zz460)
            if not zz458:
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
            # LocalVarDeclaration(name='zz454', sourcepos='`10', typ=NamedType('%bool'), value=None)
            # zz454: NamedType('%bool')
            zz454 = False
            # zz455: NamedType('%bv')
            # Assignment(result='zz455', sourcepos='`1 60:19-60:27', value=Var(name='zz453'))
            zz455 = bitvector.from_ruint(6, zz453)
            # zz456: NamedType('%bv')
            # Assignment(result='zz456', sourcepos='`1 60:19-60:27', value=BitVectorConstant(constant='0b110000'))
            zz456 = bitvector.from_ruint(6, r_uint(0b110000))
            # Operation(args=[Var(name='zz455'), Var(name='zz456')], name='zeq_bits', result='zz454', sourcepos='`1 60:19-60:27')
            zz454 = supportcode.eq_bits(machine, zz455, zz456)
            if not zz454:
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
            # LocalVarDeclaration(name='zz450', sourcepos='`12', typ=NamedType('%bool'), value=None)
            # zz450: NamedType('%bool')
            zz450 = False
            # zz451: NamedType('%bv')
            # Assignment(result='zz451', sourcepos='`1 61:19-61:27', value=Var(name='zz449'))
            zz451 = bitvector.from_ruint(6, zz449)
            # zz452: NamedType('%bv')
            # Assignment(result='zz452', sourcepos='`1 61:19-61:27', value=BitVectorConstant(constant='0b001101'))
            zz452 = bitvector.from_ruint(6, r_uint(0b001101))
            # Operation(args=[Var(name='zz451'), Var(name='zz452')], name='zeq_bits', result='zz450', sourcepos='`1 61:19-61:27')
            zz450 = supportcode.eq_bits(machine, zz451, zz452)
            if not zz450:
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
            # LocalVarDeclaration(name='zz446', sourcepos='`14', typ=NamedType('%bool'), value=None)
            # zz446: NamedType('%bool')
            zz446 = False
            # zz447: NamedType('%bv')
            # Assignment(result='zz447', sourcepos='`1 62:19-62:27', value=Var(name='zz445'))
            zz447 = bitvector.from_ruint(6, zz445)
            # zz448: NamedType('%bv')
            # Assignment(result='zz448', sourcepos='`1 62:19-62:27', value=BitVectorConstant(constant='0b110001'))
            zz448 = bitvector.from_ruint(6, r_uint(0b110001))
            # Operation(args=[Var(name='zz447'), Var(name='zz448')], name='zeq_bits', result='zz446', sourcepos='`1 62:19-62:27')
            zz446 = supportcode.eq_bits(machine, zz447, zz448)
            if not zz446:
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
            # LocalVarDeclaration(name='zz442', sourcepos='`16', typ=NamedType('%bool'), value=None)
            # zz442: NamedType('%bool')
            zz442 = False
            # zz443: NamedType('%bv')
            # Assignment(result='zz443', sourcepos='`1 63:19-63:27', value=Var(name='zz441'))
            zz443 = bitvector.from_ruint(6, zz441)
            # zz444: NamedType('%bv')
            # Assignment(result='zz444', sourcepos='`1 63:19-63:27', value=BitVectorConstant(constant='0b001111'))
            zz444 = bitvector.from_ruint(6, r_uint(0b001111))
            # Operation(args=[Var(name='zz443'), Var(name='zz444')], name='zeq_bits', result='zz442', sourcepos='`1 63:19-63:27')
            zz442 = supportcode.eq_bits(machine, zz443, zz444)
            if not zz442:
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
            # LocalVarDeclaration(name='zz438', sourcepos='`18', typ=NamedType('%bool'), value=None)
            # zz438: NamedType('%bool')
            zz438 = False
            # zz439: NamedType('%bv')
            # Assignment(result='zz439', sourcepos='`1 64:19-64:27', value=Var(name='zz437'))
            zz439 = bitvector.from_ruint(6, zz437)
            # zz440: NamedType('%bv')
            # Assignment(result='zz440', sourcepos='`1 64:19-64:27', value=BitVectorConstant(constant='0b110011'))
            zz440 = bitvector.from_ruint(6, r_uint(0b110011))
            # Operation(args=[Var(name='zz439'), Var(name='zz440')], name='zeq_bits', result='zz438', sourcepos='`1 64:19-64:27')
            zz438 = supportcode.eq_bits(machine, zz439, zz440)
            if not zz438:
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
            # LocalVarDeclaration(name='zz434', sourcepos='`20', typ=NamedType('%bool'), value=None)
            # zz434: NamedType('%bool')
            zz434 = False
            # zz435: NamedType('%bv')
            # Assignment(result='zz435', sourcepos='`1 65:19-65:27', value=Var(name='zz433'))
            zz435 = bitvector.from_ruint(6, zz433)
            # zz436: NamedType('%bv')
            # Assignment(result='zz436', sourcepos='`1 65:19-65:27', value=BitVectorConstant(constant='0b011111'))
            zz436 = bitvector.from_ruint(6, r_uint(0b011111))
            # Operation(args=[Var(name='zz435'), Var(name='zz436')], name='zeq_bits', result='zz434', sourcepos='`1 65:19-65:27')
            zz434 = supportcode.eq_bits(machine, zz435, zz436)
            if not zz434:
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
            # LocalVarDeclaration(name='zz430', sourcepos='`22', typ=NamedType('%bool'), value=None)
            # zz430: NamedType('%bool')
            zz430 = False
            # zz431: NamedType('%bv')
            # Assignment(result='zz431', sourcepos='`1 66:19-66:27', value=Var(name='zz429'))
            zz431 = bitvector.from_ruint(6, zz429)
            # zz432: NamedType('%bv')
            # Assignment(result='zz432', sourcepos='`1 66:19-66:27', value=BitVectorConstant(constant='0b110111'))
            zz432 = bitvector.from_ruint(6, r_uint(0b110111))
            # Operation(args=[Var(name='zz431'), Var(name='zz432')], name='zeq_bits', result='zz430', sourcepos='`1 66:19-66:27')
            zz430 = supportcode.eq_bits(machine, zz431, zz432)
            if not zz430:
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
            # LocalVarDeclaration(name='zz426', sourcepos='`24', typ=NamedType('%bool'), value=None)
            # zz426: NamedType('%bool')
            zz426 = False
            # zz427: NamedType('%bv')
            # Assignment(result='zz427', sourcepos='`1 67:19-67:27', value=Var(name='zz425'))
            zz427 = bitvector.from_ruint(6, zz425)
            # zz428: NamedType('%bv')
            # Assignment(result='zz428', sourcepos='`1 67:19-67:27', value=BitVectorConstant(constant='0b001110'))
            zz428 = bitvector.from_ruint(6, r_uint(0b001110))
            # Operation(args=[Var(name='zz427'), Var(name='zz428')], name='zeq_bits', result='zz426', sourcepos='`1 67:19-67:27')
            zz426 = supportcode.eq_bits(machine, zz427, zz428)
            if not zz426:
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
            # LocalVarDeclaration(name='zz422', sourcepos='`26', typ=NamedType('%bool'), value=None)
            # zz422: NamedType('%bool')
            zz422 = False
            # zz423: NamedType('%bv')
            # Assignment(result='zz423', sourcepos='`1 68:19-68:27', value=Var(name='zz421'))
            zz423 = bitvector.from_ruint(6, zz421)
            # zz424: NamedType('%bv')
            # Assignment(result='zz424', sourcepos='`1 68:19-68:27', value=BitVectorConstant(constant='0b110010'))
            zz424 = bitvector.from_ruint(6, r_uint(0b110010))
            # Operation(args=[Var(name='zz423'), Var(name='zz424')], name='zeq_bits', result='zz422', sourcepos='`1 68:19-68:27')
            zz422 = supportcode.eq_bits(machine, zz423, zz424)
            if not zz422:
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
            # LocalVarDeclaration(name='zz418', sourcepos='`28', typ=NamedType('%bool'), value=None)
            # zz418: NamedType('%bool')
            zz418 = False
            # zz419: NamedType('%bv')
            # Assignment(result='zz419', sourcepos='`1 69:19-69:27', value=Var(name='zz417'))
            zz419 = bitvector.from_ruint(6, zz417)
            # zz420: NamedType('%bv')
            # Assignment(result='zz420', sourcepos='`1 69:19-69:27', value=BitVectorConstant(constant='0b000010'))
            zz420 = bitvector.from_ruint(6, r_uint(0b000010))
            # Operation(args=[Var(name='zz419'), Var(name='zz420')], name='zeq_bits', result='zz418', sourcepos='`1 69:19-69:27')
            zz418 = supportcode.eq_bits(machine, zz419, zz420)
            if not zz418:
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
            # LocalVarDeclaration(name='zz414', sourcepos='`30', typ=NamedType('%bool'), value=None)
            # zz414: NamedType('%bool')
            zz414 = False
            # zz415: NamedType('%bv')
            # Assignment(result='zz415', sourcepos='`1 70:19-70:27', value=Var(name='zz413'))
            zz415 = bitvector.from_ruint(6, zz413)
            # zz416: NamedType('%bv')
            # Assignment(result='zz416', sourcepos='`1 70:19-70:27', value=BitVectorConstant(constant='0b010011'))
            zz416 = bitvector.from_ruint(6, r_uint(0b010011))
            # Operation(args=[Var(name='zz415'), Var(name='zz416')], name='zeq_bits', result='zz414', sourcepos='`1 70:19-70:27')
            zz414 = supportcode.eq_bits(machine, zz415, zz416)
            if not zz414:
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
            # LocalVarDeclaration(name='zz410', sourcepos='`32', typ=NamedType('%bool'), value=None)
            # zz410: NamedType('%bool')
            zz410 = False
            # zz411: NamedType('%bv')
            # Assignment(result='zz411', sourcepos='`1 71:19-71:27', value=Var(name='zz49'))
            zz411 = bitvector.from_ruint(6, zz49)
            # zz412: NamedType('%bv')
            # Assignment(result='zz412', sourcepos='`1 71:19-71:27', value=BitVectorConstant(constant='0b000111'))
            zz412 = bitvector.from_ruint(6, r_uint(0b000111))
            # Operation(args=[Var(name='zz411'), Var(name='zz412')], name='zeq_bits', result='zz410', sourcepos='`1 71:19-71:27')
            zz410 = supportcode.eq_bits(machine, zz411, zz412)
            if not zz410:
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
            # LocalVarDeclaration(name='zz46', sourcepos='`34', typ=NamedType('%bool'), value=None)
            # zz46: NamedType('%bool')
            zz46 = False
            # zz47: NamedType('%bv')
            # Assignment(result='zz47', sourcepos='`1 72:19-72:27', value=Var(name='zz45'))
            zz47 = bitvector.from_ruint(6, zz45)
            # zz48: NamedType('%bv')
            # Assignment(result='zz48', sourcepos='`1 72:19-72:27', value=BitVectorConstant(constant='0b000000'))
            zz48 = bitvector.from_ruint(6, r_uint(0b000000))
            # Operation(args=[Var(name='zz47'), Var(name='zz48')], name='zeq_bits', result='zz46', sourcepos='`1 72:19-72:27')
            zz46 = supportcode.eq_bits(machine, zz47, zz48)
            if not zz46:
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
            # LocalVarDeclaration(name='zz42', sourcepos='`36', typ=NamedType('%bool'), value=None)
            # zz42: NamedType('%bool')
            zz42 = False
            # zz43: NamedType('%bv')
            # Assignment(result='zz43', sourcepos='`1 73:19-73:27', value=Var(name='zz41'))
            zz43 = bitvector.from_ruint(6, zz41)
            # zz44: NamedType('%bv')
            # Assignment(result='zz44', sourcepos='`1 73:19-73:27', value=BitVectorConstant(constant='0b010101'))
            zz44 = bitvector.from_ruint(6, r_uint(0b010101))
            # Operation(args=[Var(name='zz43'), Var(name='zz44')], name='zeq_bits', result='zz42', sourcepos='`1 73:19-73:27')
            zz42 = supportcode.eq_bits(machine, zz43, zz44)
            if not zz42:
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
            # LocalVarDeclaration(name='zz430', sourcepos='`41', typ=NamedType('%bool'), value=None)
            # zz430: NamedType('%bool')
            zz430 = False
            # zz431: NamedType('%bv')
            # Assignment(result='zz431', sourcepos='`1 79:13-79:18', value=Var(name='zz429'))
            zz431 = bitvector.from_ruint(3, zz429)
            # zz432: NamedType('%bv')
            # Assignment(result='zz432', sourcepos='`1 79:13-79:18', value=BitVectorConstant(constant='0b000'))
            zz432 = bitvector.from_ruint(3, r_uint(0b000))
            # Operation(args=[Var(name='zz431'), Var(name='zz432')], name='zeq_bits', result='zz430', sourcepos='`1 79:13-79:18')
            zz430 = supportcode.eq_bits(machine, zz431, zz432)
            if not zz430:
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
            # LocalVarDeclaration(name='zz426', sourcepos='`43', typ=NamedType('%bool'), value=None)
            # zz426: NamedType('%bool')
            zz426 = False
            # zz427: NamedType('%bv')
            # Assignment(result='zz427', sourcepos='`1 80:13-80:18', value=Var(name='zz425'))
            zz427 = bitvector.from_ruint(3, zz425)
            # zz428: NamedType('%bv')
            # Assignment(result='zz428', sourcepos='`1 80:13-80:18', value=BitVectorConstant(constant='0b001'))
            zz428 = bitvector.from_ruint(3, r_uint(0b001))
            # Operation(args=[Var(name='zz427'), Var(name='zz428')], name='zeq_bits', result='zz426', sourcepos='`1 80:13-80:18')
            zz426 = supportcode.eq_bits(machine, zz427, zz428)
            if not zz426:
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
            # LocalVarDeclaration(name='zz422', sourcepos='`45', typ=NamedType('%bool'), value=None)
            # zz422: NamedType('%bool')
            zz422 = False
            # zz423: NamedType('%bv')
            # Assignment(result='zz423', sourcepos='`1 81:13-81:18', value=Var(name='zz421'))
            zz423 = bitvector.from_ruint(3, zz421)
            # zz424: NamedType('%bv')
            # Assignment(result='zz424', sourcepos='`1 81:13-81:18', value=BitVectorConstant(constant='0b010'))
            zz424 = bitvector.from_ruint(3, r_uint(0b010))
            # Operation(args=[Var(name='zz423'), Var(name='zz424')], name='zeq_bits', result='zz422', sourcepos='`1 81:13-81:18')
            zz422 = supportcode.eq_bits(machine, zz423, zz424)
            if not zz422:
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
            # LocalVarDeclaration(name='zz418', sourcepos='`47', typ=NamedType('%bool'), value=None)
            # zz418: NamedType('%bool')
            zz418 = False
            # zz419: NamedType('%bv')
            # Assignment(result='zz419', sourcepos='`1 82:13-82:18', value=Var(name='zz417'))
            zz419 = bitvector.from_ruint(3, zz417)
            # zz420: NamedType('%bv')
            # Assignment(result='zz420', sourcepos='`1 82:13-82:18', value=BitVectorConstant(constant='0b011'))
            zz420 = bitvector.from_ruint(3, r_uint(0b011))
            # Operation(args=[Var(name='zz419'), Var(name='zz420')], name='zeq_bits', result='zz418', sourcepos='`1 82:13-82:18')
            zz418 = supportcode.eq_bits(machine, zz419, zz420)
            if not zz418:
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
            # LocalVarDeclaration(name='zz414', sourcepos='`49', typ=NamedType('%bool'), value=None)
            # zz414: NamedType('%bool')
            zz414 = False
            # zz415: NamedType('%bv')
            # Assignment(result='zz415', sourcepos='`1 83:13-83:18', value=Var(name='zz413'))
            zz415 = bitvector.from_ruint(3, zz413)
            # zz416: NamedType('%bv')
            # Assignment(result='zz416', sourcepos='`1 83:13-83:18', value=BitVectorConstant(constant='0b100'))
            zz416 = bitvector.from_ruint(3, r_uint(0b100))
            # Operation(args=[Var(name='zz415'), Var(name='zz416')], name='zeq_bits', result='zz414', sourcepos='`1 83:13-83:18')
            zz414 = supportcode.eq_bits(machine, zz415, zz416)
            if not zz414:
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
            # LocalVarDeclaration(name='zz410', sourcepos='`51', typ=NamedType('%bool'), value=None)
            # zz410: NamedType('%bool')
            zz410 = False
            # zz411: NamedType('%bv')
            # Assignment(result='zz411', sourcepos='`1 84:13-84:18', value=Var(name='zz49'))
            zz411 = bitvector.from_ruint(3, zz49)
            # zz412: NamedType('%bv')
            # Assignment(result='zz412', sourcepos='`1 84:13-84:18', value=BitVectorConstant(constant='0b101'))
            zz412 = bitvector.from_ruint(3, r_uint(0b101))
            # Operation(args=[Var(name='zz411'), Var(name='zz412')], name='zeq_bits', result='zz410', sourcepos='`1 84:13-84:18')
            zz410 = supportcode.eq_bits(machine, zz411, zz412)
            if not zz410:
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
            # LocalVarDeclaration(name='zz46', sourcepos='`53', typ=NamedType('%bool'), value=None)
            # zz46: NamedType('%bool')
            zz46 = False
            # zz47: NamedType('%bv')
            # Assignment(result='zz47', sourcepos='`1 85:13-85:18', value=Var(name='zz45'))
            zz47 = bitvector.from_ruint(3, zz45)
            # zz48: NamedType('%bv')
            # Assignment(result='zz48', sourcepos='`1 85:13-85:18', value=BitVectorConstant(constant='0b110'))
            zz48 = bitvector.from_ruint(3, r_uint(0b110))
            # Operation(args=[Var(name='zz47'), Var(name='zz48')], name='zeq_bits', result='zz46', sourcepos='`1 85:13-85:18')
            zz46 = supportcode.eq_bits(machine, zz47, zz48)
            if not zz46:
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
            # LocalVarDeclaration(name='zz42', sourcepos='`55', typ=NamedType('%bool'), value=None)
            # zz42: NamedType('%bool')
            zz42 = False
            # zz43: NamedType('%bv')
            # Assignment(result='zz43', sourcepos='`1 86:13-86:18', value=Var(name='zz41'))
            zz43 = bitvector.from_ruint(3, zz41)
            # zz44: NamedType('%bv')
            # Assignment(result='zz44', sourcepos='`1 86:13-86:18', value=BitVectorConstant(constant='0b111'))
            zz44 = bitvector.from_ruint(3, r_uint(0b111))
            # Operation(args=[Var(name='zz43'), Var(name='zz44')], name='zeq_bits', result='zz42', sourcepos='`1 86:13-86:18')
            zz42 = supportcode.eq_bits(machine, zz43, zz44)
            if not zz42:
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
    zz421 = supportcode.int64_to_int(machine, 2)
    # zz422: NamedType('%i')
    # Operation(args=[Number(number=2)], name='zz5i64zDzKz5i', result='zz422', sourcepos='`1 112:8-112:9')
    zz422 = supportcode.int64_to_int(machine, 2)
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
    zz417 = supportcode.int64_to_int(machine, 0)
    # zz418: NamedType('%i')
    # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz418', sourcepos='`1 112:36-112:37')
    zz418 = supportcode.int64_to_int(machine, 0)
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
    zz413 = supportcode.int64_to_int(machine, 1)
    # zz414: NamedType('%i')
    # Operation(args=[Number(number=1)], name='zz5i64zDzKz5i', result='zz414', sourcepos='`1 112:22-112:23')
    zz414 = supportcode.int64_to_int(machine, 1)
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
    zz49 = supportcode.int64_to_int(machine, 2)
    # zz410: NamedType('%i')
    # Operation(args=[Number(number=2)], name='zz5i64zDzKz5i', result='zz410', sourcepos='`1 112:8-112:9')
    zz410 = supportcode.int64_to_int(machine, 2)
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
            # LocalVarDeclaration(name='zz436', sourcepos='`1 99:23-99:41', typ=NamedType('%bv1'), value=None)
            # zz436: NamedType('%bv1')
            zz436 = r_uint(0)
            # zz450: NamedType('%i')
            # Operation(args=[Number(number=15)], name='zz5i64zDzKz5i', result='zz450', sourcepos='`1 99:23-99:41')
            zz450 = supportcode.int64_to_int(machine, 15)
            # zz451: NamedType('%i')
            # Operation(args=[Number(number=15)], name='zz5i64zDzKz5i', result='zz451', sourcepos='`1 99:23-99:41')
            zz451 = supportcode.int64_to_int(machine, 15)
            # zz452: NamedType('%bv')
            # Assignment(result='zz452', sourcepos='`1 99:23-99:41', value=Var(name='zz435'))
            zz452 = bitvector.from_ruint(16, zz435)
            # zz453: NamedType('%bv')
            # Operation(args=[Var(name='zz452'), Var(name='zz450'), Var(name='zz451')], name='zsubrange_bits', result='zz453', sourcepos='`1 99:23-99:41')
            zz453 = supportcode.vector_subrange(machine, zz452, zz450, zz451)
            # Assignment(result='zz436', sourcepos='`1 99:23-99:41', value=Var(name='zz453'))
            zz436 = zz453.touint()
            # LocalVarDeclaration(name='zz437', sourcepos='`1 99:16-100:39', typ=NamedType('%bool'), value=None)
            # zz437: NamedType('%bool')
            zz437 = False
            # zz448: NamedType('%bv')
            # Assignment(result='zz448', sourcepos='`1 99:23-99:41', value=Var(name='zz436'))
            zz448 = bitvector.from_ruint(1, zz436)
            # zz449: NamedType('%bv')
            # Assignment(result='zz449', sourcepos='`1 99:23-99:41', value=BitVectorConstant(constant='0b0'))
            zz449 = bitvector.from_ruint(1, r_uint(0b0))
            # Operation(args=[Var(name='zz448'), Var(name='zz449')], name='zeq_bits', result='zz437', sourcepos='`1 99:23-99:41')
            zz437 = supportcode.eq_bits(machine, zz448, zz449)
            if not zz437:
                # inline pc=21
                pc = 44
                continue
            pc = 22
        if pc == 22:
            # LocalVarDeclaration(name='zz438', sourcepos='`1 100:3-100:39', typ=NamedType('%bv15'), value=None)
            # zz438: NamedType('%bv15')
            zz438 = r_uint(0)
            # zz444: NamedType('%i')
            # Operation(args=[Number(number=14)], name='zz5i64zDzKz5i', result='zz444', sourcepos='`1 99:29-99:30')
            zz444 = supportcode.int64_to_int(machine, 14)
            # zz445: NamedType('%i')
            # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz445', sourcepos='`1 99:29-99:30')
            zz445 = supportcode.int64_to_int(machine, 0)
            # zz446: NamedType('%bv')
            # Assignment(result='zz446', sourcepos='`1 99:29-99:30', value=Var(name='zz435'))
            zz446 = bitvector.from_ruint(16, zz435)
            # zz447: NamedType('%bv')
            # Operation(args=[Var(name='zz446'), Var(name='zz444'), Var(name='zz445')], name='zsubrange_bits', result='zz447', sourcepos='`1 99:29-99:30')
            zz447 = supportcode.vector_subrange(machine, zz446, zz444, zz445)
            # Assignment(result='zz438', sourcepos='`1 99:29-99:30', value=Var(name='zz447'))
            zz438 = zz447.touint()
            # LocalVarDeclaration(name='zz439', sourcepos='`1 100:3-100:39', typ=UnionType(name='zinstr'), value=None)
            # zz439: UnionType(name='zinstr')
            zz439 = Union_zinstr.singleton
            # LocalVarDeclaration(name='zz440', sourcepos='`1 100:8-100:38', typ=NamedType('%bv16'), value=None)
            # zz440: NamedType('%bv16')
            zz440 = r_uint(0)
            # zz441: NamedType('%i')
            # Operation(args=[Number(number=16)], name='zz5i64zDzKz5i', result='zz441', sourcepos='`1 100:14-100:37')
            zz441 = supportcode.int64_to_int(machine, 16)
            # zz442: NamedType('%bv')
            # Assignment(result='zz442', sourcepos='`1 100:14-100:37', value=Var(name='zz438'))
            zz442 = bitvector.from_ruint(15, zz438)
            # zz443: NamedType('%bv')
            # Operation(args=[Var(name='zz442'), Var(name='zz441')], name='zsail_zzero_extend', result='zz443', sourcepos='`1 100:14-100:37')
            zz443 = supportcode.zero_extend(machine, zz442, zz441)
            # Assignment(result='zz440', sourcepos='`1 100:14-100:37', value=Var(name='zz443'))
            zz440 = zz443.touint()
            # Operation(args=[Var(name='zz440')], name='zAINST', result='zz439', sourcepos='`1 100:8-100:38')
            zz439 = Union_zinstr_zAINST(zz440)
            # Operation(args=[Var(name='zz439')], name='zSomezIUinstrzIzKzK', result='zz40', sourcepos='`1 100:3-100:39')
            zz40 = Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK(zz439)
            pc = 118
        if pc == 44:
            # zz41: NamedType('%bv16')
            # Assignment(result='zz41', sourcepos='`1 118:23-118:90', value=Var(name='zmergez3var'))
            zz41 = zmergez3var
            # LocalVarDeclaration(name='zz42', sourcepos='`1 118:23-118:90', typ=NamedType('%bv3'), value=None)
            # zz42: NamedType('%bv3')
            zz42 = r_uint(0)
            # zz431: NamedType('%i')
            # Operation(args=[Number(number=15)], name='zz5i64zDzKz5i', result='zz431', sourcepos='`1 118:23-118:90')
            zz431 = supportcode.int64_to_int(machine, 15)
            # zz432: NamedType('%i')
            # Operation(args=[Number(number=13)], name='zz5i64zDzKz5i', result='zz432', sourcepos='`1 118:23-118:90')
            zz432 = supportcode.int64_to_int(machine, 13)
            # zz433: NamedType('%bv')
            # Assignment(result='zz433', sourcepos='`1 118:23-118:90', value=Var(name='zz41'))
            zz433 = bitvector.from_ruint(16, zz41)
            # zz434: NamedType('%bv')
            # Operation(args=[Var(name='zz433'), Var(name='zz431'), Var(name='zz432')], name='zsubrange_bits', result='zz434', sourcepos='`1 118:23-118:90')
            zz434 = supportcode.vector_subrange(machine, zz433, zz431, zz432)
            # Assignment(result='zz42', sourcepos='`1 118:23-118:90', value=Var(name='zz434'))
            zz42 = zz434.touint()
            # LocalVarDeclaration(name='zz43', sourcepos='`1 99:16-100:39', typ=NamedType('%bool'), value=None)
            # zz43: NamedType('%bool')
            zz43 = False
            # zz429: NamedType('%bv')
            # Assignment(result='zz429', sourcepos='`1 118:23-118:90', value=Var(name='zz42'))
            zz429 = bitvector.from_ruint(3, zz42)
            # zz430: NamedType('%bv')
            # Assignment(result='zz430', sourcepos='`1 118:23-118:90', value=BitVectorConstant(constant='0b111'))
            zz430 = bitvector.from_ruint(3, r_uint(0b111))
            # Operation(args=[Var(name='zz429'), Var(name='zz430')], name='zeq_bits', result='zz43', sourcepos='`1 118:23-118:90')
            zz43 = supportcode.eq_bits(machine, zz429, zz430)
            if not zz43:
                # inline pc=64
                pc = 117
                continue
            pc = 65
        if pc == 65:
            # LocalVarDeclaration(name='zz44', sourcepos='`1 119:4-119:82', typ=NamedType('%bv3'), value=None)
            # zz44: NamedType('%bv3')
            zz44 = r_uint(0)
            # zz425: NamedType('%i')
            # Operation(args=[Number(number=2)], name='zz5i64zDzKz5i', result='zz425', sourcepos='`1 118:76-118:80')
            zz425 = supportcode.int64_to_int(machine, 2)
            # zz426: NamedType('%i')
            # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz426', sourcepos='`1 118:76-118:80')
            zz426 = supportcode.int64_to_int(machine, 0)
            # zz427: NamedType('%bv')
            # Assignment(result='zz427', sourcepos='`1 118:76-118:80', value=Var(name='zz41'))
            zz427 = bitvector.from_ruint(16, zz41)
            # zz428: NamedType('%bv')
            # Operation(args=[Var(name='zz427'), Var(name='zz425'), Var(name='zz426')], name='zsubrange_bits', result='zz428', sourcepos='`1 118:76-118:80')
            zz428 = supportcode.vector_subrange(machine, zz427, zz425, zz426)
            # Assignment(result='zz44', sourcepos='`1 118:76-118:80', value=Var(name='zz428'))
            zz44 = zz428.touint()
            # LocalVarDeclaration(name='zz45', sourcepos='`1 118:59-118:63', typ=NamedType('%bv3'), value=None)
            # zz45: NamedType('%bv3')
            zz45 = r_uint(0)
            # zz421: NamedType('%i')
            # Operation(args=[Number(number=5)], name='zz5i64zDzKz5i', result='zz421', sourcepos='`1 118:59-118:63')
            zz421 = supportcode.int64_to_int(machine, 5)
            # zz422: NamedType('%i')
            # Operation(args=[Number(number=3)], name='zz5i64zDzKz5i', result='zz422', sourcepos='`1 118:59-118:63')
            zz422 = supportcode.int64_to_int(machine, 3)
            # zz423: NamedType('%bv')
            # Assignment(result='zz423', sourcepos='`1 118:59-118:63', value=Var(name='zz41'))
            zz423 = bitvector.from_ruint(16, zz41)
            # zz424: NamedType('%bv')
            # Operation(args=[Var(name='zz423'), Var(name='zz421'), Var(name='zz422')], name='zsubrange_bits', result='zz424', sourcepos='`1 118:59-118:63')
            zz424 = supportcode.vector_subrange(machine, zz423, zz421, zz422)
            # Assignment(result='zz45', sourcepos='`1 118:59-118:63', value=Var(name='zz424'))
            zz45 = zz424.touint()
            # LocalVarDeclaration(name='zz46', sourcepos='`1 118:45-118:46', typ=NamedType('%bv6'), value=None)
            # zz46: NamedType('%bv6')
            zz46 = r_uint(0)
            # zz417: NamedType('%i')
            # Operation(args=[Number(number=11)], name='zz5i64zDzKz5i', result='zz417', sourcepos='`1 118:45-118:46')
            zz417 = supportcode.int64_to_int(machine, 11)
            # zz418: NamedType('%i')
            # Operation(args=[Number(number=6)], name='zz5i64zDzKz5i', result='zz418', sourcepos='`1 118:45-118:46')
            zz418 = supportcode.int64_to_int(machine, 6)
            # zz419: NamedType('%bv')
            # Assignment(result='zz419', sourcepos='`1 118:45-118:46', value=Var(name='zz41'))
            zz419 = bitvector.from_ruint(16, zz41)
            # zz420: NamedType('%bv')
            # Operation(args=[Var(name='zz419'), Var(name='zz417'), Var(name='zz418')], name='zsubrange_bits', result='zz420', sourcepos='`1 118:45-118:46')
            zz420 = supportcode.vector_subrange(machine, zz419, zz417, zz418)
            # Assignment(result='zz46', sourcepos='`1 118:45-118:46', value=Var(name='zz420'))
            zz46 = zz420.touint()
            # LocalVarDeclaration(name='zz47', sourcepos='`1 118:31-118:32', typ=NamedType('%bv1'), value=None)
            # zz47: NamedType('%bv1')
            zz47 = r_uint(0)
            # zz413: NamedType('%i')
            # Operation(args=[Number(number=12)], name='zz5i64zDzKz5i', result='zz413', sourcepos='`1 118:31-118:32')
            zz413 = supportcode.int64_to_int(machine, 12)
            # zz414: NamedType('%i')
            # Operation(args=[Number(number=12)], name='zz5i64zDzKz5i', result='zz414', sourcepos='`1 118:31-118:32')
            zz414 = supportcode.int64_to_int(machine, 12)
            # zz415: NamedType('%bv')
            # Assignment(result='zz415', sourcepos='`1 118:31-118:32', value=Var(name='zz41'))
            zz415 = bitvector.from_ruint(16, zz41)
            # zz416: NamedType('%bv')
            # Operation(args=[Var(name='zz415'), Var(name='zz413'), Var(name='zz414')], name='zsubrange_bits', result='zz416', sourcepos='`1 118:31-118:32')
            zz416 = supportcode.vector_subrange(machine, zz415, zz413, zz414)
            # Assignment(result='zz47', sourcepos='`1 118:31-118:32', value=Var(name='zz416'))
            zz47 = zz416.touint()
            # LocalVarDeclaration(name='zz48', sourcepos='`1 119:4-119:82', typ=UnionType(name='zinstr'), value=None)
            # zz48: UnionType(name='zinstr')
            zz48 = Union_zinstr.singleton
            # LocalVarDeclaration(name='zz49', sourcepos='`1 119:9-119:81', typ=StructType(name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump'), value=None)
            # zz49: StructType(name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump')
            zz49 = Struct_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump(r_uint(0), -1, Struct_ztuplez3z5bool_z5bool_z5bool(False, False, False), -1)
            # zz410: EnumType(name='zarithmetic_op')
            # Operation(args=[Var(name='zz46')], name='zdecode_compute_backwards', result='zz410', sourcepos='`1 119:18-119:35')
            zz410 = func_zdecode_compute_backwards(machine, zz46)
            # zz411: StructType(name='ztuplez3z5bool_z5bool_z5bool')
            # Operation(args=[Var(name='zz45')], name='zdecode_destination', result='zz411', sourcepos='`1 119:37-119:61')
            zz411 = func_zdecode_destination(machine, zz45)
            # zz412: EnumType(name='zjump')
            # Operation(args=[Var(name='zz44')], name='zdecode_jump_backwards', result='zz412', sourcepos='`1 119:63-119:80')
            zz412 = func_zdecode_jump_backwards(machine, zz44)
            # Assignment(result='zz49', sourcepos='`1 119:9-119:81', value=StructConstruction(fieldnames=['ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump0', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump1', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump2', 'ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump3'], fieldvalues=[Var(name='zz47'), Var(name='zz410'), Var(name='zz411'), Var(name='zz412')], name='ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump'))
            zz49 = Struct_ztuplez3z5bv1_z5enumz0zzarithmetic_op_z5structz0zztuplezz3zz5bool_zz5bool_zz5bool_z5enumz0zzjump(zz47, zz410, zz411, zz412)
            # Operation(args=[Var(name='zz49')], name='zCINST', result='zz48', sourcepos='`1 119:9-119:81')
            zz48 = Union_zinstr_zCINST(zz49)
            # Operation(args=[Var(name='zz48')], name='zSomezIUinstrzIzKzK', result='zz40', sourcepos='`1 119:4-119:82')
            zz40 = Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK(zz48)
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
            # LocalVarDeclaration(name='zz441', sourcepos='`1 124:10-124:45', typ=NamedType('%bool'), value=None)
            # zz441: NamedType('%bool')
            zz441 = False
            # zz442: NamedType('%bv')
            # Assignment(result='zz442', sourcepos='`1 124:13-124:21', value=Var(name='za'))
            zz442 = bitvector.from_ruint(1, za)
            # zz443: NamedType('%bv')
            # Assignment(result='zz443', sourcepos='`1 124:13-124:21', value=BitVectorConstant(constant='0b0'))
            zz443 = bitvector.from_ruint(1, r_uint(0b0))
            # Operation(args=[Var(name='zz442'), Var(name='zz443')], name='zeq_bits', result='zz441', sourcepos='`1 124:13-124:21')
            zz441 = supportcode.eq_bits(machine, zz442, zz443)
            if zz441:
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
                                                                                # zz44: NamedType('%bv')
                                                                                # Assignment(result='zz44', sourcepos='`1 144:16-144:21', value=Var(name='zz41'))
                                                                                zz44 = bitvector.from_ruint(16, zz41)
                                                                                # zz45: NamedType('%bv')
                                                                                # Assignment(result='zz45', sourcepos='`1 144:16-144:21', value=Var(name='zz40'))
                                                                                zz45 = bitvector.from_ruint(16, zz40)
                                                                                # zz46: NamedType('%bv')
                                                                                # Operation(args=[Var(name='zz44'), Var(name='zz45')], name='zor_vec', result='zz46', sourcepos='`1 144:16-144:21')
                                                                                zz46 = supportcode.or_bits(machine, zz44, zz45)
                                                                                # Assignment(result='zz43', sourcepos='`1 144:16-144:21', value=Var(name='zz46'))
                                                                                zz43 = zz46.touint()
                                                                                pc = 144
                                                                                continue
                                                                            # zz47: NamedType('%bv')
                                                                            # Assignment(result='zz47', sourcepos='`1 143:17-143:22', value=Var(name='zz41'))
                                                                            zz47 = bitvector.from_ruint(16, zz41)
                                                                            # zz48: NamedType('%bv')
                                                                            # Assignment(result='zz48', sourcepos='`1 143:17-143:22', value=Var(name='zz40'))
                                                                            zz48 = bitvector.from_ruint(16, zz40)
                                                                            # zz49: NamedType('%bv')
                                                                            # Operation(args=[Var(name='zz47'), Var(name='zz48')], name='zand_vec', result='zz49', sourcepos='`1 143:17-143:22')
                                                                            zz49 = supportcode.and_bits(machine, zz47, zz48)
                                                                            # Assignment(result='zz43', sourcepos='`1 143:17-143:22', value=Var(name='zz49'))
                                                                            zz43 = zz49.touint()
                                                                            pc = 144
                                                                            continue
                                                                        # zz410: NamedType('%bv')
                                                                        # Assignment(result='zz410', sourcepos='`1 142:17-142:22', value=Var(name='zz40'))
                                                                        zz410 = bitvector.from_ruint(16, zz40)
                                                                        # zz411: NamedType('%bv')
                                                                        # Assignment(result='zz411', sourcepos='`1 142:17-142:22', value=Var(name='zz41'))
                                                                        zz411 = bitvector.from_ruint(16, zz41)
                                                                        # zz412: NamedType('%bv')
                                                                        # Operation(args=[Var(name='zz410'), Var(name='zz411')], name='zsub_vec', result='zz412', sourcepos='`1 142:17-142:22')
                                                                        zz412 = supportcode.sub_bits(machine, zz410, zz411)
                                                                        # Assignment(result='zz43', sourcepos='`1 142:17-142:22', value=Var(name='zz412'))
                                                                        zz43 = zz412.touint()
                                                                        pc = 144
                                                                        continue
                                                                    # zz413: NamedType('%bv')
                                                                    # Assignment(result='zz413', sourcepos='`1 141:17-141:22', value=Var(name='zz41'))
                                                                    zz413 = bitvector.from_ruint(16, zz41)
                                                                    # zz414: NamedType('%bv')
                                                                    # Assignment(result='zz414', sourcepos='`1 141:17-141:22', value=Var(name='zz40'))
                                                                    zz414 = bitvector.from_ruint(16, zz40)
                                                                    # zz415: NamedType('%bv')
                                                                    # Operation(args=[Var(name='zz413'), Var(name='zz414')], name='zsub_vec', result='zz415', sourcepos='`1 141:17-141:22')
                                                                    zz415 = supportcode.sub_bits(machine, zz413, zz414)
                                                                    # Assignment(result='zz43', sourcepos='`1 141:17-141:22', value=Var(name='zz415'))
                                                                    zz43 = zz415.touint()
                                                                    pc = 144
                                                                    continue
                                                                # zz416: NamedType('%bv')
                                                                # Assignment(result='zz416', sourcepos='`1 140:17-140:22', value=Var(name='zz41'))
                                                                zz416 = bitvector.from_ruint(16, zz41)
                                                                # zz417: NamedType('%bv')
                                                                # Assignment(result='zz417', sourcepos='`1 140:17-140:22', value=Var(name='zz40'))
                                                                zz417 = bitvector.from_ruint(16, zz40)
                                                                # zz418: NamedType('%bv')
                                                                # Operation(args=[Var(name='zz416'), Var(name='zz417')], name='zadd_bits', result='zz418', sourcepos='`1 140:17-140:22')
                                                                zz418 = supportcode.add_bits(machine, zz416, zz417)
                                                                # Assignment(result='zz43', sourcepos='`1 140:17-140:22', value=Var(name='zz418'))
                                                                zz43 = zz418.touint()
                                                                pc = 144
                                                                continue
                                                            # zz419: NamedType('%bv')
                                                            # Assignment(result='zz419', sourcepos='`1 139:17-139:27', value=Var(name='zz40'))
                                                            zz419 = bitvector.from_ruint(16, zz40)
                                                            # zz420: NamedType('%bv')
                                                            # Assignment(result='zz420', sourcepos='`1 139:17-139:27', value=BitVectorConstant(constant='0x0001'))
                                                            zz420 = bitvector.from_ruint(16, r_uint(0x0001))
                                                            # zz421: NamedType('%bv')
                                                            # Operation(args=[Var(name='zz419'), Var(name='zz420')], name='zsub_vec', result='zz421', sourcepos='`1 139:17-139:27')
                                                            zz421 = supportcode.sub_bits(machine, zz419, zz420)
                                                            # Assignment(result='zz43', sourcepos='`1 139:17-139:27', value=Var(name='zz421'))
                                                            zz43 = zz421.touint()
                                                            pc = 144
                                                            continue
                                                        # zz422: NamedType('%bv')
                                                        # Assignment(result='zz422', sourcepos='`1 138:17-138:27', value=Var(name='zz41'))
                                                        zz422 = bitvector.from_ruint(16, zz41)
                                                        # zz423: NamedType('%bv')
                                                        # Assignment(result='zz423', sourcepos='`1 138:17-138:27', value=BitVectorConstant(constant='0x0001'))
                                                        zz423 = bitvector.from_ruint(16, r_uint(0x0001))
                                                        # zz424: NamedType('%bv')
                                                        # Operation(args=[Var(name='zz422'), Var(name='zz423')], name='zsub_vec', result='zz424', sourcepos='`1 138:17-138:27')
                                                        zz424 = supportcode.sub_bits(machine, zz422, zz423)
                                                        # Assignment(result='zz43', sourcepos='`1 138:17-138:27', value=Var(name='zz424'))
                                                        zz43 = zz424.touint()
                                                        pc = 144
                                                        continue
                                                    # zz425: NamedType('%bv')
                                                    # Assignment(result='zz425', sourcepos='`1 137:17-137:27', value=Var(name='zz40'))
                                                    zz425 = bitvector.from_ruint(16, zz40)
                                                    # zz426: NamedType('%bv')
                                                    # Assignment(result='zz426', sourcepos='`1 137:17-137:27', value=BitVectorConstant(constant='0x0001'))
                                                    zz426 = bitvector.from_ruint(16, r_uint(0x0001))
                                                    # zz427: NamedType('%bv')
                                                    # Operation(args=[Var(name='zz425'), Var(name='zz426')], name='zadd_bits', result='zz427', sourcepos='`1 137:17-137:27')
                                                    zz427 = supportcode.add_bits(machine, zz425, zz426)
                                                    # Assignment(result='zz43', sourcepos='`1 137:17-137:27', value=Var(name='zz427'))
                                                    zz43 = zz427.touint()
                                                    pc = 144
                                                    continue
                                                # zz428: NamedType('%bv')
                                                # Assignment(result='zz428', sourcepos='`1 136:17-136:27', value=Var(name='zz41'))
                                                zz428 = bitvector.from_ruint(16, zz41)
                                                # zz429: NamedType('%bv')
                                                # Assignment(result='zz429', sourcepos='`1 136:17-136:27', value=BitVectorConstant(constant='0x0001'))
                                                zz429 = bitvector.from_ruint(16, r_uint(0x0001))
                                                # zz430: NamedType('%bv')
                                                # Operation(args=[Var(name='zz428'), Var(name='zz429')], name='zadd_bits', result='zz430', sourcepos='`1 136:17-136:27')
                                                zz430 = supportcode.add_bits(machine, zz428, zz429)
                                                # Assignment(result='zz43', sourcepos='`1 136:17-136:27', value=Var(name='zz430'))
                                                zz43 = zz430.touint()
                                                pc = 144
                                                continue
                                            # zz431: NamedType('%bv')
                                            # Assignment(result='zz431', sourcepos='`1 135:15-135:23', value=BitVectorConstant(constant='0x0000'))
                                            zz431 = bitvector.from_ruint(16, r_uint(0x0000))
                                            # zz432: NamedType('%bv')
                                            # Assignment(result='zz432', sourcepos='`1 135:15-135:23', value=Var(name='zz40'))
                                            zz432 = bitvector.from_ruint(16, zz40)
                                            # zz433: NamedType('%bv')
                                            # Operation(args=[Var(name='zz431'), Var(name='zz432')], name='zsub_vec', result='zz433', sourcepos='`1 135:15-135:23')
                                            zz433 = supportcode.sub_bits(machine, zz431, zz432)
                                            # Assignment(result='zz43', sourcepos='`1 135:15-135:23', value=Var(name='zz433'))
                                            zz43 = zz433.touint()
                                            pc = 144
                                            continue
                                        # zz434: NamedType('%bv')
                                        # Assignment(result='zz434', sourcepos='`1 134:15-134:23', value=BitVectorConstant(constant='0x0000'))
                                        zz434 = bitvector.from_ruint(16, r_uint(0x0000))
                                        # zz435: NamedType('%bv')
                                        # Assignment(result='zz435', sourcepos='`1 134:15-134:23', value=Var(name='zz41'))
                                        zz435 = bitvector.from_ruint(16, zz41)
                                        # zz436: NamedType('%bv')
                                        # Operation(args=[Var(name='zz434'), Var(name='zz435')], name='zsub_vec', result='zz436', sourcepos='`1 134:15-134:23')
                                        zz436 = supportcode.sub_bits(machine, zz434, zz435)
                                        # Assignment(result='zz43', sourcepos='`1 134:15-134:23', value=Var(name='zz436'))
                                        zz43 = zz436.touint()
                                        pc = 144
                                        continue
                                    # zz437: NamedType('%bv')
                                    # Assignment(result='zz437', sourcepos='`1 133:15-133:25', value=Var(name='zz40'))
                                    zz437 = bitvector.from_ruint(16, zz40)
                                    # zz438: NamedType('%bv')
                                    # Operation(args=[Var(name='zz437')], name='znot_vec', result='zz438', sourcepos='`1 133:15-133:25')
                                    zz438 = supportcode.not_bits(machine, zz437)
                                    # Assignment(result='zz43', sourcepos='`1 133:15-133:25', value=Var(name='zz438'))
                                    zz43 = zz438.touint()
                                    pc = 144
                                    continue
                                # zz439: NamedType('%bv')
                                # Assignment(result='zz439', sourcepos='`1 132:15-132:25', value=Var(name='zz41'))
                                zz439 = bitvector.from_ruint(16, zz41)
                                # zz440: NamedType('%bv')
                                # Operation(args=[Var(name='zz439')], name='znot_vec', result='zz440', sourcepos='`1 132:15-132:25')
                                zz440 = supportcode.not_bits(machine, zz439)
                                # Assignment(result='zz43', sourcepos='`1 132:15-132:25', value=Var(name='zz440'))
                                zz43 = zz440.touint()
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
                                    # LocalVarDeclaration(name='zz45', sourcepos='`1 163:15-163:33', typ=NamedType('%i64'), value=None)
                                    # zz45: NamedType('%i64')
                                    zz45 = -0xfefe
                                    # zz48: NamedType('%bv')
                                    # Assignment(result='zz48', sourcepos='`1 163:15-163:28', value=Var(name='zvalue'))
                                    zz48 = bitvector.from_ruint(16, zvalue)
                                    # zz49: NamedType('%i')
                                    # Operation(args=[Var(name='zz48')], name='zsigned', result='zz49', sourcepos='`1 163:15-163:28')
                                    zz49 = supportcode.sail_signed(machine, zz48)
                                    # Operation(args=[Var(name='zz49')], name='zz5izDzKz5i64', result='zz45', sourcepos='`1 163:15-163:28')
                                    zz45 = supportcode.int_to_int64(machine, zz49)
                                    # zz46: NamedType('%i')
                                    # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz46', sourcepos='`1 163:15-163:33')
                                    zz46 = supportcode.int64_to_int(machine, 0)
                                    # zz47: NamedType('%i')
                                    # Operation(args=[Var(name='zz45')], name='zz5i64zDzKz5i', result='zz47', sourcepos='`1 163:15-163:33')
                                    zz47 = supportcode.int64_to_int(machine, zz45)
                                    # Operation(args=[Var(name='zz47'), Var(name='zz46')], name='zlteq_int', result='zz44', sourcepos='`1 163:15-163:33')
                                    zz44 = supportcode.lteq(machine, zz47, zz46)
                                    pc = 87
                                    continue
                                # LocalVarDeclaration(name='zz410', sourcepos='`1 162:15-162:33', typ=NamedType('%i64'), value=None)
                                # zz410: NamedType('%i64')
                                zz410 = -0xfefe
                                # zz413: NamedType('%bv')
                                # Assignment(result='zz413', sourcepos='`1 162:15-162:28', value=Var(name='zvalue'))
                                zz413 = bitvector.from_ruint(16, zvalue)
                                # zz414: NamedType('%i')
                                # Operation(args=[Var(name='zz413')], name='zsigned', result='zz414', sourcepos='`1 162:15-162:28')
                                zz414 = supportcode.sail_signed(machine, zz413)
                                # Operation(args=[Var(name='zz414')], name='zz5izDzKz5i64', result='zz410', sourcepos='`1 162:15-162:28')
                                zz410 = supportcode.int_to_int64(machine, zz414)
                                # zz411: NamedType('%i')
                                # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz411', sourcepos='`1 162:15-162:33')
                                zz411 = supportcode.int64_to_int(machine, 0)
                                # zz412: NamedType('%i')
                                # Operation(args=[Var(name='zz410')], name='zz5i64zDzKz5i', result='zz412', sourcepos='`1 162:15-162:33')
                                zz412 = supportcode.int64_to_int(machine, zz410)
                                # Operation(args=[Var(name='zz412'), Var(name='zz411')], name='zneq_int', result='zz44', sourcepos='`1 162:15-162:33')
                                zz44 = func_zneq_int(machine, zz412, zz411)
                                pc = 87
                                continue
                            # LocalVarDeclaration(name='zz415', sourcepos='`1 161:15-161:32', typ=NamedType('%i64'), value=None)
                            # zz415: NamedType('%i64')
                            zz415 = -0xfefe
                            # zz418: NamedType('%bv')
                            # Assignment(result='zz418', sourcepos='`1 161:15-161:28', value=Var(name='zvalue'))
                            zz418 = bitvector.from_ruint(16, zvalue)
                            # zz419: NamedType('%i')
                            # Operation(args=[Var(name='zz418')], name='zsigned', result='zz419', sourcepos='`1 161:15-161:28')
                            zz419 = supportcode.sail_signed(machine, zz418)
                            # Operation(args=[Var(name='zz419')], name='zz5izDzKz5i64', result='zz415', sourcepos='`1 161:15-161:28')
                            zz415 = supportcode.int_to_int64(machine, zz419)
                            # zz416: NamedType('%i')
                            # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz416', sourcepos='`1 161:15-161:32')
                            zz416 = supportcode.int64_to_int(machine, 0)
                            # zz417: NamedType('%i')
                            # Operation(args=[Var(name='zz415')], name='zz5i64zDzKz5i', result='zz417', sourcepos='`1 161:15-161:32')
                            zz417 = supportcode.int64_to_int(machine, zz415)
                            # Operation(args=[Var(name='zz417'), Var(name='zz416')], name='zlt_int', result='zz44', sourcepos='`1 161:15-161:32')
                            zz44 = supportcode.lt(machine, zz417, zz416)
                            pc = 87
                            continue
                        # LocalVarDeclaration(name='zz420', sourcepos='`1 160:15-160:33', typ=NamedType('%i64'), value=None)
                        # zz420: NamedType('%i64')
                        zz420 = -0xfefe
                        # zz423: NamedType('%bv')
                        # Assignment(result='zz423', sourcepos='`1 160:15-160:28', value=Var(name='zvalue'))
                        zz423 = bitvector.from_ruint(16, zvalue)
                        # zz424: NamedType('%i')
                        # Operation(args=[Var(name='zz423')], name='zsigned', result='zz424', sourcepos='`1 160:15-160:28')
                        zz424 = supportcode.sail_signed(machine, zz423)
                        # Operation(args=[Var(name='zz424')], name='zz5izDzKz5i64', result='zz420', sourcepos='`1 160:15-160:28')
                        zz420 = supportcode.int_to_int64(machine, zz424)
                        # zz421: NamedType('%i')
                        # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz421', sourcepos='`1 160:15-160:33')
                        zz421 = supportcode.int64_to_int(machine, 0)
                        # zz422: NamedType('%i')
                        # Operation(args=[Var(name='zz420')], name='zz5i64zDzKz5i', result='zz422', sourcepos='`1 160:15-160:33')
                        zz422 = supportcode.int64_to_int(machine, zz420)
                        # Operation(args=[Var(name='zz422'), Var(name='zz421')], name='zgteq_int', result='zz44', sourcepos='`1 160:15-160:33')
                        zz44 = supportcode.gteq(machine, zz422, zz421)
                        pc = 87
                        continue
                    # LocalVarDeclaration(name='zz425', sourcepos='`1 159:15-159:33', typ=NamedType('%i64'), value=None)
                    # zz425: NamedType('%i64')
                    zz425 = -0xfefe
                    # zz428: NamedType('%bv')
                    # Assignment(result='zz428', sourcepos='`1 159:15-159:28', value=Var(name='zvalue'))
                    zz428 = bitvector.from_ruint(16, zvalue)
                    # zz429: NamedType('%i')
                    # Operation(args=[Var(name='zz428')], name='zsigned', result='zz429', sourcepos='`1 159:15-159:28')
                    zz429 = supportcode.sail_signed(machine, zz428)
                    # Operation(args=[Var(name='zz429')], name='zz5izDzKz5i64', result='zz425', sourcepos='`1 159:15-159:28')
                    zz425 = supportcode.int_to_int64(machine, zz429)
                    # zz426: NamedType('%i')
                    # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz426', sourcepos='`1 159:15-159:33')
                    zz426 = supportcode.int64_to_int(machine, 0)
                    # zz427: NamedType('%i')
                    # Operation(args=[Var(name='zz425')], name='zz5i64zDzKz5i', result='zz427', sourcepos='`1 159:15-159:33')
                    zz427 = supportcode.int64_to_int(machine, zz425)
                    # Operation(args=[Var(name='zz427'), Var(name='zz426')], name='zeq_int', result='zz44', sourcepos='`1 159:15-159:33')
                    zz44 = supportcode.eq_int(machine, zz427, zz426)
                    pc = 87
                    continue
                # LocalVarDeclaration(name='zz430', sourcepos='`1 158:15-158:32', typ=NamedType('%i64'), value=None)
                # zz430: NamedType('%i64')
                zz430 = -0xfefe
                # zz433: NamedType('%bv')
                # Assignment(result='zz433', sourcepos='`1 158:15-158:28', value=Var(name='zvalue'))
                zz433 = bitvector.from_ruint(16, zvalue)
                # zz434: NamedType('%i')
                # Operation(args=[Var(name='zz433')], name='zsigned', result='zz434', sourcepos='`1 158:15-158:28')
                zz434 = supportcode.sail_signed(machine, zz433)
                # Operation(args=[Var(name='zz434')], name='zz5izDzKz5i64', result='zz430', sourcepos='`1 158:15-158:28')
                zz430 = supportcode.int_to_int64(machine, zz434)
                # zz431: NamedType('%i')
                # Operation(args=[Number(number=0)], name='zz5i64zDzKz5i', result='zz431', sourcepos='`1 158:15-158:32')
                zz431 = supportcode.int64_to_int(machine, 0)
                # zz432: NamedType('%i')
                # Operation(args=[Var(name='zz430')], name='zz5i64zDzKz5i', result='zz432', sourcepos='`1 158:15-158:32')
                zz432 = supportcode.int64_to_int(machine, zz430)
                # Operation(args=[Var(name='zz432'), Var(name='zz431')], name='zgt_int', result='zz44', sourcepos='`1 158:15-158:32')
                zz44 = supportcode.gt(machine, zz432, zz431)
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
            # zz41: NamedType('%i')
            # Operation(args=[Number(number=1)], name='zz5i64zDzKz5i', result='zz41', sourcepos='`1 166:38-166:44')
            zz41 = supportcode.int64_to_int(machine, 1)
            # zz42: NamedType('%bv')
            # Assignment(result='zz42', sourcepos='`1 166:38-166:44', value=Var(name='zPC'))
            zz42 = bitvector.from_ruint(16, machine._reg_zPC)
            # zz43: NamedType('%bv')
            # Operation(args=[Var(name='zz42'), Var(name='zz41')], name='zadd_bits_int', result='zz43', sourcepos='`1 166:38-166:44')
            zz43 = supportcode.add_bits_int(machine, zz42, zz41)
            # Assignment(result='zPC', sourcepos='`1 166:38-166:44', value=Var(name='zz43'))
            machine._reg_zPC = zz43.touint()
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
            # zz48: NamedType('%i')
            # Operation(args=[Number(number=1)], name='zz5i64zDzKz5i', result='zz48', sourcepos='`1 103:14-103:20')
            zz48 = supportcode.int64_to_int(machine, 1)
            # zz49: NamedType('%bv')
            # Assignment(result='zz49', sourcepos='`1 103:14-103:20', value=Var(name='zPC'))
            zz49 = bitvector.from_ruint(16, machine._reg_zPC)
            # zz410: NamedType('%bv')
            # Operation(args=[Var(name='zz49'), Var(name='zz48')], name='zadd_bits_int', result='zz410', sourcepos='`1 103:14-103:20')
            zz410 = supportcode.add_bits_int(machine, zz49, zz48)
            # Assignment(result='zPC', sourcepos='`1 103:14-103:20', value=Var(name='zz410'))
            machine._reg_zPC = zz410.touint()
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
            # zz45: UnionType(name='zinstr')
            # Assignment(result='zz45', sourcepos='`1 183:13-183:18', value=Cast(expr=Var(name='zz41'), variant='zSomezIUinstrzIzKzK'))
            zz45 = Union_zoptionzIUinstrzIzKzK_zSomezIUinstrzIzKzK.convert(zz41)
            # zz46: NamedType('%unit')
            # Operation(args=[Var(name='zz45')], name='zexecute', result='zz46', sourcepos='`1 183:25-183:39')
            zz46 = func_zexecute(machine, zz45)
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
            # zz47: NamedType('%bool')
            # Operation(args=[Unit()], name='zfetch_decode_execute', result='zz47', sourcepos='`1 199:11-199:33')
            zz47 = func_zfetch_decode_execute(machine, ())
            # LocalVarDeclaration(name='zz48', sourcepos='`1 199:8-203:9', typ=NamedType('%unit'), value=None)
            # zz48: NamedType('%unit')
            zz48 = ()
            if zz47:
                # inline pc=22
                # LocalVarDeclaration(name='zz49', sourcepos='`1 200:12-202:13', typ=NamedType('%bool'), value=None)
                # zz49: NamedType('%bool')
                zz49 = False
                # LocalVarDeclaration(name='zz410', sourcepos='`1 200:15-200:50', typ=NamedType('%i64'), value=None)
                # zz410: NamedType('%i64')
                zz410 = -0xfefe
                # zz416: NamedType('%bv')
                # Assignment(result='zz416', sourcepos='`1 200:15-200:34', value=Var(name='zz40'))
                zz416 = bitvector.from_ruint(64, zz40)
                # zz417: NamedType('%i')
                # Operation(args=[Var(name='zz416')], name='zsigned', result='zz417', sourcepos='`1 200:15-200:34')
                zz417 = supportcode.sail_signed(machine, zz416)
                # Operation(args=[Var(name='zz417')], name='zz5izDzKz5i64', result='zz410', sourcepos='`1 200:15-200:34')
                zz410 = supportcode.int_to_int64(machine, zz417)
                # LocalVarDeclaration(name='zz411', sourcepos='`1 200:15-200:50', typ=NamedType('%i64'), value=None)
                # zz411: NamedType('%i64')
                zz411 = -0xfefe
                # zz414: NamedType('%bv')
                # Assignment(result='zz414', sourcepos='`1 200:37-200:50', value=Var(name='zlimit'))
                zz414 = bitvector.from_ruint(64, zlimit)
                # zz415: NamedType('%i')
                # Operation(args=[Var(name='zz414')], name='zsigned', result='zz415', sourcepos='`1 200:37-200:50')
                zz415 = supportcode.sail_signed(machine, zz414)
                # Operation(args=[Var(name='zz415')], name='zz5izDzKz5i64', result='zz411', sourcepos='`1 200:37-200:50')
                zz411 = supportcode.int_to_int64(machine, zz415)
                # zz412: NamedType('%i')
                # Operation(args=[Var(name='zz410')], name='zz5i64zDzKz5i', result='zz412', sourcepos='`1 200:15-200:50')
                zz412 = supportcode.int64_to_int(machine, zz410)
                # zz413: NamedType('%i')
                # Operation(args=[Var(name='zz411')], name='zz5i64zDzKz5i', result='zz413', sourcepos='`1 200:15-200:50')
                zz413 = supportcode.int64_to_int(machine, zz411)
                # Operation(args=[Var(name='zz412'), Var(name='zz413')], name='zlt_int', result='zz49', sourcepos='`1 200:15-200:50')
                zz49 = supportcode.lt(machine, zz412, zz413)
                if zz49:
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
            # zz45: NamedType('%bv')
            # Assignment(result='zz45', sourcepos='`1 204:22-204:54', value=BitVectorConstant(constant='0x0000000000000001'))
            zz45 = bitvector.from_ruint(64, r_uint(0x0000000000000001))
            # zz46: NamedType('%bv')
            # Operation(args=[Var(name='zz44'), Var(name='zz45')], name='zadd_bits', result='zz46', sourcepos='`1 204:22-204:54')
            zz46 = supportcode.add_bits(machine, zz44, zz45)
            # Assignment(result='zz40', sourcepos='`1 204:22-204:54', value=Var(name='zz46'))
            zz40 = zz46.touint()
            # Assignment(result='zz43', sourcepos='`1 204:8-204:54', value=Unit())
            zz43 = ()
            pc = 6
            continue




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
    # zz45: NamedType('%i')
    # Operation(args=[Number(number=16)], name='zz5i64zDzKz5i', result='zz45', sourcepos='`62')
    zz45 = supportcode.int64_to_int(machine, 16)
    # zz47: NamedType('%bv')
    # Operation(args=[Var(name='zz45')], name='zundefined_bitvector', result='zz47', sourcepos='`64')
    zz47 = supportcode.undefined_bitvector(machine, zz45)
    # Assignment(result='zPC', sourcepos='`65', value=Var(name='zz47'))
    machine._reg_zPC = zz47.touint()
    # zz46: NamedType('%unit')
    # Assignment(result='zz46', sourcepos='`67', value=Unit())
    zz46 = ()
    # zz42: NamedType('%i')
    # Operation(args=[Number(number=16)], name='zz5i64zDzKz5i', result='zz42', sourcepos='`69')
    zz42 = supportcode.int64_to_int(machine, 16)
    # zz44: NamedType('%bv')
    # Operation(args=[Var(name='zz42')], name='zundefined_bitvector', result='zz44', sourcepos='`71')
    zz44 = supportcode.undefined_bitvector(machine, zz42)
    # Assignment(result='zA', sourcepos='`72', value=Var(name='zz44'))
    machine._reg_zA = zz44.touint()
    # zz43: NamedType('%unit')
    # Assignment(result='zz43', sourcepos='`74', value=Unit())
    zz43 = ()
    # zz40: NamedType('%i')
    # Operation(args=[Number(number=16)], name='zz5i64zDzKz5i', result='zz40', sourcepos='`76')
    zz40 = supportcode.int64_to_int(machine, 16)
    # zz41: NamedType('%bv')
    # Operation(args=[Var(name='zz40')], name='zundefined_bitvector', result='zz41', sourcepos='`78')
    zz41 = supportcode.undefined_bitvector(machine, zz40)
    # Assignment(result='zD', sourcepos='`79', value=Var(name='zz41'))
    machine._reg_zD = zz41.touint()
    # Assignment(result='return', sourcepos='`80', value=Unit())
    return_ = ()
    # End()
    return return_


# Files(filenames=['"/home/cfbolz/.opam/ocaml.4.13.1/share/sail/lib/flow.sail"', '"nand2tetris.sail"'])
