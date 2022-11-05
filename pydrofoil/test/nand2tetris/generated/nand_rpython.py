from rpython.rlib import jit
from rpython.rlib import objectmodel
from rpython.rlib.rarithmetic import r_uint, intmask
import operator
from pydrofoil.test.nand2tetris import supportcodenand as supportcode
from pydrofoil import bitvector
from pydrofoil.bitvector import Integer

class Registers(supportcode.RegistersBase): pass

class Lets(object): pass

class Machine(object):
    def __init__(self): self.l = Lets(); self.r = Registers(); model_init(self)
UninitInt = bitvector.Integer.fromint(-0xfefee)

class Tuple_1(object): # TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
    def eq(self, other):
        assert isinstance(other, Tuple_1)
        if not (self.utup0 == other.utup0): return False # NamedType('%bool')
        if not (self.utup1 == other.utup1): return False # NamedType('%bool')
        if not (self.utup2 == other.utup2): return False # NamedType('%bool')
        return True

class Tuple_2(object): # TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op'), TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), EnumType(name='zjump')])
    def eq(self, other):
        assert isinstance(other, Tuple_2)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv1')
        if not (self.utup1 == other.utup1): return False # EnumType(name='zarithmetic_op')
        if not (self.utup2.eq(other.utup2)): return False # TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
        if not (self.utup3 == other.utup3): return False # EnumType(name='zjump')
        return True

class Union_zinstr(object):
    def eq(self, other):
        return False

class Union_zinstr_zAINST(Union_zinstr):
    a = r_uint(0)
    def __init__(self, a):
        self.a = a # NamedType('%bv16')
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
    utup0 = r_uint(0)
    utup1 = -1
    utup2 = Tuple_1()
    utup3 = -1
    def __init__(self, a):
        # TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op'), TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), EnumType(name='zjump')])
        self.utup0 = a.ztup0
        self.utup1 = a.ztup1
        self.utup2 = a.ztup2
        self.utup3 = a.ztup3
    def eq(self, other):
        if type(self) is not type(other): return False
        # TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op'), TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), EnumType(name='zjump')])
        if not (self.utup0 == other.utup0): return False # NamedType('%bv1')
        if not (self.utup1 == other.utup1): return False # EnumType(name='zarithmetic_op')
        if not (self.utup2.eq(other.utup2)): return False # TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
        if not (self.utup3 == other.utup3): return False # EnumType(name='zjump')
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zinstr_zCINST):
            res = Tuple_2()
            res.ztup0 = inst.utup0
            res.ztup1 = inst.utup1
            res.ztup2 = inst.utup2
            res.ztup3 = inst.utup3
            return res
        else:
            raise TypeError

class Union_zoption(object):
    def eq(self, other):
        return False

class Union_zoption_zNone(Union_zoption):
    def __init__(self, a):
        pass
    def eq(self, other):
        if type(self) is not type(other): return False
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zoption_zNone):
            return ()
        else:
            raise TypeError

class Union_zoption_zSomez3z5unionz0zzinstr(Union_zoption):
    a = Union_zinstr()
    def __init__(self, a):
        self.a = a # UnionType(name='zinstr')
    def eq(self, other):
        if type(self) is not type(other): return False
        if not (self.a.eq(other.a)): return False # UnionType(name='zinstr')
        return True
    @staticmethod
    @objectmodel.always_inline
    def convert(inst):
        if isinstance(inst, Union_zoption_zSomez3z5unionz0zzinstr):
            return inst.a
        else:
            raise TypeError

class Tuple_3(object): # TupleType(elements=[NamedType('%bool')])
    def eq(self, other):
        assert isinstance(other, Tuple_3)
        if not (self.utup0 == other.utup0): return False # NamedType('%bool')
        return True

class Tuple_4(object): # TupleType(elements=[NamedType('%bool'), NamedType('%bool')])
    def eq(self, other):
        assert isinstance(other, Tuple_4)
        if not (self.utup0 == other.utup0): return False # NamedType('%bool')
        if not (self.utup1 == other.utup1): return False # NamedType('%bool')
        return True

class Tuple_5(object): # TupleType(elements=[NamedType('%i'), NamedType('%i')])
    def eq(self, other):
        assert isinstance(other, Tuple_5)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%i')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%i')
        return True

class Tuple_6(object): # TupleType(elements=[NamedType('%bv'), NamedType('%bv')])
    def eq(self, other):
        assert isinstance(other, Tuple_6)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%bv')
        return True

class Tuple_7(object): # TupleType(elements=[NamedType('%bv')])
    def eq(self, other):
        assert isinstance(other, Tuple_7)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        return True

class Tuple_8(object): # TupleType(elements=[NamedType('%bv'), NamedType('%i')])
    def eq(self, other):
        assert isinstance(other, Tuple_8)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%i')
        return True

class Tuple_9(object): # TupleType(elements=[NamedType('%i'), NamedType('%bv')])
    def eq(self, other):
        assert isinstance(other, Tuple_9)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%i')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%bv')
        return True

class Tuple_10(object): # TupleType(elements=[NamedType('%bv'), NamedType('%bv64')])
    def eq(self, other):
        assert isinstance(other, Tuple_10)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        if not (self.utup1 == other.utup1): return False # NamedType('%bv64')
        return True

class Tuple_11(object): # TupleType(elements=[NamedType('%bv'), NamedType('%i'), NamedType('%i')])
    def eq(self, other):
        assert isinstance(other, Tuple_11)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%bv')
        if not (self.utup1.eq(other.utup1)): return False # NamedType('%i')
        if not (self.utup2.eq(other.utup2)): return False # NamedType('%i')
        return True

class Tuple_12(object): # TupleType(elements=[NamedType('%i')])
    def eq(self, other):
        assert isinstance(other, Tuple_12)
        if not (self.utup0.eq(other.utup0)): return False # NamedType('%i')
        return True
IntConst_0_1 = Integer.fromint(0)
IntConst_1_1 = Integer.fromint(1)

class Tuple_13(object): # TupleType(elements=[NamedType('%bv1')])
    def eq(self, other):
        assert isinstance(other, Tuple_13)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv1')
        return True

class Tuple_14(object): # TupleType(elements=[NamedType('%bv16'), NamedType('%bv16')])
    def eq(self, other):
        assert isinstance(other, Tuple_14)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv16')
        if not (self.utup1 == other.utup1): return False # NamedType('%bv16')
        return True

class Tuple_15(object): # TupleType(elements=[NamedType('%bv16')])
    def eq(self, other):
        assert isinstance(other, Tuple_15)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv16')
        return True

class Tuple_16(object): # TupleType(elements=[NamedType('%bv64'), NamedType('%bv16'), NamedType('%bv16'), NamedType('%bv16')])
    def eq(self, other):
        assert isinstance(other, Tuple_16)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv64')
        if not (self.utup1 == other.utup1): return False # NamedType('%bv16')
        if not (self.utup2 == other.utup2): return False # NamedType('%bv16')
        if not (self.utup3 == other.utup3): return False # NamedType('%bv16')
        return True
# Register(name='zPC', typ=NamedType('%bv16'))
Registers.zPC = r_uint(0)
# Register(name='zA', typ=NamedType('%bv16'))
Registers.zA = r_uint(0)
# Register(name='zD', typ=NamedType('%bv16'))
Registers.zD = r_uint(0)

class Tuple_17(object): # TupleType(elements=[NamedType('%bv6')])
    def eq(self, other):
        assert isinstance(other, Tuple_17)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv6')
        return True

class Tuple_18(object): # TupleType(elements=[NamedType('%bv3')])
    def eq(self, other):
        assert isinstance(other, Tuple_18)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv3')
        return True

class Tuple_19(object): # TupleType(elements=[UnionType(name='zinstr')])
    def eq(self, other):
        assert isinstance(other, Tuple_19)
        if not (self.utup0.eq(other.utup0)): return False # UnionType(name='zinstr')
        return True
IntConst_16_1 = Integer.fromint(16)

class Tuple_20(object): # TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op')])
    def eq(self, other):
        assert isinstance(other, Tuple_20)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv1')
        if not (self.utup1 == other.utup1): return False # EnumType(name='zarithmetic_op')
        return True

class Tuple_21(object): # TupleType(elements=[TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), NamedType('%bv16')])
    def eq(self, other):
        assert isinstance(other, Tuple_21)
        if not (self.utup0.eq(other.utup0)): return False # TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
        if not (self.utup1 == other.utup1): return False # NamedType('%bv16')
        return True

class Tuple_22(object): # TupleType(elements=[NamedType('%bv16'), EnumType(name='zjump')])
    def eq(self, other):
        assert isinstance(other, Tuple_22)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv16')
        if not (self.utup1 == other.utup1): return False # EnumType(name='zjump')
        return True

class Tuple_23(object): # TupleType(elements=[NamedType('%unit')])
    def eq(self, other):
        assert isinstance(other, Tuple_23)
        if not (True): return False # NamedType('%unit')
        return True

class Tuple_24(object): # TupleType(elements=[NamedType('%bv64'), NamedType('%bool')])
    def eq(self, other):
        assert isinstance(other, Tuple_24)
        if not (self.utup0 == other.utup0): return False # NamedType('%bv64')
        if not (self.utup1 == other.utup1): return False # NamedType('%bool')
        return True


def model_init(machine):
    pass



class Enum_zjump(object):
    zJDONT = 0
    zJGT = 1
    zJEQ = 2
    zJGE = 3
    zJLT = 4
    zJNE = 5
    zJLE = 6
    zJMP = 7


class Enum_zarithmetic_op(object):
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









def func_zneq_int(machine, zx, zy):
    # zgaz30_lz30: NamedType('%bool')
    # Operation(args=[Var(name='zx'), Var(name='zy')], name='zeq_int', result='zgaz30_lz30')
    zgaz30_lz30 = supportcode.eq_int(machine, zx, zy)
    # Operation(args=[Var(name='zgaz30_lz30')], name='znot_bool', result='return')
    return_ = supportcode.not_(machine, zgaz30_lz30)
    # End()
    return return_












def func_zsail_mask(machine, zlen, zv):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zgaz32_lz30', typ=NamedType('%bool'), value=None)
            # zgaz32_lz30: NamedType('%bool')
            zgaz32_lz30 = False
            # zgaz31_lz31: NamedType('%i')
            # Operation(args=[Var(name='zv')], name='zbitvector_length', result='zgaz31_lz31')
            zgaz31_lz31 = supportcode.length(machine, zv)
            # Operation(args=[Var(name='zlen'), Var(name='zgaz31_lz31')], name='zlteq_int', result='zgaz32_lz30')
            zgaz32_lz30 = supportcode.lteq(machine, zlen, zgaz31_lz31)
            if zgaz32_lz30:
                # inline pc=7
                # Operation(args=[Var(name='zv'), Var(name='zlen')], name='ztruncate', result='return')
                return_ = supportcode.sail_truncate(machine, zv, zlen)
                pc = 8
                continue
            # Operation(args=[Var(name='zv'), Var(name='zlen')], name='zsail_zzero_extend', result='return')
            return_ = supportcode.zero_extend(machine, zv, zlen)
            pc = 8
        if pc == 8:
            # End()
            return return_














def func_zsail_ones(machine, zn):
    # zgaz33_lz30: NamedType('%bv')
    # Operation(args=[Var(name='zn')], name='zsail_zzeros', result='zgaz33_lz30')
    zgaz33_lz30 = supportcode.zeros(machine, zn)
    # Operation(args=[Var(name='zgaz33_lz30')], name='znot_vec', result='return')
    return_ = supportcode.not_bits(machine, zgaz33_lz30)
    # End()
    return return_









def func_zfdiv_int(machine, zn, zm):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zgaz35_lz30', typ=NamedType('%bool'), value=None)
            # zgaz35_lz30: NamedType('%bool')
            zgaz35_lz30 = False
            # LocalVarDeclaration(name='zgaz34_lz314', typ=NamedType('%bool'), value=None)
            # zgaz34_lz314: NamedType('%bool')
            zgaz34_lz314 = False
            # LocalVarDeclaration(name='zgsz30_lz317', typ=NamedType('%i'), value=Number(number=0))
            # zgsz30_lz317: NamedType('%i')
            zgsz30_lz317 = IntConst_0_1
            # Operation(args=[Var(name='zn'), Var(name='zgsz30_lz317')], name='zlt_int', result='zgaz34_lz314')
            zgaz34_lz314 = supportcode.lt(machine, zn, zgsz30_lz317)
            # LocalVarDeclaration(name='zgsz31_lz315', typ=NamedType('%bool'), value=None)
            # zgsz31_lz315: NamedType('%bool')
            zgsz31_lz315 = False
            if zgaz34_lz314:
                # inline pc=8
                # LocalVarDeclaration(name='zgsz32_lz316', typ=NamedType('%i'), value=Number(number=0))
                # zgsz32_lz316: NamedType('%i')
                zgsz32_lz316 = IntConst_0_1
                # Operation(args=[Var(name='zm'), Var(name='zgsz32_lz316')], name='zgt_int', result='zgsz31_lz315')
                zgsz31_lz315 = supportcode.gt(machine, zm, zgsz32_lz316)
                pc = 10
                continue
            # Assignment(result='zgsz31_lz315', value=Var(name='false'))
            zgsz31_lz315 = False
            pc = 10
        if pc == 10:
            # Assignment(result='zgaz35_lz30', value=Var(name='zgsz31_lz315'))
            zgaz35_lz30 = zgsz31_lz315
            if zgaz35_lz30:
                # inline pc=34
                # LocalVarDeclaration(name='zgaz37_lz31', typ=NamedType('%i'), value=None)
                # zgaz37_lz31: NamedType('%i')
                zgaz37_lz31 = UninitInt
                # LocalVarDeclaration(name='zgaz36_lz33', typ=NamedType('%i'), value=None)
                # zgaz36_lz33: NamedType('%i')
                zgaz36_lz33 = UninitInt
                # LocalVarDeclaration(name='zgsz38_lz34', typ=NamedType('%i'), value=Number(number=1))
                # zgsz38_lz34: NamedType('%i')
                zgsz38_lz34 = IntConst_1_1
                # Operation(args=[Var(name='zn'), Var(name='zgsz38_lz34')], name='zadd_atom', result='zgaz36_lz33')
                zgaz36_lz33 = supportcode.add_int(machine, zn, zgsz38_lz34)
                # Operation(args=[Var(name='zgaz36_lz33'), Var(name='zm')], name='ztdiv_int', result='zgaz37_lz31')
                zgaz37_lz31 = supportcode.tdiv_int(machine, zgaz36_lz33, zm)
                # LocalVarDeclaration(name='zgsz39_lz32', typ=NamedType('%i'), value=Number(number=1))
                # zgsz39_lz32: NamedType('%i')
                zgsz39_lz32 = IntConst_1_1
                # Operation(args=[Var(name='zgaz37_lz31'), Var(name='zgsz39_lz32')], name='zsub_atom', result='return')
                return_ = supportcode.sub_int(machine, zgaz37_lz31, zgsz39_lz32)
                pc = 41
                continue
            # LocalVarDeclaration(name='zgaz39_lz35', typ=NamedType('%bool'), value=None)
            # zgaz39_lz35: NamedType('%bool')
            zgaz39_lz35 = False
            # LocalVarDeclaration(name='zgaz38_lz310', typ=NamedType('%bool'), value=None)
            # zgaz38_lz310: NamedType('%bool')
            zgaz38_lz310 = False
            # LocalVarDeclaration(name='zgsz33_lz313', typ=NamedType('%i'), value=Number(number=0))
            # zgsz33_lz313: NamedType('%i')
            zgsz33_lz313 = IntConst_0_1
            # Operation(args=[Var(name='zn'), Var(name='zgsz33_lz313')], name='zgt_int', result='zgaz38_lz310')
            zgaz38_lz310 = supportcode.gt(machine, zn, zgsz33_lz313)
            # LocalVarDeclaration(name='zgsz34_lz311', typ=NamedType('%bool'), value=None)
            # zgsz34_lz311: NamedType('%bool')
            zgsz34_lz311 = False
            if zgaz38_lz310:
                # inline pc=20
                # LocalVarDeclaration(name='zgsz35_lz312', typ=NamedType('%i'), value=Number(number=0))
                # zgsz35_lz312: NamedType('%i')
                zgsz35_lz312 = IntConst_0_1
                # Operation(args=[Var(name='zm'), Var(name='zgsz35_lz312')], name='zlt_int', result='zgsz34_lz311')
                zgsz34_lz311 = supportcode.lt(machine, zm, zgsz35_lz312)
                pc = 22
                continue
            # Assignment(result='zgsz34_lz311', value=Var(name='false'))
            zgsz34_lz311 = False
            pc = 22
        if pc == 22:
            # Assignment(result='zgaz39_lz35', value=Var(name='zgsz34_lz311'))
            zgaz39_lz35 = zgsz34_lz311
            if zgaz39_lz35:
                # inline pc=26
                # LocalVarDeclaration(name='zgaz311_lz36', typ=NamedType('%i'), value=None)
                # zgaz311_lz36: NamedType('%i')
                zgaz311_lz36 = UninitInt
                # LocalVarDeclaration(name='zgaz310_lz38', typ=NamedType('%i'), value=None)
                # zgaz310_lz38: NamedType('%i')
                zgaz310_lz38 = UninitInt
                # LocalVarDeclaration(name='zgsz36_lz39', typ=NamedType('%i'), value=Number(number=1))
                # zgsz36_lz39: NamedType('%i')
                zgsz36_lz39 = IntConst_1_1
                # Operation(args=[Var(name='zn'), Var(name='zgsz36_lz39')], name='zsub_atom', result='zgaz310_lz38')
                zgaz310_lz38 = supportcode.sub_int(machine, zn, zgsz36_lz39)
                # Operation(args=[Var(name='zgaz310_lz38'), Var(name='zm')], name='ztdiv_int', result='zgaz311_lz36')
                zgaz311_lz36 = supportcode.tdiv_int(machine, zgaz310_lz38, zm)
                # LocalVarDeclaration(name='zgsz37_lz37', typ=NamedType('%i'), value=Number(number=1))
                # zgsz37_lz37: NamedType('%i')
                zgsz37_lz37 = IntConst_1_1
                # Operation(args=[Var(name='zgaz311_lz36'), Var(name='zgsz37_lz37')], name='zsub_atom', result='return')
                return_ = supportcode.sub_int(machine, zgaz311_lz36, zgsz37_lz37)
                pc = 33
                continue
            # Operation(args=[Var(name='zn'), Var(name='zm')], name='ztdiv_int', result='return')
            return_ = supportcode.tdiv_int(machine, zn, zm)
            pc = 33
        if pc == 33:
            pc = 41
        if pc == 41:
            # End()
            return return_





def func_zbits1_to_bool(machine, zb):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zgsz310_lz30', typ=NamedType('%bool'), value=None)
            # zgsz310_lz30: NamedType('%bool')
            zgsz310_lz30 = False
            # zb__0_lz33: NamedType('%bv1')
            # Assignment(result='zb__0_lz33', value=Var(name='zb'))
            zb__0_lz33 = zb
            # zgsz311_lz34: NamedType('%bool')
            # Operation(args=[Var(name='zb__0_lz33'), BitVectorConstant(constant='0b1')], name='@eq', result='zgsz311_lz34')
            zgsz311_lz34 = zb__0_lz33 == r_uint(0b1)
            if not zgsz311_lz34:
                # inline pc=7
                pc = 10
                continue
            pc = 8
        if pc == 8:
            # Assignment(result='zgsz310_lz30', value=Var(name='true'))
            zgsz310_lz30 = True
            pc = 20
        if pc == 10:
            # zb__1_lz31: NamedType('%bv1')
            # Assignment(result='zb__1_lz31', value=Var(name='zb'))
            zb__1_lz31 = zb
            # zgsz312_lz32: NamedType('%bool')
            # Operation(args=[Var(name='zb__1_lz31'), BitVectorConstant(constant='0b0')], name='@eq', result='zgsz312_lz32')
            zgsz312_lz32 = zb__1_lz31 == r_uint(0b0)
            if not zgsz312_lz32:
                # inline pc=16
                pc = 19
                continue
            pc = 17
        if pc == 17:
            # Assignment(result='zgsz310_lz30', value=Var(name='false'))
            zgsz310_lz30 = False
            pc = 20
        if pc == 19:
            # Failure()
            raise TypeError
        if pc == 20:
            # Assignment(result='return', value=Var(name='zgsz310_lz30'))
            return_ = zgsz310_lz30
            # End()
            return return_











def func_zdecode_compute_backwards(machine, zargz3):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zgsz313_lz30', typ=EnumType(name='zarithmetic_op'), value=None)
            # zgsz313_lz30: EnumType(name='zarithmetic_op')
            zgsz313_lz30 = -1
            # zb__0_lz335: NamedType('%bv6')
            # Assignment(result='zb__0_lz335', value=Var(name='zargz3'))
            zb__0_lz335 = zargz3
            # zgsz314_lz336: NamedType('%bool')
            # Operation(args=[Var(name='zb__0_lz335'), BitVectorConstant(constant='0b101010')], name='@eq', result='zgsz314_lz336')
            zgsz314_lz336 = zb__0_lz335 == r_uint(0b101010)
            if not zgsz314_lz336:
                # inline pc=7
                pc = 10
                continue
            pc = 8
        if pc == 8:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_ZERO'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_ZERO
            pc = 164
        if pc == 10:
            # zb__1_lz333: NamedType('%bv6')
            # Assignment(result='zb__1_lz333', value=Var(name='zargz3'))
            zb__1_lz333 = zargz3
            # zgsz315_lz334: NamedType('%bool')
            # Operation(args=[Var(name='zb__1_lz333'), BitVectorConstant(constant='0b111111')], name='@eq', result='zgsz315_lz334')
            zgsz315_lz334 = zb__1_lz333 == r_uint(0b111111)
            if not zgsz315_lz334:
                # inline pc=16
                pc = 19
                continue
            pc = 17
        if pc == 17:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_ONE'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_ONE
            pc = 164
        if pc == 19:
            # zb__2_lz331: NamedType('%bv6')
            # Assignment(result='zb__2_lz331', value=Var(name='zargz3'))
            zb__2_lz331 = zargz3
            # zgsz316_lz332: NamedType('%bool')
            # Operation(args=[Var(name='zb__2_lz331'), BitVectorConstant(constant='0b111010')], name='@eq', result='zgsz316_lz332')
            zgsz316_lz332 = zb__2_lz331 == r_uint(0b111010)
            if not zgsz316_lz332:
                # inline pc=25
                pc = 28
                continue
            pc = 26
        if pc == 26:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_MINUSONE'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_MINUSONE
            pc = 164
        if pc == 28:
            # zb__3_lz329: NamedType('%bv6')
            # Assignment(result='zb__3_lz329', value=Var(name='zargz3'))
            zb__3_lz329 = zargz3
            # zgsz317_lz330: NamedType('%bool')
            # Operation(args=[Var(name='zb__3_lz329'), BitVectorConstant(constant='0b001100')], name='@eq', result='zgsz317_lz330')
            zgsz317_lz330 = zb__3_lz329 == r_uint(0b001100)
            if not zgsz317_lz330:
                # inline pc=34
                pc = 37
                continue
            pc = 35
        if pc == 35:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_D'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_D
            pc = 164
        if pc == 37:
            # zb__4_lz327: NamedType('%bv6')
            # Assignment(result='zb__4_lz327', value=Var(name='zargz3'))
            zb__4_lz327 = zargz3
            # zgsz318_lz328: NamedType('%bool')
            # Operation(args=[Var(name='zb__4_lz327'), BitVectorConstant(constant='0b110000')], name='@eq', result='zgsz318_lz328')
            zgsz318_lz328 = zb__4_lz327 == r_uint(0b110000)
            if not zgsz318_lz328:
                # inline pc=43
                pc = 46
                continue
            pc = 44
        if pc == 44:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_A'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_A
            pc = 164
        if pc == 46:
            # zb__5_lz325: NamedType('%bv6')
            # Assignment(result='zb__5_lz325', value=Var(name='zargz3'))
            zb__5_lz325 = zargz3
            # zgsz319_lz326: NamedType('%bool')
            # Operation(args=[Var(name='zb__5_lz325'), BitVectorConstant(constant='0b001101')], name='@eq', result='zgsz319_lz326')
            zgsz319_lz326 = zb__5_lz325 == r_uint(0b001101)
            if not zgsz319_lz326:
                # inline pc=52
                pc = 55
                continue
            pc = 53
        if pc == 53:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_NOT_D'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_NOT_D
            pc = 164
        if pc == 55:
            # zb__6_lz323: NamedType('%bv6')
            # Assignment(result='zb__6_lz323', value=Var(name='zargz3'))
            zb__6_lz323 = zargz3
            # zgsz320_lz324: NamedType('%bool')
            # Operation(args=[Var(name='zb__6_lz323'), BitVectorConstant(constant='0b110001')], name='@eq', result='zgsz320_lz324')
            zgsz320_lz324 = zb__6_lz323 == r_uint(0b110001)
            if not zgsz320_lz324:
                # inline pc=61
                pc = 64
                continue
            pc = 62
        if pc == 62:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_NOT_A'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_NOT_A
            pc = 164
        if pc == 64:
            # zb__7_lz321: NamedType('%bv6')
            # Assignment(result='zb__7_lz321', value=Var(name='zargz3'))
            zb__7_lz321 = zargz3
            # zgsz321_lz322: NamedType('%bool')
            # Operation(args=[Var(name='zb__7_lz321'), BitVectorConstant(constant='0b001111')], name='@eq', result='zgsz321_lz322')
            zgsz321_lz322 = zb__7_lz321 == r_uint(0b001111)
            if not zgsz321_lz322:
                # inline pc=70
                pc = 73
                continue
            pc = 71
        if pc == 71:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_NEG_D'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_NEG_D
            pc = 164
        if pc == 73:
            # zb__8_lz319: NamedType('%bv6')
            # Assignment(result='zb__8_lz319', value=Var(name='zargz3'))
            zb__8_lz319 = zargz3
            # zgsz322_lz320: NamedType('%bool')
            # Operation(args=[Var(name='zb__8_lz319'), BitVectorConstant(constant='0b110011')], name='@eq', result='zgsz322_lz320')
            zgsz322_lz320 = zb__8_lz319 == r_uint(0b110011)
            if not zgsz322_lz320:
                # inline pc=79
                pc = 82
                continue
            pc = 80
        if pc == 80:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_NEG_A'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_NEG_A
            pc = 164
        if pc == 82:
            # zb__9_lz317: NamedType('%bv6')
            # Assignment(result='zb__9_lz317', value=Var(name='zargz3'))
            zb__9_lz317 = zargz3
            # zgsz323_lz318: NamedType('%bool')
            # Operation(args=[Var(name='zb__9_lz317'), BitVectorConstant(constant='0b011111')], name='@eq', result='zgsz323_lz318')
            zgsz323_lz318 = zb__9_lz317 == r_uint(0b011111)
            if not zgsz323_lz318:
                # inline pc=88
                pc = 91
                continue
            pc = 89
        if pc == 89:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_D_ADD_1'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_D_ADD_1
            pc = 164
        if pc == 91:
            # zb__10_lz315: NamedType('%bv6')
            # Assignment(result='zb__10_lz315', value=Var(name='zargz3'))
            zb__10_lz315 = zargz3
            # zgsz324_lz316: NamedType('%bool')
            # Operation(args=[Var(name='zb__10_lz315'), BitVectorConstant(constant='0b110111')], name='@eq', result='zgsz324_lz316')
            zgsz324_lz316 = zb__10_lz315 == r_uint(0b110111)
            if not zgsz324_lz316:
                # inline pc=97
                pc = 100
                continue
            pc = 98
        if pc == 98:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_A_ADD_1'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_A_ADD_1
            pc = 164
        if pc == 100:
            # zb__11_lz313: NamedType('%bv6')
            # Assignment(result='zb__11_lz313', value=Var(name='zargz3'))
            zb__11_lz313 = zargz3
            # zgsz325_lz314: NamedType('%bool')
            # Operation(args=[Var(name='zb__11_lz313'), BitVectorConstant(constant='0b001110')], name='@eq', result='zgsz325_lz314')
            zgsz325_lz314 = zb__11_lz313 == r_uint(0b001110)
            if not zgsz325_lz314:
                # inline pc=106
                pc = 109
                continue
            pc = 107
        if pc == 107:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_D_SUB_1'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_D_SUB_1
            pc = 164
        if pc == 109:
            # zb__12_lz311: NamedType('%bv6')
            # Assignment(result='zb__12_lz311', value=Var(name='zargz3'))
            zb__12_lz311 = zargz3
            # zgsz326_lz312: NamedType('%bool')
            # Operation(args=[Var(name='zb__12_lz311'), BitVectorConstant(constant='0b110010')], name='@eq', result='zgsz326_lz312')
            zgsz326_lz312 = zb__12_lz311 == r_uint(0b110010)
            if not zgsz326_lz312:
                # inline pc=115
                pc = 118
                continue
            pc = 116
        if pc == 116:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_A_SUB_1'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_A_SUB_1
            pc = 164
        if pc == 118:
            # zb__13_lz39: NamedType('%bv6')
            # Assignment(result='zb__13_lz39', value=Var(name='zargz3'))
            zb__13_lz39 = zargz3
            # zgsz327_lz310: NamedType('%bool')
            # Operation(args=[Var(name='zb__13_lz39'), BitVectorConstant(constant='0b000010')], name='@eq', result='zgsz327_lz310')
            zgsz327_lz310 = zb__13_lz39 == r_uint(0b000010)
            if not zgsz327_lz310:
                # inline pc=124
                pc = 127
                continue
            pc = 125
        if pc == 125:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_D_ADD_A'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_D_ADD_A
            pc = 164
        if pc == 127:
            # zb__14_lz37: NamedType('%bv6')
            # Assignment(result='zb__14_lz37', value=Var(name='zargz3'))
            zb__14_lz37 = zargz3
            # zgsz328_lz38: NamedType('%bool')
            # Operation(args=[Var(name='zb__14_lz37'), BitVectorConstant(constant='0b010011')], name='@eq', result='zgsz328_lz38')
            zgsz328_lz38 = zb__14_lz37 == r_uint(0b010011)
            if not zgsz328_lz38:
                # inline pc=133
                pc = 136
                continue
            pc = 134
        if pc == 134:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_D_SUB_A'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_D_SUB_A
            pc = 164
        if pc == 136:
            # zb__15_lz35: NamedType('%bv6')
            # Assignment(result='zb__15_lz35', value=Var(name='zargz3'))
            zb__15_lz35 = zargz3
            # zgsz329_lz36: NamedType('%bool')
            # Operation(args=[Var(name='zb__15_lz35'), BitVectorConstant(constant='0b000111')], name='@eq', result='zgsz329_lz36')
            zgsz329_lz36 = zb__15_lz35 == r_uint(0b000111)
            if not zgsz329_lz36:
                # inline pc=142
                pc = 145
                continue
            pc = 143
        if pc == 143:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_A_SUB_D'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_A_SUB_D
            pc = 164
        if pc == 145:
            # zb__16_lz33: NamedType('%bv6')
            # Assignment(result='zb__16_lz33', value=Var(name='zargz3'))
            zb__16_lz33 = zargz3
            # zgsz330_lz34: NamedType('%bool')
            # Operation(args=[Var(name='zb__16_lz33'), BitVectorConstant(constant='0b000000')], name='@eq', result='zgsz330_lz34')
            zgsz330_lz34 = zb__16_lz33 == r_uint(0b000000)
            if not zgsz330_lz34:
                # inline pc=151
                pc = 154
                continue
            pc = 152
        if pc == 152:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_D_AND_A'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_D_AND_A
            pc = 164
        if pc == 154:
            # zb__17_lz31: NamedType('%bv6')
            # Assignment(result='zb__17_lz31', value=Var(name='zargz3'))
            zb__17_lz31 = zargz3
            # zgsz331_lz32: NamedType('%bool')
            # Operation(args=[Var(name='zb__17_lz31'), BitVectorConstant(constant='0b010101')], name='@eq', result='zgsz331_lz32')
            zgsz331_lz32 = zb__17_lz31 == r_uint(0b010101)
            if not zgsz331_lz32:
                # inline pc=160
                pc = 163
                continue
            pc = 161
        if pc == 161:
            # Assignment(result='zgsz313_lz30', value=Var(name='zC_D_OR_A'))
            zgsz313_lz30 = Enum_zarithmetic_op.zC_D_OR_A
            pc = 164
        if pc == 163:
            # Failure()
            raise TypeError
        if pc == 164:
            # Assignment(result='return', value=Var(name='zgsz313_lz30'))
            return_ = zgsz313_lz30
            # End()
            return return_




def func_zdecode_jump_backwards(machine, zargz3):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zgsz332_lz30', typ=EnumType(name='zjump'), value=None)
            # zgsz332_lz30: EnumType(name='zjump')
            zgsz332_lz30 = -1
            # zb__0_lz315: NamedType('%bv3')
            # Assignment(result='zb__0_lz315', value=Var(name='zargz3'))
            zb__0_lz315 = zargz3
            # zgsz333_lz316: NamedType('%bool')
            # Operation(args=[Var(name='zb__0_lz315'), BitVectorConstant(constant='0b000')], name='@eq', result='zgsz333_lz316')
            zgsz333_lz316 = zb__0_lz315 == r_uint(0b000)
            if not zgsz333_lz316:
                # inline pc=7
                pc = 10
                continue
            pc = 8
        if pc == 8:
            # Assignment(result='zgsz332_lz30', value=Var(name='zJDONT'))
            zgsz332_lz30 = Enum_zjump.zJDONT
            pc = 74
        if pc == 10:
            # zb__1_lz313: NamedType('%bv3')
            # Assignment(result='zb__1_lz313', value=Var(name='zargz3'))
            zb__1_lz313 = zargz3
            # zgsz334_lz314: NamedType('%bool')
            # Operation(args=[Var(name='zb__1_lz313'), BitVectorConstant(constant='0b001')], name='@eq', result='zgsz334_lz314')
            zgsz334_lz314 = zb__1_lz313 == r_uint(0b001)
            if not zgsz334_lz314:
                # inline pc=16
                pc = 19
                continue
            pc = 17
        if pc == 17:
            # Assignment(result='zgsz332_lz30', value=Var(name='zJGT'))
            zgsz332_lz30 = Enum_zjump.zJGT
            pc = 74
        if pc == 19:
            # zb__2_lz311: NamedType('%bv3')
            # Assignment(result='zb__2_lz311', value=Var(name='zargz3'))
            zb__2_lz311 = zargz3
            # zgsz335_lz312: NamedType('%bool')
            # Operation(args=[Var(name='zb__2_lz311'), BitVectorConstant(constant='0b010')], name='@eq', result='zgsz335_lz312')
            zgsz335_lz312 = zb__2_lz311 == r_uint(0b010)
            if not zgsz335_lz312:
                # inline pc=25
                pc = 28
                continue
            pc = 26
        if pc == 26:
            # Assignment(result='zgsz332_lz30', value=Var(name='zJEQ'))
            zgsz332_lz30 = Enum_zjump.zJEQ
            pc = 74
        if pc == 28:
            # zb__3_lz39: NamedType('%bv3')
            # Assignment(result='zb__3_lz39', value=Var(name='zargz3'))
            zb__3_lz39 = zargz3
            # zgsz336_lz310: NamedType('%bool')
            # Operation(args=[Var(name='zb__3_lz39'), BitVectorConstant(constant='0b011')], name='@eq', result='zgsz336_lz310')
            zgsz336_lz310 = zb__3_lz39 == r_uint(0b011)
            if not zgsz336_lz310:
                # inline pc=34
                pc = 37
                continue
            pc = 35
        if pc == 35:
            # Assignment(result='zgsz332_lz30', value=Var(name='zJGE'))
            zgsz332_lz30 = Enum_zjump.zJGE
            pc = 74
        if pc == 37:
            # zb__4_lz37: NamedType('%bv3')
            # Assignment(result='zb__4_lz37', value=Var(name='zargz3'))
            zb__4_lz37 = zargz3
            # zgsz337_lz38: NamedType('%bool')
            # Operation(args=[Var(name='zb__4_lz37'), BitVectorConstant(constant='0b100')], name='@eq', result='zgsz337_lz38')
            zgsz337_lz38 = zb__4_lz37 == r_uint(0b100)
            if not zgsz337_lz38:
                # inline pc=43
                pc = 46
                continue
            pc = 44
        if pc == 44:
            # Assignment(result='zgsz332_lz30', value=Var(name='zJLT'))
            zgsz332_lz30 = Enum_zjump.zJLT
            pc = 74
        if pc == 46:
            # zb__5_lz35: NamedType('%bv3')
            # Assignment(result='zb__5_lz35', value=Var(name='zargz3'))
            zb__5_lz35 = zargz3
            # zgsz338_lz36: NamedType('%bool')
            # Operation(args=[Var(name='zb__5_lz35'), BitVectorConstant(constant='0b101')], name='@eq', result='zgsz338_lz36')
            zgsz338_lz36 = zb__5_lz35 == r_uint(0b101)
            if not zgsz338_lz36:
                # inline pc=52
                pc = 55
                continue
            pc = 53
        if pc == 53:
            # Assignment(result='zgsz332_lz30', value=Var(name='zJNE'))
            zgsz332_lz30 = Enum_zjump.zJNE
            pc = 74
        if pc == 55:
            # zb__6_lz33: NamedType('%bv3')
            # Assignment(result='zb__6_lz33', value=Var(name='zargz3'))
            zb__6_lz33 = zargz3
            # zgsz339_lz34: NamedType('%bool')
            # Operation(args=[Var(name='zb__6_lz33'), BitVectorConstant(constant='0b110')], name='@eq', result='zgsz339_lz34')
            zgsz339_lz34 = zb__6_lz33 == r_uint(0b110)
            if not zgsz339_lz34:
                # inline pc=61
                pc = 64
                continue
            pc = 62
        if pc == 62:
            # Assignment(result='zgsz332_lz30', value=Var(name='zJLE'))
            zgsz332_lz30 = Enum_zjump.zJLE
            pc = 74
        if pc == 64:
            # zb__7_lz31: NamedType('%bv3')
            # Assignment(result='zb__7_lz31', value=Var(name='zargz3'))
            zb__7_lz31 = zargz3
            # zgsz340_lz32: NamedType('%bool')
            # Operation(args=[Var(name='zb__7_lz31'), BitVectorConstant(constant='0b111')], name='@eq', result='zgsz340_lz32')
            zgsz340_lz32 = zb__7_lz31 == r_uint(0b111)
            if not zgsz340_lz32:
                # inline pc=70
                pc = 73
                continue
            pc = 71
        if pc == 71:
            # Assignment(result='zgsz332_lz30', value=Var(name='zJMP'))
            zgsz332_lz30 = Enum_zjump.zJMP
            pc = 74
        if pc == 73:
            # Failure()
            raise TypeError
        if pc == 74:
            # Assignment(result='return', value=Var(name='zgsz332_lz30'))
            return_ = zgsz332_lz30
            # End()
            return return_






def func_zdecode_destination(machine, zb):
    # LocalVarDeclaration(name='zgsz341_lz30', typ=TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), value=None)
    # zgsz341_lz30: TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
    zgsz341_lz30 = Tuple_1()
    # zv__0_lz31: NamedType('%bv3')
    # Assignment(result='zv__0_lz31', value=Var(name='zb'))
    zv__0_lz31 = zb
    # LocalVarDeclaration(name='za_lz32', typ=NamedType('%bv1'), value=None)
    # za_lz32: NamedType('%bv1')
    za_lz32 = r_uint(0)
    # TemplatedOperation(args=[Var(name='zv__0_lz31'), Number(number=2)], name='@slice', result='za_lz32', templateparam=Number(number=1))
    za_lz32 = (supportcode.safe_rshift(machine, zv__0_lz31, 2)) & r_uint(0x1)
    # LocalVarDeclaration(name='zm_lz33', typ=NamedType('%bv1'), value=None)
    # zm_lz33: NamedType('%bv1')
    zm_lz33 = r_uint(0)
    # TemplatedOperation(args=[Var(name='zv__0_lz31'), Number(number=0)], name='@slice', result='zm_lz33', templateparam=Number(number=1))
    zm_lz33 = (zv__0_lz31) & r_uint(0x1)
    # LocalVarDeclaration(name='zd_lz34', typ=NamedType('%bv1'), value=None)
    # zd_lz34: NamedType('%bv1')
    zd_lz34 = r_uint(0)
    # TemplatedOperation(args=[Var(name='zv__0_lz31'), Number(number=1)], name='@slice', result='zd_lz34', templateparam=Number(number=1))
    zd_lz34 = (supportcode.safe_rshift(machine, zv__0_lz31, 1)) & r_uint(0x1)
    # LocalVarDeclaration(name='zashadowz30_lz35', typ=NamedType('%bv1'), value=None)
    # zashadowz30_lz35: NamedType('%bv1')
    zashadowz30_lz35 = r_uint(0)
    # TemplatedOperation(args=[Var(name='zv__0_lz31'), Number(number=2)], name='@slice', result='zashadowz30_lz35', templateparam=Number(number=1))
    zashadowz30_lz35 = (supportcode.safe_rshift(machine, zv__0_lz31, 2)) & r_uint(0x1)
    # zgaz312_lz36: NamedType('%bool')
    # Operation(args=[Var(name='zashadowz30_lz35')], name='zbits1_to_bool', result='zgaz312_lz36')
    zgaz312_lz36 = func_zbits1_to_bool(machine, zashadowz30_lz35)
    # zgaz313_lz37: NamedType('%bool')
    # Operation(args=[Var(name='zd_lz34')], name='zbits1_to_bool', result='zgaz313_lz37')
    zgaz313_lz37 = func_zbits1_to_bool(machine, zd_lz34)
    # zgaz314_lz38: NamedType('%bool')
    # Operation(args=[Var(name='zm_lz33')], name='zbits1_to_bool', result='zgaz314_lz38')
    zgaz314_lz38 = func_zbits1_to_bool(machine, zm_lz33)
    # LocalVarDeclaration(name='zgsz342_lz39', typ=TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), value=None)
    # zgsz342_lz39: TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
    zgsz342_lz39 = Tuple_1()
    # TupleElementAssignment(index=0, tup='zgsz342_lz39', value=Var(name='zgaz312_lz36'))
    zgsz342_lz39.ztup0 = zgaz312_lz36
    # TupleElementAssignment(index=1, tup='zgsz342_lz39', value=Var(name='zgaz313_lz37'))
    zgsz342_lz39.ztup1 = zgaz313_lz37
    # TupleElementAssignment(index=2, tup='zgsz342_lz39', value=Var(name='zgaz314_lz38'))
    zgsz342_lz39.ztup2 = zgaz314_lz38
    # Assignment(result='zgsz341_lz30', value=Var(name='zgsz342_lz39'))
    zgsz341_lz30 = zgsz342_lz39
    # Assignment(result='return', value=Var(name='zgsz341_lz30'))
    return_ = zgsz341_lz30
    # End()
    return return_



def func_zdecode(machine, zmergez3var):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zgsz344_lz30', typ=UnionType(name='zoption'), value=None)
            # zgsz344_lz30: UnionType(name='zoption')
            zgsz344_lz30 = Union_zoption()
            # zv__1_lz315: NamedType('%bv16')
            # Assignment(result='zv__1_lz315', value=Var(name='zmergez3var'))
            zv__1_lz315 = zmergez3var
            # LocalVarDeclaration(name='zgaz317_lz316', typ=NamedType('%bv1'), value=None)
            # zgaz317_lz316: NamedType('%bv1')
            zgaz317_lz316 = r_uint(0)
            # TemplatedOperation(args=[Var(name='zv__1_lz315'), Number(number=15)], name='@slice', result='zgaz317_lz316', templateparam=Number(number=1))
            zgaz317_lz316 = (supportcode.safe_rshift(machine, zv__1_lz315, 15)) & r_uint(0x1)
            # zgsz348_lz317: NamedType('%bool')
            # Operation(args=[Var(name='zgaz317_lz316'), BitVectorConstant(constant='0b0')], name='@eq', result='zgsz348_lz317')
            zgsz348_lz317 = zgaz317_lz316 == r_uint(0b0)
            if not zgsz348_lz317:
                # inline pc=9
                pc = 24
                continue
            pc = 10
        if pc == 10:
            # LocalVarDeclaration(name='zx_lz318', typ=NamedType('%bv15'), value=None)
            # zx_lz318: NamedType('%bv15')
            zx_lz318 = r_uint(0)
            # TemplatedOperation(args=[Var(name='zv__1_lz315'), Number(number=0)], name='@slice', result='zx_lz318', templateparam=Number(number=15))
            zx_lz318 = (zv__1_lz315) & r_uint(0x7fff)
            # LocalVarDeclaration(name='zgaz316_lz319', typ=UnionType(name='zinstr'), value=None)
            # zgaz316_lz319: UnionType(name='zinstr')
            zgaz316_lz319 = Union_zinstr()
            # LocalVarDeclaration(name='zgaz315_lz321', typ=NamedType('%bv16'), value=None)
            # zgaz315_lz321: NamedType('%bv16')
            zgaz315_lz321 = r_uint(0)
            # LocalVarDeclaration(name='zgsz345_lz322', typ=NamedType('%bv'), value=Var(name='zx_lz318'))
            # zgsz345_lz322: NamedType('%bv')
            zgsz345_lz322 = bitvector.from_ruint(15, zx_lz318)
            # LocalVarDeclaration(name='zgsz346_lz323', typ=NamedType('%i'), value=Number(number=16))
            # zgsz346_lz323: NamedType('%i')
            zgsz346_lz323 = IntConst_16_1
            # zgsz347_lz324: NamedType('%bv')
            # Operation(args=[Var(name='zgsz345_lz322'), Var(name='zgsz346_lz323')], name='zsail_zzero_extend', result='zgsz347_lz324')
            zgsz347_lz324 = supportcode.zero_extend(machine, zgsz345_lz322, zgsz346_lz323)
            # Assignment(result='zgaz315_lz321', value=Var(name='zgsz347_lz324'))
            zgaz315_lz321 = zgsz347_lz324.touint()
            # Operation(args=[Var(name='zgaz315_lz321')], name='zAINST', result='zgaz316_lz319')
            zgaz316_lz319 = Union_zinstr_zAINST(zgaz315_lz321)
            # zgsz3111_lz320: UnionType(name='zinstr')
            # Assignment(result='zgsz3111_lz320', value=Var(name='zgaz316_lz319'))
            zgsz3111_lz320 = zgaz316_lz319
            # Operation(args=[Var(name='zgsz3111_lz320')], name='zSomez3z5unionz0zzinstr', result='zgsz344_lz30')
            zgsz344_lz30 = Union_zoption_zSomez3z5unionz0zzinstr(zgsz3111_lz320)
            pc = 61
        if pc == 24:
            # zv__3_lz31: NamedType('%bv16')
            # Assignment(result='zv__3_lz31', value=Var(name='zmergez3var'))
            zv__3_lz31 = zmergez3var
            # LocalVarDeclaration(name='zgaz323_lz32', typ=NamedType('%bv3'), value=None)
            # zgaz323_lz32: NamedType('%bv3')
            zgaz323_lz32 = r_uint(0)
            # TemplatedOperation(args=[Var(name='zv__3_lz31'), Number(number=13)], name='@slice', result='zgaz323_lz32', templateparam=Number(number=3))
            zgaz323_lz32 = (supportcode.safe_rshift(machine, zv__3_lz31, 13)) & r_uint(0x7)
            # zgsz350_lz33: NamedType('%bool')
            # Operation(args=[Var(name='zgaz323_lz32'), BitVectorConstant(constant='0b111')], name='@eq', result='zgsz350_lz33')
            zgsz350_lz33 = zgaz323_lz32 == r_uint(0b111)
            if not zgsz350_lz33:
                # inline pc=32
                pc = 60
                continue
            pc = 33
        if pc == 33:
            # LocalVarDeclaration(name='zjump_lz34', typ=NamedType('%bv3'), value=None)
            # zjump_lz34: NamedType('%bv3')
            zjump_lz34 = r_uint(0)
            # TemplatedOperation(args=[Var(name='zv__3_lz31'), Number(number=0)], name='@slice', result='zjump_lz34', templateparam=Number(number=3))
            zjump_lz34 = (zv__3_lz31) & r_uint(0x7)
            # LocalVarDeclaration(name='zdest_lz35', typ=NamedType('%bv3'), value=None)
            # zdest_lz35: NamedType('%bv3')
            zdest_lz35 = r_uint(0)
            # TemplatedOperation(args=[Var(name='zv__3_lz31'), Number(number=3)], name='@slice', result='zdest_lz35', templateparam=Number(number=3))
            zdest_lz35 = (supportcode.safe_rshift(machine, zv__3_lz31, 3)) & r_uint(0x7)
            # LocalVarDeclaration(name='zc_lz36', typ=NamedType('%bv6'), value=None)
            # zc_lz36: NamedType('%bv6')
            zc_lz36 = r_uint(0)
            # TemplatedOperation(args=[Var(name='zv__3_lz31'), Number(number=6)], name='@slice', result='zc_lz36', templateparam=Number(number=6))
            zc_lz36 = (supportcode.safe_rshift(machine, zv__3_lz31, 6)) & r_uint(0x3f)
            # LocalVarDeclaration(name='za_lz37', typ=NamedType('%bv1'), value=None)
            # za_lz37: NamedType('%bv1')
            za_lz37 = r_uint(0)
            # TemplatedOperation(args=[Var(name='zv__3_lz31'), Number(number=12)], name='@slice', result='za_lz37', templateparam=Number(number=1))
            za_lz37 = (supportcode.safe_rshift(machine, zv__3_lz31, 12)) & r_uint(0x1)
            # LocalVarDeclaration(name='zgaz322_lz38', typ=UnionType(name='zinstr'), value=None)
            # zgaz322_lz38: UnionType(name='zinstr')
            zgaz322_lz38 = Union_zinstr()
            # LocalVarDeclaration(name='zgaz321_lz310', typ=TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op'), TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), EnumType(name='zjump')]), value=None)
            # zgaz321_lz310: TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op'), TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), EnumType(name='zjump')])
            zgaz321_lz310 = Tuple_2()
            # zgaz318_lz311: EnumType(name='zarithmetic_op')
            # Operation(args=[Var(name='zc_lz36')], name='zdecode_compute_backwards', result='zgaz318_lz311')
            zgaz318_lz311 = func_zdecode_compute_backwards(machine, zc_lz36)
            # zgaz319_lz312: TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
            # Operation(args=[Var(name='zdest_lz35')], name='zdecode_destination', result='zgaz319_lz312')
            zgaz319_lz312 = func_zdecode_destination(machine, zdest_lz35)
            # zgaz320_lz313: EnumType(name='zjump')
            # Operation(args=[Var(name='zjump_lz34')], name='zdecode_jump_backwards', result='zgaz320_lz313')
            zgaz320_lz313 = func_zdecode_jump_backwards(machine, zjump_lz34)
            # LocalVarDeclaration(name='zgsz349_lz314', typ=TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op'), TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), EnumType(name='zjump')]), value=None)
            # zgsz349_lz314: TupleType(elements=[NamedType('%bv1'), EnumType(name='zarithmetic_op'), TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')]), EnumType(name='zjump')])
            zgsz349_lz314 = Tuple_2()
            # TupleElementAssignment(index=0, tup='zgsz349_lz314', value=Var(name='za_lz37'))
            zgsz349_lz314.ztup0 = za_lz37
            # TupleElementAssignment(index=1, tup='zgsz349_lz314', value=Var(name='zgaz318_lz311'))
            zgsz349_lz314.ztup1 = zgaz318_lz311
            # TupleElementAssignment(index=2, tup='zgsz349_lz314', value=Var(name='zgaz319_lz312'))
            zgsz349_lz314.ztup2 = zgaz319_lz312
            # TupleElementAssignment(index=3, tup='zgsz349_lz314', value=Var(name='zgaz320_lz313'))
            zgsz349_lz314.ztup3 = zgaz320_lz313
            # Assignment(result='zgaz321_lz310', value=Var(name='zgsz349_lz314'))
            zgaz321_lz310 = zgsz349_lz314
            # Operation(args=[Var(name='zgaz321_lz310')], name='zCINST', result='zgaz322_lz38')
            zgaz322_lz38 = Union_zinstr_zCINST(zgaz321_lz310)
            # zgsz3112_lz39: UnionType(name='zinstr')
            # Assignment(result='zgsz3112_lz39', value=Var(name='zgaz322_lz38'))
            zgsz3112_lz39 = zgaz322_lz38
            # Operation(args=[Var(name='zgsz3112_lz39')], name='zSomez3z5unionz0zzinstr', result='zgsz344_lz30')
            zgsz344_lz30 = Union_zoption_zSomez3z5unionz0zzinstr(zgsz3112_lz39)
            pc = 61
        if pc == 60:
            # Operation(args=[Unit()], name='zNone', result='zgsz344_lz30')
            zgsz344_lz30 = Union_zoption_zNone(())
            pc = 61
        if pc == 61:
            # Assignment(result='return', value=Var(name='zgsz344_lz30'))
            return_ = zgsz344_lz30
            # End()
            return return_




def func_zcompute_value(machine, za, zop):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zashadowz31_lz30', typ=NamedType('%bv16'), value=None)
            # zashadowz31_lz30: NamedType('%bv16')
            zashadowz31_lz30 = r_uint(0)
            # zgaz324_lz34: NamedType('%bool')
            # Operation(args=[Var(name='za'), BitVectorConstant(constant='0b0')], name='@eq', result='zgaz324_lz34')
            zgaz324_lz34 = za == r_uint(0b0)
            if zgaz324_lz34:
                # inline pc=6
                # Assignment(result='zashadowz31_lz30', value=Var(name='zA'))
                zashadowz31_lz30 = machine.r.zA
                pc = 7
                continue
            # Operation(args=[Var(name='zA')], name='zread_mem', result='zashadowz31_lz30')
            zashadowz31_lz30 = supportcode.my_read_mem(machine, machine.r.zA)
            pc = 7
        if pc == 7:
            # zd_lz31: NamedType('%bv16')
            # Assignment(result='zd_lz31', value=Var(name='zD'))
            zd_lz31 = machine.r.zD
            # LocalVarDeclaration(name='zresult_lz32', typ=NamedType('%bv16'), value=None)
            # zresult_lz32: NamedType('%bv16')
            zresult_lz32 = r_uint(0)
            # LocalVarDeclaration(name='zgsz352_lz33', typ=NamedType('%bv16'), value=None)
            # zgsz352_lz33: NamedType('%bv16')
            zgsz352_lz33 = r_uint(0)
            if not (Enum_zarithmetic_op.zC_ZERO == zop):
                # inline pc=14
                if not (Enum_zarithmetic_op.zC_ONE == zop):
                    # inline pc=17
                    if not (Enum_zarithmetic_op.zC_MINUSONE == zop):
                        # inline pc=20
                        if not (Enum_zarithmetic_op.zC_D == zop):
                            # inline pc=23
                            if not (Enum_zarithmetic_op.zC_A == zop):
                                # inline pc=26
                                if not (Enum_zarithmetic_op.zC_NOT_D == zop):
                                    # inline pc=29
                                    if not (Enum_zarithmetic_op.zC_NOT_A == zop):
                                        # inline pc=32
                                        if not (Enum_zarithmetic_op.zC_NEG_D == zop):
                                            # inline pc=35
                                            if not (Enum_zarithmetic_op.zC_NEG_A == zop):
                                                # inline pc=38
                                                if not (Enum_zarithmetic_op.zC_D_ADD_1 == zop):
                                                    # inline pc=41
                                                    if not (Enum_zarithmetic_op.zC_A_ADD_1 == zop):
                                                        # inline pc=44
                                                        if not (Enum_zarithmetic_op.zC_D_SUB_1 == zop):
                                                            # inline pc=47
                                                            if not (Enum_zarithmetic_op.zC_A_SUB_1 == zop):
                                                                # inline pc=50
                                                                if not (Enum_zarithmetic_op.zC_D_ADD_A == zop):
                                                                    # inline pc=53
                                                                    if not (Enum_zarithmetic_op.zC_D_SUB_A == zop):
                                                                        # inline pc=56
                                                                        if not (Enum_zarithmetic_op.zC_A_SUB_D == zop):
                                                                            # inline pc=59
                                                                            if not (Enum_zarithmetic_op.zC_D_AND_A == zop):
                                                                                # inline pc=62
                                                                                if not (Enum_zarithmetic_op.zC_D_OR_A == zop):
                                                                                    # inline pc=65
                                                                                    # Failure()
                                                                                    raise TypeError
                                                                                    continue
                                                                                # Operation(args=[Var(name='zd_lz31'), Var(name='zashadowz31_lz30')], name='@bvor', result='zgsz352_lz33')
                                                                                zgsz352_lz33 = (zd_lz31 | zashadowz31_lz30) & r_uint(0xffff)
                                                                                pc = 66
                                                                                continue
                                                                            # Operation(args=[Var(name='zd_lz31'), Var(name='zashadowz31_lz30')], name='@bvand', result='zgsz352_lz33')
                                                                            zgsz352_lz33 = (zd_lz31 & zashadowz31_lz30) & r_uint(0xffff)
                                                                            pc = 66
                                                                            continue
                                                                        # Operation(args=[Var(name='zashadowz31_lz30'), Var(name='zd_lz31')], name='@bvsub', result='zgsz352_lz33')
                                                                        zgsz352_lz33 = (zashadowz31_lz30 - zd_lz31) & r_uint(0xffff)
                                                                        pc = 66
                                                                        continue
                                                                    # Operation(args=[Var(name='zd_lz31'), Var(name='zashadowz31_lz30')], name='@bvsub', result='zgsz352_lz33')
                                                                    zgsz352_lz33 = (zd_lz31 - zashadowz31_lz30) & r_uint(0xffff)
                                                                    pc = 66
                                                                    continue
                                                                # Operation(args=[Var(name='zd_lz31'), Var(name='zashadowz31_lz30')], name='@bvadd', result='zgsz352_lz33')
                                                                zgsz352_lz33 = (zd_lz31 + zashadowz31_lz30) & r_uint(0xffff)
                                                                pc = 66
                                                                continue
                                                            # Operation(args=[Var(name='zashadowz31_lz30'), BitVectorConstant(constant='0x0001')], name='@bvsub', result='zgsz352_lz33')
                                                            zgsz352_lz33 = (zashadowz31_lz30 - r_uint(0x0001)) & r_uint(0xffff)
                                                            pc = 66
                                                            continue
                                                        # Operation(args=[Var(name='zd_lz31'), BitVectorConstant(constant='0x0001')], name='@bvsub', result='zgsz352_lz33')
                                                        zgsz352_lz33 = (zd_lz31 - r_uint(0x0001)) & r_uint(0xffff)
                                                        pc = 66
                                                        continue
                                                    # Operation(args=[Var(name='zashadowz31_lz30'), BitVectorConstant(constant='0x0001')], name='@bvadd', result='zgsz352_lz33')
                                                    zgsz352_lz33 = (zashadowz31_lz30 + r_uint(0x0001)) & r_uint(0xffff)
                                                    pc = 66
                                                    continue
                                                # Operation(args=[Var(name='zd_lz31'), BitVectorConstant(constant='0x0001')], name='@bvadd', result='zgsz352_lz33')
                                                zgsz352_lz33 = (zd_lz31 + r_uint(0x0001)) & r_uint(0xffff)
                                                pc = 66
                                                continue
                                            # Operation(args=[BitVectorConstant(constant='0x0000'), Var(name='zashadowz31_lz30')], name='@bvsub', result='zgsz352_lz33')
                                            zgsz352_lz33 = (r_uint(0x0000) - zashadowz31_lz30) & r_uint(0xffff)
                                            pc = 66
                                            continue
                                        # Operation(args=[BitVectorConstant(constant='0x0000'), Var(name='zd_lz31')], name='@bvsub', result='zgsz352_lz33')
                                        zgsz352_lz33 = (r_uint(0x0000) - zd_lz31) & r_uint(0xffff)
                                        pc = 66
                                        continue
                                    # Operation(args=[Var(name='zashadowz31_lz30')], name='@bvnot', result='zgsz352_lz33')
                                    zgsz352_lz33 = (~zashadowz31_lz30) & r_uint(0xffff)
                                    pc = 66
                                    continue
                                # Operation(args=[Var(name='zd_lz31')], name='@bvnot', result='zgsz352_lz33')
                                zgsz352_lz33 = (~zd_lz31) & r_uint(0xffff)
                                pc = 66
                                continue
                            # Assignment(result='zgsz352_lz33', value=Var(name='zashadowz31_lz30'))
                            zgsz352_lz33 = zashadowz31_lz30
                            pc = 66
                            continue
                        # Assignment(result='zgsz352_lz33', value=Var(name='zd_lz31'))
                        zgsz352_lz33 = zd_lz31
                        pc = 66
                        continue
                    # Assignment(result='zgsz352_lz33', value=BitVectorConstant(constant='0xFFFF'))
                    zgsz352_lz33 = r_uint(0xFFFF)
                    pc = 66
                    continue
                # Assignment(result='zgsz352_lz33', value=BitVectorConstant(constant='0x0001'))
                zgsz352_lz33 = r_uint(0x0001)
                pc = 66
                continue
            # Assignment(result='zgsz352_lz33', value=BitVectorConstant(constant='0x0000'))
            zgsz352_lz33 = r_uint(0x0000)
            pc = 66
        if pc == 66:
            # Assignment(result='zresult_lz32', value=Var(name='zgsz352_lz33'))
            zresult_lz32 = zgsz352_lz33
            # Assignment(result='return', value=Var(name='zresult_lz32'))
            return_ = zresult_lz32
            # End()
            return return_




def func_zassign_dest(machine, zgsz371, zvalue):
    pc = 0
    while 1:
        if pc == 0:
            # za_lz30: NamedType('%bool')
            # Assignment(result='za_lz30', value=FieldAccess(element='ztup0', obj=Var(name='zgsz371')))
            za_lz30 = zgsz371.ztup0
            # zd_lz31: NamedType('%bool')
            # Assignment(result='zd_lz31', value=FieldAccess(element='ztup1', obj=Var(name='zgsz371')))
            zd_lz31 = zgsz371.ztup1
            # zm_lz32: NamedType('%bool')
            # Assignment(result='zm_lz32', value=FieldAccess(element='ztup2', obj=Var(name='zgsz371')))
            zm_lz32 = zgsz371.ztup2
            # LocalVarDeclaration(name='zgsz373_lz34', typ=NamedType('%unit'), value=None)
            # zgsz373_lz34: NamedType('%unit')
            zgsz373_lz34 = ()
            if zm_lz32:
                # inline pc=10
                # Operation(args=[Var(name='zA'), Var(name='zvalue')], name='zwrite_mem', result='zgsz373_lz34')
                zgsz373_lz34 = supportcode.my_write_mem(machine, machine.r.zA, zvalue)
                pc = 11
                continue
            # Assignment(result='zgsz373_lz34', value=Unit())
            zgsz373_lz34 = ()
            pc = 11
        if pc == 11:
            # LocalVarDeclaration(name='zgsz372_lz33', typ=NamedType('%unit'), value=None)
            # zgsz372_lz33: NamedType('%unit')
            zgsz372_lz33 = ()
            if za_lz30:
                # inline pc=15
                # Assignment(result='zA', value=Var(name='zvalue'))
                machine.r.zA = zvalue
                # Assignment(result='zgsz372_lz33', value=Unit())
                zgsz372_lz33 = ()
                pc = 17
                continue
            # Assignment(result='zgsz372_lz33', value=Unit())
            zgsz372_lz33 = ()
            pc = 17
        if pc == 17:
            if zd_lz31:
                # inline pc=20
                # Assignment(result='zD', value=Var(name='zvalue'))
                machine.r.zD = zvalue
                # Assignment(result='return', value=Unit())
                return_ = ()
                pc = 22
                continue
            # Assignment(result='return', value=Unit())
            return_ = ()
            pc = 22
        if pc == 22:
            # End()
            return return_




def func_zmaybe_jump(machine, zvalue, zj):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zcond_lz30', typ=NamedType('%bool'), value=None)
            # zcond_lz30: NamedType('%bool')
            zcond_lz30 = False
            # LocalVarDeclaration(name='zgsz374_lz34', typ=NamedType('%bool'), value=None)
            # zgsz374_lz34: NamedType('%bool')
            zgsz374_lz34 = False
            if not (Enum_zjump.zJDONT == zj):
                # inline pc=5
                if not (Enum_zjump.zJGT == zj):
                    # inline pc=10
                    if not (Enum_zjump.zJEQ == zj):
                        # inline pc=15
                        if not (Enum_zjump.zJGE == zj):
                            # inline pc=20
                            if not (Enum_zjump.zJLT == zj):
                                # inline pc=25
                                if not (Enum_zjump.zJNE == zj):
                                    # inline pc=32
                                    if not (Enum_zjump.zJLE == zj):
                                        # inline pc=37
                                        if not (Enum_zjump.zJMP == zj):
                                            # inline pc=40
                                            # Failure()
                                            raise TypeError
                                            continue
                                        # Assignment(result='zgsz374_lz34', value=Var(name='true'))
                                        zgsz374_lz34 = True
                                        pc = 41
                                        continue
                                    # LocalVarDeclaration(name='zgaz330_lz35', typ=NamedType('%i64'), value=None)
                                    # zgaz330_lz35: NamedType('%i64')
                                    zgaz330_lz35 = -0xfefe
                                    # TemplatedOperation(args=[Var(name='zvalue')], name='@signed', result='zgaz330_lz35', templateparam=Number(number=64))
                                    zgaz330_lz35 = supportcode.fast_signed(machine, zvalue, 16)
                                    # Operation(args=[Var(name='zgaz330_lz35'), Number(number=0)], name='@lteq', result='zgsz374_lz34')
                                    zgsz374_lz34 = (zgaz330_lz35 <= 0)
                                    pc = 41
                                    continue
                                # LocalVarDeclaration(name='zgaz329_lz36', typ=NamedType('%i64'), value=None)
                                # zgaz329_lz36: NamedType('%i64')
                                zgaz329_lz36 = -0xfefe
                                # TemplatedOperation(args=[Var(name='zvalue')], name='@signed', result='zgaz329_lz36', templateparam=Number(number=64))
                                zgaz329_lz36 = supportcode.fast_signed(machine, zvalue, 16)
                                # LocalVarDeclaration(name='zgsz382_lz37', typ=NamedType('%i'), value=Number(number=0))
                                # zgsz382_lz37: NamedType('%i')
                                zgsz382_lz37 = IntConst_0_1
                                # LocalVarDeclaration(name='zgsz381_lz38', typ=NamedType('%i'), value=Var(name='zgaz329_lz36'))
                                # zgsz381_lz38: NamedType('%i')
                                zgsz381_lz38 = Integer.fromint(zgaz329_lz36)
                                # Operation(args=[Var(name='zgsz381_lz38'), Var(name='zgsz382_lz37')], name='zneq_int', result='zgsz374_lz34')
                                zgsz374_lz34 = func_zneq_int(machine, zgsz381_lz38, zgsz382_lz37)
                                pc = 41
                                continue
                            # LocalVarDeclaration(name='zgaz328_lz39', typ=NamedType('%i64'), value=None)
                            # zgaz328_lz39: NamedType('%i64')
                            zgaz328_lz39 = -0xfefe
                            # TemplatedOperation(args=[Var(name='zvalue')], name='@signed', result='zgaz328_lz39', templateparam=Number(number=64))
                            zgaz328_lz39 = supportcode.fast_signed(machine, zvalue, 16)
                            # Operation(args=[Var(name='zgaz328_lz39'), Number(number=0)], name='@lt', result='zgsz374_lz34')
                            zgsz374_lz34 = (zgaz328_lz39 < 0)
                            pc = 41
                            continue
                        # LocalVarDeclaration(name='zgaz327_lz310', typ=NamedType('%i64'), value=None)
                        # zgaz327_lz310: NamedType('%i64')
                        zgaz327_lz310 = -0xfefe
                        # TemplatedOperation(args=[Var(name='zvalue')], name='@signed', result='zgaz327_lz310', templateparam=Number(number=64))
                        zgaz327_lz310 = supportcode.fast_signed(machine, zvalue, 16)
                        # Operation(args=[Var(name='zgaz327_lz310'), Number(number=0)], name='@gteq', result='zgsz374_lz34')
                        zgsz374_lz34 = (zgaz327_lz310 >= 0)
                        pc = 41
                        continue
                    # LocalVarDeclaration(name='zgaz326_lz311', typ=NamedType('%i64'), value=None)
                    # zgaz326_lz311: NamedType('%i64')
                    zgaz326_lz311 = -0xfefe
                    # TemplatedOperation(args=[Var(name='zvalue')], name='@signed', result='zgaz326_lz311', templateparam=Number(number=64))
                    zgaz326_lz311 = supportcode.fast_signed(machine, zvalue, 16)
                    # Operation(args=[Var(name='zgaz326_lz311'), Number(number=0)], name='@eq', result='zgsz374_lz34')
                    zgsz374_lz34 = (zgaz326_lz311 == 0)
                    pc = 41
                    continue
                # LocalVarDeclaration(name='zgaz325_lz312', typ=NamedType('%i64'), value=None)
                # zgaz325_lz312: NamedType('%i64')
                zgaz325_lz312 = -0xfefe
                # TemplatedOperation(args=[Var(name='zvalue')], name='@signed', result='zgaz325_lz312', templateparam=Number(number=64))
                zgaz325_lz312 = supportcode.fast_signed(machine, zvalue, 16)
                # Operation(args=[Var(name='zgaz325_lz312'), Number(number=0)], name='@gt', result='zgsz374_lz34')
                zgsz374_lz34 = (zgaz325_lz312 > 0)
                pc = 41
                continue
            # Assignment(result='zgsz374_lz34', value=Var(name='false'))
            zgsz374_lz34 = False
            pc = 41
        if pc == 41:
            # Assignment(result='zcond_lz30', value=Var(name='zgsz374_lz34'))
            zcond_lz30 = zgsz374_lz34
            if zcond_lz30:
                # inline pc=50
                # Assignment(result='zPC', value=Var(name='zA'))
                machine.r.zPC = machine.r.zA
                # Assignment(result='return', value=Unit())
                return_ = ()
                pc = 52
                continue
            # LocalVarDeclaration(name='zgsz385_lz31', typ=NamedType('%bv'), value=Var(name='zPC'))
            # zgsz385_lz31: NamedType('%bv')
            zgsz385_lz31 = bitvector.from_ruint(16, machine.r.zPC)
            # LocalVarDeclaration(name='zgsz386_lz32', typ=NamedType('%i'), value=Number(number=1))
            # zgsz386_lz32: NamedType('%i')
            zgsz386_lz32 = IntConst_1_1
            # zgsz387_lz33: NamedType('%bv')
            # Operation(args=[Var(name='zgsz385_lz31'), Var(name='zgsz386_lz32')], name='zadd_bits_int', result='zgsz387_lz33')
            zgsz387_lz33 = supportcode.add_bits_int(machine, zgsz385_lz31, zgsz386_lz32)
            # Assignment(result='zPC', value=Var(name='zgsz387_lz33'))
            machine.r.zPC = zgsz387_lz33.touint()
            # Assignment(result='return', value=Unit())
            return_ = ()
            pc = 52
        if pc == 52:
            # End()
            return return_



def func_zexecute(machine, zmergez3var):
    return zmergez3var.meth_zexecute(machine, )

def zexecute_zAINST(zmergez3var, machine, ):
    pc = 0
    while 1:
        if pc == 0:
            # LocalVarDeclaration(name='zgsz388_lz30', typ=NamedType('%unit'), value=None)
            # zgsz388_lz30: NamedType('%unit')
            zgsz388_lz30 = ()
            # zx_lz37: NamedType('%bv16')
            # Assignment(result='zx_lz37', value=Cast(expr=Var(name='zmergez3var'), variant='zAINST'))
            zx_lz37 = Union_zinstr_zAINST.convert(zmergez3var)
            # Assignment(result='zA', value=Var(name='zx_lz37'))
            machine.r.zA = zx_lz37
            # zgsz389_lz311: NamedType('%unit')
            # Assignment(result='zgsz389_lz311', value=Unit())
            zgsz389_lz311 = ()
            # LocalVarDeclaration(name='zgsz390_lz38', typ=NamedType('%bv'), value=Var(name='zPC'))
            # zgsz390_lz38: NamedType('%bv')
            zgsz390_lz38 = bitvector.from_ruint(16, machine.r.zPC)
            # LocalVarDeclaration(name='zgsz391_lz39', typ=NamedType('%i'), value=Number(number=1))
            # zgsz391_lz39: NamedType('%i')
            zgsz391_lz39 = IntConst_1_1
            # zgsz392_lz310: NamedType('%bv')
            # Operation(args=[Var(name='zgsz390_lz38'), Var(name='zgsz391_lz39')], name='zadd_bits_int', result='zgsz392_lz310')
            zgsz392_lz310 = supportcode.add_bits_int(machine, zgsz390_lz38, zgsz391_lz39)
            # Assignment(result='zPC', value=Var(name='zgsz392_lz310'))
            machine.r.zPC = zgsz392_lz310.touint()
            # Assignment(result='zgsz388_lz30', value=Unit())
            zgsz388_lz30 = ()
            pc = 30
        if pc == 30:
            # Assignment(result='return', value=Var(name='zgsz388_lz30'))
            return_ = zgsz388_lz30
            # End()
            return return_
Union_zinstr_zAINST.meth_zexecute = zexecute_zAINST

def zexecute_zCINST(zmergez3var, machine, ):
    pc = 14
    while 1:
        if pc == 14:
            # LocalVarDeclaration(name='zgsz388_lz30', typ=NamedType('%unit'), value=None)
            # zgsz388_lz30: NamedType('%unit')
            zgsz388_lz30 = ()
            # za_lz31: NamedType('%bv1')
            # Assignment(result='za_lz31', value=FieldAccess(element='ztup0', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')))
            za_lz31 = Union_zinstr_zCINST.convert(zmergez3var).ztup0
            # zop_lz32: EnumType(name='zarithmetic_op')
            # Assignment(result='zop_lz32', value=FieldAccess(element='ztup1', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')))
            zop_lz32 = Union_zinstr_zCINST.convert(zmergez3var).ztup1
            # zdest_lz33: TupleType(elements=[NamedType('%bool'), NamedType('%bool'), NamedType('%bool')])
            # Assignment(result='zdest_lz33', value=FieldAccess(element='ztup2', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')))
            zdest_lz33 = Union_zinstr_zCINST.convert(zmergez3var).ztup2
            # zjump_lz34: EnumType(name='zjump')
            # Assignment(result='zjump_lz34', value=FieldAccess(element='ztup3', obj=Cast(expr=Var(name='zmergez3var'), variant='zCINST')))
            zjump_lz34 = Union_zinstr_zCINST.convert(zmergez3var).ztup3
            # zvalue_lz35: NamedType('%bv16')
            # Operation(args=[Var(name='za_lz31'), Var(name='zop_lz32')], name='zcompute_value', result='zvalue_lz35')
            zvalue_lz35 = func_zcompute_value(machine, za_lz31, zop_lz32)
            # zgsz394_lz36: NamedType('%unit')
            # Operation(args=[Var(name='zdest_lz33'), Var(name='zvalue_lz35')], name='zassign_dest', result='zgsz394_lz36')
            zgsz394_lz36 = func_zassign_dest(machine, zdest_lz33, zvalue_lz35)
            # Operation(args=[Var(name='zvalue_lz35'), Var(name='zjump_lz34')], name='zmaybe_jump', result='zgsz388_lz30')
            zgsz388_lz30 = func_zmaybe_jump(machine, zvalue_lz35, zjump_lz34)
            pc = 30
        if pc == 30:
            # Assignment(result='return', value=Var(name='zgsz388_lz30'))
            return_ = zgsz388_lz30
            # End()
            return return_
Union_zinstr_zCINST.meth_zexecute = zexecute_zCINST

def zexecute_default(zmergez3var, machine, ):
    pc = 29
    while 1:
        if pc == 29:
            # LocalVarDeclaration(name='zgsz388_lz30', typ=NamedType('%unit'), value=None)
            # zgsz388_lz30: NamedType('%unit')
            zgsz388_lz30 = ()
            # Failure()
            raise TypeError
Union_zinstr.meth_zexecute = zexecute_default



def func_zfetch_decode_execute(machine, zgsz396):
    pc = 0
    while 1:
        if pc == 0:
            # zinstr_lz30: NamedType('%bv16')
            # Operation(args=[Var(name='zPC')], name='zread_rom', result='zinstr_lz30')
            zinstr_lz30 = supportcode.my_read_rom(machine, machine.r.zPC)
            # zx_lz31: UnionType(name='zoption')
            # Operation(args=[Var(name='zinstr_lz30')], name='zdecode', result='zx_lz31')
            zx_lz31 = func_zdecode(machine, zinstr_lz30)
            # zcont_lz32: NamedType('%bool')
            # Assignment(result='zcont_lz32', value=Var(name='false'))
            zcont_lz32 = False
            # LocalVarDeclaration(name='zgsz397_lz33', typ=NamedType('%unit'), value=None)
            # zgsz397_lz33: NamedType('%unit')
            zgsz397_lz33 = ()
            if type(zx_lz31) is not Union_zoption_zSomez3z5unionz0zzinstr:
                # inline pc=15
                if type(zx_lz31) is not Union_zoption_zNone:
                    # inline pc=19
                    # Failure()
                    raise TypeError
                    continue
                # Assignment(result='zcont_lz32', value=Var(name='false'))
                zcont_lz32 = False
                # Assignment(result='zgsz397_lz33', value=Unit())
                zgsz397_lz33 = ()
                pc = 20
                continue
            # zinstrshadowz32_lz35: UnionType(name='zinstr')
            # Assignment(result='zinstrshadowz32_lz35', value=Cast(expr=Var(name='zx_lz31'), variant='zSomez3z5unionz0zzinstr'))
            zinstrshadowz32_lz35 = Union_zoption_zSomez3z5unionz0zzinstr.convert(zx_lz31)
            # zgsz398_lz36: NamedType('%unit')
            # Operation(args=[Var(name='zinstrshadowz32_lz35')], name='zexecute', result='zgsz398_lz36')
            zgsz398_lz36 = func_zexecute(machine, zinstrshadowz32_lz35)
            # Assignment(result='zcont_lz32', value=Var(name='true'))
            zcont_lz32 = True
            # Assignment(result='zgsz397_lz33', value=Unit())
            zgsz397_lz33 = ()
            pc = 20
        if pc == 20:
            # zgsz3101_lz34: NamedType('%unit')
            # Assignment(result='zgsz3101_lz34', value=Var(name='zgsz397_lz33'))
            zgsz3101_lz34 = zgsz397_lz33
            # Assignment(result='return', value=Var(name='zcont_lz32'))
            return_ = zcont_lz32
            # End()
            return return_




def func_zrun(machine, zlimit, zdebug):
    pc = 0
    while 1:
        if pc == 0:
            # zcycle_count_lz30: NamedType('%bv64')
            # Assignment(result='zcycle_count_lz30', value=BitVectorConstant(constant='0x0000000000000000'))
            zcycle_count_lz30 = r_uint(0x0000000000000000)
            # zcont_lz31: NamedType('%bool')
            # Assignment(result='zcont_lz31', value=Var(name='true'))
            zcont_lz31 = True
            # LocalVarDeclaration(name='zgsz3105_lz32', typ=NamedType('%bool'), value=None)
            # zgsz3105_lz32: NamedType('%bool')
            zgsz3105_lz32 = False
            # LocalVarDeclaration(name='zgsz3106_lz33', typ=NamedType('%unit'), value=None)
            # zgsz3106_lz33: NamedType('%unit')
            zgsz3106_lz33 = ()
            pc = 6
        if pc == 6:
            # Assignment(result='zgsz3105_lz32', value=Var(name='zcont_lz31'))
            zgsz3105_lz32 = zcont_lz31
            if not zgsz3105_lz32:
                # inline pc=36
                # Assignment(result='return', value=Unit())
                return_ = ()
                # End()
                return return_
                continue
            # Assignment(result='zcont_lz31', value=Var(name='false'))
            zcont_lz31 = False
            # zgsz3104_lz310: NamedType('%unit')
            # Assignment(result='zgsz3104_lz310', value=Unit())
            zgsz3104_lz310 = ()
            # LocalVarDeclaration(name='zgsz3103_lz39', typ=NamedType('%unit'), value=None)
            # zgsz3103_lz39: NamedType('%unit')
            zgsz3103_lz39 = ()
            if zdebug:
                # inline pc=15
                # Operation(args=[Var(name='zcycle_count_lz30'), Var(name='zPC'), Var(name='zA'), Var(name='zD')], name='zprint_debug', result='zgsz3103_lz39')
                zgsz3103_lz39 = supportcode.my_print_debug(machine, zcycle_count_lz30, machine.r.zPC, machine.r.zA, machine.r.zD)
                pc = 16
                continue
            # Assignment(result='zgsz3103_lz39', value=Unit())
            zgsz3103_lz39 = ()
            pc = 16
        if pc == 16:
            # zgaz331_lz34: NamedType('%bool')
            # Operation(args=[Unit()], name='zfetch_decode_execute', result='zgaz331_lz34')
            zgaz331_lz34 = func_zfetch_decode_execute(machine, ())
            # LocalVarDeclaration(name='zgsz3102_lz35', typ=NamedType('%unit'), value=None)
            # zgsz3102_lz35: NamedType('%unit')
            zgsz3102_lz35 = ()
            if zgaz331_lz34:
                # inline pc=22
                # LocalVarDeclaration(name='zgaz334_lz36', typ=NamedType('%bool'), value=None)
                # zgaz334_lz36: NamedType('%bool')
                zgaz334_lz36 = False
                # LocalVarDeclaration(name='zgaz332_lz37', typ=NamedType('%i64'), value=None)
                # zgaz332_lz37: NamedType('%i64')
                zgaz332_lz37 = -0xfefe
                # TemplatedOperation(args=[Var(name='zcycle_count_lz30')], name='@signed', result='zgaz332_lz37', templateparam=Number(number=64))
                zgaz332_lz37 = supportcode.fast_signed(machine, zcycle_count_lz30, 64)
                # LocalVarDeclaration(name='zgaz333_lz38', typ=NamedType('%i64'), value=None)
                # zgaz333_lz38: NamedType('%i64')
                zgaz333_lz38 = -0xfefe
                # TemplatedOperation(args=[Var(name='zlimit')], name='@signed', result='zgaz333_lz38', templateparam=Number(number=64))
                zgaz333_lz38 = supportcode.fast_signed(machine, zlimit, 64)
                # Operation(args=[Var(name='zgaz332_lz37'), Var(name='zgaz333_lz38')], name='@lt', result='zgaz334_lz36')
                zgaz334_lz36 = (zgaz332_lz37 < zgaz333_lz38)
                if zgaz334_lz36:
                    # inline pc=31
                    # Assignment(result='zcont_lz31', value=Var(name='true'))
                    zcont_lz31 = True
                    # Assignment(result='zgsz3102_lz35', value=Unit())
                    zgsz3102_lz35 = ()
                    pc = 33
                    continue
                # Assignment(result='zgsz3102_lz35', value=Unit())
                zgsz3102_lz35 = ()
                pc = 33
                continue
            # Assignment(result='zgsz3102_lz35', value=Unit())
            zgsz3102_lz35 = ()
            pc = 33
        if pc == 33:
            # Operation(args=[Var(name='zcycle_count_lz30'), BitVectorConstant(constant='0x0000000000000001')], name='@bvadd', result='zcycle_count_lz30')
            zcycle_count_lz30 = zcycle_count_lz30 + r_uint(0x0000000000000001)
            # Assignment(result='zgsz3106_lz33', value=Unit())
            zgsz3106_lz33 = ()
            pc = 6




def func_zmymain(machine, zlimit, zdebug):
    # Assignment(result='zPC', value=BitVectorConstant(constant='0x0000'))
    machine.r.zPC = r_uint(0x0000)
    # zgsz3109_lz32: NamedType('%unit')
    # Assignment(result='zgsz3109_lz32', value=Unit())
    zgsz3109_lz32 = ()
    # Assignment(result='zA', value=BitVectorConstant(constant='0x0000'))
    machine.r.zA = r_uint(0x0000)
    # zgsz3108_lz31: NamedType('%unit')
    # Assignment(result='zgsz3108_lz31', value=Unit())
    zgsz3108_lz31 = ()
    # Assignment(result='zD', value=BitVectorConstant(constant='0x0000'))
    machine.r.zD = r_uint(0x0000)
    # zgsz3107_lz30: NamedType('%unit')
    # Assignment(result='zgsz3107_lz30', value=Unit())
    zgsz3107_lz30 = ()
    # Operation(args=[Var(name='zlimit'), Var(name='zdebug')], name='zrun', result='return')
    return_ = func_zrun(machine, zlimit, zdebug)
    # End()
    return return_




def func_zmain(machine, zgsz3110):
    # zgaz335_lz30: NamedType('%unit')
    # Operation(args=[BitVectorConstant(constant='0x0000000000000010'), Var(name='false')], name='zmymain', result='zgaz335_lz30')
    zgaz335_lz30 = func_zmymain(machine, r_uint(0x0000000000000010), False)
    # Assignment(result='return', value=Var(name='zgaz335_lz30'))
    return_ = zgaz335_lz30
    # End()
    return return_

