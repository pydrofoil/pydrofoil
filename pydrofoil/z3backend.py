import z3
from pydrofoil import ir, types
from copy import deepcopy

class Value(object):

    def __init__(self):
        # TODO: Resolved_Type
        self.value = None
        self._raise = False
        self._type = None
    
    def __str__(self):
        return str(self.value)
    
    def __repr__(self):
        return self.__str__()

class Enum(Value):# AbstractConstant

    @classmethod
    def blank_raise_enum(cls): 
        r_enum = Enum("","", None)
        r_enum._raise = True
        r_enum._type = None
        return r_enum
    
    def __init__(self, name, variant, z3value):
        self.enum_name = name
        self.variant = variant
        self.value = z3value
        self._type = Enum
        self._raise = False

    def toz3(self):
        return self.value
    
    def __eq__(self, other):
        # So we can eval enums on Interpreter level
        if not isinstance(other, Enum): return False
        return self.enum_name == other.enum_name and self.variant == other.variant


class AbstractConstant(Value):
    pass

class Constant(AbstractConstant):
    
    def __init__(self, val):
        self.value = val
        self._type = Constant
        self._raise = False

    def toz3(self):
        return int(self.value)
    
class UnionConstant(AbstractConstant):

    def __init__(self, variant_name, w_val, resolved_type, z3type):
        self.variant_name = variant_name
        self.w_val = w_val
        self._type = UnionConstant
        self._raise = False
        self.resolved_type = resolved_type
        self.z3type = z3type
    
    def toz3(self):
        return int(self.value)

class Z3Value(Value):
    
    def __init__(self, val):
        self.value = val
        self._type = Z3Value
        self._raise = False

    def toz3(self):
        return self.value
    
    
class SharedState(object):

    def __init__(self, functions={}):
        self.funcs = functions
        self.enums = {}
        self.type_cache = {}
        self.fork_counter = 0

    def get_z3_struct_type(self, resolved_type):
        if resolved_type in self.type_cache:
            return self.type_cache[resolved_type]
        sname = "struct_%s" % resolved_type.name
        struct = z3.Datatype(sname)
        fields = []
        # create struct
        for fieldname, typ in resolved_type.internalfieldtyps.items():
            fields.append((fieldname, self.convert_type_to_z3(typ)))
    
        struct.declare("a", *fields)
        struct = struct.create()
        self.type_cache[resolved_type] = struct
        return struct

    def get_z3_union_type(self, resolved_type):
        if resolved_type in self.type_cache:
            return self.type_cache[resolved_type]
        uname = "union_%s" % resolved_type.name
        union = z3.Datatype(uname)
        # create union variants
        for variant, typ in resolved_type.variants.items():
            if typ is types.Unit():
                union.declare(variant)
            else:
                union.declare(variant, ("a", self.convert_type_to_z3(typ)))
        union = union.create()
        self.type_cache[resolved_type] = union
        return union
    
    def get_z3_enum_type(self, resolved_type):
        if not resolved_type in self.type_cache:
            enum = self.register_enum(resolved_type.name, resolved_type.elements)
            self.type_cache[resolved_type] = enum
        return self.type_cache[resolved_type]
    
    def convert_type_to_z3(self, typ):
        if isinstance(typ, types.SmallFixedBitVector):
            return z3.BitVecSort(typ.width)
        elif isinstance(typ, types.Union):
            return self.get_z3_union_type(typ)
        elif isinstance(typ, types.Struct):
            return self.get_z3_struct_type(typ)
        elif isinstance(typ, types.Enum):
            return self.get_z3_enum_type(typ)
        elif isinstance(typ, types.Bool):
            return z3.BoolSort()
        else:
            import pdb; pdb.set_trace()

    def register_enum(self, name, variants):
        """ register new enum """
        ename = "enum_%s" % name
        enum = z3.Datatype(ename)
        # create enum variants
        for variant in variants:
            enum.declare(variant)
        # hack: ir is type consistent but we need to model exceptions somehow and z3 cant do if(cond, ret_type_A, ret_type_B)
        enum.declare("___Exception___")
        # 
        enum = enum.create()
        # create mapping to easily use z3 enum variants 
        mapping = {variant:getattr(enum, variant) for variant in variants}
        mapping["___Exception___"] = getattr(enum, "___Exception___")
        self.enums[ename] = (enum, mapping)
        return enum

    def copy(self):
        """ for tests """
        copystate = SharedState(self.funcs.copy())
        copystate.enums = self.enums.copy()
        return copystate
    
    def get_abstract_enum_const_of_type(self, enum_name, var_name):
        """ Returns Const of given type that is neither equal nor unequal to any variant of given enum type """
        return z3.Const(var_name, self.get_enum_type(enum_name))
    
    def get_enum_type(self, name):
        """ Returns the Z3 Datatype Object of this enum """
        return self.enums["enum_" + name][0]

    def get_w_enum(self, name, variant):
        """ Returns the Z3 enum variant obj wrapped in Enum class """
        return Enum(name, variant, self.get_enum(name, variant))

    def get_enum(self, name, variant):
        """ Returns the Z3 enum variant obj """
        return self.enums["enum_" + name][1][variant]

    def get_basic_excpetion(self):
        return Enum("Basic", "Exception", self.enums["enum_Basic"][1]["Exception"])


class Interpreter(object):
    
    def __init__(self, graph, args, shared_state=None):
        self.cls = Interpreter
        self.sharedstate = shared_state if shared_state != None else SharedState()
        self.graph = graph
        self.args = args
        self.forknum = self.sharedstate.fork_counter
        self.sharedstate.fork_counter += 1
        assert len(args) == len(graph.args)
        self.environment = {graph.args[i]:args[i] for i in range(len(args))} # assume args are an instance of some z3backend.Value subclass
        self.registers = {}
        self.memory = z3.Array('memory', z3.BitVecSort(64), z3.BitVecSort(64))
        assert not graph.has_loop
        # TODO: Move this to SharedState
        if not "enum_Basic" in self.sharedstate.enums:
            self.create_z3_enum("Basic", ["Exception"])

    def run(self, block=None):
        """ interpret a graph, either begin with graph.startblock or the block passed as arg """
        if block:
            cur_block = block
        else:
            cur_block = self.graph.startblock

        while True:
            for op in cur_block.operations:
                self.execute_op(op)
            
            next = cur_block.next
            self.prev_block = cur_block
            cur_block = self.execute_next(next)
            if not cur_block:
                break
        return self.w_result
    
    def fork(self):
        """ create a copy of the interpreter, for evaluating non constant branches """
        cls = self.cls
        f_interp = cls(self.graph, self.args, self.sharedstate)
        f_interp.environment = self.environment.copy()
        # TODO: How to model x86_64's registers for 64,32 and 16 bit ?  
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        return f_interp
    
    def call_fork(self):
        """ create a copy of the interpreter, for evaluating func calls"""
        #f_interp.registers = {}
        #f_interp.memory = z3.Array('memory', z3.BitVecSort(64), z3.BitVecSort(64))
        pass

    def cast_raise(self, w_to_cast, wtype):
        if isinstance(wtype, Constant):
            return Z3Value(z3.BitVec("Basic_Exception", 64))
        elif isinstance(wtype, Enum):
            return Enum(wtype.enum_name, "___Exception___", self.sharedstate.get_enum(wtype.enum_name, "___Exception___"))
        else:
            assert 0

    def check_cast_raise(self, w0, w1):
        """ specialise placeholder raise to certain type 
            Z3 doesnt allow returning mixed types in if e.g. if(cond, BitVEcVal(117), raise_as_enum_variant)
            So we replace that with the same type e.g. if(cond, BitVecVal(117), BitVec("raise"))"""
        if w0._type == w1._type and w1._type != None:
            return w0, w1 # all types set, doesnt even matter if raise or not
        elif w0._raise and w1._raise and w0._type == w1._type and w1._type == None:
            w0 = w1 = self.sharedstate.get_basic_excpetion()# case if(cond, raise A, raise B) # no type for raised Exceptions
        elif w0._raise and w0._type == None:
            w0 = self.cast_raise(w0, w1) # case if(cond, raise A, instance_of_type_B) # cast raised Exception to type B
        elif w1._raise and w1._type == None:
            w1 = self.cast_raise(w1, w0) # case if(cond, instance_of_type_A, raise B) # cast raised Exception to type A
        else:
            assert 0
        return w0, w1
    
    def _assert_types(self, a, b):
        """ sanity check """
        if a._type == b._type:
            assert 1
        elif a._type in (Z3Value, Constant) and b._type in (Z3Value, Constant):
            assert 1
        else:
            assert 0, str((a, b, a._type, b._type))

    def execute_next(self, next):
        """ get next block to execute, or set ret value and return None, or fork interpreter on non const cond. goto """
        if isinstance(next, ir.Goto):
            return next.target
        elif isinstance(next, ir.ConditionalGoto):
            w_cond = self.convert(next.booleanvalue)
            if isinstance(w_cond, Constant):
                if w_cond.value:
                    return next.truetarget
                return next.falsetarget
            else:
                # fork 
                interp1 = self.fork()
                interp2 = self.fork()
                w_res_true = interp1.run(next.truetarget)
                w_res_false = interp2.run(next.falsetarget)
                if w_res_true._raise or w_res_false._raise:
                    w_res_true, w_res_false = self.check_cast_raise(w_res_true, w_res_false)
                self._assert_types(w_res_true, w_res_false)
                z3cond = w_cond.toz3()
                self.w_result = Z3Value(z3.If(z3cond, w_res_true.toz3(), w_res_false.toz3()))
                self.registers = {reg:Z3Value(z3.If(z3cond, interp1.registers[reg].toz3(), interp2.registers[reg].toz3())) for reg in self.registers}
                self.memory = z3.If(z3cond, interp1.memory, interp2.memory)
                self.w_result._type = w_res_true._type 
        elif isinstance(next, ir.Return):
            self.w_result = self.convert(next.value)
        elif isinstance(next, ir.Raise):
            self.w_result = Enum.blank_raise_enum()# raising an error 
        else:
            assert 0, "implement %s" %str(next)
        return None
    
    def _debug_print(self, msg=""):
        print "%s__interp_%s:" % (self.cls, self.forknum), msg

    def create_z3_enum(self, name, variants):
        """ create a z3 datatype for an enum and store in shared state """
        self.sharedstate.register_enum(name, variants)

    def convert(self, arg):
        """ wrap an argument or load wrapped arg from env """
        if isinstance(arg, ir.SmallBitVectorConstant):
            w_arg = Constant(arg.value)
            w_arg._type = Constant
        elif isinstance(arg, ir.EnumConstant):
            enumname =  "enum_%s" % arg.resolved_type.name
            if not enumname in self.sharedstate.enums:
                self.create_z3_enum(arg.resolved_type.name, arg.resolved_type.elements)
            z3variant = self.sharedstate.enums[enumname][1][arg.variant] # self.sharedstate.enums[enumname][0] is z3 Datatype obj [1] is mapping variant_name:z3variant
            w_arg = Enum(arg.resolved_type.name, arg.variant, z3variant)
        elif isinstance(arg, ir.Constant):
            if isinstance(arg, ir.MachineIntConstant):
                w_arg = Constant(arg.number)
                w_arg._type = Constant
            else:
                assert 0, "Some ir Constant " + str(arg) 
        else:
            w_arg = self.environment[arg]    
        return w_arg


    def getargs(self, op):
        """ get all wrapped args of an operation """
        res = []
        for arg in op.args:
            res.append(self.convert(arg))
        return res
    
    def read_register(self, register):
        """ read from register, creates new 'empty' z3 Val for registers on first access """
        if register not in self.registers:
            self.registers[register] = Z3Value(z3.BitVec("reg_%s" % register, 64))
        return self.registers[register]
    
    def write_register(self, register, value):
        """ write to register """
        self.registers[register] = value

    def read_memory(self, addr):
        """ read from memory, creates new 'empty' z3 Val for mem addresses on first access """
        return self.memory[addr.toz3()]
    
    def wrte_memory(self, addr, value):
        """ rwrite to memory """
        self.memory = z3.Store(self.memory, addr, value)

    def exec_phi(self, op):
        """ get value of actual predecessor """
        index = op.prevblocks.index(self.prev_block)
        return self.convert(op.prevvalues[index])
    
    def execute_op(self, op):
        """ execute an operation and write result into environment """
        if isinstance(op, ir.Phi):
            result = self.exec_phi(op)
        elif isinstance(op, ir.GlobalRead):
            result = self.read_register(op.name)
        elif hasattr(self, "exec_%s" % op.name.replace("@","")):
            func = getattr(self, "exec_%s" % op.name.replace("@",""))
            result = func(op) # self passed implicitly
        elif op.is_union_creation():
            result = self.exec_union_creation(op)
        else:
            assert 0 , str(op.name) + ", " + str(op) + "," + "exec_%s" % op.name.replace("@","")
        self.environment[op] = result
    
    ### Generic Operations ###

    def exec_union_creation(self, op):
        z3type = self.sharedstate.get_z3_union_type(op.resolved_type)
        return UnionConstant(op.name, self.getargs(op)[0], op.resolved_type, z3type)

    def exec_eq_bits_bv_bv(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, Constant) and isinstance(arg1, Constant):
            return Constant(arg0.value == arg1.value)
        else:
            return Z3Value(arg0.toz3() == arg1.toz3())
    
    def exec_eq(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, Constant) and isinstance(arg1, Constant):
            return Constant(arg0.value == arg1.value)
        elif isinstance(arg0, Enum) and isinstance(arg1, Enum):
            return Constant(arg0 == arg1)
        else:
            return Z3Value(arg0.toz3() == arg1.toz3())
        
    def exec_not_vec_bv(self, op):
        arg0, _ = self.getargs(op) # TODO: start using the passed width everywhere and not always 64 bit
        if isinstance(arg0, Constant):
            return Constant(~arg0.value)
        else:
            return Z3Value(~arg0.toz3())
        
    def exec_sub_bits_bv_bv(self, op):
        # TODO: bitvec width benutzen
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, Constant) and isinstance(arg1, Constant):
            return Constant(arg0.value - arg1.value)
        else:
            return Z3Value(arg0.toz3() - arg1.toz3())

    def exec_add_bits_bv_bv(self, op):
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, Constant) and isinstance(arg1, Constant):
            return Constant(arg0.value + arg1.value)
        else:
            return Z3Value(arg0.toz3() + arg1.toz3())

    def exec_and_vec_bv_bv(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, Constant) and isinstance(arg1, Constant):
            return Constant(arg0.value & arg1.value)
        else:
            return Z3Value(arg0.toz3() & arg1.toz3())

    def exec_or_vec_bv_bv(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, Constant) and isinstance(arg1, Constant):
            return Constant(arg0.value | arg1.value)
        else:
            return Z3Value(arg0.toz3() | arg1.toz3())
        
    def exec_vector_subrange_fixed_bv_i_i(self, op):
        """ slice bitvector as bv[arg1:arg0] both inclusive """
        arg0, arg1, arg2 = self.getargs(op)
        # TODO: use supportcode func
        # TODO: rhsift
        if isinstance(arg0, Constant):
            return Constant(arg0.value & ((2**arg1.value - 1) - (2**(arg2.value-1) - 1)))
        else:
            return Z3Value(arg0.toz3() & ((2**arg1.value - 1) - (2**(arg2.value-1) - 1)))
        
    def exec_zero_extend_bv_i_i(self, op):
        """ extend bitvector from arg1 to arg2 with zeros """
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, Constant):
            return Constant(arg0.value) # left zero extend doesnt change const int
        else:
            padding = z3.BitVec("padding", arg2.value - arg1.value)
            return z3.Concat(padding, arg0.toz3())
        
    ### Arch specific Operations in subclass ###

class NandInterpreter(Interpreter):
    """ Interpreter subclass for nand2tetris CPU """

    def __init__(self, graph, args, shared_state=None):
        super(NandInterpreter, self).__init__(graph, args, shared_state)# py2 super 
        self.cls = NandInterpreter
    
    ### Nand specific Operations ###

    def exec_my_read_mem(self, op):
        """ read from memory """
        addr,  = self.getargs(op)
        return Z3Value(self.read_memory(addr))
