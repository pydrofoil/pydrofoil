import z3
from pydrofoil import supportcode
from pydrofoil import ir, types

class Value(object):

    def __init__(self):
        # TODO: Resolved_Type
        self.value = None
        self._raise = False
    
    def __str__(self):
        return str(self.value)
    
    def __repr__(self):
        return self.__str__()

class Enum(Value):# AbstractConstant
    
    def __init__(self, name, variant, z3value):
        self.enum_name = name
        self.variant = variant
        self.value = z3value
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
        self._raise = False

    def toz3(self):
        return int(self.value)
    
class BooleanConstant(AbstractConstant):
    
    def __init__(self, val):
        self.value = val
        self._raise = False

    def toz3(self):
        return self.value

class RaiseConstant(AbstractConstant):

    def __init__(self, kind):
        self.kind = kind

    def __str__(self):
        return self.kind

class UnitConstant(AbstractConstant):
    
    def __init__(self):
        self._raise = False

    def toz3(self):
        assert 0
        return self.value
    
class UnionConstant(AbstractConstant):

    def __init__(self, variant_name, w_val, resolved_type, z3type):
        self.variant_name = variant_name
        self.w_val = w_val
        self._raise = False
        self.resolved_type = resolved_type
        self.z3type = z3type
    
    def toz3(self):
        if isinstance(self.w_val, UnitConstant):
            return getattr(self.z3type, self.variant_name)
        z3val = self.w_val.toz3()
        return getattr(self.z3type, self.variant_name)(z3val)
    
class StructConstant(AbstractConstant):

    def __init__(self, vals_w, resolved_type, z3type):
        self.vals_w = vals_w
        self._raise = False
        self.resolved_type = resolved_type
        self.z3type = z3type
    
    def toz3(self):
        z3vals = [w_val.toz3() for w_val in self.vals_w]
        return self.z3type.a(*z3vals)

class Z3Value(Value):
    
    def __init__(self, val):
        self.value = val
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
        # 
        enum = enum.create()
        # create mapping to easily use z3 enum variants 
        mapping = {variant:getattr(enum, variant) for variant in variants}
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
        self.w_exception = Z3Value(z3.StringVal("No Exception"))
        self.w_raises = Z3Value(False)

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
        cls = type(self)
        f_interp = cls(self.graph, self.args, self.sharedstate)
        f_interp.environment = self.environment.copy()
        # TODO: How to model x86_64's registers for 64,32 and 16 bit ?  
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        return f_interp
    
    def call_fork(self, graph, args):
        """ create a copy of the interpreter, for evaluating func calls"""
        cls = type(self)
        f_interp = cls(graph, args, self.sharedstate)
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        return f_interp

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
                z3cond = w_cond.toz3()

                # Handle Exceptions, when a raise block raises the forks result is an instance of RaiseConstant
                if isinstance(w_res_true, RaiseConstant) and isinstance(w_res_false, RaiseConstant):
                    self.w_result = RaiseConstant("/") # result of computation
                    # Exception as String e.g. z3.If(cond, z3.StringVal("Excpetion A"), z3.StringVal("No Exception/ Exception B"))
                    self.w_exception = Z3Value(z3.If(z3cond, z3.StringVal(str(w_res_true)), z3.StringVal(str(w_res_false)))) 
                    self.w_raises = Z3Value(True) # bool cond for raise
                elif isinstance(w_res_true, RaiseConstant):
                    self.w_result = w_res_false
                    self.w_exception = Z3Value(z3.If(z3cond, z3.StringVal(str(w_res_true)), interp2.w_exception.toz3())) 
                    self.w_raises = Z3Value(z3.If(z3cond, True, interp2.w_raises.toz3()))
                elif isinstance(w_res_false, RaiseConstant):
                    self.w_result = w_res_true
                    self.w_exception = Z3Value(z3.If(z3cond, interp1.w_exception.toz3(), z3.StringVal(str(w_res_false)))) 
                    self.w_raises = Z3Value(z3.If(z3cond, interp1.w_raises.toz3(), True))
                else:
                    self.w_result = Z3Value(z3.If(z3cond, w_res_true.toz3(), w_res_false.toz3()))
                    self.w_exception = Z3Value(z3.If(z3cond, interp1.w_exception.toz3(), interp2.w_exception.toz3())) 
                    self.w_raises = Z3Value(z3.If(z3cond, interp1.w_raises.toz3(), interp2.w_raises.toz3()))

                # TODO: maybe we dont need any merges on raise??
                self.registers = {reg:Z3Value(z3.If(z3cond, interp1.registers[reg].toz3(), interp2.registers[reg].toz3())) for reg in self.registers}
                self.memory = z3.If(z3cond, interp1.memory, interp2.memory)

        elif isinstance(next, ir.Return):
            self.w_result = self.convert(next.value)
        elif isinstance(next, ir.Raise):
            self.w_result = RaiseConstant(str(next.kind))
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
        elif isinstance(arg, ir.EnumConstant):
            enumname =  "enum_%s" % arg.resolved_type.name
            if not enumname in self.sharedstate.enums:
                self.create_z3_enum(arg.resolved_type.name, arg.resolved_type.elements)
            z3variant = self.sharedstate.enums[enumname][1][arg.variant] # self.sharedstate.enums[enumname][0] is z3 Datatype obj [1] is mapping variant_name:z3variant
            w_arg = Enum(arg.resolved_type.name, arg.variant, z3variant)
        elif isinstance(arg, ir.Constant):
            if isinstance(arg, ir.MachineIntConstant):
                w_arg = Constant(arg.number)
            elif isinstance(arg, ir.BooleanConstant):
                w_arg = BooleanConstant(arg.value)
            elif isinstance(arg, ir.UnitConstant):
                w_arg = UnitConstant()
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
        elif op.name in self.sharedstate.funcs:
            result = self.exec_func_call(op, self.sharedstate.funcs[op.name])
        elif isinstance(op, ir.Comment):
            return
        elif isinstance(op, ir.StructConstruction):
            result = self.exec_struct_construction(op)
        else:
            assert 0 , str(op.name) + ", " + str(op) + "," + "exec_%s" % op.name.replace("@","")
        self.environment[op] = result
    
    ### Generic Operations ###

    
    def exec_func_call(self, op, graph):
        args = self.getargs(op)
        interp_fork = self.call_fork(graph, args)
        w_res = interp_fork.run()
        self.registers = interp_fork.registers
        self.memory = interp_fork.memory
        return w_res

    def exec_struct_construction(self, op):
        z3type = self.sharedstate.get_z3_struct_type(op.resolved_type)
        return StructConstant(self.getargs(op), op.resolved_type, z3type)

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
        arg0, arg1, arg2 = self.getargs(op) 
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
        if isinstance(arg0, Constant):
            return Constant(supportcode.vector_subrange_fixed_bv_i_i(None, arg0.value, arg1.value, arg2.value))
        else:
            return Z3Value(z3.Extract(arg1.value, arg2.value, arg0.toz3()))
        
    def exec_zero_extend_bv_i_i(self, op):
        """ extend bitvector from arg1 to arg2 with zeros """
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, Constant):
            return Constant(arg0.value) # left zero extend doesnt change const int
        else:
            padding = z3.BitVec("padding", arg2.value - arg1.value)
            return Z3Value(z3.Concat(padding, arg0.toz3()))
        
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
