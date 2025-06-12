import z3
import collections
from pydrofoil import supportcode
from pydrofoil import ir, types

class Value(object):

    def __init__(self):
        # TODO: Resolved_Type
        self.value = None
    
    def __str__(self):
        return str(self.value)
    
    def __repr__(self):
        return self.__str__()
    
    def same_value(self, other):
        if not isinstance(other, Value):
            return False
        return self.value == other.value

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

class ConstantSmallBitVector(AbstractConstant): # TODO: rename to ConstantSmallBitVector
    
    def __init__(self, val):
        self.value = val

    def toz3(self):
        return int(self.value)
    
    def same_value(self, other):
        if not isinstance(other, ConstantSmallBitVector):
            return False
        return (self.value == other.value)


class ConstantInt(AbstractConstant): # TODO: renname to ConstantMachineInt
    def __init__(self, val):
        assert isinstance(val, int)
        self.value = val

    def toz3(self):
        return self.value
    
    def same_value(self, other):
        if not isinstance(other, ConstantInt):
            return False
        return self.value == other.value
  

class ConstantGenericInt(AbstractConstant):
    def __init__(self, val):
        assert isinstance(val, (int, long))
        self.value = val

    def toz3(self):
        return self.value
    
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

class UnitConstant(AbstractConstant):
    
    def __init__(self):
        pass

    def toz3(self):
        """ should never be called """
        assert 0
        return self.value
    
    def __str__(self):
        return "UNIT"
    
    def same_value(self, other):
        import pdb; pdb.set_trace()

    
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
        return self.w_val == other.w_val
    
    
class StructConstant(AbstractConstant):

    def __init__(self, vals_w, resolved_type, z3type):
        self.vals_w = vals_w
        self.resolved_type = resolved_type
        self.z3type = z3type
    
    def toz3(self):
        z3vals = [w_val.toz3() for w_val in self.vals_w]
        return self.z3type.a(*z3vals)
    
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
        
class Z3Value(Value):
    
    def __init__(self, val):
        self.value = val

    def toz3(self):
        return self.value
    
    def same_value(self, other):
        return False

    def not_(self):
        return Z3NotValue(self.value)
    
class Z3NotValue(Z3Value):

    def toz3(self):
        return z3.Not(self.value)
    
    def same_value(self, other):
        return False

    def not_(self):
        return Z3Value(self.value)
    
class SharedState(object):

    def __init__(self, functions={}, registers={}):
        self.funcs = functions
        self.registers = registers # type: dict[str, types.Type]
        self.enums = {}
        self.type_cache = {}
        self.union_field_cache = {} # (union_name,union_field):z3_type
        self.fork_counter = 0

    def get_z3_struct_type(self, resolved_type):
        if resolved_type in self.type_cache:
            return self.type_cache[resolved_type]
        sname = "struct_%s" % resolved_type.name
        struct = z3.Datatype(sname)
        fields = []
        # create struct
        for fieldname, typ in resolved_type.internalfieldtyps.items():
            fields.append((fieldname, self.convert_type_to_z3_type(typ)))
        # TODO: give the constructor a real names that contain struct name, calling it 'a' makes results very hard to read
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
                self.union_field_cache[(uname, variant)] = None # TODO: is this ok? this could go horribly wrong
            else:
                z3typ = self.convert_type_to_z3_type(typ)
                self.union_field_cache[(uname, variant)] = z3typ
                union.declare(variant, ("acc_" + variant, z3typ))# why
        union = union.create()
        self.type_cache[resolved_type] = union
        return union
    
    def ir_union_variant_to_z3_type(self, instance, union_type, field, to_type):
        """ create or get an instance of to_type as cast variant of given union variant
            args must be types not names """
        if not isinstance(to_type, tuple):# union
            assert isinstance(union_type, types.Union), "only unions allowed"
            union_type_z3 = self.get_z3_union_type(union_type)
            ftype = self.union_field_cache[(union_type_z3.name(), field)]
            typechecker = getattr(union_type_z3, "is_" + field)
            ### dont call accessor here, wont work ### 
            accessor = getattr(union_type_z3, "acc_" + field)
            ### dont call accessor here, wont work ### 
            default_value = z3.FreshConst(ftype, "error_in_typecast")
            ### call accessor only in z3 if ###
            return z3.If(typechecker(instance.toz3()), accessor(instance.toz3()), default_value)
        else:
            assert 0

    def get_z3_enum_type(self, resolved_type):
        """ get declared z3 enum type via ir type """
        if not resolved_type in self.type_cache:
            enum = self.register_enum(resolved_type.name, resolved_type.elements)
            self.type_cache[resolved_type] = enum
        return self.type_cache[resolved_type]
    
    def convert_type_or_instance_to_z3_instance(self, typ, name=""):
        """ create instance from ir type 
            e.g. for casting between types """
        z3type = self.convert_type_to_z3_type(typ)
        return z3.FreshConst(z3type, prefix=name or "temp")

    def convert_type_to_z3_type(self, typ):
        if isinstance(typ, types.SmallFixedBitVector):
            return z3.BitVecSort(typ.width)
        elif isinstance(typ, types.BigFixedBitVector):
            return z3.BitVecSort(typ.width)
        elif isinstance(typ, types.Union):
            return self.get_z3_union_type(typ)
        elif isinstance(typ, types.Struct):
            return self.get_z3_struct_type(typ)
        elif isinstance(typ, types.Enum):
            return self.get_z3_enum_type(typ)
        elif isinstance(typ, types.Bool) or typ == types.Bool:
            return z3.BoolSort()
        elif isinstance(typ, types.FVec):
            subtyp = self.convert_type_to_z3_type(typ.typ)
            return z3.ArraySort(z3.IntSort(), subtyp)
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
        """ copy state for tests """
        copystate = SharedState(self.funcs.copy(), self.registers.copy())
        copystate.enums = self.enums.copy()
        return copystate
    
    ## TODO: get_abstract... funcs can be unified to one, but requires test refactoring

    def get_abstract_enum_const_of_type(self, enum_name, var_name):
        """ Returns Const of given type that is neither equal nor unequal to any variant of given enum type """
        # TODO: change Const to FreshConst (needs test refactoring)
        return z3.Const(var_name, self.get_enum_type(enum_name))
    
    def get_abstract_union_const_of_type(self, union_type, var_name):
        """ Returns Const of given type that is neither equal nor unequal to any variant of given enum type """
        return z3.FreshConst(self.get_z3_union_type(union_type), prefix=var_name or "temp")
    
    def get_abstract_struct_const_of_type(self, struct_type, var_name):
        """ Returns Const of given type that is neither equal nor unequal to any variant of given enum type """
        return z3.FreshConst(self.get_z3_struct_type(struct_type), prefix=var_name or "temp")
    
    ## 
    
    def get_enum_type(self, name):
        """ Returns the Z3 Datatype Object of this enum """
        return self.enums["enum_" + name][0]

    def get_w_enum(self, name, variant):
        """ Returns the Z3 enum variant obj wrapped in Enum class """
        return Enum(name, variant, self.get_enum(name, variant))

    def get_enum(self, name, variant):
        """ Returns the Z3 enum variant obj """
        return self.enums["enum_" + name][1][variant]

class Interpreter(object):
    
    def __init__(self, graph, args, shared_state=None, entrymap=None):
        self.cls = Interpreter
        self.sharedstate = shared_state if shared_state != None else SharedState()
        self.graph = graph
        self.entrymap = entrymap if entrymap!=None else graph.make_entrymap()
        assert not graph.has_loop
        self.args = args
        assert len(args) == len(graph.args)
        self.environment = {graph.args[i]:args[i] for i in range(len(args))} # assume args are an instance of some z3backend.Value subclass
        self.forknum = self.sharedstate.fork_counter
        self.sharedstate.fork_counter += 1
        self.registers = {key: Z3Value(self.sharedstate.convert_type_or_instance_to_z3_instance(typ, "init_" + key)) for key, typ in self.sharedstate.registers.iteritems()}
        self.w_raises = BooleanConstant(False)
        ### TODO: Technicaly RPython cant return different types from a func, so this None handling, could be removed ???
        self.unconditional_raise = False # set to true to stop execution after encountering an unconditional raise
        self.w_result = None
        self.path_condition = []

    def run(self, block=None):
        """ interpret a graph, either begin with graph.startblock or the block passed as arg """
        todo = collections.deque() # what exactly is in the todo deque?
        block_to_interp = {} # block: interp | None
        def schedule(block, interp):
            if block in block_to_interp:
                assert block_to_interp[block] is None
                return
            block_to_interp[block] = None
            todo.append((block, interp))
        schedule(self.graph.startblock, self)
        while todo:
            index = 0
            current, interp = todo.popleft()
            assert block_to_interp[current] is None
            block_to_interp[current] = interp
            if len(self.entrymap[current]) > 1:
                ### BFS order does NOT guarantee that all block preceeding a phi are executed before encountering the phi, see Nand2Tetris decode_compute_backwards ###
                if self._check_if_merge_possible(self.entrymap[current], block_to_interp):
                    interp, index = self._compute_merge(current, interp, block_to_interp)
                else:
                    ### If we did not execute all preceeding blocks already, reschedule the phi and try again later ###
                    block_to_interp.pop(current)
                    schedule(current, interp)
                    continue
                ### TODO: think of a better solution for this ###
            interp._run_block(current, index)
            interp._schedule_next(current.next, schedule)
            if interp.w_result is not None:
                assert not todo
                # TODO: run should return w_result, memory, registers
                self.registers = interp.registers
                self.memory = interp.memory
                return interp.w_result
            
        return self.w_result

    def _run_block(self, block, index=0):
        for op in block.operations[index:]:
            self.execute_op(op)

    
    def _schedule_next(self, next, schedule):
        """ get next block to execute, or set ret value and return None, or fork interpreter on non const cond. goto """
        if isinstance(next, ir.Goto):
            schedule(next.target, self)
            return
        elif isinstance(next, ir.ConditionalGoto):
            w_cond = self.convert(next.booleanvalue)
            if 0 and isinstance(w_cond, BooleanConstant):
                # TODO: fix this
                if w_cond.value:
                    block = next.truetarget
                else:
                    block = next.falsetarget
                interp = self.fork()
                block = interp._run(block)
                for index, op in enumerate(block.operations):
                    if isinstance(op, ir.Phi):
                        assert len(op.prevvalues) == 2
                        trueindex = op.prevblocks.index(interp.prev_block)
                        self.environment[op] = interp.environment[op.prevvalues[trueindex]]
                    else:
                        break
                else:
                    index += 1
                self.registers = interp.registers
                self.memory = interp.memory
                self.w_result = interp.w_result
                # TODO: raise ...
                return block, index, True
            else:
                # fork 
                #print "fork in", self.graph.name, next.booleanvalue, "==", w_cond
                #self._debug_print("fork in " + self.graph.name)
                
                interp1 = self.fork(self.path_condition + [w_cond])
                interp1.environment[next.booleanvalue] = BooleanConstant(True)
                interp2 = self.fork(self.path_condition + [w_cond.not_()])
                interp2.environment[next.booleanvalue] = BooleanConstant(False)
                schedule(next.truetarget, interp1)
                schedule(next.falsetarget, interp2)
                return
        elif isinstance(next, ir.Return):
            self.w_result = self.convert(next.value)
        elif isinstance(next, ir.Raise):
            self.w_raises = BooleanConstant(True)
            #self.w_result = UnitConstant()
        else:
            assert 0, "implement %s" %str(next)
        return 
    
    def _check_if_merge_possible(self, prevblocks, block_to_interp):
        for prevblock in prevblocks:
            if block_to_interp.get(prevblock) is None: return False
        return True

    def _compute_merge(self, block, scheduleinterp, block_to_interp):
        prevblocks = self.entrymap[block]
        interp = scheduleinterp.fork()
        #for prevblock in prevblocks: # this check is already done in run
        #    assert block_to_interp.get(prevblock) is not None
        assert len(prevblocks) > 1
        for prevblock in prevblocks:
            previnterp = block_to_interp[prevblock]
            if previnterp is scheduleinterp: continue
            w_cond = previnterp.w_path_condition()
            interp.path_condition = [self._create_w_z3_or(interp.w_path_condition(), w_cond)]
            interp.registers = {reg:self._create_w_z3_if(w_cond, previnterp.registers[reg], interp.registers[reg]) for reg in self.registers}
            interp.memory = self._create_z3_if(w_cond.toz3(), previnterp.memory, interp.memory)
            interp.w_raises = self._create_w_z3_if(w_cond, previnterp.w_raises, interp.w_raises)     
        for index, op in enumerate(block.operations):
            if isinstance(op, ir.Phi):
                w_value = None
                for prevblock, prevvalue in zip(op.prevblocks, op.prevvalues):
                    previnterp = block_to_interp[prevblock]
                    w_prevvalue = previnterp.convert(prevvalue)
                    w_cond = previnterp.w_path_condition()
                    if w_value is None:
                        w_value = w_prevvalue
                    else:
                        w_value = self._create_w_z3_if(w_cond, w_prevvalue, w_value)
                interp.environment[op] = w_value
            else:
                return interp, index
        return interp, len(block.operations) # only phis in this block
        
    def w_path_condition(self):
        return self._create_w_z3_and(*self.path_condition)

    def _run(self, block=None):
        """ interpret a graph, either begin with graph.startblock or the block passed as arg """
        if block:
            cur_block = block
        else:
            cur_block = self.graph.startblock

        index = 0
        _cont = True
        while True:
            if len(self.entrymap[cur_block]) > 1 and not _cont:
                return cur_block

            for op in cur_block.operations[index:]:
                self.execute_op(op)
            
            next = cur_block.next
            self.prev_block = cur_block
            cur_block, index, _cont = self.execute_next(next)
            if (not cur_block) or self.unconditional_raise:
                break
        return None
    
    def fork(self, path_condition=None):
        """ create a copy of the interpreter, for evaluating non constant branches """
        cls = type(self)
        f_interp = cls(self.graph, self.args, self.sharedstate, self.entrymap)
        f_interp.environment = self.environment.copy()
        # TODO: How to model x86_64's registers for 64,32 and 16 bit ?  
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        f_interp.path_condition = self.path_condition if path_condition is None else path_condition
        return f_interp
    
    def call_fork(self, graph, args):
        """ create a copy of the interpreter, for evaluating func calls"""
        cls = type(self)
        f_interp = cls(graph, args, self.sharedstate, self.entrymap)
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        return f_interp
    
    def _create_z3_if(self, cond, true, false):
        return z3.If(cond, true, false)
    
    def _create_w_z3_if(self, w_cond, w_true, w_false):
        """ create z3 if, but only if w_true and w_false are non Constant or unequal"""
        if isinstance(w_cond, BooleanConstant):
            if w_cond.value:
                return w_true
            else:
                return w_false
        if w_true.same_value(w_false): return w_true
        # TODO: check for z3Not Value swap a and b theen
        if isinstance(w_cond, Z3NotValue):
            return Z3Value(z3.If(w_cond.value, w_false.toz3(), w_true.toz3()))
        return Z3Value(z3.If(w_cond.toz3(), w_true.toz3(), w_false.toz3()))
    
    def _create_w_z3_or(self, w_a, w_b):
        """ create z3 if, but only if w_true and w_false are non Constant or unequal"""
        if isinstance(w_a, BooleanConstant):
            if w_a.value:
                return w_a
            return w_b
        if isinstance(w_b, BooleanConstant):
            if w_b.value:
                return w_b
            return w_a
        if w_a.same_value(w_b): return w_a
        # TODO: check for equal z3value and not z3value
        return Z3Value(z3.Or(w_a.toz3(), w_b.toz3()))

    def _create_w_z3_and(self, *args_w):
        if args_w == []:
            return BooleanConstant(True)
        if len(args_w) == 1:
            return args_w[0]
        for w_arg in args_w:
            if isinstance(w_arg, BooleanConstant):
                if not w_arg.value: return BooleanConstant(False)
        # TODO: filter out true args
        return Z3Value(z3.And(*[w_arg.toz3() for w_arg in args_w]))  
    
    def merge_raise(self, w_cond, w_res_true, w_res_false, interp1, interp2):
        """ Handle Exceptions, when a raise block raises the forks result is UNIT """
        if (isinstance(interp1.w_raises, BooleanConstant) and interp1.w_raises.value == True 
           and isinstance(interp2.w_raises, BooleanConstant) and interp2.w_raises.value == True):
            self.w_result = UnitConstant() # if both forks raise, then there is no result
            self.w_raises = BooleanConstant(True)
        elif isinstance(interp1.w_raises, BooleanConstant) and interp1.w_raises.value == True:
            self.w_raises = self._create_w_z3_if(w_cond, BooleanConstant(True), interp2.w_raises)
        elif isinstance(interp2.w_raises, BooleanConstant) and interp2.w_raises.value == True:
            self.w_raises = self._create_w_z3_if(w_cond, interp1.w_raises, BooleanConstant(True))
        else:
            self.w_raises = self._create_w_z3_if(w_cond, interp1.w_raises, interp2.w_raises)

    def merge_result(self, w_cond, w_res_true, w_res_false, interp1, interp2):
        """ Handle Unit ~ None, when we return a UNIT we must handle it without converting it to z3
            Neither raise nor UNIT return somthing """
        if isinstance(w_res_true, UnitConstant) and isinstance(w_res_false, UnitConstant):
            self.w_result = UnitConstant() # parent interpreter must handle this or this is the generel return value
        elif isinstance(w_res_true, UnitConstant): 
            self.w_result = w_res_false
        elif isinstance(w_res_false, UnitConstant):
            self.w_result = w_res_true
        else:
            self.w_result = self._create_w_z3_if(w_cond, w_res_true, w_res_false)

    def execute_next(self, next):
        """ get next block to execute, or set ret value and return None, or fork interpreter on non const cond. goto """
        if isinstance(next, ir.Goto):
            return next.target, 0, False
        elif isinstance(next, ir.ConditionalGoto):
            w_cond = self.convert(next.booleanvalue)
            import pdb;  pdb.set_trace()
            if isinstance(w_cond, BooleanConstant):
                if w_cond.value:
                    block = next.truetarget
                else:
                    block = next.falsetarget
                interp = self.fork()
                block = interp._run(block)
                for index, op in enumerate(block.operations):
                    if isinstance(op, ir.Phi):
                        assert len(op.prevvalues) == 2
                        trueindex = op.prevblocks.index(interp.prev_block)
                        self.environment[op] = interp.environment[op.prevvalues[trueindex]]
                    else:
                        break
                else:
                    index += 1
                self.registers = interp.registers
                self.memory = interp.memory
                self.w_result = interp.w_result
                # TODO: raise ...
                return block, index, True
            else:
                # fork 
                #print "fork in", self.graph.name, next.booleanvalue, "==", w_cond
                #self._debug_print("fork in " + self.graph.name)
                interp1 = self.fork()
                interp1.environment[next.booleanvalue] = BooleanConstant(True)
                interp2 = self.fork()
                interp2.environment[next.booleanvalue] = BooleanConstant(False)
                block1 = interp1._run(next.truetarget)
                block2 = interp2._run(next.falsetarget)
                assert block1 == block2
                # TODO: run_to_phi that returns interp
                # merge excepions, remove not needed branches of one interp raises
                self.merge_raise(w_cond, w_res_true, w_res_false, interp1, interp2)
                # merge results, remove not needed branches of one interp returns UNIT
                self.merge_result(w_cond, w_res_true, w_res_false, interp1, interp2)

                import pdb; pdb.set_trace()
                for index, op in enumerate(block1.operations):
                    if isinstance(op, ir.Phi):
                        assert len(op.prevvalues) == 2
                        trueindex = op.prevblocks.index(interp1.prev_block)
                        w_res_true = interp1.environment[op.prevvalues[trueindex]]
                        falseindex = op.prevblocks.index(interp2.prev_block)
                        w_res_false = interp2.environment[op.prevvalues[falseindex]]
                        self.environment[op] = self._create_w_z3_if(w_cond, w_res_true, w_res_false)
                    else:
                        break
                else:
                    index += 1

                # merge memory and registers
                self.registers = {reg:self._create_w_z3_if(w_cond, interp1.registers[reg], interp2.registers[reg]) for reg in self.registers}
                self.memory = self._create_z3_if(w_cond.toz3(), interp1.memory, interp2.memory)
                #self._debug_print("merge " + self.graph.name + " " + str(self.w_result))
                return block1, index, True

        elif isinstance(next, ir.Return):
            self.w_result = self.convert(next.value)
        elif isinstance(next, ir.Raise):
            self.w_raises = BooleanConstant(True)
            self.w_result = UnitConstant()
        else:
            assert 0, "implement %s" %str(next)
        return None, 0, False
    
    def _debug_print(self, msg=""):
        print "interp_%s:" % self.forknum, msg

    def create_z3_enum(self, name, variants):
        """ create a z3 datatype for an enum and store in shared state """
        self.sharedstate.register_enum(name, variants)

    def convert(self, arg):
        """ wrap an argument or load wrapped arg from env """
        if isinstance(arg, ir.SmallBitVectorConstant):
            w_arg = ConstantSmallBitVector(arg.value)
        elif isinstance(arg, ir.EnumConstant):
            enumname =  "enum_%s" % arg.resolved_type.name
            if not enumname in self.sharedstate.enums:
                self.create_z3_enum(arg.resolved_type.name, arg.resolved_type.elements)
            z3variant = self.sharedstate.enums[enumname][1][arg.variant] # self.sharedstate.enums[enumname][0] is z3 Datatype obj [1] is mapping variant_name:z3variant
            w_arg = Enum(arg.resolved_type.name, arg.variant, z3variant)
        elif isinstance(arg, ir.Constant):
            if isinstance(arg, ir.MachineIntConstant):
                w_arg = ConstantInt(arg.number)
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
        """ read from register, (registers must be all created on class init) """
        return self.registers[register]
    
    def write_register(self, register, value):
        """ write to register """
        self.registers[register] = value

    def read_memory(self, addr):
        """ read from memory, creates new 'empty' z3 Val for mem addresses on first access """
        return self.memory[addr.toz3()]
    
    def wrte_memory(self, addr, value):
        """ write to memory """
        self.memory = z3.Store(self.memory, addr.toz3(), value.toz3())

    def exec_phi(self, op):
        """ get value of actual predecessor """
        assert 0, "Every phi should be handled in _compute_merge"
        index = op.prevblocks.index(self.prev_block)
        return self.convert(op.prevvalues[index])
    
    def execute_op(self, op):
        """ execute an operation and write result into environment """
        if isinstance(op, ir.Phi):
            result = self.exec_phi(op)
        elif isinstance(op, ir.UnionCast):
            result = self.exec_union_cast(op)
        elif isinstance(op, ir.GlobalRead):
            result = self.read_register(op.name)
        elif isinstance(op, ir.GlobalWrite):
            ### TODO: Are register writes supposed to return the written value?? ###
            self.write_register(op.name, self.getargs(op)[0])
            return
        elif hasattr(self, "exec_%s" % op.name.replace("@","")):
            func = getattr(self, "exec_%s" % op.name.replace("@",""))
            result = func(op) # self passed implicitly
            if result == None: return
        elif isinstance(op, ir.NonSSAAssignment):
            import pdb; pdb.set_trace()
        elif op.is_union_creation():
            result = self.exec_union_creation(op)
        elif isinstance(op, ir.FieldAccess):
            result = self.exec_field_access(op)
        elif op.name in self.sharedstate.funcs:
            result = self.exec_func_call(op, self.sharedstate.funcs[op.name])
        elif isinstance(op, ir.Comment):
            return
        elif isinstance(op, ir.StructConstruction):
            result = self.exec_struct_construction(op)
        elif isinstance(op, ir.UnionVariantCheck):
            result = self.exec_union_variant_check(op)
        else:
            assert 0 , str(op.name) + ", " + str(op) + "," + "exec_%s" % op.name.replace("@","")
        self.environment[op] = result
    
    ### Generic Operations ###

    def exec_func_call(self, op, graph):
        self._debug_print("graph " + self.graph.name + " func call " + op.name)

        args = self.getargs(op)
        interp_fork = self.call_fork(graph, args)
        w_res = interp_fork.run()
        self.registers = interp_fork.registers
        self.memory = interp_fork.memory
        if isinstance(interp_fork.w_raises, BooleanConstant):
            if interp_fork.w_raises.value == True:# case: func raises without condition
                self.w_raises = BooleanConstant(True)
                self.unconditional_raise = True
                self.w_result = UnitConstant()
            else:
                # self.w_raises is self.w_raises or False
                pass
        else: # case: func did or didnt raise, but raise was behind a condition
            self.w_raises = self._create_w_z3_or(self.w_raises, interp_fork.w_raises)
        self._debug_print("return from " + op.name + " -> " + str(w_res))
        return w_res

    def exec_struct_construction(self, op):
        """ Execute a Lazy Struct creation"""
        z3type = self.sharedstate.get_z3_struct_type(op.resolved_type)
        return StructConstant(self.getargs(op), op.resolved_type, z3type)
    
    def exec_field_access(self, op):
        """ access field of struct """
        field = op.name
        struct, = self.getargs(op)
        struct_type = op.args[0].resolved_type
        struct_type_z3 = self.sharedstate.get_z3_struct_type(struct_type)
        if isinstance(struct, StructConstant):
            index = struct.resolved_type.names.index(op.name)
            return struct.vals_w[index]
        res = getattr(struct_type_z3, field)(struct.toz3())# get accessor from slot with getattr
        return Z3Value(res)

    def exec_union_variant_check(self, op):
        instance, = self.getargs(op)
        if isinstance(instance, UnionConstant):
            return BooleanConstant(instance.variant_name != op.name) # confusingly enough, the result is negated from what one would expect
        else:
            import pdb;pdb.set_trace()
        
    def exec_union_cast(self, op):
        ###  this cast specializes an instance of a union to one if its subtypes like:
        ###    union(bird, (duck, goose), ...)
        ###    instance_of_duck = UnionCast(instance_of_bird, duck)
        ### TODO: Did RPython already check that the types fit, or could that fail?
        ###       if yes => remove typecheck in sharedstate.ir_union_variant_to_z3_type
        union_type = op.args[0].resolved_type
        to_specialized_variant = op.name 
        res_type = op.resolved_type# TODO: res_type can be removed, maybe ? 
        instance, = self.getargs(op)
        if isinstance(instance, Z3Value):
            z3_cast_instance = self.sharedstate.ir_union_variant_to_z3_type(instance, union_type, to_specialized_variant, res_type)
            return Z3Value(z3_cast_instance)
        elif isinstance(instance, UnionConstant):
            assert op.name == instance.variant_name
            return instance.w_val
        else:
            assert 0

    def exec_union_creation(self, op):
        """ Execute a Lazy Union creation"""
        z3type = self.sharedstate.get_z3_union_type(op.resolved_type)
        return UnionConstant(op.name, self.getargs(op)[0], op.resolved_type, z3type)

    def exec_signed_bv(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt):
            res = ConstantInt(supportcode.signed_bv(None, arg0.value, arg1.value))
        else:
            # machine ints are represented as 64-bit bit vectors in z3
            res = Z3Value(z3.SignExt(64 - arg1.value, arg0.toz3()))
        return res

    def exec_eq_bits_bv_bv(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return BooleanConstant(arg0.value == arg1.value)
        else:
            return Z3Value(arg0.toz3() == arg1.toz3())
    
    def exec_eq(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value == arg1.value)
        if isinstance(arg0, Enum) and isinstance(arg1, Enum):
            return BooleanConstant(arg0 == arg1)
        else:
            assert isinstance(arg0, Z3Value) or isinstance(arg1, Z3Value)
            return Z3Value(arg0.toz3() == arg1.toz3())
    
    def exec_gt(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value > arg1.value)
        else:
            return Z3Value(arg0.toz3() > arg1.toz3())
    
    def exec_gteq(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value >= arg1.value)
        else:
            return Z3Value(arg0.toz3() >= arg1.toz3())

            
    def exec_lt(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value < arg1.value)
        else:
            return Z3Value(arg0.toz3() < arg1.toz3())

            
    def exec_lteq(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value <= arg1.value)
        else:
            return Z3Value(arg0.toz3() <= arg1.toz3())
        
    def exec_lt_unsigned64(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value < arg1.value)
        else:
            return Z3Value(z3.ULT(arg0.toz3(), arg1.toz3()))
            
    def exec_not(self, op):
        arg0, = self.getargs(op)
        if isinstance(arg0, BooleanConstant):
            return BooleanConstant(not arg0.value)
        else:
            return arg0.not_()
        
    def exec_not_vec_bv(self, op):
        arg0, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(~arg0.value)
        else:
            return Z3Value(~arg0.toz3())
        
    def exec_sub_bits_bv_bv(self, op):
        arg0, arg1, arg2 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value - arg1.value)
        else:
            return Z3Value(arg0.toz3() - arg1.toz3())

    def exec_add_bits_int_bv_i(self, op):
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt):
            return ConstantSmallBitVector(supportcode.add_bits_int_bv_i(None, arg0.value, arg1.value)) 
        else:
            return Z3Value(arg0.toz3() + arg1.toz3())

    def exec_add_bits_bv_bv(self, op):
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value + arg1.value) 
        else:
            return Z3Value(arg0.toz3() + arg1.toz3())

    def exec_and_vec_bv_bv(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value & arg1.value) 
        else:
            return Z3Value(arg0.toz3() & arg1.toz3())
        
    def exec_xor_vec_bv_bv(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value ^ arg1.value) 
        else:
            return Z3Value(arg0.toz3() ^ arg1.toz3())

    def exec_or_vec_bv_bv(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value | arg1.value) 
        else:
            return Z3Value(arg0.toz3() | arg1.toz3())
        
    def exec_vector_subrange_fixed_bv_i_i(self, op):
        """ slice bitvector as bv[arg1:arg0] both inclusive """
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(supportcode.vector_subrange_fixed_bv_i_i(None, arg0.value, arg1.value, arg2.value))
        else:
            return Z3Value(z3.Extract(arg1.value, arg2.value, arg0.toz3()))

    def exec_zero_extend_bv_i_i(self, op):
        """ extend bitvector from arg1 to arg2 with zeros """
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.valued)
        else:
            return Z3Value(z3.ZeroExt(arg2.value - arg1.value, arg0.toz3()))

    def exec_sign_extend_bv_i_i(self, op):
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(supportcode.sign_extend_bv_i_i(None, arg0.value, arg1.value, arg2.value))
        else:
            return Z3Value(z3.SignExt(arg2.value - arg1.value, arg0.toz3()))

    def exec_unsigned_bv(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt):
            return ConstantInt(supportcode.unsigned_bv(None, arg0.value, arg1.value))
        else:
            return Z3Value(z3.ZeroExt(64 - arg1.value, arg0.toz3()))

    def exec_zz5i64zDzKz5i(self, op): # %i64->%i
        arg0, = self.getargs(op)
        if isinstance(arg0, ConstantInt):
            return ConstantGenericInt(arg0.value)
        else:
            return Z3Value(z3.BV2Int(arg0.toz3()))

    ### Arch specific Operations in subclass ###

class NandInterpreter(Interpreter):
    """ Interpreter subclass for nand2tetris ISA """

    def __init__(self, graph, args, shared_state=None, entrymap=None):
        super(NandInterpreter, self).__init__(graph, args, shared_state, entrymap)# py2 super 
        self.memory = z3.Array('memory', z3.BitVecSort(16), z3.BitVecSort(16))
        self.cls = NandInterpreter
    
    ### Nand specific Operations ###

    def exec_my_read_mem(self, op):
        """ read from memory """
        addr,  = self.getargs(op)
        return Z3Value(self.read_memory(addr))
    
    def exec_my_write_mem(self, op):
        """ write value to memory """
        ### TODO: Are mem writes supposed to return the written value?? ###
        addr, value  = self.getargs(op)
        self.wrte_memory(addr, value) # TODO: fix typo

class RiscvInterpreter(Interpreter):
    """ Interpreter subclass for RISCV ISA """

    def __init__(self, graph, args, shared_state=None, _64bit=False):# TODO , entrymap=None
        bits = 64 if _64bit else 32 
        super(RiscvInterpreter, self).__init__(graph, args, shared_state)# py2 super 
        self.memory = z3.Array('memory', z3.BitVecSort(bits), z3.BitVecSort(bits))
        self.cls = RiscvInterpreter

    def exec_zsys_enable_zzfinx(self, op):
        return BooleanConstant(True)

    def exec_zsys_enable_svinval(self, op):
        return BooleanConstant(True)

    def exec_zsys_enable_zzicbozz(self, op):
        return BooleanConstant(True)

    def exec_zget_config_print_reg(self, op):
        return BooleanConstant(False)
