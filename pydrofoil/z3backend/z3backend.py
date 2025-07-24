import z3
import collections
from pydrofoil import supportcode
from pydrofoil import ir, types
from pydrofoil.z3backend.z3btypes import *

class SharedState(object):

    def __init__(self, functions={}, registers={}, methods={}):
        self.funcs = functions
        self.mthds = methods
        self.registers = registers # type: dict[str, types.Type]
        self.enums = {}
        self.type_cache = {}
        self.union_field_cache = {} # (union_name,union_field):z3_type
        self.struct_z3_field_map = {}
        self.struct_unit_fields = set()
        unit = z3.Datatype("____unit____")
        unit.declare("UNIT")
        self._z3_unit_type = unit.create()
        self._z3_unit = self._z3_unit_type.UNIT
        self.fork_counter = 0


    def get_z3_struct_type(self, resolved_type):
        if resolved_type in self.type_cache:
            return self.type_cache[resolved_type]
        sname = "struct_%s" % resolved_type.name
        struct = z3.Datatype(sname)
        fields = []
        # create struct
        for fieldname, typ in resolved_type.internalfieldtyps.items():
            if isinstance(typ, types.Unit):
                self.struct_unit_fields.add((struct, fieldname))
                fields.append((fieldname, self._z3_unit_type))
            else:
                fields.append((fieldname, self.convert_type_to_z3_type(typ)))
        # TODO: give the constructor a real names that contain struct name, calling it 'a' makes results very hard to read
        struct.declare("a", *fields)
        struct = struct.create()
        self.type_cache[resolved_type] = struct
        self.struct_z3_field_map[struct] = (fields, resolved_type)
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
            import pdb; pdb.set_trace()
    
    def get_ir_union_typechecker(self, union_type, variant):
        """ get the is_x method for a union, e.g, for union variant check """
        assert isinstance(union_type, types.Union), "only unions allowed"
        union_type_z3 = self.get_z3_union_type(union_type)
        return getattr(union_type_z3, "is_" + variant)
      

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
        elif isinstance(typ, types.GenericBitVector):
            return z3.BitVecSort(64)# TODO: generic bs as 64 bit bv?
            #return z3.BitVecSort()
        elif isinstance(typ, types.MachineInt):
            return z3.IntSort()# This must be the number bits of the machine that runs pydrofoil
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
        elif isinstance(typ, types.String):
            return z3.StringSort()
        elif isinstance(typ, types.Packed):# packed only in python, not on z3 level
            return self.convert_type_to_z3_type(typ.typ)
        else:
            import pdb; pdb.set_trace()

    def get_w_class_for_ztype(self, ztype):
        """ get the z3backend  wrapper class appropriate for the given z3 type """
        # TODO: think of how to get more specialised types
        if ztype == z3.BoolSort(): return Z3BoolValue 
        if ztype == z3.StringSort(): return Z3StringValue
        # TODO. maybe this must check for the shared_state unit constant?
        return Z3Value

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
        copystate = SharedState(self.funcs.copy(), self.registers.copy(), self.mthds.copy())
        copystate.enums = self.enums.copy()
        return copystate
    
    ## TODO: Replace usage of those funcs with get_abstract_const_of_ztype and convert_type_to_z3_type

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

    def get_abstract_const_of_ztype(self, ztype, var_name):
        """ Returns Const of given type that is neither equal nor unequal to any variant of given enum type """
        return z3.FreshConst(ztype, prefix=var_name)
    
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
        self.sharedstate = shared_state if shared_state != None else SharedState()
        self.graph = graph
        self.entrymap = entrymap if entrymap != None else graph.make_entrymap()
        assert not graph.has_loop
        self.args = args
        assert len(args) == len(graph.args)
        self.environment = {graph.args[i]:args[i] for i in range(len(args))} # assume args are an instance of some z3backend.Value subclass
        self.forknum = self.sharedstate.fork_counter
        self.sharedstate.fork_counter += 1
        self.registers = {key: Z3Value(self.sharedstate.convert_type_or_instance_to_z3_instance(typ, "init_" + key)) for key, typ in self.sharedstate.registers.iteritems()}
        self.w_raises = BooleanConstant(False)
        self.w_result = None
        self.path_condition = []

    def _set_graph_reset_env_set_args(self, graph, args):
        """ only for z3backend_executor.
            do not use elsewhere """
        self.graph = graph
        self.environment = {graph.args[i]:args[i] for i in range(len(args))} # assume args are an instance of some z3backend.Value subclass

    def run(self, block=None):
        """ interpret a graph, either begin with graph.startblock or the block passed as arg """
        todo = collections.deque()
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
                    self.registers = interp.registers
                    self.memory = interp.memory
                else:
                    ### If we did not execute all preceeding blocks already, reschedule the phi and try again later ###
                    block_to_interp.pop(current)
                    schedule(current, interp)
                    continue
                ### TODO: think of a better solution for this ###
            #interp._debug_print("run block %s" % str(current.next))
            interp._run_block(current, index)
            interp._schedule_next(current.next, schedule)
            if not self is interp:
                self.w_raises = self._top_level_raise_merge(interp.w_raises)

            if interp.w_result is not None:
                assert not todo
                ## important for a block like : func_call("func_write_register", "RAX",  "54646545"), return 17 ##
                self.memory = interp.memory
                self.registers = interp.registers
                ##
                return interp.w_result # TODO: run should return w_result, memory, registers
        
        assert not todo     
        return self.w_result
    
    def _top_level_raise_merge(self, w_raises):
        if isinstance(w_raises, BooleanConstant):
            if w_raises.value:
                return w_raises
            else:
                return self.w_raises
        return self.w_raises._create_w_z3_or(w_raises)
    
    def _is_unreachable(self):
        for w_cond in self.path_condition:
            if isinstance(w_cond, BooleanConstant) and not w_cond.value:
                return True
        return False

    def _run_block(self, block, index=0):
        if self._is_unreachable():
            for op in block.operations[index:]:
                self.execute_default_op(op)
        else:    
            for op in block.operations[index:]:
                self.execute_op(op)

    
    def _schedule_next(self, block_next, schedule):
        """ get next block to execute, or set ret value and return None, or fork interpreter on non const cond. goto """
        if isinstance(block_next, ir.Goto):
            schedule(block_next.target, self.fork(self.path_condition))
            return
        elif isinstance(block_next, ir.ConditionalGoto):
            w_cond = self.convert(block_next.booleanvalue)

            interp1 = self.fork(self.path_condition + [w_cond])# TODO: handle the conditions better
            interp1.environment[block_next.booleanvalue] = BooleanConstant(True)

            interp2 = self.fork(self.path_condition + [w_cond.not_()])
            interp2.environment[block_next.booleanvalue] = BooleanConstant(False)

            ### we need to now in merge if the current block is actually reachable ###
            self.child_cond_map = {block_next.truetarget: w_cond, block_next.falsetarget: w_cond.not_()}

            schedule(block_next.truetarget, interp1)
            schedule(block_next.falsetarget, interp2)
        elif isinstance(block_next, ir.Return):
            if not self._is_unreachable(): # only set result if it is reachable
                self.w_result = self.convert(block_next.value)
        elif isinstance(block_next, ir.Raise):
            self.w_raises = self.w_path_condition()
        else:
            assert 0, "implement %s" %str(block_next)
        return 
    
    def _check_if_merge_possible(self, prevblocks, block_to_interp):
        for prevblock in prevblocks:
            if block_to_interp.get(prevblock) is None: return False
        return True

    def _compute_merge(self, block, scheduleinterp, block_to_interp):
        prevblocks = self.entrymap[block]
        assert len(prevblocks) > 1
        for prevblock in prevblocks:
            previnterp = block_to_interp[prevblock]
            if previnterp is scheduleinterp: continue
            w_cond = previnterp.w_path_condition()
            if isinstance(prevblock.next, ir.ConditionalGoto):
                # if prev was a ConditionalGoto we need to add cond to the parents path
                w_cond = w_cond._create_w_z3_and(previnterp.child_cond_map[block])
            scheduleinterp.path_condition = [scheduleinterp.w_path_condition()._create_w_z3_or(w_cond)]
            scheduleinterp.registers = {reg:w_cond._create_w_z3_if(previnterp.registers[reg], scheduleinterp.registers[reg]) for reg in self.registers}
            scheduleinterp.memory = self._create_z3_if(w_cond.toz3(), previnterp.memory, scheduleinterp.memory)
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
                        w_value = w_cond._create_w_z3_if(w_prevvalue, w_value)
                scheduleinterp.environment[op] = w_value
            else:
                return scheduleinterp, index
        return scheduleinterp, len(block.operations) # only phis in this block
        
    def w_path_condition(self):
        # TODO: think of a better way to handle this
        return BooleanConstant(True)._create_w_z3_and(*self.path_condition)
    
    def fork(self, path_condition=None):
        """ create a copy of the interpreter, for evaluating non constant branches """
        cls = type(self)
        f_interp = cls(self.graph, self.args, self.sharedstate, self.entrymap)
        f_interp.environment = self.environment.copy()
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        f_interp.path_condition = self.path_condition if path_condition is None else path_condition
        f_interp.w_raises = self.w_raises # if self raises, the fork must to
        return f_interp
    
    def call_fork(self, graph, args):
        """ create a copy of the interpreter, for evaluating func calls"""
        cls = type(self)
        f_interp = cls(graph, args, self.sharedstate)# dont pass entrymap, must compute entrymap for new graph in init
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        f_interp.w_raises = self.w_raises
        f_interp.path_condition = self.path_condition
        return f_interp
    
    def _create_z3_if(self, cond, true, false):
        return z3.If(cond, true, false)
    
    def _debug_print(self, msg=""):
        print "interp_%s: " % self.forknum, msg

    def convert(self, arg):
        """ wrap an argument or load wrapped arg from env """
        if isinstance(arg, ir.SmallBitVectorConstant):
            w_arg = ConstantSmallBitVector(arg.value, arg.resolved_type.width)
        elif isinstance(arg, ir.EnumConstant):
            enumname =  "enum_%s" % arg.resolved_type.name
            if not enumname in self.sharedstate.enums:
                self.sharedstate.register_enum(arg.resolved_type.name, arg.resolved_type.elements)
            z3variant = self.sharedstate.enums[enumname][1][arg.variant] # self.sharedstate.enums[enumname][0] is z3 Datatype obj [1] is mapping variant_name:z3variant
            w_arg = Enum(arg.resolved_type.name, arg.variant, z3variant)
        elif isinstance(arg, ir.Constant):
            if isinstance(arg, ir.MachineIntConstant):
                w_arg = ConstantInt(arg.number)
            elif isinstance(arg, ir.BooleanConstant):
                w_arg = BooleanConstant(arg.value)
            elif isinstance(arg, ir.UnitConstant):
                w_arg = UnitConstant()
            elif isinstance(arg, ir.StringConstant):
                w_arg = StringConstant(arg.string)
            else:
                assert 0, "Some ir Constant " + str(arg) 
        elif isinstance(arg, types.Packed):
            # TODO: can this even happen?
            import pdb; pdb.set_trace()
        else:
            w_arg = self.environment[arg]    
        return w_arg

    def getargs(self, op):
        """ get all wrapped args of an operation """
        res = []
        for arg in op.args:
            w_arg = self.convert(arg)
            res.append(w_arg)
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
    
    def write_memory(self, addr, value):
        """ write to memory """
        self.memory = z3.Store(self.memory, addr.toz3(), value.toz3())

    def exec_phi(self, op):
        """ get value of actual predecessor """
        assert 0, "Every phi should be handled in _compute_merge"
        index = op.prevblocks.index(self.prev_block)
        return self.convert(op.prevvalues[index])
    
    def execute_default_op(self, op):
        """ pseudo execute an operation, write default value into env """
        if isinstance(op, ir.Phi):
            assert 0, "Every phi should be handled in _compute_merge"
        elif op.resolved_type == types.Unit():
            pass
        elif op.resolved_type == types.GenericBitVector():
            pass
        else:
            rtype = op.resolved_type
            ztype = self.sharedstate.convert_type_to_z3_type(rtype)
            z_instance = self.sharedstate.get_abstract_const_of_ztype(ztype, "unreachable_const_of_" + str(ztype))
            w_class = self.sharedstate.get_w_class_for_ztype(ztype)
            self.environment[op] = w_class(z_instance)
    
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
        elif hasattr(self, "exec_%s" % op.name.replace("@","").replace("$","")):
            func = getattr(self, "exec_%s" % op.name.replace("@","").replace("$",""))
            result = func(op) # self passed implicitly
            if result == None: return
        elif isinstance(op, ir.NonSSAAssignment):
            import pdb; pdb.set_trace()
        elif op.is_union_creation():
            result = self.exec_union_creation(op)
        elif isinstance(op, ir.FieldAccess):
            result = self.exec_field_access(op)
        elif isinstance(op,  ir.FieldWrite):
            self.exec_field_write(op)
            return
        elif op.name in self.sharedstate.mthds:
            result = self.exec_method_call(op, self.sharedstate.mthds[op.name])
        elif op.name in self.sharedstate.funcs:
            result = self.exec_func_call(op, self.sharedstate.funcs[op.name])
        elif isinstance(op, ir.Comment):
            return
        elif isinstance(op, ir.StructConstruction):
            result = self.exec_struct_construction(op)
        elif isinstance(op, ir.StructCopy):
            result = self.exec_struct_copy(op)
        elif isinstance(op, ir.UnionVariantCheck):
            result = self.exec_union_variant_check(op)
        elif op.name.startswith("zeq_anything"):
            result = self.exec_eq_anything(op)
        else:
            assert 0 , str(op.name) + ", " + str(op) + "," + "exec_%s" % op.name.replace("@","").replace("$","")
        self.environment[op] = result
    
    ### Generic Operations ###

    def exec_eq_anything(self, op):
        """ check for equality """
        ### TODO: is this really generic or only for RISC-V ??? ###
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, Z3Value) or isinstance(arg1, Z3Value):
            return Z3BoolValue(arg0.toz3() == arg1.toz3())
        elif isinstance(arg0, UnionConstant) and isinstance(arg1, UnionConstant):
            same = arg0.same_value(arg1)# TODO: change this, so it does not return three different values (True, False, z3Val)
            if same == True:
                return BooleanConstant(True)
            elif same == False:
                return BooleanConstant(False)
            else:
                return Z3BoolValue(same)
        else:
            import pdb; pdb.set_trace()

    def exec_func_call(self, op, graph):
        self._debug_print("graph " + self.graph.name + " func call " + op.name)
        func_args = self.getargs(op)
        interp_fork = self.call_fork(graph, func_args)
        w_res = interp_fork.run()
        self.registers = interp_fork.registers
        self.memory = interp_fork.memory
        if isinstance(interp_fork.w_raises, BooleanConstant):
            if interp_fork.w_raises.value == True:# case: func raises without condition
                self.w_raises = BooleanConstant(True)
                self.w_result = UnitConstant()
            else:
                # self.w_raises is self.w_raises or False
                pass
        else: 
            # case: func did or didnt raise, but raise was behind a condition
            self.w_raises = self.w_raises._create_w_z3_or(interp_fork.w_raises)
        self._debug_print("return from " + op.name) #+ " -> " + str(w_res))
        return w_res
    
    def _select_method_graph(self, arg0, method_graphs):
        """ select method graph depending on first arg for method call """
        ## arg0 is the 'object' the method is called on
        if isinstance(arg0, UnionConstant):
            if arg0.variant_name in method_graphs: return method_graphs[arg0.variant_name]
            # these methods usually have an else case, and that graph has no name
            # on caching these graphs in test_z3riscv.py I named that graph ___default___
            return method_graphs["___default___"] 
        assert 0, "implement method selection on %s" % str(type(arg0))

    def exec_method_call(self, op, graphs):
        func_args = self.getargs(op)
        graph = self._select_method_graph(func_args[0], graphs)
        self._debug_print("graph " + self.graph.name + " mthd call " + op.name)
        interp_fork = self.call_fork(graph, func_args)
        w_res = interp_fork.run()
        self.registers = interp_fork.registers
        self.memory = interp_fork.memory
        if isinstance(interp_fork.w_raises, BooleanConstant):
            if interp_fork.w_raises.value == True:# case: func raises without condition
                self.w_raises = BooleanConstant(True)
                self.w_result = UnitConstant()
            else:
                # self.w_raises is self.w_raises or False
                pass
        else: 
            # case: func did or didnt raise, but raise was behind a condition
            self.w_raises = self.w_raises._create_w_z3_or(interp_fork.w_raises)
        self._debug_print("return from " + op.name) #+ " -> " + str(w_res))
        return w_res
    
    def exec_allocate(self, op):
        if isinstance(op.resolved_type, types.Struct):
            z3type = self.sharedstate.get_z3_struct_type(op.resolved_type)
            fields, _ = self.sharedstate.struct_z3_field_map[z3type]
            vals_w = []
            for field, typ in fields:
                if type is not self.sharedstate._z3_unit:
                    val = self.sharedstate.get_abstract_const_of_ztype(typ, "alloc_uninit_%s_" % field)
                else:
                    val = self.sharedstate._z3_unit
                vals_w.append(self.sharedstate.get_w_class_for_ztype(typ)(val))
            return StructConstant(vals_w, op.resolved_type, z3type)
        assert 0 , "implement allocate %s" % str(op.resolved_type)
    
    def exec_struct_construction(self, op):
        """ Execute a Lazy Struct creation """
        z3type = self.sharedstate.get_z3_struct_type(op.resolved_type)
        return StructConstant(self.getargs(op), op.resolved_type, z3type)
    
    def exec_struct_copy(self, op):
        """ TODO: is this a shallow or deep copy? """
        arg, = self.getargs(op)
        return arg.copy()

    def exec_field_access(self, op):
        """ access field of struct """
        field = op.name
        struct, = self.getargs(op)
        struct_type = op.args[0].resolved_type
        struct_type_z3 = self.sharedstate.get_z3_struct_type(struct_type)
        ## structs can have fields of type  unit, those are always UNIT
        if (struct_type_z3, field) in self.sharedstate.struct_unit_fields:
            return UnitConstant() 
        if isinstance(struct, StructConstant):
            index = struct.resolved_type.names.index(op.name)
            return struct.vals_w[index]
        res = getattr(struct_type_z3, field)(struct.toz3())# get accessor from slot with getattr
        if res.sort() == z3.BoolSort():
            return Z3BoolValue(res)
        return Z3Value(res)

    def exec_field_write(self, op):
        """ write into struct field.
            By creating a new struct instance """
        field_to_replace = op.name
        struct, new_value = self.getargs(op)
        struct_type = op.args[0].resolved_type
        struct_type_z3 = self.sharedstate.get_z3_struct_type(struct_type)
        fields, resolved_type = self.sharedstate.struct_z3_field_map[struct_type_z3]
        new_args  = []
        for fieldname, _ in fields:
            if fieldname == field_to_replace:
                new_args.append(new_value)
            else:
                res = getattr(struct_type_z3, fieldname)(struct.toz3())# TODO get from vals_w
                if res.sort() == z3.BoolSort():
                    new_args.append(Z3BoolValue(res))
                else:
                    new_args.append(Z3Value(res))  
        new_struct = StructConstant(new_args, resolved_type, struct_type_z3)

        # replace struct in env
        # old struct shall not be used anymore
        self.environment[op.args[0]] = new_struct

    def exec_union_variant_check(self, op):
        instance, = self.getargs(op)
        if isinstance(instance, UnionConstant):
            return BooleanConstant(instance.variant_name != op.name) # confusingly enough, the result is negated from what one would expect
        elif isinstance(instance, Z3Value):
            union_type = op.args[0].resolved_type
            checker = self.sharedstate.get_ir_union_typechecker(union_type, op.name)
            return Z3BoolValue(checker(instance.toz3()))
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
        res_type = op.resolved_type# TODO: can res_type can be removed ? 
        instance, = self.getargs(op)
        if isinstance(instance, Z3Value):
            z3_cast_instance = self.sharedstate.ir_union_variant_to_z3_type(instance, union_type, to_specialized_variant, res_type)
            # TODO: do we need to check for BoolSort here too?
            return Z3Value(z3_cast_instance)
        elif isinstance(instance, UnionConstant):
            assert op.name == instance.variant_name
            return instance.w_val
        else:
            assert 0

    def exec_union_creation(self, op):
        """ Execute union creation"""
        z3type = self.sharedstate.get_z3_union_type(op.resolved_type)
        return UnionConstant(op.name, self.getargs(op)[0], op.resolved_type, z3type)
    
    def exec_cast(self, op):
        arg0, = self.getargs(op)
        if isinstance(op.args[0].resolved_type, types.SmallFixedBitVector): # from
            if isinstance(op.resolved_type, types.GenericBitVector): # to
                if isinstance(arg0, ConstantSmallBitVector):
                    return ConstantSmallBitVector(arg0.value, op.args[0].resolved_type.width)
                else:
                    return Z3Value(arg0.value)
                
        elif isinstance(op.args[0].resolved_type, types.GenericBitVector): # from
            if isinstance(op.resolved_type, types.SmallFixedBitVector): # to
                if isinstance(arg0, ConstantSmallBitVector):
                    return ConstantSmallBitVector(arg0.value, op.resolved_type.width)
                else: 
                    return Z3Value(arg0.value)
                
        assert 0, "implement cast %s to %s" % (op.args[0].resolved_type, op.resolved_type)

    def exec_signed_bv(self, op):
        w_value, w_width = self.getargs(op)
        return self._signed_bv(w_value, w_width)

    def _signed_bv(self, w_value, w_width):
        if isinstance(w_value, ConstantSmallBitVector) and isinstance(w_width, ConstantInt):
            return ConstantInt(supportcode.signed_bv(None, w_value.value, w_width.value))
        else:
            # machine ints are represented as 64-bit bit vectors in z3
            return Z3Value(z3.SignExt(64 - w_width.value, w_value.toz3()))
    
    def exec_bitvector_concat_bv_bv(self, op):
        bv0, width, bv1 = self.getargs(op)
        return self._bitvector_concat_bv_bv(bv0, bv1, width)
    
    def _bitvector_concat_bv_bv(self, bv0, bv1, width):
        if (isinstance(bv0, ConstantSmallBitVector) and
             isinstance(bv1, ConstantSmallBitVector) and
             isinstance(width, ConstantInt)): 
            return ConstantSmallBitVector(supportcode.bitvector_concat_bv_bv(None, bv0.value, width.value, bv1.value), bv0.width + width.value)
        else:
            return Z3Value(z3.Concat(bv0.toz3(), bv1.toz3()))

    def exec_eq_bits_bv_bv(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return BooleanConstant(arg0.value == arg1.value)
        else:
            return Z3BoolValue(arg0.toz3() == arg1.toz3())
    
    def exec_eq(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value == arg1.value)
        if isinstance(arg0, Enum) and isinstance(arg1, Enum):
            return BooleanConstant(arg0 == arg1)
        else:
            assert isinstance(arg0, Z3Value) or isinstance(arg1, Z3Value)
            return Z3BoolValue(arg0.toz3() == arg1.toz3())
        
    def exec_zeq_bit(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return BooleanConstant(arg0.value == arg1.value)
        else:
            return Z3BoolValue(arg0.value == arg1.value)
    
    def exec_gt(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value > arg1.value)
        else:
            return Z3BoolValue(arg0.toz3() > arg1.toz3())
        
    def exec_gteq_unsigned64(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, (ConstantInt, ConstantSmallBitVector)) and isinstance(arg1, (ConstantInt, ConstantSmallBitVector)):
            return BooleanConstant(arg0.value > arg1.value)
        else:
            return Z3BoolValue(z3.UGE(arg0.toz3(), arg1.toz3()))
    
    def exec_gteq(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value >= arg1.value)
        else:
            return Z3BoolValue(arg0.toz3() >= arg1.toz3())

            
    def exec_lt(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value < arg1.value)
        else:
            return Z3BoolValue(arg0.toz3() < arg1.toz3())

    def exec_lteq(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value <= arg1.value)
        else:
            return Z3BoolValue(arg0.toz3() <= arg1.toz3())
        
    def exec_lt_unsigned64(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value < arg1.value)
        else:
            return Z3BoolValue(z3.ULT(arg0.toz3(), arg1.toz3()))
            
    def exec_not(self, op):
        arg0, = self.getargs(op)
        return arg0.not_()
        
    def exec_not_vec_bv(self, op):
        arg0, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(~arg0.value, op.resolved_type.width)
        else:
            return Z3Value(~arg0.toz3())
        
    def exec_sub_bits_bv_bv(self, op):
        arg0, arg1, arg2 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value - arg1.value, op.resolved_type.width)
        else:
            return Z3Value(arg0.toz3() - arg1.toz3())

    def exec_add_bits_int_bv_i(self, op):
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt):
            return ConstantSmallBitVector(supportcode.add_bits_int_bv_i(None, arg0.value, arg1.value), op.resolved_type.width) 
        else:
            return Z3Value(arg0.toz3() + arg1.toz3())

    def exec_add_bits_bv_bv(self, op):
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value + arg1.value, op.resolved_type.width) 
        else:
            return Z3Value(arg0.toz3() + arg1.toz3())

    def exec_and_vec_bv_bv(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value & arg1.value, op.resolved_type.width) 
        else:
            return Z3Value(arg0.toz3() & arg1.toz3())
        
    def exec_xor_vec_bv_bv(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value ^ arg1.value, op.resolved_type.width) 
        else:
            return Z3Value(arg0.toz3() ^ arg1.toz3())

    def exec_or_vec_bv_bv(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value | arg1.value, op.resolved_type.width) 
        else:
            return Z3Value(arg0.toz3() | arg1.toz3())
        
    def exec_shiftl_bv_i(self, op):
        ## Assume that this is meant to be an logical shift ##
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt) and isinstance(arg2, ConstantInt):
            return ConstantSmallBitVector(arg0.value << arg2.value, arg1.value) 
        else:
            arg2_z3 = arg2.toz3() if not isinstance(arg2.toz3(), int) else z3.Int(arg2.toz3())
            return Z3Value(arg0.toz3() << z3.Int2BV(arg2_z3, arg0.toz3().sort().size()))
        
    def exec_shiftr_bv_i(self, op):
        # Assume that this is meant to be an logical shift ##
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt) and isinstance(arg2, ConstantInt):
            return ConstantSmallBitVector(arg0.value >> arg2.value, arg1.value) 
        else:
            arg2_z3 = arg2.toz3() if not isinstance(arg2.toz3(), int) else z3.Int(arg2.toz3())
            return Z3Value(arg0.toz3() >> z3.Int2BV(arg2_z3, arg0.toz3().sort().size()))
    
    def exec_shiftr_o_i(self, op):
        """ shift generic bv to the right """
        ## Assume that this is meant to be an logical shift ##
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt):
            return ConstantSmallBitVector(arg0.value >> arg1.value, arg0.width) # TODO. we currently cannot represent generic bvs very good 
        else:
            # This assumes that the shift is by less than 2**arg0's-width
            arg1_z3 = arg1.toz3() if not isinstance(arg1.toz3(), int) else z3.Int(arg1.toz3())
            return Z3Value(arg0.toz3() >> z3.Int2BV(arg1_z3, arg0.toz3().sort().size()))

    def exec_vector_subrange_fixed_bv_i_i(self, op):
        """ slice bitvector as arg0[arg1:arg2] both inclusive (bv read from right)"""
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):# ConstantGenericBitVector
            return ConstantSmallBitVector(supportcode.vector_subrange_fixed_bv_i_i(None, arg0.value, arg1.value, arg2.value), op.resolved_type.width)
        else:
            return Z3Value(z3.Extract(arg1.value, arg2.value, arg0.toz3()))
        
    def exec_vector_subrange_o_i_i_unwrapped_res(self, op):
        """ slice generic bitvector as arg0[arg1:arg2] both inclusive (bv read from right)"""
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            mask_low = 2 ** (arg2 + 1) - 1
            mask_high = 2 ** (arg1 + 1) - 1
            mask = mask_high - mask_low
            # supportcode cant handle morethan 64 bits #
            return ConstantSmallBitVector(arg0.value & mask, op.resolved_type.width)
        else:
            return Z3Value(z3.Extract(arg1.value, arg2.value, arg0.toz3()))
                
    def exec_vector_update_subrange_fixed_bv_i_i_bv(self, op):
        arg0, arg1, arg2, arg3 = self.getargs(op)#  bv high low new_val 
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(supportcode.vector_update_subrange_fixed_bv_i_i_bv(None, arg0.value, arg1.value, arg2.value, arg3.value), op.resolved_type.width)
        else:
            res = arg3.toz3()
            bv_size = arg0.toz3().sort().size()
            if arg1.value != (bv_size - 1):
                res = z3.Concat(z3.Extract(bv_size - 1, arg1.value + 1, arg0.toz3()), res)
            if arg2.value != 0:
                res = z3.Concat(res, z3.Extract(arg2.value - 1, 0, arg0.toz3()))
            if res.sort().size() != op.resolved_type.width: 
                import pdb;  pdb.set_trace()
                
            return Z3Value(res)
     
    def exec_vector_access_bv_i(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(supportcode.vector_access_bv_i(None, arg0.value, arg1.value), op.resolved_type.width)
        else:
            return Z3Value(z3.Extract(arg1.value, arg1.value, arg0.toz3()))

    def exec_pack_smallfixedbitvector(self, op):
        """ pack a smallfixedbitvector into a Packed Wrapper object 
            DONT omit this, there are 'unpack' operations """
        arg0, arg1 = self.getargs(op) #arg0 = bits? ,arg1 = SmallFixedBV
        return Packed(arg1)

    def exec_zero_extend_bv_i_i(self, op):
        """ extend bitvector from arg1 to arg2 with zeros """
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value, op.resolved_type.width)
        else:
            return Z3Value(z3.ZeroExt(arg2.value - arg1.value, arg0.toz3()))

    def exec_sign_extend_bv_i_i(self, op):
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(supportcode.sign_extend_bv_i_i(None, arg0.value, arg1.value, arg2.value), op.resolved_type.width)
        else:
            return Z3Value(z3.SignExt(arg2.value - arg1.value, arg0.toz3()))
        
    def exec_sign_extend_o_i(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value, op.resolved_type.width)
        else:
            # this assumes arg1 is larger than arg0's size
            return Z3Value(z3.SignExt(arg1.value - arg0.toz3().sort().size(), arg0.toz3()))

    def exec_unsigned_bv(self, op):
        """ arg is a bv , result is that bv cast to (Machine) int """
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt):
            return ConstantInt(supportcode.unsigned_bv(None, arg0.value, arg1.value))
        else:
            return Z3Value(z3.BV2Int(z3.ZeroExt(64 - arg1.value, arg0.toz3())))

    def exec_zz5i64zDzKz5i(self, op): # %i64->%i
        arg0, = self.getargs(op)
        if isinstance(arg0, ConstantInt):
            return ConstantGenericInt(arg0.value)
        else:
            return Z3Value(arg0.toz3())

    def exec_zbits_str(self, op):
        """ convert bits of bv to string repr e.g. bv: 01010 -> str: '01010' """
        arg0, = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return StringConstant(bin(arg0.value))
        else:
            if not arg0.toz3().sort().size(): return StringConstant("") 
            zero, one = z3.StringVal("0"), z3.StringVal("1") 
            res = z3.If(z3.Extract(0,0,arg0.toz3()) == 0, zero, one)# index read from right
            for i in range(1, arg0.toz3().sort().size()):
                res = z3.Concat(z3.If(z3.Extract(i, i, arg0.toz3()) == 0, zero, one), res) # concat(x,y) = xy, but bv extract index 0is on the right side
            return Z3StringValue(res)

    def exec_zconcat_str(self, op):
        """ str concat arg0 and arg1 """
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, StringConstant) and isinstance(arg1, StringConstant):
            return StringConstant("".join([arg0.value, arg1.value]))
        else:
            return Z3StringValue(z3.Concat(arg0.toz3(), arg1.toz3()))

    ### Arch specific Operations in subclass ###

class NandInterpreter(Interpreter):
    """ Interpreter subclass for nand2tetris ISA """

    def __init__(self, graph, args, shared_state=None, entrymap=None):
        super(NandInterpreter, self).__init__(graph, args, shared_state, entrymap)# py2 super 
        self.memory = z3.Array('memory', z3.BitVecSort(16), z3.BitVecSort(16))
    
    ### Nand2Tetris specific Operations ###

    def exec_my_read_mem(self, op):
        """ read from memory """
        addr,  = self.getargs(op)
        return Z3Value(self.read_memory(addr))
    
    def exec_my_write_mem(self, op):
        """ write value to memory """
        ### TODO: Are mem writes supposed to return the written value?? ###
        addr, value  = self.getargs(op)
        self.write_memory(addr, value)

class RiscvInterpreter(Interpreter):
    """ Interpreter subclass for RISCV ISA """

    def __init__(self, graph, args, shared_state=None, entrymap=None):
        super(RiscvInterpreter, self).__init__(graph, args, shared_state, entrymap)# py2 super 
        self.memory = z3.Array('memory', z3.BitVecSort(64), z3.BitVecSort(64))

    ### RISCV specific Operations ###

    def exec_zsys_enable_zzfinx(self, op):
        return BooleanConstant(True)

    def exec_zsys_enable_svinval(self, op):
        return BooleanConstant(True)

    def exec_zsys_enable_zzicbozz(self, op):
        return BooleanConstant(True)
    
    def exec_zsys_enable_zzicbom(self, op):
        return BooleanConstant(True)
    
    def exec_zplat_enable_misaligned_access(self, op):
        return BooleanConstant(False)

    def exec_zget_config_print_reg(self, op):
        return BooleanConstant(False)
    
    def exec_zget_config_print_platform(self, op):
        ### TODO: False?
        return BooleanConstant(False)
    