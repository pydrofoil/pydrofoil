import z3
import collections
import struct
from pydrofoil import supportcode
from pydrofoil import ir, types
from pydrofoil.z3backend.z3btypes import *

class SharedState(object):

    def __init__(self, functions={}, registers={}, methods={}):
        self.funcs = functions # rpython graphs for sail functions
        self.mthds = methods # rpython graphs for sail methods
        self.backedges = {} # graph:{block: backedges_to_block}
        self.registers = registers # type: dict[str, types.Type]
        self.enums = {}
        self.type_cache = {}
        self.union_field_cache = {} # (union_name,union_field):z3_type
        self.struct_z3_field_map = {}# z3type:(fields, resolved_type)
        self.struct_unit_fields = set() # (structtype, fieldname) # to remember which fields are unit 
        self.fork_counter = 0
        # z3 unit type
        unit = z3.Datatype("____unit____")
        unit.declare("UNIT")
        self._z3_unit_type = unit.create()
        self._z3_unit = self._z3_unit_type.UNIT
        # z3 generic bv type
        genericbvz3type = z3.Datatype("__generic_bv_val_width_tuple__")
        genericbvz3type.declare("a", ("value", z3.IntSort()), ("width", z3.IntSort()))
        self._genericbvz3type = genericbvz3type.create()
        self._unreachable_error_constants = {} # save unreachable_const_of_... and error_in_typecast_... const, as they are needed in parse_smt2_string
        self._reschedule_ctr = 0

    def _build_type_dict(self):
        """ typenames: z3type dict for smtlib expressions """
        # TODO: remove the prefixes, re-adding them here is weird
        z3types = {} 
        for resolved_type, z3type in self.type_cache.iteritems():
            if isinstance(resolved_type, types.Struct):
                name = "struct_%s" % resolved_type.name
            elif isinstance(resolved_type, types.Enum):
                name = "enum_%s" % resolved_type.name
            elif isinstance(resolved_type, types.Union):
                name = "union_%s" % resolved_type.name
            else:
                assert 0
            z3types[name] = z3type
        z3types["____unit____"] = self._z3_unit_type
        z3types["__generic_bv_val_width_tuple__"] = self._genericbvz3type
        return z3types
    
    def get_backedges(self, graph, block):
        if block not in self.backedges[graph]: return []
        return self.backedges[graph][block]

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
            elif isinstance(typ, types.GenericBitVector):
                fields.append((fieldname, self._genericbvz3type))
            else:
                fields.append((fieldname, self.convert_type_to_z3_type(typ)))
        # TODO: give the constructor a real name that contains the struct name, calling it 'a' makes results very hard to read
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
            elif isinstance(typ, types.GenericBitVector):
                z3typ = self._genericbvz3type
                self.union_field_cache[(uname, variant)] = z3typ
                union.declare(variant, ("acc_" + variant, z3typ))
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
            self._unreachable_error_constants[str(default_value)] = default_value # needed for smtlib expressions
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
            return self._genericbvz3type# TODO: replace this with a z3 (int, int) tuple for val, width
        elif isinstance(typ, types.Int):
            return z3.IntSort()
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
        elif isinstance(typ, types.Vec):
            subtyp = self.convert_type_to_z3_type(typ.typ)
            return z3.ArraySort(z3.IntSort(), subtyp)
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
        if ztype == self._genericbvz3type: return Z3DeferredIntGenericBitVector
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
        copystate.backedges = self.backedges # i dont think we ever alter backedges
        # type cache?
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
        #assert not graph.has_loop
        self.args = args
        assert len(args) == len(graph.args)
        self.environment = {graph.args[i]:args[i] for i in range(len(args))} # assume args are an instance of some z3backend.Value subclass
        self.forknum = self.sharedstate.fork_counter
        self.sharedstate.fork_counter += 1
        # TODO: implement and use `get_w_class_for_rtype` here instead of using Z3Value
        self.registers = {key: Z3Value(self.sharedstate.convert_type_or_instance_to_z3_instance(typ, "init_" + key)) for key, typ in self.sharedstate.registers.iteritems()}
        # TODO: Make this optional: only execute _init_non_isa_registers if they are not present already
        # These registers should be set from the outside, e.g., in z3backend_executor
        # Add htif_... register to  _init_non_isa_registers
        self._init_non_isa_registers()
        self.w_raises = BooleanConstant(False)
        self.w_result = None
        self.path_condition = []
        self.bits = struct.calcsize("P") * 8
        self._allow_ir_print = False
        self._verbosity = 1

    def set_verbosity(self, newverbosity):
        self._verbosity = newverbosity

    def _init_non_isa_registers(self):
        """ init registers that are not declared in the isa, e.g., for sail exception handling """
        self.registers["have_exception"] = Z3BoolValue(self.sharedstate.convert_type_or_instance_to_z3_instance(types.Bool, "init_have_exception"))

    def _reset_env(self):
        """ only for z3backend_executor.
            do not use elsewhere """
        self.environment = {}

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
            is_loop_header = current in self.sharedstate.backedges[interp.graph]
            if len(self.entrymap[current]) > 1:
                backedges = self.sharedstate.get_backedges(interp.graph, current)
                assert not (self._check_if_loop_merge_possible(self.entrymap[current], backedges, block_to_interp) and 
                            self._check_if_normal_merge_possible(self.entrymap[current], backedges, block_to_interp)), "both merge types possible"
                # LOOP-TODO: check if current is a loop header
                if is_loop_header and self._check_if_loop_merge_possible(self.entrymap[current], backedges, block_to_interp):
                    interp, index = self._compute_loop_merge(current, interp, block_to_interp)
                    self.registers = interp.registers
                    self.memory = interp.memory
                # elif, because loop merge and normal merge cant be done at the same time
                # if we enter the header for the first time, we come from 'normal' preds and loop merge is impossible
                ### BFS order does NOT guarantee that all block preceeding a phi are executed before encountering the phi, see Nand2Tetris decode_compute_backwards ###
                elif self._check_if_normal_merge_possible(self.entrymap[current], backedges, block_to_interp):
                    interp, index = self._compute_normal_merge(current, interp, block_to_interp)
                    self.registers = interp.registers
                    self.memory = interp.memory
                else:
                    ### If we did not execute all preceeding blocks already, reschedule the phi and try again later ###
                    self.sharedstate._reschedule_ctr += 1
                    block_to_interp.pop(current)
                    schedule(current, interp)
                    #self._debug_print("rescheduling block %s, cant merge yet" % str(current)[:64], True)
                    #self._debug_print("reschedule no. %d" % self.sharedstate._reschedule_ctr)

                    if self.sharedstate._reschedule_ctr  > 10000: # catch an endless loop
                        interp.graph.view(highlight_blocks={current})
                        import pdb; pdb.set_trace()
                    #self._debug_reason_for_impossible_merge(self.entrymap[current], backedges, block_to_interp)
                    continue
                ### TODO: think of a better solution for this ###
            interp._clean_up_block_to_interp(current, block_to_interp, self.entrymap[current])
            interp._run_block(current, index)
            interp._schedule_next(current.next, is_loop_header, schedule)
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
    
    def _clean_up_block_to_interp(self, block, block_to_interp, prevblocks):
        """ remove blocks from block_to_interp that are no longer needed.
            This is done because in loops we schedule blocks that have been executed once already"""
        for prevblock in prevblocks:
            if isinstance(prevblock.next, ir.Goto) and prevblock in block_to_interp:
                # this prevblock has only on successor: block
                # we merged already; thus remove it
                #self._debug_print("remove block  %s from block_to_interp goto" % str(prevblock)[:64])
                block_to_interp.pop(prevblock)
            elif isinstance(prevblock.next, ir.ConditionalGoto) and prevblock in block_to_interp:
                # this prevblock has two successors: oneof them is block
                # check if both successors are already done; if so => remove it
                if block_to_interp.get(prevblock.next.truetarget) is not None and block_to_interp.get(prevblock.next.falsetarget) is not None:
                    #self._debug_print("remove block %s from block_to_interp condgoto %s %s" % (str(prevblock)[:64], block_to_interp[prevblock.next.truetarget], block_to_interp[prevblock.next.falsetarget]))
                    block_to_interp.pop(prevblock)
                # or one of the paths is done already, and block is a loop header
                elif block_to_interp.get(prevblock.next.truetarget) is not None or block_to_interp.get(prevblock.next.falsetarget) is not None:
                    if prevblock in self.sharedstate.backedges[self.graph]:
                        # loop header soe not schedule the false path
                        # thus its no longer of use
                        block_to_interp.pop(prevblock)

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
    
    def _schedule_next(self, block_next, is_loop_header, schedule):
        """ get next block to execute, or set ret value and return None, or fork interpreter on non const cond. goto """
        if isinstance(block_next, ir.Goto):
            # LOOP-TODO: nothing i guess??
            schedule(block_next.target, self.fork(self.path_condition))
            return
        elif isinstance(block_next, ir.ConditionalGoto):
            # LOOP-TODO: check if this is a loop header
            # if so, check whether block_next.booleanvalue is abstract
            # if its constant true or false: we can just continue as usual
            # if its a Z3Value: raise some error # We cannot unroll a loop for an abstract loop condition
            w_cond = self.convert(block_next.booleanvalue)

            if is_loop_header:
                #self._debug_print("schedule loop header with cond %s" % str(block_next.booleanvalue), True)
                assert isinstance(w_cond, BooleanConstant), "cant execute abstract loops"

            # LOOP-TODO. it is crucial that _is_unreachable is false for the loop path that we DONT go in this iteration
            # because usually we execute both paths and merge, 
            # unreachable paths may not not executed normaly but are just set to dummy values
            # however, to be able to always merge correclty, even unreachable paths are scheduled
            # this would result in an endless loop
            # The solution could be to NOT schedule the loop path that is not taken
            # e.g.
            # if is_loop and w_cond.value == True: 
            interp1 = self.fork(self.path_condition + [w_cond])# TODO: handle the conditions better
            # and
            # if is_loop and w_cond.value == False: 
            interp2 = self.fork(self.path_condition + [w_cond.not_()])

            # sanity check
            if is_loop_header:
                assert interp1._is_unreachable() == True or interp2._is_unreachable() == True, "one of the forks MUST be unreachable"

            ### we need to now in merge if the current block is actually reachable ###
            self.child_cond_map = {block_next.truetarget: w_cond, block_next.falsetarget: w_cond.not_()}

            # This is the opposite of what we do usually
            # usually even if a block is unreachable, it is scheduled
            # but tot avoid endless looping, we must not schedule the false path of a loop header
            if not (is_loop_header and interp1._is_unreachable()):
                schedule(block_next.truetarget, interp1)
            if not (is_loop_header and interp2._is_unreachable()):
                schedule(block_next.falsetarget, interp2)
        elif isinstance(block_next, ir.Return):
            if not self._is_unreachable(): # only set result if it is reachable
                self.w_result = self.convert(block_next.value)
        elif isinstance(block_next, ir.Raise):
            self.w_raises = self.w_path_condition()
        else:
            assert 0, "implement %s" %str(block_next)
        return 
    
    def _check_if_normal_merge_possible(self, prevblocks, backedges, block_to_interp):
        """ returns True if all 'normal' predecessors were executed and there is at least one normal predecessor """
        # LOOP-TODO: split this function into a 'normal  check if merge possible'
        # that only checks for 'normal' prevblocks (i.e. blocks that arent back edges)
        # and a check_if_merge_possible_loopheader function
        normal_preds = False
        for prevblock in prevblocks:
            # we can merge if all predecessor blocks (that  are not part of a loop) were already executed
            if block_to_interp.get(prevblock) is None and prevblock not in backedges: return False
            # check if at least one predecessor is not part of a loop
            if prevblock not in backedges: normal_preds = True
        return normal_preds
    
    def _check_if_loop_merge_possible(self, prevblocks, backedges, block_to_interp):
        """ returns True if all 'loop' predecessors were executed and there is at least one loop predecessor """
        # LOOP-TODO: split this function into a 'normal  check if merge possible'
        # that only checks for 'normal' prevblocks (i.e. blocks that arent back edges)
        # and a check_if_merge_possible_loopheader function
        loop_preds = False
        for prevblock in prevblocks:
            # check if at least one predecessor is part of a loop and was executed already
            # why only check for one block? because we only support concrete loop executions, thus only one path is ever taken
            if prevblock in backedges and block_to_interp.get(prevblock) is not None:
                if not loop_preds:
                    loop_preds = True
                else:
                    assert 0, "multiple paths of concrete loop were executed"
        return loop_preds
    
    def _debug_reason_for_impossible_merge(self, prevblocks, backedges, block_to_interp):
        if len(prevblocks) == 0: self._debug_print("cannot merge because there are not prevblocks")
        for prevblock in prevblocks:
            if block_to_interp.get(prevblock) is None and prevblock not in backedges: 
                self._debug_print("cant normal merge block because of non executed predecessors")
            if block_to_interp.get(prevblock) is None and prevblock in backedges:           
                self._debug_print("cant loop merge block because of non executed predecessors")

    
    def _compute_loop_merge(self, block, scheduleinterp, block_to_interp):
        """ Merge the results of the loop predecessor blocks (backedges) of block into and its interpreter (scheduleinterp)"""
        # LOOP-TODO: rename this function into 'normal' merge for merges of 'normal' (non backedge) predecessors
        # and introduce another for loop merges
        prevblocks = self.entrymap[block]
        backedges = self.sharedstate.get_backedges(scheduleinterp.graph, block)
        is_loop_header = block in self.sharedstate.backedges[scheduleinterp.graph]
        assert is_loop_header
        for prevblock in prevblocks:
            # LOOP-TODO: if we are a loop header merge backedges here, skip normal predecessors
            if prevblock not in backedges: continue
            # as we only support concrete loop executions, only one path through the loop is actually taken
            # thus some loop predecessors were not executed; skip them
            if block_to_interp.get(prevblock) is None: continue
            previnterp = block_to_interp[prevblock]
            # we merge with scheduleinterp; thus skip it
            if previnterp is scheduleinterp: continue
            w_cond = previnterp.w_path_condition()
            if isinstance(prevblock.next, ir.ConditionalGoto):
                # if prev was a ConditionalGoto we need to add cond to the parents path
                w_cond = w_cond._create_w_z3_and(previnterp.child_cond_map[block])
            scheduleinterp.path_condition = [scheduleinterp.w_path_condition()._create_w_z3_or(w_cond)]
            scheduleinterp.registers = {reg:w_cond._create_w_z3_if(previnterp.registers[reg], scheduleinterp.registers[reg]) for reg in self.registers}
            scheduleinterp.memory = self._create_z3_if(w_cond, previnterp.memory, scheduleinterp.memory)
        for index, op in enumerate(block.operations):
            if isinstance(op, ir.Phi):
                w_value = None
                for prevblock, prevvalue in zip(op.prevblocks, op.prevvalues):
                    # LOOP-TODO: skip prevblocks that dont have backedges to 'block' here
                    if prevblock not in backedges: continue
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

    def _compute_normal_merge(self, block, scheduleinterp, block_to_interp):
        """ Merge the results of the normal (non-loop) predecessor blocks of block into and its interpreter (scheduleinterp)"""
        # LOOP-TODO: rename this function into 'normal' merge for merges of 'normal' (non backedge) predecessors
        # and introduce another for loop merges
        prevblocks = self.entrymap[block]
        backedges = self.sharedstate.get_backedges(scheduleinterp.graph, block)
        is_loop_header = block in self.sharedstate.backedges[scheduleinterp.graph]
        for prevblock in prevblocks:
            # LOOP-TODO: if we are a loop header dont merge backedges here
            if is_loop_header and prevblock in backedges: continue
            previnterp = block_to_interp[prevblock]
            # we merge with scheduleinterp; thus skip it
            if previnterp is scheduleinterp: continue
            w_cond = previnterp.w_path_condition()
            if isinstance(prevblock.next, ir.ConditionalGoto):
                # if prev was a ConditionalGoto we need to add cond to the parents path
                w_cond = w_cond._create_w_z3_and(previnterp.child_cond_map[block])
            scheduleinterp.path_condition = [scheduleinterp.w_path_condition()._create_w_z3_or(w_cond)]
            scheduleinterp.registers = {reg:w_cond._create_w_z3_if(previnterp.registers[reg], scheduleinterp.registers[reg]) for reg in self.registers}
            scheduleinterp.memory = self._create_z3_if(w_cond, previnterp.memory, scheduleinterp.memory)
        for index, op in enumerate(block.operations):
            if isinstance(op, ir.Phi):
                w_value = None
                for prevblock, prevvalue in zip(op.prevblocks, op.prevvalues):
                    # LOOP-TODO: skip prevblocks that have backedges to 'block' here
                    if prevblock in backedges: continue
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
        wpc = BooleanConstant(True)._create_w_z3_and(*self.path_condition)
        return wpc
    
    def fork(self, path_condition=None):
        """ create a copy of the interpreter, for evaluating non constant branches """
        cls = type(self)
        f_interp = cls(self.graph, self.args, self.sharedstate, self.entrymap)
        f_interp.environment = self.environment.copy()
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        f_interp.path_condition = self.path_condition if path_condition is None else path_condition
        f_interp.w_raises = self.w_raises # if self raises, the fork must also raise
        f_interp._verbosity = self._verbosity
        return f_interp
    
    def call_fork(self, graph, args, extra_w_cond=None):
        """ create a copy of the interpreter, for evaluating func calls"""
        cls = type(self)
        f_interp = cls(graph, args, self.sharedstate)# dont pass entrymap, must compute entrymap for new graph in init
        f_interp.registers = self.registers.copy()
        f_interp.memory = self.memory # z3 array is immutable
        f_interp.w_raises = self.w_raises
        f_interp.path_condition = self.path_condition if extra_w_cond == None else (self.path_condition + [extra_w_cond])
        f_interp._verbosity = self._verbosity
        return f_interp
    
    def _create_z3_if(self, wcond, true, false):
        # dont create if on BooleanConst or Z3Bool, memory merging is special case
        # this is only used for memory merging
        if isinstance(wcond, BooleanConstant):
            if wcond.value == True: return true
            return false
        elif wcond.toz3().eq(z3.BoolVal(True)):
            return true
        elif wcond.toz3().eq(z3.BoolVal(False)):
            return false
        else:
            return z3.If(wcond.toz3(), true, false)

    def _debug_print(self, msg="", force=False):
        if (self._verbosity > 0) or force:
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
            elif isinstance(arg, ir.IntConstant):
                w_arg = ConstantGenericInt(arg.number)# TODO: maybe just use ConstantInt here
            elif isinstance(arg, ir.BooleanConstant):
                w_arg = BooleanConstant(arg.value)
            elif isinstance(arg, ir.UnitConstant):
                w_arg = UnitConstant(self.sharedstate._z3_unit)
            elif isinstance(arg, ir.StringConstant):
                w_arg = StringConstant(arg.string)
            elif isinstance(arg, ir.DefaultValue):
                val = self.sharedstate.convert_type_or_instance_to_z3_instance(arg.resolved_type, "DefaultValue(%s)" % str(arg.resolved_type))
                if arg.resolved_type == types.Bool:
                    w_arg = Z3BoolValue(val)
                else:
                    w_arg = Z3Value(val)
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
            z3type = self.sharedstate.convert_type_to_z3_type(rtype)
            z_instance = self.sharedstate.get_abstract_const_of_ztype(z3type, "unreachable_const_of_" + str(z3type))
            self.sharedstate._unreachable_error_constants[str(z_instance)] = z_instance # needed for smtlib expressions
            w_class = self.sharedstate.get_w_class_for_ztype(z3type)
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
        arg0, arg1 = self.getargs(op)
        return self._eq_anything(arg0, arg1)
    
    def _eq_anything(self, arg0, arg1):
        if isinstance(arg0, Z3Value) or isinstance(arg1, Z3Value):
            return Z3BoolValue(arg0.toz3() == arg1.toz3())
        else :
            same = arg0.same_value(arg1)
            if same == True:
                return BooleanConstant(True)
            elif same == False:
                return BooleanConstant(False)
            return Z3BoolValue(same)

    def exec_func_call(self, op, graph):
        """ execute a sail function call"""
        # TODO: make either method call set the call registers itself or change that here
        self._debug_print("graph " + self.graph.name + " func call " + op.name)
        func_args = self.getargs(op)
        w_res, memory, registers = self._func_call(graph, func_args)
        self.memory = memory
        self.registers = registers 
        self._debug_print("return from " + op.name)# + " " + str((w_res.toz3().sort(), op.resolved_type))) #+ " -> " + str(w_res))
        return w_res
    
    def _func_call(self, graph, func_args):
        interp_fork = self.call_fork(graph, func_args)
        w_res = interp_fork.run()
        if isinstance(interp_fork.w_raises, BooleanConstant):
            if interp_fork.w_raises.value == True:# case: func raises without condition
                self.w_raises = BooleanConstant(True)
                self.w_result = UnitConstant(self.sharedstate._z3_unit)
            else:
                # self.w_raises is self.w_raises or False
                pass
        else: 
            # case: func did or didnt raise, but raise was behind a condition
            self.w_raises = self.w_raises._create_w_z3_or(interp_fork.w_raises)
        return w_res, interp_fork.memory, interp_fork.registers
    
    def _select_method_graph(self, instance, method_graphs):
        """ select method graph depending on first arg for method call """
        ## arg0 is the 'object/instance' the method is called on
        if instance.variant_name in method_graphs: 
            return method_graphs[instance.variant_name]
        # these methods usually have an else case, and that graph has no name
        # on caching these graphs in test_z3riscv.py I named that graph ___default___
        ### AFAIK the unnamed (___default___)  method is always an unconditional raise ###
        return method_graphs["___default___"]


    def exec_method_call(self, op, graphs):
        """ execute a sail method call """
        mthd_args = self.getargs(op)
        self._debug_print("graph " + self.graph.name + " mthd call " + op.name)
        if isinstance(mthd_args[0], UnionConstant):
            w_res = self._concrete_method_call(graphs, mthd_args)
        elif isinstance(mthd_args[0], Z3Value):
            w_res = self._abstract_method_call(graphs, mthd_args, op.args[0].resolved_type)
        else:
            assert 0, "illegal method argument type: %s" % str(mthd_args[0].__class__)
        self._debug_print("return from " + op.name)# + " " + str((w_res.toz3().sort(), op.resolved_type)))
        return w_res
    
    def _concrete_method_call(self, graphs, mthd_args):
        """ execute a method call on a UnionConstant """
        method_graph = self._select_method_graph(mthd_args[0], graphs)
        w_res, memory, registers = self._method_call(method_graph, mthd_args)
        self.memory = memory
        self.registers = registers
        return w_res
    
    def _abstract_method_call(self, graphs, mthd_args,  union_type):
        """ execute all possible methods on an abstract UnionConstant (Z3Value of a Union) """
        variant_mthd_graphs = graphs.keys()
        w_res = None
        ### TODO: implement executing  ___default___ method
        ### ___default___ method just raises unconditionally 
        ### or maybe remove ___default___ in general?
        for variant in variant_mthd_graphs:
            if variant == "___default___": continue
            w_checker = self._get_w_checker_union_variant(mthd_args[0], union_type, variant)
            #args = [Z3Value(self.sharedstate.ir_union_variant_to_z3_type(mthd_args[0], union_type, variant, "?"))]
            temp_w_res, memory, registers = self._method_call(graphs[variant], mthd_args, w_checker)
            w_cond = BooleanConstant(True)._create_w_z3_and(*(self.path_condition + [w_checker]))
            if w_res == None:
                w_res = temp_w_res
                self.memory = memory
                self.registers = registers
            else:
                w_res = w_cond._create_w_z3_if(temp_w_res, w_res)
                self.memory = z3.If(w_cond.toz3(), memory, self.memory)
                self.registers = {reg:w_cond._create_w_z3_if(registers[reg], self.registers[reg]) for reg in self.registers}
        return w_res
    
    def _get_w_checker_union_variant(self, instance, union_type, variant_name):
        """ create Z3BoolValue for checking if an instance of a union is a certain variant"""
        checker = self.sharedstate.get_ir_union_typechecker(union_type, variant_name)
        return Z3BoolValue(checker(instance.toz3()))
    
    def _method_call(self, graph, mthd_args, extra_w_cond=None):
        interp_fork = self.call_fork(graph, mthd_args, extra_w_cond)
        w_res = interp_fork.run()
        if isinstance(interp_fork.w_raises, BooleanConstant):
            if interp_fork.w_raises.value == True:# case: func raises without condition
                self.w_raises = BooleanConstant(True)
                self.w_result = UnitConstant(self.sharedstate._z3_unit)
            else:
                # self.w_raises is self.w_raises or False
                pass
        else: 
            # case: func did or didnt raise, but raise was behind a condition
            self.w_raises = self.w_raises._create_w_z3_or(interp_fork.w_raises)
        return w_res, interp_fork.memory, interp_fork.registers

    def exec_allocate(self, op):
        return self._allocate(op.resolved_type)
    
    def _allocate(self, resolved_type):
        if isinstance(resolved_type, types.Struct):
            z3type = self.sharedstate.get_z3_struct_type(resolved_type)
            fields, _ = self.sharedstate.struct_z3_field_map[z3type]
            vals_w = []
            for field, typ in fields:
                # Generic Bv type is created as abstract constant, no need to do something here
                if typ is not self.sharedstate._z3_unit_type:
                    val = self.sharedstate.get_abstract_const_of_ztype(typ, "alloc_uninit_%s_" % field)
                    self.sharedstate._unreachable_error_constants[str(val)] = val # needed for smtlib expressions
                    vals_w.append(self.sharedstate.get_w_class_for_ztype(typ)(val))
                else:
                    #val = self.sharedstate._z3_unit
                    vals_w.append(UnitConstant(self.sharedstate._z3_unit))
            return StructConstant(vals_w, resolved_type, z3type)
        assert 0 , "implement allocate %s" % str(resolved_type)
    
    def exec_struct_construction(self, op):
        """ Execute a Lazy Struct creation """
        return self._struct_construction(self.getargs(op), [arg.resolved_type for arg in op.args], op.resolved_type)
    
    def _w_generic_bv_struct(self, w_generic_bv):
        # TODO: remove this function
        if isinstance(w_generic_bv, ConstantGenericBitVector):
            return w_generic_bv
        elif isinstance(w_generic_bv, Z3GenericBitVector):
            return w_generic_bv#
        elif isinstance(w_generic_bv, Z3DeferredIntGenericBitVector):
            return w_generic_bv
        elif isinstance(w_generic_bv, Z3Value):
            assert 0, "should not happen anymore"
        else:
            assert 0, "class %s not allowed for generic bitvector" % str(w_generic_bv.__class__)

    def _struct_construction(self, wargs, argtypes, resolved_type):
        for i in range(len(wargs)):
            if isinstance(argtypes[i], types.GenericBitVector):
                wargs[i] = self._w_generic_bv_struct(wargs[i])
        z3type = self.sharedstate.get_z3_struct_type(resolved_type)
        return StructConstant(wargs, resolved_type, z3type)
    
    def exec_struct_copy(self, op):
        """ TODO: is this a shallow or deep copy? """
        arg, = self.getargs(op)
        return self._struct_copy(arg)
    
    def _struct_copy(self, struct_instance):
        return struct_instance.copy()

    def exec_field_access(self, op):
        """ access field of struct """
        field = op.name
        struct, = self.getargs(op)
        struct_type = op.args[0].resolved_type
        # TODO: is there a nicer way of checking whether the return val shall be packed?
        pack = "Packed" in str(op.resolved_type)
        return self._field_access(field, struct, struct_type, pack)
    
    def _field_access(self, field, struct, struct_type, packed):
        struct_type_z3 = self.sharedstate.get_z3_struct_type(struct_type)
        ## structs can have fields of type  unit, those are always UNIT
        if (struct_type_z3, field) in self.sharedstate.struct_unit_fields:
            if packed:
                return Packed(UnitConstant(self.sharedstate._z3_unit))
            else:
                return UnitConstant(self.sharedstate._z3_unit)
        if isinstance(struct, StructConstant):
            index = struct.resolved_type.names.index(field)
            w_val = struct.vals_w[index]
            return Packed(w_val) if packed else w_val
        res = getattr(struct_type_z3, field)(struct.toz3())# get accessor from slot with getattr
        if res.sort() == z3.BoolSort():
            return Packed(Z3BoolValue(res)) if packed else Z3BoolValue(res)
        elif res.sort() == self.sharedstate._genericbvz3type:
            value = getattr(self.sharedstate._genericbvz3type, "value")(res)
            width = getattr(self.sharedstate._genericbvz3type, "width")(res)
            # Big Problem: width  is a z3 expression and not a python int
            # int2bv must be called with a python int width
            # we must simplify :(
            self._debug_print("simplifying generic bv width now", True)
            const_width = z3.simplify(width)
            self._debug_print("finish simplifying", True)
            #assert isinstance(const_width, z3.z3.IntNumRef), "cant cast int 2 bv without constant width"
            if isinstance(const_width, z3.z3.IntNumRef):
                long_width = const_width.as_long()
                w_val = Z3GenericBitVector(z3.Int2BV(value, long_width), long_width, self.sharedstate._genericbvz3type)
            else:
                self._debug_print("couldnt find concrete generic bv width for %s,making z3_lazy_int_generic_bv" % str(res), True)
                w_val = Z3DeferredIntGenericBitVector(res)
            return Packed(w_val) if packed else w_val
        # TODO: check for Unit
        return Packed(Z3Value(res)) if packed else Z3Value(res)

    def exec_field_write(self, op):
        """ write into struct field.
            By creating a new struct instance """
        field_to_replace = op.name
        struct, new_value = self.getargs(op)
        struct_type = op.args[0].resolved_type
        new_struct = self._field_write(struct, struct_type, field_to_replace, new_value)
        # replace struct in env
        # old struct shall not be used anymore
        self.environment[op.args[0]] = new_struct

    def _field_write(self, struct, struct_type, field_to_replace, new_value):
        struct_type_z3 = self.sharedstate.get_z3_struct_type(struct_type)
        fields, resolved_type = self.sharedstate.struct_z3_field_map[struct_type_z3]
        new_args  = []
        if isinstance(new_value, Packed): new_value = new_value.w_value # it seems fieldwrites unpack  implicitly
        for fieldname, fieldtype in fields:
            if fieldname == field_to_replace:
                if fieldtype == self.sharedstate._genericbvz3type:
                    new_args.append(self._w_generic_bv_struct(new_value))
                else:
                    new_args.append(new_value)
            else:
                res = getattr(struct_type_z3, fieldname)(struct.toz3())# TODO get from vals_w
                if res.sort() == z3.BoolSort():
                    new_args.append(Z3BoolValue(res))
                elif res.sort() == self.sharedstate._genericbvz3type:
                    new_args.append(Z3DeferredIntGenericBitVector(res))
                else:
                    new_args.append(Z3Value(res))  
        return StructConstant(new_args, resolved_type, struct_type_z3)

    def exec_union_variant_check(self, op):
        instance, = self.getargs(op)
        union_type = op.args[0].resolved_type
        variant_name = op.name
        return self._union_variant_check(instance, union_type, variant_name)

    def _union_variant_check(self, instance, union_type, variant_name):
        if isinstance(instance, UnionConstant):
            return BooleanConstant(instance.variant_name != variant_name) # confusingly enough, the result is negated from what one would expect
        elif isinstance(instance, Z3Value):
            checker = self.sharedstate.get_ir_union_typechecker(union_type, variant_name)
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
            # TODO: do we need to check for BoolSort here too? we could but we dont have to
            if z3_cast_instance.sort() == self.sharedstate._genericbvz3type: 
                value = getattr(self.sharedstate._genericbvz3type, "value")(z3_cast_instance)
                width = getattr(self.sharedstate._genericbvz3type, "width")(z3_cast_instance)
                # Big Problem: width  is a z3 expression and not a python int
                # int2bv m8ust be called with a python int width
                # we must simplify :(
                self._debug_print("simplifying generic bv width now", True)
                const_width = z3.simplify(width)
                self._debug_print("finish simplifying", True)
                #assert isinstance(const_width, z3.z3.IntNumRef), "cant cast int 2 bv without constant width"
                if isinstance(const_width, z3.z3.IntNumRef):
                    long_width = const_width.as_long()
                    return Z3GenericBitVector(z3.Int2BV(value, long_width), long_width, self.sharedstate._genericbvz3type)
                else:
                    self._debug_print("couldnt find concrete generic bv width for %s,making z3_lazy_int_generic_bv" % str(op), True)
                    return Z3DeferredIntGenericBitVector(z3_cast_instance)
            return Z3Value(z3_cast_instance)
        elif isinstance(instance, UnionConstant):
            assert op.name == instance.variant_name
            w_val = instance.w_val
            return w_val
        else:
            assert 0 , "%s is not allowed in unioncast" % str(union_type) 

    def exec_union_creation(self, op):
        """ Execute union creation"""
        z3type = self.sharedstate.get_z3_union_type(op.resolved_type)
        w_arg = self.getargs(op)[0]
        if isinstance(op.args[0].resolved_type, types.GenericBitVector):
            w_arg = self._w_generic_bv_struct(w_arg)
        return UnionConstant(op.name, w_arg, op.resolved_type, z3type)
    
    def exec_cast(self, op):
        arg0, = self.getargs(op)
        from_type = op.args[0].resolved_type
        to_type = op.resolved_type
        if isinstance(from_type, types.SmallFixedBitVector): # from
            if isinstance(to_type, types.GenericBitVector): # to
                if isinstance(arg0, ConstantSmallBitVector):
                    return ConstantGenericBitVector(arg0.value, arg0.width, self.sharedstate._genericbvz3type)
                else:
                    return Z3GenericBitVector(arg0.value, from_type.width, self.sharedstate._genericbvz3type)
                
        elif isinstance(from_type, types.GenericBitVector): # from
            if isinstance(to_type, types.SmallFixedBitVector): # to
                if isinstance(arg0, ConstantGenericBitVector):
                    return ConstantSmallBitVector(arg0.value, to_type.width)
                elif isinstance(arg0, Z3GenericBitVector):
                    return Z3Value(self._adapt_z3bv_width(arg0.value, to_type.width))
                elif isinstance(arg0, Z3DeferredIntGenericBitVector):
                    # we can cast because we know the width at this point
                    intval = getattr(self.sharedstate._genericbvz3type, "value")(arg0.toz3())
                    return Z3Value(z3.Int2BV(intval, to_type.width))
                elif isinstance(arg0, Z3Value): # Z3Value & sort == int
                    assert 0
                    return Z3Value(z3.Int2BV(arg0.toz3(), to_type.width))
                else:
                    assert 0, "type %s for generic bv not allowed" % str(arg0.__class__)

        elif isinstance(from_type, types.FVec):
            if isinstance(to_type, types.Vec):
                return Vec(arg0)# Vec takes a w arg

        assert 0, "implement cast %s to %s" % (from_type, to_type)

    def exec_signed_bv(self, op):
        w_value, w_width = self.getargs(op)
        return self._signed_bv(w_value, w_width)

    def _signed_bv(self, w_value, w_width):
        if isinstance(w_value, ConstantSmallBitVector) and isinstance(w_width, ConstantInt):
            return ConstantInt(supportcode.signed_bv(None, w_value.value, w_width.value))
        else:
            return Z3Value(z3.BV2Int(w_value.toz3(), is_signed=True))
    
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
        
    def exec_eq_int_o_i(self, op):
        """ compare GenericInt and MachineInt """
        arg0, arg1 = self.getargs(op)
        if ((isinstance(arg0, ConstantGenericInt) or isinstance(arg0, ConstantInt)) and 
            (isinstance(arg1, ConstantGenericInt) or isinstance(arg1, ConstantInt))):
            return BooleanConstant(arg0.value == arg1.value)
        else:
            return Z3BoolValue(arg0.toz3() == arg1.toz3())
        
    def exec_zeq_bit(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return BooleanConstant(arg0.value == arg1.value)
        else:
            return Z3BoolValue(arg0.toz3() == arg1.toz3())
    
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

    def exec_lt_unsigned64(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value < arg1.value)
        else:
            return Z3BoolValue(z3.ULT(arg0.toz3(), arg1.toz3()))
        
    def exec_lteq(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value <= arg1.value)
        else:
            return Z3BoolValue(arg0.toz3() <= arg1.toz3())
        
    def exec_lteq_unsigned64(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return BooleanConstant(arg0.value <= arg1.value)
        else:
            return Z3BoolValue(z3.ULE(arg0.toz3(), arg1.toz3()))
        
    def exec_zlteq_int(self, op):
        arg0, arg1 = self.getargs(op)# TODO: every constantInt or ConstantGenericInt case applies for both
        if ((isinstance(arg0, ConstantInt) or isinstance(arg0, ConstantGenericInt)) 
            and (isinstance(arg1, ConstantInt) or isinstance(arg1, ConstantGenericInt))):
            return BooleanConstant(arg0.value <= arg1.value)
        else:
            return Z3BoolValue(arg0.toz3()  <= arg1.toz3())
        
    def exec_not(self, op):
        arg0, = self.getargs(op)
        return arg0.not_()
        
    def exec_not_vec_bv(self, op):
        arg0, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(~arg0.value, op.resolved_type.width)
        else:
            return Z3Value(~arg0.toz3())

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
                  
    def exec_sub_bits_bv_bv(self, op):
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value - arg1.value, op.resolved_type.width)
        else:
            return Z3Value(arg0.toz3() - arg1.toz3())
        
    def exec_sub_i_i_must_fit(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantInt(arg0.value - arg1.value)
        else:
            return Z3Value(arg0.toz3() - arg1.toz3())
    
    def exec_isub(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantInt(arg0.value - arg1.value)
        else:
            return Z3Value(arg0.toz3() - arg1.toz3())

    def exec_add_bits_int_bv_i(self, op):
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(supportcode.add_bits_int_bv_i(None, arg0.value, arg1.value), op.resolved_type.width) 
        else:
            return Z3Value(arg0.toz3() + z3.Int2BV(arg1.toz3(), arg0.toz3().sort().size()))

    def exec_add_bits_bv_bv(self, op):
        arg0, arg1, _ = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value + arg1.value, op.resolved_type.width) 
        else:
            return Z3Value(arg0.toz3() + arg1.toz3())
        
    def exec_add_i_i_must_fit(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantInt(arg0.value + arg1.value)
        else:
            return Z3Value(arg0.toz3() + arg1.toz3())
        
    def exec_add_o_i_wrapped_res(self, op):
        """ Gets GenericInt and MachineInt and returns thier sum as GenericInt"""
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantGenericInt(arg0.value + arg1.value)
        else:
            return Z3Value(arg0.toz3() + arg1.toz3())
        
    def exec_add_unsigned_bv64_unsigned_bv64_wrapped_res(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantSmallBitVector):
            return ConstantGenericInt(arg0.value + arg1.value) 
        else:
            return Z3Value(z3.BV2Int(arg0.toz3() + arg1.toz3(), is_signed=False))

    def exec_mult_i_i_must_fit(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantInt(arg0.value * arg1.value)
        else:
            return Z3Value(arg0.toz3() * arg1.toz3())
        
    def exec_zmult_atom(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantInt(arg0.value * arg1.value)
        else:
            return Z3Value(arg0.toz3() * arg1.toz3())
        
    def exec_zemod_int(self, op):
        arg0, arg1 = self.getargs(op) 
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantInt(arg0.value % arg1.value)
        else:
            return Z3Value(arg0.toz3() % arg1.toz3())
        
    def _adapt_z3bv_width(self, z3bv, targetwidth, sign_ext=False):
        z3bvsize = z3bv.sort().size()
        if z3bvsize < targetwidth:
            if sign_ext:
                return z3.SignExt(targetwidth - z3bvsize, z3bv)
            else:
                return z3.ZeroExt(targetwidth - z3bvsize, z3bv)
        elif z3bvsize > targetwidth:
            return z3.Extract(targetwidth-1, 0, z3bv)
        else:
            return z3bv

    def exec_shiftl_bv_i(self, op):
        ## Assume that this is meant to be an logical shift ##
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt) and isinstance(arg2, ConstantInt):
            return ConstantSmallBitVector(arg0.value << arg2.value, arg1.value) 
        else:
            if isinstance(arg2, Z3CastedValue) and isinstance(arg2.value, z3.z3.BitVecRef):
                arg2_z3 = self._adapt_z3bv_width(arg2.value, arg0.toz3().sort().size())
                return Z3Value(arg0.toz3() << arg2_z3)
            else:
                arg2_z3 = arg2.toz3() if not isinstance(arg2.toz3(), int) else z3.Int(arg2.toz3())
                return Z3Value(arg0.toz3() << z3.Int2BV(arg2_z3, arg0.toz3().sort().size()))
        
    def exec_shl_int_i_i_must_fit(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantInt(arg0.value << arg1.value) 
        elif isinstance(arg1, Z3CastedValue):
            assert 0, "implement me"    
        else:
            if isinstance(arg1, ConstantInt):
                arg1z3 = z3.BitVecVal(arg1.value, self.bits)
            else:
                arg1z3 = z3.Int2BV(arg1.toz3(), self.bits)
            # z3 does not support int shifts, thus we convert to bvs with host machine size
            return Z3Value(z3.BV2Int(z3.Int2BV(arg0.toz3(), self.bits) << arg1z3, is_signed=True))
        
    def exec_shiftr_bv_i(self, op):
        #shiftr_bv_i is used when executing a rv64 logical right shit instruction => this is a logical shift
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt) and isinstance(arg2, ConstantInt):
            return ConstantSmallBitVector(arg0.value >> arg2.value, arg1.value) 
        else:
            if isinstance(arg2, Z3CastedValue) and isinstance(arg2.value, z3.z3.BitVecRef):
                arg2_z3 = self._adapt_z3bv_width(arg2.value, arg0.toz3().sort().size())
                return Z3Value(z3.LShR(arg0.toz3(), arg2_z3))
            else:
                arg2_z3 = arg2.toz3() if not isinstance(arg2.toz3(), int) else z3.IntVal(arg2.toz3())
                return Z3Value(z3.LShR(arg0.toz3(), z3.Int2BV(arg2_z3, arg0.toz3().sort().size())))
    
    def exec_shiftr_o_i(self, op):
        """ shift generic bv to the right """
        # This shift is used when executing a rv64 arithmetic right shit instruction => this is an arithmetic shift
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantGenericBitVector) and isinstance(arg1, ConstantInt):
             return ConstantGenericBitVector(arg0.value >> arg1.value, arg0.width, self.sharedstate._genericbvz3type)
        else:
            if isinstance(arg1, Z3CastedValue) and isinstance(arg1.value, z3.z3.BitVecRef): 
                arg1z3 = self._adapt_z3bv_width(arg1.value, arg0.width)
            else:
                arg1z3 = z3.Int2BV(arg1.toz3(), arg0.width)
            if isinstance(arg0, Z3GenericBitVector):
                return Z3GenericBitVector(arg0.value >> arg1z3, arg0.width, self.sharedstate._genericbvz3type)# Z3GenericBitVector.value is bv,t
            else:
                assert 0, "class %s for generic bv not allowed" % str(arg0.__class__)

    def exec_vector_subrange_fixed_bv_i_i(self, op):
        """ slice bitvector as arg0[arg1:arg2] both inclusive (bv read from right)"""
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) or isinstance(arg0, ConstantGenericBitVector):
            return ConstantSmallBitVector(supportcode.vector_subrange_fixed_bv_i_i(None, arg0.value, arg1.value, arg2.value), op.resolved_type.width)
        else:
            return Z3Value(z3.Extract(arg1.value, arg2.value, arg0.toz3()))
        
    def exec_vector_subrange_o_i_i_unwrapped_res(self, op):
        """ slice generic bitvector as arg0[arg1:arg2] both inclusive (bv read from right)"""
        arg0, arg1, arg2 = self.getargs(op)
        assert isinstance(arg1, ConstantInt) and isinstance(arg2, ConstantInt), "abstract slicing not allowed"
        if isinstance(arg0, ConstantGenericBitVector) and isinstance(arg1, ConstantInt) and isinstance(arg2, ConstantInt):
            mask_high = 2 ** (arg1.value + 1) - 1
            return ConstantSmallBitVector((arg0.value & mask_high) >> arg2.value, 1 + arg1.value - arg2.value)
        elif isinstance(arg0, Z3GenericBitVector):
            return Z3Value(z3.Extract(arg1.value, arg2.value, arg0.value))
        else:
            assert 0, "class %s for generic bv not allowed" % str(arg0.__class__)

    def exec_vector_subrange_o_i_i(self, op):
        arg0, arg1, arg2 = self.getargs(op)
        assert isinstance(arg1, ConstantInt) and isinstance(arg2, ConstantInt), "abstract slicing not allowed"
        if isinstance(arg0, ConstantGenericBitVector):
            mask_high = 2 ** (arg1.value + 1) - 1
            return ConstantGenericBitVector((arg0.value & mask_high) >> arg2.value, 1 + arg1.value - arg2.value, self.sharedstate._genericbvz3type)
        elif isinstance(arg0, Z3GenericBitVector):
            return Z3GenericBitVector(z3.Extract(arg1.value, arg2.value, arg0.value), 1 + arg1.value - arg2.value, self.sharedstate._genericbvz3type)
        else:
            assert 0, "class %s for generic bv not allowed" % str(arg0.__class__)
                
    def exec_get_slice_int_i_o_i(self, op):
        """ returns int2bv(arg1)[arg0: arg2] (read from right)
            arg0 = len, arg1 = value, arg2 = start"""
        # o = generic int in this case
        arg0, arg1, arg2 = self.getargs(op)
        if ((isinstance(arg0, ConstantInt) or isinstance(arg0, ConstantGenericInt)) 
            and (isinstance(arg1, ConstantInt) or isinstance(arg1, ConstantGenericInt))
            and (isinstance(arg2, ConstantInt) or isinstance(arg2, ConstantGenericInt))):
            return ConstantGenericBitVector((arg1.value >> arg2.value) & ((1 << arg0.value) - 1), arg0.value + 1, self.sharedstate._genericbvz3type)
        elif isinstance(arg1, Z3Value):
            # z3 shift and logic and only allowed on bvs
            val = z3.Int2BV(arg1.toz3(), arg0.value)
            # is this supposed to return a bv of size arg0 or arg0-arg2
            #val = z3.Extract(arg0.value, arg2.value, val)
            val = val >> arg2.value # this returns a bv of size arg0
            return Z3GenericBitVector(val, arg0.value, self.sharedstate._genericbvz3type)
        else:
            assert 0, "class %s for generic int not allowed" % str(arg0.__class__)

    def exec_get_slice_int_i_o_i_unwrapped_res(self, op):
        """ returns int2bv(arg1)[arg0: arg2] (read from right)
            arg0 = len, arg1 = value, arg2 = start"""
        # o = generic int in this case
        arg0, arg1, arg2 = self.getargs(op)
        if ((isinstance(arg0, ConstantInt) or isinstance(arg0, ConstantGenericInt)) 
            and (isinstance(arg1, ConstantInt) or isinstance(arg1, ConstantGenericInt))
            and (isinstance(arg2, ConstantInt) or isinstance(arg2, ConstantGenericInt))):
            return ConstantSmallBitVector((arg1.value >> arg2.value) & ((1 << arg0.value) - 1), op.resolved_type.width)
        elif isinstance(arg1, Z3Value):
            # z3 shift and logic and only allowed on bvs
            val = z3.Int2BV(arg1.toz3(), arg0.value)
            val = val >> arg2.value # this returns a bv of size arg0
            return Z3Value(val)
        else:
            assert 0, "class %s for generic int not allowed" % str(arg0.__class__)

    def exec_vector_update_subrange_fixed_bv_i_i_bv(self, op):
        arg0, arg1, arg2, arg3 = self.getargs(op)#  bv high low new_val 
        if (isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt)
             and isinstance(arg2, ConstantInt) and isinstance(arg3, ConstantSmallBitVector)):
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

    def exec_vector_update_subrange_o_i_i_o(self, op):
        arg0, arg1, arg2, arg3 = self.getargs(op)#  bv high low new_val 
        # case everything is constant
        if (isinstance(arg0, ConstantGenericBitVector) and isinstance(arg1, ConstantInt)
             and isinstance(arg2, ConstantInt) and isinstance(arg3, ConstantGenericBitVector)):
            return ConstantGenericBitVector(supportcode.vector_update_subrange_fixed_bv_i_i_bv(None, arg0.value, arg1.value, arg2.value, arg3.value), op.resolved_type.width)
        else:
            # arg0 or arg3 is not constant
            if isinstance(arg3, ConstantGenericBitVector):
                res = z3.BitVecVal(arg3.value, arg1.value - arg2.value + 1)
            elif isinstance(arg3, Z3GenericBitVector):
                res = arg3.value
            else:
                import pdb; pdb.set_trace()

            if isinstance(arg0, ConstantGenericBitVector):
                arg0value = z3.BitVecVal(arg0.value, arg1.value)
                bv_size = arg1.value + 1
            elif isinstance(arg0, Z3DeferredIntGenericBitVector):
                import pdb; pdb.set_trace()
            elif isinstance(arg0, Z3GenericBitVector):
                arg0value = self._adapt_z3bv_width(arg0.value, arg1.value, False)
                bv_size = arg1.value + 1
            else:
                assert 0, "class %s for generic int not allowed" % str(arg0.__class__)
            if arg1.value != (bv_size - 1):
                res = z3.Concat(z3.Extract(bv_size - 1, arg1.value + 1, arg0value), res)
            if arg2.value != 0:
                res = z3.Concat(res, z3.Extract(arg2.value - 1, 0, arg0value))
            return Z3GenericBitVector(res, res.sort().size(), self.sharedstate._genericbvz3type)


    def exec_vector_access_bv_i(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            if arg0.value == 0:
                # very usefull if arg1 is abstract
                # happens on rv64 mem access: load could throw an exception
                # medeleg is arg0 then, but type of exception is unknown (depending on addr of load)
                # type of exception is index into medeleg (arg1 here)
                # bv[arg1] with an abstract arg1 is not allowed
                # if bv is constant 0 anyways, we can just return 0 
                # TODO: think if this kind of workaround would be usefull elsewhere too
                return ConstantSmallBitVector(0, op.resolved_type.width)
            return ConstantSmallBitVector(supportcode.vector_access_bv_i(None, arg0.value, arg1.value), op.resolved_type.width)
        else:
            return Z3Value(z3.Extract(arg1.value, arg1.value, arg0.toz3()))

    def exec_vector_access_o_i(self, op):
        """ Is this function supposed to access a vector  e.g. vec = [a,b,c], vector_access_o_i(vec,1) = b
            Or is it supposed to return one bit of a bv e.g. bv = 010100..., vector_access_o_i(bv,2) = 0?"""
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantGenericBitVector):
            if arg1.value == 0: return ConstantGenericBitVector(1 & arg1.value, op.resolved_type.width, self.sharedstate._genericbvz3type)
            return ConstantSmallBitVector(1 & (arg0.value >> arg1.value), op.resolved_type.width)
        elif isinstance(arg0, Z3GenericBitVector):
            if arg1.value < arg0.width:
                return Z3Value(z3.Extract(arg1.value, arg1.value, arg0.value))
            else:
                import pdb; pdb.set_trace()
        else:
            import pdb; pdb.set_trace()

    def exec_packed_field_cast_smallfixedbitvector(self, op):
        """ cast packed generic bv to small fixed bv"""
        arg0, arg1 = self.getargs(op)
        assert isinstance(arg1, Packed), "arg1 should be packed"
        unpackedarg1 = arg1.w_value
        if isinstance(unpackedarg1, ConstantGenericBitVector):
            return ConstantSmallBitVector(unpackedarg1.value, arg0.value)
        elif isinstance(unpackedarg1, Z3GenericBitVector):
            return Z3Value(unpackedarg1.value)
        elif isinstance(unpackedarg1, Z3DeferredIntGenericBitVector):
            intval = getattr(self.sharedstate._genericbvz3type, "value")(unpackedarg1.toz3())
            return Z3Value(z3.Int2BV(intval, arg0.value))
        else:
            assert 0, "class %s for generic bv not allowed" % str(arg1.__class__)

    def exec_pack_smallfixedbitvector(self, op):
        """ convert smallfixedbitvector into GenericBitVector and pack into a Packed Wrapper object 
            DONT omit this, there are 'unpack' operations """
        arg0, arg1 = self.getargs(op) #arg0 = bits? ,arg1 = SmallFixedBV
        if isinstance(arg1, ConstantSmallBitVector):
            return Packed(ConstantGenericBitVector(arg1.value, arg0.value, self.sharedstate._genericbvz3type))
        else:
            return Packed(Z3GenericBitVector(arg1.toz3(), arg0.value, self.sharedstate._genericbvz3type))
    
    def exec_pack_machineint(self, op):
        """ pack a MachineInt into a Packed Wrapper object """
        arg0, = self.getargs(op) 
        return Packed(arg0)
    
    def exec_pack(self, op):
        """ pack arg into a Packed Wrapper object"""
        arg, = self.getargs(op)
        return Packed(arg)
    
    def exec_unpack(self, op):
        arg, = self.getargs(op)
        return arg.w_value
      
    def exec_ones_zero_extended_unwrapped_res(self, op):
        """ create a bv of arg0 many ones and  a leading 0 ???"""
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantInt) and isinstance(arg1, ConstantInt):
            return ConstantSmallBitVector(supportcode.ones_zero_extended_unwrapped_res(arg0.value, arg1.value))
        else:
            return Z3Value(z3.If(arg0.toz3() < arg1.toz3(),
                                  (1 << z3.Int2BV(arg0.toz3(), op.resolved_type.width)) - 1,
                                  (1 << z3.Int2BV(arg1.toz3(), op.resolved_type.width)) - 1))

    def exec_zero_extend_bv_i_i(self, op):
        """ extend bitvector from arg1 to arg2 with zeros """
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(arg0.value, op.resolved_type.width)
        else:
            return Z3Value(z3.ZeroExt(arg2.value - arg1.value, arg0.toz3()))

    def exec_zero_extend_o_i_unwrapped_res(self, op):
        """ extend GenericBitvector to arg2 long smallfixed bv with zeros """
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantGenericBitVector):
            return ConstantSmallBitVector(arg0.value & (2**op.reolved_type.width - 1), op.resolved_type.width)
        elif isinstance(arg0, Z3GenericBitVector):
            return Z3Value(self._adapt_z3bv_width(arg0.value, op.resolved_type.width, False))
        elif isinstance(arg0, Z3DeferredIntGenericBitVector):
            intval = getattr(self.sharedstate._genericbvz3type, "value")(arg0.toz3())
            return Z3Value(z3.Int2BV(intval, op.resolved_Type.width))
        else:
            assert 0, "class %s for generic bv not allowed" % str(arg0.__class__)

    def exec_sign_extend_bv_i_i(self, op):
        arg0, arg1, arg2 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector):
            return ConstantSmallBitVector(supportcode.sign_extend_bv_i_i(None, arg0.value, arg1.value, arg2.value), op.resolved_type.width)
        else:
            return Z3Value(z3.SignExt(arg2.value - arg1.value, arg0.toz3()))
        
    def exec_sign_extend_o_i(self, op):
        arg0, arg1 = self.getargs(op)
        ### Generic BVs are storedas  z3 or py int, thus a sign extension does not do anything
        if isinstance(arg0, ConstantGenericBitVector):
            return ConstantGenericBitVector(arg0.value, arg1.value, self.sharedstate._genericbvz3type)
        elif isinstance(arg0, Z3GenericBitVector):
            return Z3GenericBitVector(z3.SignExt(arg1.value - arg0.width, arg0.value), arg1.value, self.sharedstate._genericbvz3type)
        elif isinstance(arg0, Z3Value):
            assert 0
        else:
            assert 0, "class %s for generic bv not allowed" % str(arg0.__class__)
    
    def exec_sign_extend_o_i_unwrapped_res(self, op):
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantGenericBitVector) and isinstance(arg1, ConstantInt):
             return ConstantSmallBitVector(arg0.value, op.resolved_ype.width)
        elif isinstance(arg0, Z3GenericBitVector):
           targetwidth = op.resolved_type.width
           Z3Value(z3.SignExt(targetwidth - arg0.value.sort().size(), arg0.value))
        elif isinstance(arg0, Z3DeferredIntGenericBitVector):
            # nice case: here we dont know the size of the former bv to turn the int
            # but int2bv(arg0.toz3(), arg1.value) is exactly the sign ext
            #TODO: move the getattr everywhere into a separate private function
            intval = getattr(self.sharedstate._genericbvz3type, "value")(arg0.toz3())
            return Z3Value(z3.Int2BV(intval, arg1.value))
        else: 
            assert 0, "class %s for generic bv not allowed" % str(arg0.__class__)

    def exec_unsigned_bv(self, op):
        """ arg is a bv , result is that bv cast to MachineInt """
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantSmallBitVector) and isinstance(arg1, ConstantInt):
            return ConstantInt(supportcode.unsigned_bv(None, arg0.value, arg1.value))
        else:
            val = z3.ZeroExt(64 - arg1.value, arg0.toz3())
            return Z3CastedValue(val, z3.BV2Int, [False])
        
    def exec_unsigned_bv_wrapped_res(self, op):
        """ arg is a bv , result is that bv cast to generic int """
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, ConstantGenericInt) and isinstance(arg1, ConstantInt):
            return ConstantGenericInt(supportcode.unsigned_bv(None, arg0.value, arg1.value))
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
        if isinstance(arg0, Packed): arg0 = arg0.w_value
        if isinstance(arg0, ConstantSmallBitVector) or isinstance(arg0, ConstantGenericBitVector):
            return StringConstant(bin(arg0.value))
        elif isinstance(arg0, Z3GenericBitVector):
            bvval = arg0.value
        elif isinstance(arg0, Z3DeferredIntGenericBitVector):
            intval = getattr(self.sharedstate._genericbvz3type, "value")(arg0.toz3())
            bvval = z3.Int2BV(intval, 64) # if we dont know the generic bvs size here, just assume 64
            self._debug_print("zbits_str: generic bv with unkown size", True)
            self._debug_print("zbits_str: using 64 bit", True)
        else:
            assert 0, "class %s for generic bv not allowed" % str(arg0.__class__)
        zero, one = z3.StringVal("0"), z3.StringVal("1") 
        res = z3.If(z3.Extract(0, 0, bvval) == 0, zero, one)# index read from right
        for i in range(1, bvval.sort().size()):
            res = z3.Concat(z3.If(z3.Extract(i, i, bvval) == 0, zero, one), res) # concat(x,y) = xy, but bv extract index 0is on the right side
        return Z3StringValue(res)
        
    def exec_zhex_str(self, op):
        """convert int? to hex as string
           currently only the lowest 64 bits can be used when converting an abstract argument"""
        arg0, = self.getargs(op)
        if isinstance(arg0, ConstantInt) or isinstance(arg0, ConstantGenericInt):
            return StringConstant(hex(arg0.value))
        else:
            res = None
            bits = 64#arg0.toz3().sort().size()
            bv = z3.Int2BV(arg0.toz3(), bits)
            i = 0
            while (bits-i) > 0:
                num = z3.BV2Int(z3.Extract(i + min(3, bits-i), i, bv))
                i += 4
                if res == None:
                    res = self._build_4bit_hex_expr(num, 2**(min(3, bits-i)+2)-1)
                else:
                    res = z3.Concat(self._build_4bit_hex_expr(num, 2**(min(3, bits-i)+2)-1), res)
            return Z3StringValue(res)

    def _build_4bit_hex_expr(self, num, ctr):
        if ctr != 1:
            sym = chr(ctr+30) if (ctr>=0 and ctr<=9) else chr(ctr+131)
            return z3.If(num == ctr, z3.StringVal(sym), self._build_4bit_hex_expr(num, ctr - 1))
        return z3.If(num == ctr, z3.StringVal("1"), z3.StringVal("0"))

    def exec_zconcat_str(self, op):
        """ str concat arg0 and arg1 """
        arg0, arg1 = self.getargs(op)
        if isinstance(arg0, StringConstant) and isinstance(arg1, StringConstant):
            return StringConstant("".join([arg0.value, arg1.value]))
        else:
            return Z3StringValue(z3.Concat(arg0.toz3(), arg1.toz3()))
        
    def exec_zsail_barrier(self, op):
        assert 0, "TODO"

    def exec_zprint(self, op):
        # I dont know if this is riscv specific
        if self._allow_ir_print:
            print str(self.getargs(op)[0])

    ### Arch specific Operations in subclass ###

class NandInterpreter(Interpreter):
    """ Interpreter subclass for nand2tetris ISA """

    def __init__(self, graph, args, shared_state=None, entrymap=None):
        super(NandInterpreter, self).__init__(graph, args, shared_state, entrymap)# py2 super 
        self.memory = z3.Array('memory', z3.BitVecSort(16), z3.BitVecSort(16)) # nand2tetris memory cells are 16 bit each
    
    ### Nand2Tetris specific Operations ###

    def exec_my_read_mem(self, op):
        """ read from memory """
        # res type = SmallFixedBitVector(16)
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
        self.memory = z3.Array('memory', z3.BitVecSort(64), z3.BitVecSort(8))

    def _init_mem(self):
        """ initial memory def is needed for smtlib expressions """
        self.memory = z3.Array('memory', z3.BitVecSort(64), z3.BitVecSort(8))
        return self.memory

    ### RISCV specific Operations ###

    def exec_read_mem_o_o_o_i(self, op):
        """ return mem[arg2:arg2+arg3] as generic bv """
        arg0, _, arg2, arg3 = self.getargs(op) # layout, addr_size, addr, n_bytes
        #TODO: what todo with the layout
        assert isinstance(arg3, ConstantInt), "abstract width memory access impossible"
        if isinstance(arg2, ConstantSmallBitVector) or isinstance(arg2, ConstantGenericBitVector):
            addr = z3.BitVecVal(arg2.value, 64) # mem access only via 64 bit bvs
        elif isinstance(arg2, Z3GenericBitVector):
            addr = self._adapt_z3bv_width(arg2.value, 64) # mem access only via 64 bit bvs
        elif isinstance(arg2, Z3DeferredIntGenericBitVector):
            intval = getattr(self.sharedstate._genericbvz3type, "value")(arg2.toz3())
            addr = z3.Int2BV(intval, 64) # mem access only via 64 bit bvs
        else:
            assert 0, "class %s for generic bv not allowed" % str(arg2.__class__)

        # TODO: use read_memory(addr) instead
        val = self.memory[addr]
        for i in range(arg3.value - 1):
            val = z3.Concat(val, self.memory[addr + i])

        return Z3GenericBitVector(val, arg3.value * 8, self.sharedstate._genericbvz3type)
    
    def exec_read_mem_exclusive_o_o_o_i(self, op):
        return self.exec_read_mem_o_o_o_i(op)

    def exec_zsys_enable_zzfinx(self, op):
        return BooleanConstant(False) 

    def exec_zsys_enable_svinval(self, op):
        return BooleanConstant(True)

    def exec_zsys_enable_zzicbozz(self, op):
        return BooleanConstant(True)
    
    def exec_zsys_enable_zzicbom(self, op):
        return BooleanConstant(True)
    
    def exec_zsys_enable_zzcb(self, op):
        return BooleanConstant(True)
    
    def exec_zplat_enable_misaligned_access(self, op):
        return BooleanConstant(False)

    def exec_zget_config_print_reg(self, op):
        return BooleanConstant(False)
    
    def exec_zget_config_print_platform(self, op):
        return BooleanConstant(False)
    
    def exec_zget_config_print_mem(self, op):
        return BooleanConstant(True)
    
    def exec_zplat_mtval_has_illegal_inst_bits(self, op):
        return BooleanConstant(False)
    
    def exec_zsys_pmp_count(self, op):
        # pmp enabling not supported yet, thus 0 
        return ConstantInt(0)
    
    def exec_zplat_clint_base(self, op):
        # value copied from supportcoderiscv
        return ConstantSmallBitVector(0x2000000, op.resolved_type.width)
    
    def exec_zplat_clint_sizze(self, op):
        # value copied from supportcoderiscv
        return ConstantSmallBitVector(0xc0000, op.resolved_type.width)
    
    def exec_zplat_htif_tohost(self, op):
        # value copied from supportcoderiscv
        return ConstantSmallBitVector(0x80001000, op.resolved_type.width)
    
    def exec_zplat_ram_base(self, op):
        return ConstantSmallBitVector(0x80000000, op.resolved_type.width)
    
    def exec_zplat_ram_sizze(self, op): 
        # this function is actually called zplat_ram_sizze, its not a spelling mistake
        return ConstantSmallBitVector(0x4000000, op.resolved_type.width)
    
    def exec_zplat_rom_base(self, op):
        return ConstantSmallBitVector(0x1000, op.resolved_type.width)
    
    def exec_zplat_rom_sizze(self, op):
        # this function is actually called zplat_rom_sizze, its not a spelling mistake
        return ConstantSmallBitVector(0x100, op.resolved_type.width)

    def exec_zprint_platform(self, op):
        if self._allow_ir_print:
            print str(self.getargs(op)[0])

    def exec_zprint_mem(self, op):
        if self._allow_ir_print:
            print str(self.getargs(op)[0])

    def exec_zplat_term_write(self, op):
        # seems to be riscv specific
        if self._allow_ir_print:
            print str(self.getargs(op)[0])
