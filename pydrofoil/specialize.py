import sys
from collections import defaultdict
from pydrofoil import types, ir, parse, supportcode, bitvector

# type specialization: func_zAArch64_AddrTop should return MachineInt
# and "supply" (arguments from outside)

# focus on: MemSingle_read

# - demanded result casts
# - make extract* deal with defaultvalue

# zFPDefaultNaN__1_specialized_16_o

# add a runtime check if one of the variants we have fits the data we have, for
# unspecialized functions (particularly with loops)

# should analyze whether booleans are actually switched on in the body of the
# function?

# "demanded" casts of results


def usefully_specializable(graph):
    numblocks = 0
    restype = None
    for block in graph.iterblocks():
        if isinstance(block.next, ir.Return):
            if block.next.value is None:
                return False
            restype = block.next.value.resolved_type
        numblocks += 1
    if not any(isinstance(arg.resolved_type, (types.Int, types.GenericBitVector, types.MachineInt, types.Bool)) for arg in graph.args):
        if restype is not types.Int() and restype is not types.GenericBitVector():
            return False
    return numblocks < 100


class Specializer(object):
    def __init__(self, graph, codegen):
        self.graph = graph
        for block in graph.iterblocks():
            if isinstance(block.next, ir.Return):
                if block.next.value is not None:
                    self.resulttyp = block.next.value.resolved_type
        self.argtyps = [arg.resolved_type for arg in graph.args]
        self.demanded_argtyps = [None] * len(self.argtyps)

        # XXX super wasteful to compute anticipated_casts all the time :-(
        optimizer = ir.BaseOptimizer(graph, codegen)
        for index, arg in enumerate(graph.args):
            if arg.resolved_type is types.Int():
                anticipated = optimizer.anticipated_casts.get(graph.startblock, set())
                if (arg, types.MachineInt()) in anticipated:
                    self.demanded_argtyps[index] = types.MachineInt()
        self.cache = {}
        self.codegen = codegen
        self.dependencies = set()
        self.name_to_restyp = {}

    def specialize_call(self, call, optimizer):
        if self.graph is optimizer.graph:
            return
        key, args = self._extract_key(call, optimizer)
        if key is None:
            return None
        if key in self.cache:
            value = self.cache[key]
            if value is None:
                return None # recursive graph building, will be fixed later
            stubgraph, restype = value
        else:
            if len(self.cache) > 64:
                self.codegen.print_debug_msg("TOO MANY VARIANTS!", self.graph.name)
                return None
            self.cache[key] = None # meaning "in progress"
            stubgraph, restype = self._make_stub(key)
            self.cache[key] = stubgraph, restype
        self.dependencies.add(optimizer.graph)
        if call.name == stubgraph.name:
            return None # no change in optimization level
        newcall = optimizer.newop(stubgraph.name, args, restype, call.sourcepos, call.varname_hint)
        return self._reconstruct_result(restype, call.resolved_type, newcall, optimizer)

    def _reconstruct_result(self, restype, original_restype, newcall, optimizer):
        if restype is original_restype:
            return newcall
        if restype is types.MachineInt():
            if original_restype is types.Int():
                return optimizer._make_int64_to_int(newcall)
            else:
                assert original_restype is types.Packed(types.Int())
                return optimizer.newop(
                        "@pack_machineint", [newcall], original_restype)
        if isinstance(restype, types.SmallFixedBitVector):
            if original_restype is types.GenericBitVector():
                return optimizer.newcast(newcall, types.GenericBitVector())
            else:
                assert original_restype is types.Packed(types.GenericBitVector())
                return optimizer.newop(
                        "@pack_smallfixedbitvector", [ir.MachineIntConstant(restype.width), newcall], original_restype)
        if isinstance(restype, types.Struct):
            fields = []
            for fieldtyp, fieldtyp_orig, name in zip(restype.typs, original_restype.internaltyps, restype.names):
                field = ir.FieldAccess(name, [newcall], fieldtyp)
                optimizer.newoperations.append(field)
                converted_field = self._reconstruct_result(fieldtyp, fieldtyp_orig, field, optimizer)
                fields.append(converted_field)
            result = ir.StructConstruction(original_restype.name, fields, original_restype)
            optimizer.newoperations.append(result)
            return result

    def _make_stub(self, key):
        args = []
        ops = []
        callargs = []
        sargs = []
        for oldarg, (typ, value) in zip(self.graph.args, key):
            arg = ir.Argument(oldarg.name, typ)
            args.append(arg)
            if typ != oldarg.resolved_type:
                if typ is types.MachineInt():
                    if value is not None:
                        sargs.append(str(value).replace('-', 'minus'))
                        arg = ir.MachineIntConstant(value)
                    else:
                        sargs.append('i')
                    op = ir.Operation('zz5i64zDzKz5i', [arg], types.Int())
                    ops.append(op)
                    callargs.append(op)
                else:
                    assert isinstance(typ, types.SmallFixedBitVector)
                    op = ir.Cast(arg, oldarg.resolved_type)
                    ops.append(op)
                    callargs.append(op)
                    sargs.append('bv%s' % (typ.width, ))
            else:
                if value is not None:
                    sargs.append(str(value).replace('-', 'minus'))
                    if typ is types.Bool():
                        callargs.append(ir.BooleanConstant.TRUE if value else ir.BooleanConstant.FALSE)
                    else:
                        assert typ is types.MachineInt()
                        callargs.append(ir.MachineIntConstant(value))
                else:
                    callargs.append(arg)
                    sargs.append('o')
        ops.append(ir.Operation(self.graph.name, callargs, self.resulttyp))
        block = ir.Block(ops)
        block.next = ir.Return(ops[-1])
        graph = ir.Graph(self.graph.name + "_specialized_" + "_".join(sargs), args, block)
        self.codegen.print_debug_msg("MAKING SPECIALIZATION", graph.name)
        ir._inline(graph, self.codegen, block, len(ops) - 1, self.graph, add_comment=False)
        graph.has_loop = self.graph.has_loop
        ir.light_simplify(graph, self.codegen)
        # check whether we can specialize on the return type
        resulttyp, nameextension = self.find_result_type(graph)
        if nameextension is not None:
            graph.name += "__" + nameextension
            ir.remove_dead(graph, self.codegen)
        if ir.should_inline(graph, self.codegen.should_inline):
            self.codegen.inlinable_functions[graph.name] = graph
        self.codegen.schedule_graph_specialization(graph)
        self.codegen.specialization_functions[graph.name] = self
        self.name_to_restyp[graph.name] = resulttyp
        return graph, resulttyp

    def find_result_type(self, graph):
        resulttyp = self.resulttyp
        # only support a single return block for now
        returnblock = self._extract_single_return_block(graph)
        if returnblock:
            res, nameextension = self._find_result(graph, returnblock, returnblock.next.value)
            if res:
                returnblock.next.value = res
                resulttyp = res.resolved_type
                return resulttyp, nameextension
        return resulttyp, None

    def _extract_single_return_block(self, graph):
        returnblock = None
        for block in graph.iterblocks():
            if isinstance(block.next, ir.Return):
                if returnblock is not None:
                    return None
                returnblock = block
        return returnblock

    def check_return_type_change(self, graph):
        returnblock = self._extract_single_return_block(graph)
        if returnblock is None:
            return False
        old_resulttyp = returnblock.next.value.resolved_type
        resulttyp, nameextension = self.find_result_type(graph)
        if nameextension and resulttyp is not old_resulttyp and resulttyp is not self.resulttyp:
            # bit annoying name manipulation
            name = graph.name
            if old_resulttyp is not self.resulttyp:
                graph.name = graph.name.rsplit("__", 1)[0]
                ir.remove_dead(graph, self.codegen)
            graph.name += "__" + nameextension
            self.codegen.graph_changed_name(name, graph)
            del self.name_to_restyp[name]
            self.name_to_restyp[graph.name] = resulttyp
            for key, (g, typ) in self.cache.iteritems():
                if g is graph:
                    assert typ is old_resulttyp
                    self.cache[key] = (g, resulttyp)
                    break
            else:
                assert 0
            return True
        return False

    def _find_result(self, graph, returnblock, returnvalue, optimizer=None):
        if optimizer is None:
            optimizer = ir.BaseOptimizer(graph, self.codegen)
        if returnvalue.resolved_type is types.Int():
            try:
                return optimizer._extract_machineint(returnvalue), "i"
            except ir.NoMatchException:
                pass
        elif returnvalue.resolved_type is types.GenericBitVector():
            try:
                res, resulttyp = optimizer._extract_smallfixedbitvector(returnvalue)
            except ir.NoMatchException:
                pass
            else:
                return res, "bv%s" % resulttyp.width
        elif returnvalue.resolved_type is types.Packed(types.Int()):
            if type(returnvalue) is ir.Operation and returnvalue.name == '@pack_machineint':
                res = returnvalue.args[0]
                resulttyp = res.resolved_type
                return res, "i"
        elif returnvalue.resolved_type is types.Packed(types.GenericBitVector()):
            if type(returnvalue) is ir.Operation and returnvalue.name == '@pack_smallfixedbitvector':
                res = returnvalue.args[1]
                resulttyp = res.resolved_type
                return res, "bv%s" % resulttyp.width
        elif isinstance(returnvalue.resolved_type, types.Struct) and returnvalue.resolved_type.tuplestruct and isinstance(returnvalue, ir.StructConstruction):
            fields = []
            extensions = []
            fieldtyps = []
            useful = False
            for value in returnvalue.args:
                res, nameextension = self._find_result(graph, returnblock, value, optimizer)
                if res is not None:
                    useful = True
                    fields.append(res)
                    extensions.append(nameextension)
                else:
                    fields.append(value)
                    extensions.append('o')
                fieldtyps.append(fields[-1].resolved_type)
            if useful:
                names = tuple(['%s_%s' % (name, index) for index, name in enumerate(extensions)])
                fieldtyps = tuple(fieldtyps)
                origname = returnvalue.resolved_type.name
                name = "tup_%s_%s" % (origname, '_'.join(extensions))
                newtyp = types.Struct(name, names, fieldtyps, True)
                self.codegen.add_struct_type(newtyp.name, "TupSpec_" + newtyp.name, newtyp)
                newres = ir.StructConstruction(newtyp.name, fields, newtyp)
                returnblock.operations.append(newres)
                return newres, "_".join(['tup'] + extensions + ['put'])
        return None, None

    def _extract_key(self, call, optimizer):
        key = []
        args = []
        useful = False
        for arg, argtyp, demanded_argtyp in zip(call.args, self.argtyps, self.demanded_argtyps):
            if argtyp is types.Int() or argtyp is types.MachineInt():
                try:
                    arg = optimizer._extract_machineint(arg)
                except ir.NoMatchException:
                    pass
                else:
                    if isinstance(arg, ir.MachineIntConstant) and 0 <= arg.number <= 64:
                        value = arg.number
                    else:
                        #if isinstance(arg, ir.Phi) and all(isinstance(prev, ir.Constant) for prev in arg.prevvalues):
                        #    import pdb;pdb.set_trace()
                        value = None
                    key.append((types.MachineInt(), value))
                    args.append(arg)
                    useful = argtyp is types.Int() or value is not None or useful
                    continue
            elif isinstance(argtyp, types.GenericBitVector):
                try:
                    arg, typ = optimizer._extract_smallfixedbitvector(arg)
                except ir.NoMatchException:
                    pass
                else:
                    key.append((typ, None))
                    args.append(arg)
                    useful = True
                    continue
            elif isinstance(argtyp, types.Bool) and isinstance(arg, ir.BooleanConstant):
                key.append((argtyp, arg.value))
                args.append(arg)
                useful = True
                continue
            if demanded_argtyp is types.MachineInt():
                key.append((types.MachineInt(), None))
                args.append(optimizer._make_int_to_int64(arg))
                useful = True
                continue
            key.append((arg.resolved_type, None))
            args.append(arg)
        if not useful:
            if self.resulttyp is not types.Int() and self.resulttyp is not types.GenericBitVector():
                return None, None
            # for Int and GenericBitVector we might still benefit from result type specialization
        key = tuple(key)
        assert len(key) == len(args) == len(call.args)
        return key, args


class SpecializingOptimizer(ir.BaseOptimizer):
    def __init__(self, graph, codegen, *args, **kwargs):
        split_for_arg_constness(graph, codegen)
        ir.BaseOptimizer.__init__(self, graph, codegen, *args, **kwargs)

    def _optimize_op(self, block, index, op):
        if (isinstance(op, ir.Operation) and
                op.name in self.codegen.specialization_functions):
            specializer = self.codegen.specialization_functions[op.name]
            newop = specializer.specialize_call(op, self)
            if newop:
                return newop
        return ir.BaseOptimizer._optimize_op(self, block, index, op)

SPECIALIZABLE_BUILTINS = frozenset("""
@zero_extend_o_i @undefined_bitvector_i
@zeros_i
""".split())

@ir.repeat
def split_for_arg_constness(graph, codegen):
    for block in graph.iterblocks():
        for index, op in enumerate(block.operations):
            if not isinstance(op, ir.Operation):
                continue
            if op.name not in codegen.specialization_functions and op.name not in SPECIALIZABLE_BUILTINS:
                continue
            for argindex, arg in enumerate(op.args):
                if not isinstance(arg, ir.Phi):
                    continue
                if arg.resolved_type is not types.MachineInt():
                    continue
                if all(isinstance(prev, ir.Constant) and 0 <= prev.number <= 64 for prev in arg.prevvalues):
                    break
            else:
                continue
            newblock = block.split(index, keep_op=True)
            switchblock = newblock.split(len(newblock.operations), keep_op=True)
            replacements = {}
            ops_from_newblock = set(newblock.operations)
            callvalues = {copied_op: [] for copied_op in newblock.operations}
            prevblocks = []
            for valueindex, constvalue in enumerate(arg.prevvalues):
                last = valueindex == len(arg.prevvalues) - 1
                if not last:
                    callblock = ir.Block()
                    nextblock = ir.Block()
                    cond = block.emit(ir.Operation, "@eq", [arg, constvalue], types.Bool())
                    block.next = ir.ConditionalGoto(cond, callblock, nextblock)
                    block = nextblock
                else:
                    callblock = block

                # copy the operations
                for to_copy_op in newblock.operations:
                    for value in to_copy_op.getargs():
                        if value not in ops_from_newblock:
                            replacements[value] = value
                replacements[arg] = constvalue
                copy = newblock.copy_operations(replacements)
                for copied_op in newblock.operations:
                    callvalues[copied_op].append(replacements[copied_op])
                callblock.operations.extend(copy)
                prevblocks.append(callblock)
                callblock.next = ir.Goto(switchblock)
            replacements = {}
            for copied_op in newblock.operations:
                if copied_op.resolved_type is types.Unit():
                    continue
                phi = ir.Phi(prevblocks, callvalues[copied_op], copied_op.resolved_type)
                switchblock.operations.insert(0, phi)
                replacements[copied_op] = phi
            graph.replace_ops(replacements)
            return True
    return False


class FixpointSpecializer(object):
    should_inline = None

    def __init__(self, entrypoints=None):
        import collections
        import py
        self.specialization_todo = collections.deque()
        self.specialization_todo_set = set()
        self.inlinable_functions = {}
        self.specialization_functions = {}
        self.all_graph_by_name = {}
        self.method_graphs_by_name = {} # name -> list of graphs
        self.inline_dependencies = defaultdict(set) # graph -> {graphs}
        self.program_entrypoints = entrypoints
        # attributes for printing
        self._highlevel_task_msg = ''
        self._terminal_columns = py.io.get_terminal_width()

    def schedule_graph_specialization(self, graph):
        self.all_graph_by_name[graph.name] = graph
        self.specialization_todo.append(graph)
        self.specialization_todo_set.add(graph)

    def graph_changed_name(self, oldname, graph):
        assert self.all_graph_by_name[oldname] is graph
        assert oldname != graph.name
        del self.all_graph_by_name[oldname]
        self.all_graph_by_name[graph.name] = graph
        self.specialization_functions[graph.name] = self.specialization_functions[oldname]

    def specialize_all(self):
        import sys
        todo = self.specialization_todo
        while todo:
            graph = todo.popleft()
            self.print_highlevel_task("(todo: %s) OPTIMIZING %s" % (len(todo), graph.name))
            self.specialization_todo_set.remove(graph)
            changed = ir.optimize(graph, self)
            schedule_deps = None
            if changed and graph.name in self.specialization_functions:
                spec = self.specialization_functions[graph.name]
                if spec.graph is graph:
                    continue
                if ir.should_inline(graph, self.should_inline):
                    self.inlinable_functions[graph.name] = graph
                    schedule_deps = spec.dependencies
                elif spec.check_return_type_change(graph):
                    schedule_deps = spec.dependencies
            elif changed and graph.name not in self.inlinable_functions:
                if ir.should_inline(graph, self.should_inline):
                    self.inlinable_functions[graph.name] = graph
                    schedule_deps = self.inline_dependencies[graph.name]
            if schedule_deps:
                for othergraph in schedule_deps:
                    if othergraph not in self.specialization_todo_set:
                        todo.append(othergraph)
                        self.specialization_todo_set.add(othergraph)

    def extract_needed_extra_graphs(self, starting_graphs):
        result = set()
        starting_graphs_set = set(starting_graphs)
        todo = list(starting_graphs)
        while todo:
            graph = todo.pop()
            for op, block in graph.iterblockops():
                if type(op) is not ir.Operation:
                    continue
                if op.name not in self.all_graph_by_name:
                    continue
                called_graph = self.all_graph_by_name[op.name]
                if called_graph in starting_graphs_set:
                    continue
                if called_graph not in result:
                    todo.append(called_graph)
                    result.add(called_graph)
        l = []
        for graph in result:
            typ = None
            if graph.name in self.specialization_functions:
                spec = self.specialization_functions[graph.name]
                if graph.name in spec.name_to_restyp:
                    restyp = spec.name_to_restyp[graph.name]
                    typ = types.Function(types.Tuple(tuple(a.resolved_type for a in graph.args)), restyp)
            l.append((graph, typ))
        return l

    def print_highlevel_task(self, *args):
        msg = " ".join(str(x) for x in args)
        self._highlevel_task_msg = "\033[1K\r%s" % msg
        print self._highlevel_task_msg[:self._terminal_columns],
        sys.stdout.flush()

    def print_debug_msg(self, *args):
        msg = self._highlevel_task_msg + " " + " ".join(str(x) for x in args)
        msg = msg[:self._terminal_columns]
        print msg,
        sys.stdout.flush()

    def print_persistent_msg(self, *args):
        print
        print " ".join(str(x) for x in args)
