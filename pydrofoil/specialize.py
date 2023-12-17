from pydrofoil import types, ir, parse, supportcode, bitvector

# type specialization: func_zAArch64_AddrTop should return MachineInt
# and "supply" (arguments from outside)

# focus on: MemSingle_read

# - demanded result casts
# - make extract* deal with defaultvalue

# allow inlining of small specialized functions
# specialize phi as constants?

# zFPDefaultNaN__1_specialized_16_o

# need to switch to full cfg fix point approach eventually


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
        self.name_to_typ = {}

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
            if len(self.cache) > 32:
                print "TOO MANY VARIANTS!", self.graph.name
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
            return optimizer._make_int64_to_int(newcall)
        if isinstance(restype, types.SmallFixedBitVector):
            assert original_restype is types.GenericBitVector()
            return optimizer.newcast(newcall, types.GenericBitVector())
        if isinstance(restype, types.Struct):
            fields = []
            for fieldtyp, fieldtyp_orig, name in zip(restype.typs, original_restype.typs, restype.names):
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
        print "MAKING SPECIALIZATION", graph.name
        ir._inline(graph, block, len(ops) - 1, self.graph, add_comment=False)
        graph.has_loop = self.graph.has_loop
        ir.light_simplify(graph, self.codegen)
        # check whether we can specialize on the return type
        resulttyp, nameextension = self.find_result_type(graph)
        if nameextension is not None:
            graph.name += "__" + nameextension
            ir.remove_dead(graph, self.codegen)
        if ir.should_inline(graph):
            import pdb;pdb.set_trace()
            self.codegen.inlinable_functions[graph.name] = graph
        self.codegen.schedule_graph_specialization(graph)
        self.codegen.specialization_functions[graph.name] = self
        self.name_to_typ[graph.name] = resulttyp
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
            del self.name_to_typ[name]
            self.name_to_typ[graph.name] = resulttyp
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
                        value = None
                    key.append((types.MachineInt(), value))
                    args.append(arg)
                    useful = argtyp is types.Int() or value is not None
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
    def _optimize_op(self, block, index, op):
        if (isinstance(op, ir.Operation) and
                op.name in self.codegen.specialization_functions):
            specializer = self.codegen.specialization_functions[op.name]
            newop = specializer.specialize_call(op, self)
            if newop:
                return newop
        self.newoperations.append(op)


class FixpointSpecializer(object):
    def __init__(self):
        import collections
        self.specialization_todo = collections.deque()
        self.specialization_todo_set = set()
        self.inlinable_functions = {}
        self.specialization_functions = {}
        self.all_graph_by_name = {}

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
            print "\033[1K\rSPECIALIZING %s (todo: %s)" % (graph.name, len(todo)),
            sys.stdout.flush()
            self.specialization_todo_set.remove(graph)
            changed = ir.optimize(graph, self)
            if changed and graph.name in self.specialization_functions:
                spec = self.specialization_functions[graph.name]
                if spec.graph is graph:
                    continue
                schedule_deps = False
                if ir.should_inline(graph, self.should_inline):
                    import pdb;pdb.set_trace()
                    self.inlinable_functions[graph.name] = graph
                    schedule_deps = True
                elif spec.check_return_type_change(graph):
                    schedule_deps = True
                if schedule_deps:
                    for graph in spec.dependencies:
                        if graph not in self.specialization_todo_set:
                            todo.append(graph)
                            self.specialization_todo_set.add(graph)

    def extract_needed_extra_graphs(self, starting_graphs):
        result = set()
        starting_graphs_set = set(starting_graphs)
        todo = list(starting_graphs)
        while todo:
            graph = todo.pop()
            for op, block in graph.iterblockops():
                if not isinstance(op, ir.Operation):
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
            restyp = self.specialization_functions[graph.name].name_to_typ[graph.name]
            typ = types.Function(types.Tuple(tuple(a.resolved_type for a in graph.args)), restyp)
            l.append((graph, typ))
        return l

