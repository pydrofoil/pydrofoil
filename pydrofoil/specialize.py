from pydrofoil import types, ir, parse, supportcode, bitvector

# type specialization: func_zAArch64_AddrTop should return MachineInt
# and "supply" (arguments from outside)

# focus on: MemSingle_read

# - demand ints of arguments
# - demanded result casts
# - make extract* deal with defaultvalue

# later: need to specialize tuple return types

# allow inlining of small specialized functions
# specialize phi as constants?

def usefully_specializable(graph):
    if not any(isinstance(arg.resolved_type, (types.Int, types.GenericBitVector, types.MachineInt, types.Bool)) for arg in graph.args):
        return False
    numblocks = 0
    for block in graph.iterblocks():
        if isinstance(block.next, ir.Return):
            if block.next.value is None:
                return False
        numblocks += 1
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

    def specialize_call(self, call, optimizer):
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
                print "TOO MANY VARIANTS!", self.graph.name
                return None
            self.cache[key] = None # meaning "in progress"
            stubgraph, restype = self._make_stub(key)
            self.cache[key] = stubgraph, restype
        if call.name == stubgraph.name:
            return None # no change in optimization level
        newcall = optimizer.newop(stubgraph.name, args, restype, call.sourcepos, call.varname_hint)
        if restype != call.resolved_type:
            if restype is types.MachineInt():
                return optimizer._make_int64_to_int(newcall)
            else:
                assert isinstance(restype, types.SmallFixedBitVector)
                assert call.resolved_type is types.GenericBitVector()
                return optimizer.newcast(newcall, types.GenericBitVector())
        return newcall

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
        ir._inline(graph, block, len(ops) - 1, self.graph)
        graph.has_loop = self.graph.has_loop
        ir.optimize(graph, self.codegen)

        # check whether we can specialize on the return type
        resulttyp = self.resulttyp
        returnblock = None
        for block in graph.iterblocks():
            if isinstance(block.next, ir.Return):
                if returnblock is not None:
                    break # only support a single return block for now
                returnblock = block
        else:
            res, nameextension = self._find_result(graph, returnblock)
            if res:
                returnblock.next.value = res
                resulttyp = res.resolved_type
                graph.name += nameextension
                ir.remove_dead(graph, self.codegen)
        typ = types.Function(types.Tuple(tuple(key)), resulttyp)
        self.codegen.emit_extra_graph(graph, typ)
        self.codegen.specialization_functions[graph.name] = self
        return graph, resulttyp

    def _find_result(self, graph, returnblock):
        optimizer = ir.BaseOptimizer(graph, self.codegen)
        returnvalue = returnblock.next.value
        if self.resulttyp is types.Int():
            try:
                return optimizer._extract_machineint(returnvalue), "__i"
            except ir.NoMatchException:
                pass
        elif self.resulttyp is types.GenericBitVector():
            try:
                res, resulttyp = optimizer._extract_smallfixedbitvector(returnvalue)
            except ir.NoMatchException:
                pass
            else:
                return res, "__bv%s" % resulttyp.width
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
            key = None
        else:
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
