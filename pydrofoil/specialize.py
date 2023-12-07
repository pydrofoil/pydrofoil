from pydrofoil import types, ir, parse, supportcode, bitvector

# type specialization: func_zAArch64_AddrTop should return MachineInt
# is_zero/one_subrange is a nice example for something that could accept SmallFixedBitVector (and MachineInts)
# can have both "demand" (casts inside a function)
# and "supply" (arguments from outside)

# focus on: MemSingle_read

# - demand ints
# - result casts


def usefully_specializable(graph):
    if graph.has_loop:
        return False
    if not any(isinstance(arg.resolved_type, (types.Int, types.GenericBitVector)) for arg in graph.args):
        return False
    for block in graph.iterblocks():
        if isinstance(block.next, ir.Return):
            if block.next.value is None:
                return False
    return True


class Specializer(object):
    def __init__(self, graph, codegen):
        self.graph = graph
        for block in graph.iterblocks():
            if isinstance(block.next, ir.Return):
                if block.next.value is not None:
                    self.resulttyp = block.next.value.resolved_type
        self.argtyps = [arg.resolved_type for arg in graph.args]
        self.cache = {}
        self.codegen = codegen

    def specialize_call(self, call, optimizer):
        key, args = self._extract_key(call, optimizer)
        if key is None:
            return None
        if key in self.cache:
            stubgraph = self.cache[key]
        else:
            stubgraph = self._make_stub(key)
            self.cache[key] = stubgraph
        return optimizer.newop(stubgraph.name, args, call.resolved_type, call.sourcepos, call.varname_hint)

    def _make_stub(self, key):
        args = []
        ops = []
        callargs = []
        sargs = []
        for oldarg, typ in zip(self.graph.args, key):
            arg = ir.Argument(oldarg.name, typ)
            args.append(arg)
            if typ != oldarg.resolved_type:
                if typ is types.MachineInt():
                    op = ir.Operation('zz5i64zDzKz5i', [arg], types.Int())
                    ops.append(op)
                    callargs.append(op)
                    sargs.append('i')
                else:
                    op = ir.Cast(arg, oldarg.resolved_type)
                    ops.append(op)
                    callargs.append(op)
                    sargs.append('bv%s' % (typ.width, ))
            else:
                callargs.append(arg)
                sargs.append('o')
        ops.append(ir.Operation(self.graph.name, callargs, self.resulttyp))
        block = ir.Block(ops)
        block.next = ir.Return(ops[-1])
        graph = ir.Graph(self.graph.name + "_specialized_" + "_".join(sargs), args, block)
        print "MAKING SPECIALIZATION", graph.name
        ir._inline(graph, block, len(ops) - 1, self.graph)
        ir.simplify(graph, self.codegen)
        typ = types.Function(types.Tuple(tuple(key)), self.resulttyp)
        self.codegen.emit_extra_graph(graph, typ)
        self.codegen.specialization_functions[graph.name] = self
        return graph

    def _extract_key(self, call, optimizer):
        key = []
        args = []
        useful = False
        for arg, argtyp in zip(call.args, self.argtyps):
            if argtyp is types.Int():
                try:
                    arg = optimizer._extract_machineint(arg)
                except ir.NoMatchException:
                    pass
                else:
                    key.append(types.MachineInt())
                    args.append(arg)
                    useful = True
                    continue
            elif isinstance(argtyp, types.GenericBitVector):
                try:
                    arg, typ = optimizer._extract_smallfixedbitvector(arg)
                except ir.NoMatchException:
                    pass
                else:
                    key.append(typ)
                    args.append(arg)
                    useful = True
                    continue
            key.append(arg.resolved_type)
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
