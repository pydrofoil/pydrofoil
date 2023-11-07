from collections import defaultdict

from rpython.tool.pairtype import pair

from pydrofoil import ir, parse, types

def emit_function_code(graph, functionast, codegen):
    CodeEmitter(graph, functionast, codegen).emit()

class CodeEmitter(object):
    def __init__(self, graph, functionast, codegen):
        self.graph = graph
        self.functionast = functionast
        self.codegen = codegen
        remove_critical_edges(graph)
        remove_phis(graph)

        # assign PCs
        blocks = list(graph.iterblocks())
        for i, block in enumerate(blocks):
            block._pc = i
        self.blocks = blocks

        self.entrymap = graph.make_entrymap()
        self.print_varnames = defaultdict(lambda : "i%s" % len(self.print_varnames))

    def emit(self):
        codegen = self.codegen
        if len(self.blocks) == 1:
            self.emit_block_ops(self.blocks[0])
            return
        codegen.emit("pc = 0")
        with codegen.emit_indent("while 1:"):
            for block in self.blocks:
                blockpc = block._pc
                #if block in emitted:
                    # inlined by emit_block_ops
                #    continue
                with codegen.emit_indent("if pc == %s:" % (blockpc, )):
                    self.emit_block_ops(block)

    def emit_block_ops(self, block):
        codegen = self.codegen
        for i, op in enumerate(block.operations):
            assert not isinstance(op, ir.Phi) # should have been removed
            getattr(self, "emit_op_" + op.__class__.__name__, self.emit_op_default)(op)
        getattr(self, "emit_next_" + block.next.__class__.__name__, self.emit_next_default)(block.next)
        # elif isinstance(op, parse.Goto):
        #     codegen.emit("pc = %s" % (op.target, ))
        #     if op.target < i:
        #         codegen.emit("continue")
        #     return
        # elif isinstance(op, parse.Arbitrary):
        #     codegen.emit("# arbitrary")
        #     codegen.emit("return %s" % (codegen.gettyp(self.name).restype.uninitialized_value, ))
        # else:
        #     codegen.emit("# %s" % (op, ))
        #     op.make_op_code(codegen)
        # handle_next

    # ________________________________________________
    # operations

    def _get_print_varname(self, op):
        if isinstance(op, ir.Argument):
            return op.name
        return self.print_varnames[op]

    def _get_arg(self, value):
        if isinstance(value, (ir.Phi, ir.Operation)):
            return self._get_print_varname(value)
        if isinstance(value, ir.Argument):
            return value.name
        if isinstance(value, ir.BooleanConstant):
            return str(value.value)
        if isinstance(value, ir.AstConstant):
            ast = value.ast
            if isinstance(ast, parse.BitVectorConstant):
                return "r_uint(%s)" % (ast.constant, )
            if isinstance(ast, parse.Number):
                return str(ast.number)
            if isinstance(ast, parse.String):
                return ast.string
            if isinstance(ast, parse.Unit):
                return "()"
        import pdb; pdb.set_trace()

    def _get_args(self, args):
        return ", ".join([self._get_arg(arg) for arg in args])

    def _op_helper(self, op, svalue):
        assert isinstance(svalue, str)
        res = self._get_print_varname(op)
        emit = "%s = %s" % (res, svalue)
        sourcepos = op.sourcepos
        if sourcepos:
            emit += " # " + sourcepos
        self.codegen.emit(emit)

    def emit_op_default(self, op):
        import pdb; pdb.set_trace()

    def emit_op_Operation(self, op):
        codegen = self.codegen
        name = op.name
        args = self._get_args(op.args)
        argtyps = [arg.resolved_type for arg in op.args]
        restyp = op.resolved_type
        if name in codegen.globalnames:
            n = codegen.globalnames[name].pyname
            if "eq_string" in name:
                name = "@eq"
            elif name == "znot_bool":
                name = "@not"
            elif n == "supportcode.eq_anything":
                name = "@eq"
        if name.startswith("@"):
            meth = getattr(op.args[0].resolved_type, "make_op_code_special_" + name[1:], None)
            if meth:
                res = meth(self.codegen, [self._get_arg(arg) for arg in op.args], argtyps, restyp)
                self._op_helper(op, res)
                return
        opname = codegen.getname(name)
        info = codegen.getinfo(name)
        if isinstance(info.typ, types.Function):
            # pass machine, even to supportcode functions
            res = "%s(machine, %s)" % (opname, args)
        elif isinstance(info.typ, types.Union):
            res = info.ast.constructor(info, opname, args, argtyps)
        else:
            res = "%s(%s)" % (opname, args)
        self._op_helper(op, res)

    def emit_op_NonSSAAssignment(self, op):
        arg0, arg1 = op.args
        res = self._get_print_varname(arg0)
        arg1 = self._get_arg(arg1)
        self.codegen.emit("%s = %s" % (res, arg1))

    def emit_op_GlobalRead(self, op):
        pyname= self.codegen.getname(op.name)
        self._op_helper(op, pyname)

    def emit_op_GlobalWrite(self, op):
        target = self.codegen.getinfo(op.name).write_pyname
        value = self._get_arg(op.args[0])
        self.codegen.emit("%s = %s" % (target, value))

    def emit_op_UnionVariantCheck(self, op):
        clsname = self.codegen.getname(op.name)
        self._op_helper(op, "not isinstance(%s, %s)" % (self._get_arg(op.args[0]), clsname))

    def emit_op_UnionCast(self, op):
        clsname = self.codegen.getname(op.name)
        self._op_helper(op, "%s.convert(%s)" % (clsname, self._get_arg(op.args[0])))

    def emit_op_StructConstruction(self, op):
        ast_type = op.resolved_type.ast
        args = ", ".join([self._get_arg(arg) for arg in op.args])
        self._op_helper(op, "%s(%s)" % (ast_type.pyname, args))

    def emit_op_Cast(self, op):
        fromtyp = op.args[0].resolved_type
        totyp = op.resolved_type
        arg = self._get_arg(op.args[0])
        self._op_helper(op, pair(fromtyp, totyp).convert(arg, self.codegen))

    def emit_op_FieldAccess(self, op):
        return self._op_helper(op, "%s.%s" % (self._get_arg(op.args[0]), op.name))

    def emit_op_FieldWrite(self, op):
        self.codegen.emit("%s.%s = %s" % (self._get_arg(op.args[0]), op.name, self._get_arg(op.args[1])))

    def emit_op_RefAssignment(self, op):
        # XXX think long and hard about refs!
        self.codegen.emit("%s.copy_into(%s)" % (self._get_arg(op.args[0]), self._get_arg(op.args[1])))

    def emit_op_Allocate(self, op):
        self._op_helper(op, op.resolved_type.uninitialized_value)

    def emit_op_DefaultValue(self, op):
        self._op_helper(op, op.resolved_type.uninitialized_value)

    def emit_op_RefOf(self, op):
        return self._op_helper(op, self._get_arg(op.args[0]))

    def emit_op_VectorInit(self, op):
        oftyp = op.resolved_type.typ
        self._op_helper(op,  "[%s] * %s" % (oftyp.uninitialized_value, self._get_arg(op.args[0])))

    def emit_op_VectorUpdate(self, op):
        oftyp = op.resolved_type.typ
        res = self._get_print_varname(op)
        args = self._get_args(op.args)
        # xxx feels wrong
        self._op_helper(op, "supportcode.vector_update_inplace(machine, %s, %s)" % (res, args))

    # ________________________________________________
    # jumps etc

    def _emit_next_helper(self, next, s):
        if next.sourcepos:
            s += " # " + next.sourcepos
        self.codegen.emit(s)

    def emit_next_Return(self, next):
        if next.value is not None:
            res = self._get_arg(next.value)
        else:
            res = '# no result'
        self._emit_next_helper(next, "return %s" % res)

    def emit_next_Raise(self, next):
        self._emit_next_helper(next, "assert 0, %r" % (next.kind, ))

    def emit_next_Goto(self, next):
        self._emit_next_helper(next, "pc = %s" % (next.target._pc, ))
        self.codegen.emit("continue")

    def emit_next_ConditionalGoto(self, next):
        res = self._get_arg(next.booleanvalue)
        self._emit_next_helper(next, "pc = %s if %s else %s" % (next.truetarget._pc, res, next.falsetarget._pc))
        self.codegen.emit("continue")

    def emit_next_Arbitrary(self, next):
        self._emit_next_helper(next, "break") # XXX not 100% sure that's correct

    def emit_next_default(self, next):
        import pdb; pdb.set_trace()

def remove_critical_edges(graph):
    entrymap = graph.make_entrymap()
    for block in list(graph.iterblocks()):
        next_blocks = block.next.next_blocks()
        if len(next_blocks) == 1:
            continue
        for next_block in next_blocks:
            # edge next->next_block is critical if next_block has more than one
            # predecessor
            if len(entrymap[next_block]) == 1:
                continue
            # insert a new empty block along the edge
            new_block = ir.Block([])
            new_block.next = ir.Goto(next_block)
            block.next.replace_next(next_block, new_block)
            next_block.replace_prev(block, new_block)
            
def remove_phis(graph):
    all_newops = defaultdict(list)
    allblocks = list(graph.iterblocks())
    for block in allblocks:
        for op in block.operations:
            if not isinstance(op, ir.Phi):
                continue
            for prevblock, prevvalue in zip(op.prevblocks, op.prevvalues):
                if op is not prevvalue: # x = x is unnecessary
                    all_newops[prevblock].append((op, prevvalue))
    if all_newops:
        for block, ops in all_newops.iteritems():
            assert not {target for target, _ in ops}.intersection({source for _, source in ops})
            for target, source in ops:
                block.operations.append(ir.NonSSAAssignment(target, source))
        for block in allblocks:
            block.operations[:] = [op for op in block.operations if not isinstance(op, ir.Phi)]

    
