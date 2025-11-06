from collections import defaultdict

from rpython.tool.pairtype import pair

from pydrofoil import ir, parse, types, supportcode


def emit_function_code(graph, functionast, codegen):
    CodeEmitter(graph, functionast, codegen).emit()


class CodeEmitter(object):
    def __init__(self, graph, functionast, codegen):
        self.graph = graph
        self.functionast = functionast
        self.codegen = codegen
        self.graph_construction_code = ir.print_graph_construction(
            self.graph, codegen
        )
        remove_critical_edges(graph)

        self.use_count_ops = count_uses(graph)
        remove_phis(graph)

        # assign PCs
        blocks = list(graph.iterblocks())
        for i, block in enumerate(blocks):
            block._pc = i
        self.blocks = blocks

        self.entrymap = graph.make_entrymap()
        self.emitted = set()
        self.print_varnames = {}
        self._single_use_ops = {}

    def emit(self):
        codegen = self.codegen
        try:
            codegen.emit(
                "# return type %s%s"
                % (
                    self.functionast.resolved_type.restype,
                    " has loop" if self.graph.has_loop else "",
                )
            )
        except AttributeError:
            pass
        for comment in self.graph_construction_code:
            codegen.emit("# " + comment)
        if len(self.blocks) == 1:
            self.emit_block_ops(self.blocks[0])
            return
        # first give out variable names
        for block in self.blocks:
            for index, op in enumerate(block.operations):
                unique_suffix = "_%s_%s" % (block._pc, index)
                self._get_print_varname(op, unique_suffix)
        codegen.emit("pc = 0")
        with codegen.emit_indent("while 1:"):
            for block in self.blocks:
                if block in self.emitted:
                    # inlined by emit_block_ops
                    continue
                blockpc = block._pc
                with codegen.emit_indent("if pc == %s:" % (blockpc,)):
                    self.emit_block_ops(block)

    def emit_block_ops(self, block):
        self.emitted.add(block)
        codegen = self.codegen
        for i, op in enumerate(block.operations):
            getattr(
                self, "emit_op_" + op.__class__.__name__, self.emit_op_default
            )(op)
        getattr(
            self,
            "emit_next_" + block.next.__class__.__name__,
            self.emit_next_default,
        )(block.next)

    # ________________________________________________
    # operations

    def _get_print_varname(self, op, unique_suffix=None):
        if isinstance(op, ir.Argument):
            return op.name
        if op in self.print_varnames:
            return self.print_varnames[op]
        name = getattr(op, "varname_hint", None) or "i"
        if unique_suffix is not None:
            varname = name + unique_suffix
        else:
            varname = "%s_%s" % (name, len(self.print_varnames))
        self.print_varnames[op] = varname
        return varname

    def _can_print_op_anywhere(self, op):
        if isinstance(op, ir.Cast):
            return True
        if isinstance(op, ir.RefOf):
            return True
        if isinstance(op, ir.UnpackPackedField):
            return True
        if isinstance(op, ir.PackPackedField):
            return True
        if op.name == "@not":
            return True
        return type(op) is ir.Operation and ir.builtin_is_pure(
            op.name, self.codegen
        )

    def _get_arg(self, value):
        if isinstance(value, (ir.Phi, ir.Operation)):
            varname = self._get_print_varname(value)
            if varname in self._single_use_ops:
                arg = self._single_use_ops[varname]
                assert arg is not None
                self._single_use_ops[varname] = None
                return arg
            return varname
        if isinstance(value, ir.Argument):
            return value.name
        if isinstance(value, ir.BooleanConstant):
            return str(value.value)
        if isinstance(value, ir.MachineIntConstant):
            return str(value.number)
        if isinstance(value, ir.IntConstant):
            s = str(value.number)
            name = "intconst%s" % s
            name = name.replace("-", "_minus_")
            with self.codegen.cached_declaration(s, name) as pyname:
                self.codegen.emit(
                    "%s = bitvector.Integer.fromlong(%s)" % (pyname, s)
                )
            return pyname
        if isinstance(value, ir.SmallBitVectorConstant):
            size = value.resolved_type.width
            val = value.value
            if size % 4 == 0:
                value = "0x" + hex(val)[2:].rjust(size // 4, "0")
            else:
                value = "0b" + bin(val)[2:].rjust(size, "0")
            return "r_uint(%s)" % (value,)
        if isinstance(value, ir.DefaultValue):
            return value.resolved_type.uninitialized_value
        if isinstance(value, ir.EnumConstant):
            pyname = self.codegen.getname(value.variant)
            return pyname
        if isinstance(value, ir.UnitConstant):
            return "()"
        if isinstance(value, ir.StringConstant):
            return repr(value.string)
        if isinstance(value, ir.GenericBitVectorConstant):
            name = "bitvectorconstant%s_%s" % (
                value.value.size(),
                value.value.tolong(),
            )
            constr = value._construction_expr()
            with self.codegen.cached_declaration(constr, name) as arg:
                self.codegen.emit("%s = %s" % (arg, constr))
            return arg
        import pdb

        pdb.set_trace()

    def _get_args(self, args):
        return ", ".join([self._get_arg(arg) for arg in args])

    def _op_helper(self, op, svalue):
        assert isinstance(svalue, str)
        use_count = self.use_count_ops[op]
        if use_count == 0:
            emit = svalue
        else:
            res = self._get_print_varname(op)
            if use_count == 1 and self._can_print_op_anywhere(op):
                self._single_use_ops[res] = svalue
                return
            emit = "%s = %s" % (res, svalue)
        sourcepos = op.sourcepos
        if sourcepos:
            emit += " # " + sourcepos
        self.codegen.emit(emit)

    def emit_op_default(self, op):
        import pdb

        pdb.set_trace()

    def emit_op_Operation(self, op):
        codegen = self.codegen
        name = op.name
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
            meth = getattr(
                op.args[0].resolved_type,
                "make_op_code_special_" + name[1:],
                None,
            )
            if meth:
                res = meth(
                    self.codegen,
                    [self._get_arg(arg) for arg in op.args],
                    argtyps,
                    restyp,
                )
                self._op_helper(op, res)
                return
        args = self._get_args(op.args)
        opname = codegen.getname(name)
        info = codegen.getinfo(name)
        if isinstance(info.typ, types.Function) or opname.startswith(
            "supportcode."
        ):
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
        pyname = self.codegen.getname(op.name)
        self._op_helper(op, pyname)

    def emit_op_GlobalWrite(self, op):
        target = self.codegen.getinfo(op.name).write_pyname
        value = self._get_arg(op.args[0])
        if "%" not in target:
            self.codegen.emit("%s = %s" % (target, value))
        else:
            self.codegen.emit(target % (value,))

    def emit_op_UnionVariantCheck(self, op):
        clsname = self.codegen.getname(op.name)
        self._op_helper(
            op,
            "not %s.check_variant(%s)" % (clsname, self._get_arg(op.args[0])),
        )

    def emit_op_UnionCast(self, op):
        clsname = self.codegen.getname(op.name)
        self._op_helper(
            op, "%s.convert(%s)" % (clsname, self._get_arg(op.args[0]))
        )

    def emit_op_StructConstruction(self, op):
        pyname = self.codegen.namedtypes[op.resolved_type.name].pyname
        args = ", ".join([self._get_arg(arg) for arg in op.args])
        self._op_helper(op, "%s(%s)" % (pyname, args))

    def emit_op_StructCopy(self, op):
        pyname = self.codegen.namedtypes[op.resolved_type.name].pyname
        self._op_helper(
            op, "%s.copy_into(machine)" % self._get_arg(op.args[0])
        )

    def emit_op_Cast(self, op):
        fromtyp = op.args[0].resolved_type
        totyp = op.resolved_type
        if (
            isinstance(fromtyp, types.SmallFixedBitVector)
            and totyp is types.GenericBitVector()
            and isinstance(op.args[0], ir.SmallBitVectorConstant)
        ):
            name = "bitvectorconstant%s" % op.args[0].value
            with self.codegen.cached_declaration(fromtyp, name) as arg:
                self.codegen.emit(
                    "%s = bitvector.from_ruint(%s, r_uint(%s))"
                    % (arg, fromtyp.width, op.args[0].value)
                )

        else:
            arg = self._get_arg(op.args[0])
            arg = pair(fromtyp, totyp).convert(arg, self.codegen)
        self._op_helper(op, arg)

    def emit_op_FieldAccess(self, op):
        read = op.resolved_type.packed_field_read(
            "%s.%s" % (self._get_arg(op.args[0]), op.name), bare=True
        )
        return self._op_helper(op, read)

    def emit_op_FieldWrite(self, op):
        lhs = "%s.%s" % (self._get_arg(op.args[0]), op.name)
        assert (
            op.args[0].resolved_type.internalfieldtyps[op.name]
            == op.args[1].resolved_type
        )
        write = op.args[1].resolved_type.packed_field_write(
            lhs, self._get_arg(op.args[1]), bare=True
        )
        self.codegen.emit(write)

    def emit_op_RefAssignment(self, op):
        self.codegen.emit(
            "%s.update_with(machine, %s)"
            % (self._get_arg(op.args[0]), self._get_arg(op.args[1]))
        )

    def emit_op_Allocate(self, op):
        pyname = self.codegen.namedtypes[op.resolved_type.name].pyname
        self._op_helper(op, "objectmodel.instantiate(%s)" % pyname)

    def emit_op_RefOf(self, op):
        regname = op.name
        register = self.codegen.all_registers[regname]
        pyname = register.make_register_ref(self.codegen)
        # name = "ref_%s" % (regname, )
        # with self.codegen.cached_declaration(regname, name) as pyname:
        #    with self.codegen.emit_indent("class %s(supportcode.RegRef):" % (pyname, )):
        #        with self.codegen.emit_indent("def deref(self, machine):"):
        #            self.codegen.emit("return machine.%s" % (register.pyname, ))
        #        if isinstance(op.resolved_type.typ, types.Struct):
        #            with self.codegen.emit_indent("def copy_into(self, machine, res=None):"):
        #                self.codegen.emit("return machine.%s.copy_into(machine, res)" % (register.pyname, ))
        #    self.codegen.emit("%s = %s() # singleton" % (pyname, pyname))
        return self._op_helper(op, pyname)

    def emit_op_VectorInit(self, op):
        oftyp = op.resolved_type.typ
        self._op_helper(
            op,
            "[%s] * %s"
            % (oftyp.uninitialized_value, self._get_arg(op.args[0])),
        )

    def emit_op_VectorUpdate(self, op):
        oftyp = op.resolved_type.typ
        res = self._get_print_varname(op)
        args = self._get_args(op.args)
        # is optimized away in the common case
        self._op_helper(
            op, "supportcode.vector_update_list(machine, %s)" % (args,)
        )

    def emit_op_Comment(self, op):
        self.codegen.emit("# %s" % (op.name,))

    def emit_op_Phi(self, op):
        pass

    def emit_op_UnpackPackedField(self, op):
        assert op.args[0].resolved_type.typ.packed_field_size > 1
        read = op.resolved_type.packed_field_unpack(self._get_arg(op.args[0]))
        return self._op_helper(op, read)

    def emit_op_PackPackedField(self, op):
        assert op.args[0].resolved_type.packed_field_size > 1
        read = op.args[0].resolved_type.packed_field_pack(
            self._get_arg(op.args[0])
        )
        return self._op_helper(op, read)

    def emit_op_RangeCheck(self, op):
        arg0 = self._get_arg(op.args[0])
        arg3 = self._get_arg(op.args[3])

        if op.args[0].resolved_type == types.Bool():
            low = op.args[1].number
            high = op.args[2].number
            if low == high:
                self.codegen.emit(
                    "if %s%s: raise supportcode.SailError(%s)"
                    % (
                        "not " if low else "",
                        arg0,
                        arg3,
                    )
                )
            return
        elif op.args[0].resolved_type == types.MachineInt():
            self.codegen.emit(
                "if not (%s <= %s <= %s): raise supportcode.SailError(%s)"
                % (
                    op.args[1].number,
                    arg0,
                    op.args[2].number,
                    arg3,
                )
            )
            return
        low_optional = op.args[1]
        high_optional = op.args[2]
        low_is_unit = isinstance(low_optional, ir.UnitConstant)
        high_is_unit = isinstance(high_optional, ir.UnitConstant)
        if low_is_unit and high_is_unit:
            return
        if op.args[0].resolved_type == types.Int():
            self.codegen.emit(
                "if not (%s%s%s): raise supportcode.SailError(%s)"
                % (
                    ""
                    if low_is_unit
                    else "%s.le(%s)" % (self._get_arg(low_optional), arg0),
                    "" if low_is_unit or high_is_unit else " and ",
                    ""
                    if high_is_unit
                    else "%s.le(%s)" % (arg0, self._get_arg(high_optional)),
                    arg3,
                )
            )
        elif op.args[0].resolved_type == types.Packed(types.Int()):
            self.codegen.emit(
                "if not (%s%s%s): raise supportcode.SailError(%s)"
                % (
                    ""
                    if low_is_unit
                    else "%s.le_packed(%s)"
                    % (self._get_arg(low_optional), arg0),
                    "" if low_is_unit or high_is_unit else " and ",
                    ""
                    if high_is_unit
                    else "%s.ge_packed(%s)"
                    % (self._get_arg(high_optional), arg0),
                    arg3,
                )
            )
        elif op.args[0].resolved_type == types.GenericBitVector():
            if op.args[2].number <= 64:
                self.codegen.emit(
                    (
                        "if not isinstance(%s, bitvector.SmallBitVector): "
                        "raise supportcode.SailError(%s)"
                    )
                    % (arg0, arg3)
                )
            assert not low_is_unit and not high_is_unit
            self.codegen.emit(
                (
                    "if not (%s <= %s.size() <= %s): "
                    "raise supportcode.SailError(%s)"
                )
                % (op.args[1].number, arg0, op.args[2].number, arg3)
            )
        elif op.args[0].resolved_type == types.Packed(
            types.GenericBitVector()
        ):
            if op.args[2].number <= 64:
                self.codegen.emit(
                    "if %s[2] is not None: raise supportcode.SailError(%s)"
                    % (arg0, arg3)
                )
            self.codegen.emit(
                "if not (%s <= %s[0] <= %s): raise supportcode.SailError(%s)"
                % (op.args[1].number, arg0, op.args[2].number, arg3)
            )
            pass
        else:
            assert 0, "unknown type in RangeCheck"

    # ________________________________________________
    # jumps etc

    def _emit_next_helper(self, next, s):
        if next is not None and next.sourcepos:
            s += " # " + next.sourcepos
        self.codegen.emit(s)

    def _emit_jump(self, block, next=None):
        if len(self.entrymap[block]) == 1:
            self._emit_next_helper(next, "# pc = %s, inlined" % (block._pc,))
            self.emit_block_ops(block)
        else:
            self._emit_next_helper(next, "pc = %s" % (block._pc,))
            self.codegen.emit("continue")

    def emit_next_Return(self, next):
        if next.value is not None:
            res = self._get_arg(next.value)
            self._emit_next_helper(next, "return %s" % res)
        else:
            # no result, unreachable
            res = "# no result"
            self._emit_next_helper(next, "assert 0, 'unreachable'")

    def emit_next_Raise(self, next):
        res = self._get_arg(next.kind)
        self._emit_next_helper(
            next, "raise supportcode.SailError(%s)" % (res,)
        )

    def emit_next_Goto(self, next):
        self._emit_jump(next.target, next)

    def emit_next_ConditionalGoto(self, next):
        res = self._get_arg(next.booleanvalue)
        self._emit_next_helper(next, "if %s:" % (res,))
        with self.codegen.emit_indent():
            self._emit_jump(next.truetarget)
        # the truetarget ends with a continue or similar, so we can just write
        # the code without an else
        self._emit_jump(next.falsetarget)

    def emit_next_JustStop(self, next):
        pass

    def emit_next_default(self, next):
        import pdb

        pdb.set_trace()


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
                if op is not prevvalue:  # x = x is unnecessary
                    all_newops[prevblock].append((op, prevvalue))
    if all_newops:
        for block, ops in all_newops.iteritems():
            assert not {target for target, _ in ops}.intersection(
                {source for _, source in ops}
            )
            for target, source in ops:
                block.operations.append(ir.NonSSAAssignment(target, source))


def count_uses(graph):
    uses = defaultdict(int)
    for block in graph.iterblocks():
        for op in block.operations:
            if op is None:
                continue
            for arg in op.getargs():
                uses[arg] += 1
        for arg in block.next.getargs():
            uses[arg] += 1
    return uses
