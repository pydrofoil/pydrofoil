from pydrofoil import parse, makecode, types, supportcode
from collections import defaultdict


# optimize operation ASTs before generating code


def identify_replacements(blocks, predefined=None):
    decls, defs, uses = find_decl_defs_uses(blocks, predefined)
    replacements = {}
    for var, varuses in uses.iteritems():
        if len(varuses) != 1:
            continue
        vardefs = defs[var]
        if len(vardefs) != 1:
            continue
        [(useblock, useindex)] = varuses
        [(defblock, defindex)] = vardefs
        if var not in decls:
            continue
        declblock, declindex = decls[var]
        if not (declblock is defblock is useblock):
            continue
        if defindex is None or useindex is None:
            continue
        defop = useblock[defindex]
        useop = useblock[useindex]
        if isinstance(defop, parse.Operation) and defop.name.startswith(("@", "$")):
            continue
        if any(len(defs[argvar]) != 1 for argvar in defop.find_used_vars()):
            continue
        replacements[var] = (useblock, declindex, defindex, useindex)
    return replacements


def do_replacements(replacements):
    repl_list = list(replacements.items())
    repl_list.sort(key=lambda element: (element[1][0], element[1][2]))
    for var, (block, declindex, defindex, useindex) in repl_list:
        declop = block[declindex]
        defop = block[defindex]
        useop = block[useindex]
        if isinstance(defop, parse.Operation):
            expr = parse.OperationExpr(
                defop.name, defop.args, defop.resolved_type, defop.sourcepos
            )
        else:
            assert isinstance(defop, parse.Assignment)
            assert defop.resolved_type
            expr = parse.CastExpr(defop.value, defop.resolved_type)
        block[useindex] = newop = useop.replace_var(var, expr)
        assert newop != useop
        if type(block[-1]) is not set:
            block.append({defindex, declindex})
        else:
            block[-1].add(declindex)
            block[-1].add(defindex)
    for _, (block, _, _, _) in repl_list:
        if type(block[-1]) is not set:
            continue
        newblock = []
        delete_index = block.pop()
        for i, op in enumerate(block):
            if i in delete_index:
                continue
            newblock.append(op)
        block[:] = newblock


def optimize_blocks(blocks, codegen, predefined=None):
    inline(blocks, codegen.inlinable_functions)
    do_replacements(identify_replacements(blocks, predefined))
    specialize_ops(blocks, codegen)


def find_decl_defs_uses(blocks, predefined=None):
    defs = defaultdict(list)
    uses = defaultdict(list)
    decls = {}
    if predefined:
        for var, typ in predefined.iteritems():
            decls[var] = (blocks[0], None)
            if var != "return_":
                defs[var].append((blocks[0], None))
    for _, block in sorted(blocks.items()):
        for i, op in enumerate(block):
            used_vars = op.find_used_vars()
            for var in used_vars:
                uses[var].append((block, i))
            if isinstance(op, (parse.Assignment, parse.Operation)):
                defs[op.result].append((block, i))
            elif isinstance(op, parse.LocalVarDeclaration):
                assert op.name not in decls
                decls[op.name] = (block, i)
    return decls, defs, uses


def inline(blocks, inlinable_functions):
    for num, block in blocks.iteritems():
        index = 0
        while index < len(block):
            op = block[index]
            if isinstance(op, parse.Operation) and op.name in inlinable_functions:
                functionast, targetblocks = inlinable_functions[op.name]
                newops = copy_ops(op, functionast, targetblocks)
                if newops is not None:
                    block[index : index + 1] = newops
                    index = 0
                    continue
            index += 1


def copy_ops(op, functionast, targetblocks):
    assert len(targetblocks) == 1
    block = targetblocks[0]
    if len(block) != 2:
        return None
    targetop, endop = block
    if not isinstance(endop, parse.End):
        return
    if not isinstance(targetop, parse.Assignment) or targetop.result != "return":
        return None
    expr = targetop.value
    for argname, argexpr in zip(functionast.args, op.args):
        expr = expr.replace_var(argname, argexpr)
    return [parse.Assignment(op.result, expr, op.sourcepos, op.resolved_type)]


def specialize_ops(blocks, codegen):
    v = OptVisitor(codegen)
    for num, block in blocks.iteritems():
        for i, op in enumerate(block):
            while 1:
                v.changed = False
                res = op.mutate_with(v)
                if res is not None:
                    block[i] = op = res
                elif not v.changed:
                    break


class NoMatchException(Exception):
    pass


class CollectSourceVisitor(parse.Visitor):
    def __init__(self):
        self.seen = set()

    def default_visit(self, ast):
        sourcepos = getattr(ast, "sourcepos", None)
        sourcepos = self._parse(sourcepos)
        if sourcepos:
            self.seen.add(sourcepos)
        for key, value in ast.__dict__.items():
            if isinstance(value, parse.BaseAst):
                self.visit(value)
            elif (
                isinstance(value, list)
                and value
                and isinstance(value[0], parse.BaseAst)
            ):
                for i, item in enumerate(value):
                    self.visit(item)

    def _parse(self, sourcepos):
        if sourcepos is None:
            return None
        sourcepos = sourcepos.lstrip("`")
        l = sourcepos.split(" ", 1)
        if len(l) == 1:
            return None
        filenum, rest = l
        from_, to = rest.split("-", 1)
        fromline, frompos = from_.split(":", 1)
        toline, topos = to.split(":", 1)
        return int(filenum), int(fromline), int(frompos), int(toline), int(topos)


class OptVisitor(parse.Visitor):
    def __init__(self, codegen):
        self.codegen = codegen

    def visit_CastExpr(self, cast):
        if isinstance(cast.expr, parse.CastExpr):
            return parse.CastExpr(cast.expr.expr, cast.resolved_type)
        if (
            isinstance(cast.expr, parse.OperationExpr)
            and cast.expr.resolved_type is cast.resolved_type
        ):
            return cast.expr

    def _builtinname(self, name):
        return self.codegen.builtin_names.get(name, name)

    def visit_OperationExpr(self, expr):
        assert expr.resolved_type is not None
        name = self._builtinname(expr.name)
        if name in supportcode.all_unwraps:
            specs, unwrapped_name = supportcode.all_unwraps[name]
            # these are unconditional unwraps, just rewrite them right here
            assert len(specs) == len(expr.args)
            newargs = []
            for argspec, arg in zip(specs, expr.args):
                if argspec == "o":
                    newargs.append(arg)
                elif argspec == "i":
                    newargs.append(self._convert_to_machineint(arg))
                else:
                    assert 0, "unknown spec"
            return parse.OperationExpr(
                "@" + unwrapped_name,
                newargs,
                expr.resolved_type,
                expr.sourcepos,
            )
        meth = getattr(self, "optimize_%s" % name.lstrip("@"), None)
        if not meth:
            return None
        try:
            return meth(expr)
        except NoMatchException:
            return None

    def _convert_to_machineint(self, arg):
        try:
            return self._extract_machineint(arg)
        except NoMatchException:
            # call int_to_int64
            return parse.OperationExpr("zz5izDzKz5i64", [arg], types.MachineInt())

    def visit_Operation(self, operation):
        assert operation.resolved_type is not None
        if operation.name == "$zinternal_vector_update":
            return
        expr = parse.OperationExpr(
            operation.name,
            operation.args,
            operation.resolved_type,
            operation.sourcepos,
        )
        return parse.Assignment(
            operation.result,
            expr,
            operation.sourcepos,
            operation.resolved_type,
        )

    def visit_Assignment(self, expr):
        while isinstance(expr.value, parse.CastExpr):
            expr.value = expr.value.expr

    def visit_FieldAccess(self, expr):
        if not isinstance(expr.obj, parse.StructConstruction):
            return
        index = expr.obj.fieldnames.index(expr.element)
        return expr.obj.fieldvalues[index]

    # def visit_StructElementAssignment(self, assign):
    #    if assign.resolved_type != assign.value.resolved_type:
    #        value = parse.CastExpr(assign.value, assign.resolved_type)
    #        return parse.StructElementAssignment(assign.obj, assign.fields, value, assign.resolved_type, assign.sourcepos)

    def visit_GeneralAssignment(self, assign):
        lhs = assign.lhs
        rhs = assign.rhs
        if isinstance(rhs, parse.Operation):
            value = parse.OperationExpr(rhs.name, rhs.args, rhs.resolved_type)
        else:
            return None
        if isinstance(lhs, parse.StructElementAssignment):
            return parse.StructElementAssignment(
                lhs.obj, lhs.fields, value, lhs.resolved_type, assign.sourcepos
            )

    def _gettyp(self, expr):
        assert expr.resolved_type is not None
        return expr.resolved_type

    def _extract_smallfixedbitvector(self, arg):
        if not isinstance(arg, parse.CastExpr):
            raise NoMatchException
        typ = self._gettyp(arg.expr)
        if not isinstance(typ, types.SmallFixedBitVector):
            assert typ is types.GenericBitVector() or isinstance(
                typ, types.BigFixedBitVector
            )
            raise NoMatchException
        arg = arg.expr
        return arg, typ

    def _extract_machineint(self, arg):
        if arg.resolved_type is types.MachineInt():
            return arg
        if (
            not isinstance(arg, parse.OperationExpr)
            or self._builtinname(arg.name) != "int64_to_int"
        ):
            raise NoMatchException
        return arg.args[0]

    def _extract_number(self, arg):
        if isinstance(arg, parse.Number):
            return arg
        num = self._extract_machineint(arg)
        if not isinstance(num, parse.Number):
            raise NoMatchException
        return num

    def optimize_vector_subrange_o_i_i(self, expr):
        arg0, arg1, arg2 = expr.args
        assert expr.resolved_type is types.GenericBitVector()
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)

        arg1 = self._extract_number(arg1)
        arg2 = self._extract_number(arg2)
        width = arg1.number - arg2.number + 1
        if width > 64:
            return

        res = parse.CastExpr(
            parse.OperationExpr(
                "@slice_fixed_bv_i_i",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(width),
                expr.sourcepos,
            ),
            expr.resolved_type,
        )
        return res

    def optimize_vector_access_o_i(self, expr):
        arg0, arg1 = expr.args
        if isinstance(arg0.resolved_type, types.Vec):
            return
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self._extract_machineint(arg1)
        return parse.OperationExpr(
            "@vector_access_bv_i",
            [arg0, arg1],
            expr.resolved_type,
            expr.sourcepos,
        )

    def optimize_eq_bits(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        if typ0 is not typ1:
            return
        res = parse.OperationExpr(
            "@eq_bits_bv_bv", [arg0, arg1], expr.resolved_type, expr.sourcepos
        )
        return res

    def optimize_neq_bits(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        if typ0 is not typ1:
            return
        res = parse.OperationExpr(
            "@neq_bits_bv_bv", [arg0, arg1], expr.resolved_type, expr.sourcepos
        )
        return res

    def optimize_append(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        reswidth = typ0.width + typ1.width
        if reswidth > 64:
            return
        res = parse.CastExpr(
            parse.OperationExpr(
                "@bitvector_concat_bv_bv",
                [arg0, parse.Number(typ1.width), arg1],
                types.SmallFixedBitVector(reswidth),
                expr.sourcepos,
            ),
            expr.resolved_type,
        )
        return res

    def optimize_eq_int(self, expr):
        arg0, arg1 = expr.args
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return parse.OperationExpr(
            "@eq_int_i_i", [arg0, arg1], expr.resolved_type, expr.sourcepos
        )

    def optimize_int64_to_int(self, expr):
        (arg0,) = expr.args
        if (
            not isinstance(arg0, parse.OperationExpr)
            or self._builtinname(arg0.name) != "int_to_int64"
        ):
            return
        return arg0.args[0]

    def optimize_int_to_int64(self, expr):
        (arg0,) = expr.args

        if not isinstance(arg0, parse.OperationExpr):
            return
        if self._builtinname(arg0.name) == "int64_to_int":
            return arg0.args[0]
        if arg0.name == "@unsigned_bv_wrapped_res":
            return parse.OperationExpr(
                "@unsigned_bv", arg0.args, expr.resolved_type, expr.sourcepos
            )
        return None

    def optimize_xor_bits(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        if typ0 is not typ1:
            return
        return parse.CastExpr(
            parse.OperationExpr(
                "@xor_vec_bv_bv",
                [arg0, arg1],
                typ0,
                expr.sourcepos,
            ),
            expr.resolved_type,
        )

    def optimize_and_bits(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        if typ0 is not typ1:
            return
        return parse.CastExpr(
            parse.OperationExpr(
                "@and_vec_bv_bv",
                [arg0, arg1],
                typ0,
                expr.sourcepos,
            ),
            expr.resolved_type,
        )

    def optimize_or_bits(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        if typ0 is not typ1:
            return
        return parse.CastExpr(
            parse.OperationExpr("@or_vec_bv_bv", [arg0, arg1], typ0, expr.sourcepos),
            expr.resolved_type,
        )

    def optimize_not_bits(self, expr):
        (arg0,) = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)

        return parse.CastExpr(
            parse.OperationExpr(
                "@not_vec_bv", [arg0, parse.Number(typ0.width)], typ0, expr.sourcepos
            ),
            expr.resolved_type,
        )

    def optimize_add_bits(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        if typ0 is not typ1:
            return
        return parse.CastExpr(
            parse.OperationExpr(
                "@add_bits_bv_bv",
                [arg0, arg1, parse.Number(typ0.width)],
                typ0,
                expr.sourcepos,
            ),
            expr.resolved_type,
        )

    def optimize_sub_bits(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1, typ1 = self._extract_smallfixedbitvector(arg1)
        if typ0 is not typ1:
            return
        return parse.CastExpr(
            parse.OperationExpr(
                "@sub_bits_bv_bv",
                [arg0, arg1, parse.Number(typ0.width)],
                typ0,
                expr.sourcepos,
            ),
            expr.resolved_type,
        )

    def optimize_sail_signed(self, expr):
        (arg0,) = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        return parse.CastExpr(
            parse.OperationExpr(
                "@signed_bv",
                [arg0, parse.Number(typ0.width)],
                types.MachineInt(),
                expr.sourcepos,
            ),
            expr.resolved_type,
        )

    def optimize_sail_unsigned(self, expr):
        (arg0,) = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        return parse.OperationExpr(
            "@unsigned_bv_wrapped_res",
            [arg0, parse.Number(typ0.width)],
            expr.resolved_type,
            expr.sourcepos,
        )

    def optimize_zero_extend_o_i(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self._extract_number(arg1)
        if arg1.number > 64:
            return
        return parse.CastExpr(
            parse.OperationExpr(
                "@zero_extend_bv_i_i",
                [arg0, parse.Number(typ0.width), arg1],
                types.SmallFixedBitVector(arg1.number),
                expr.sourcepos,
            ),
            expr.resolved_type,
        )

    def optimize_add_int(self, expr):
        arg0, arg1 = expr.args
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return parse.OperationExpr(
            "@add_i_i_wrapped_res",
            [arg0, arg1],
            expr.resolved_type,
            expr.sourcepos,
        )

    def optimize_sub_int(self, expr):
        arg0, arg1 = expr.args
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return parse.OperationExpr(
            "@sub_i_i_wrapped_res",
            [arg0, arg1],
            expr.resolved_type,
            expr.sourcepos,
        )

    def optimize_add_bits_int(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        arg1 = self._extract_machineint(arg1)

        return parse.CastExpr(
            parse.OperationExpr(
                "@add_bits_int_bv_i",
                [arg0, parse.Number(typ0.width), arg1],
                typ0,
                expr.sourcepos,
            ),
            expr.resolved_type,
        )

    def optimize_shiftl_o_i(self, expr):
        arg0, arg1 = expr.args
        arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        assert arg1.resolved_type is types.MachineInt()

        return parse.CastExpr(
            parse.OperationExpr(
                "@shiftl_bv_i",
                [arg0, parse.Number(typ0.width), arg1],
                typ0,
                expr.sourcepos,
            ),
            expr.resolved_type,
        )
