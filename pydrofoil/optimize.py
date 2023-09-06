from pydrofoil import parse, makecode, types, supportcode
from collections import defaultdict


# optimize operation ASTs before generating code

def move_regs_into_locals(blocks, registers):
    """ Registers cannot easily be put back into more complicated
    OperationExprs, because the place they are read must not change (they are
    mutable). This often prevents optimization of bitvector/integer operations.
    Therefore we insert a new local variable that stores the correct register
    value, without a cast. Then the operations that operate on that register
    value (with a cast) can use the local variable, and the optimizations are
    possible. """
    if registers is None:
        return
    decls, defs, uses = find_decl_defs_uses(blocks)
    replacements = []
    for var, varuses in uses.iteritems():
        if var in decls or var not in registers:
            continue
        for useblock, useindex in varuses:
            op = useblock[useindex]
            if not isinstance(op, parse.Assignment) or not isinstance(op.value, parse.Var):
                continue
            assert op.value.name == var
            if op.resolved_type == op.value.resolved_type:
                continue
            declblock, declindex = decls[op.result]
            if useblock is not declblock:
                continue
            if useindex != declindex + 1:
                continue
            replacements.append((var, useblock, declindex))
    if not replacements:
        return
    for index, (var, useblock, declindex) in enumerate(replacements):
        declop = useblock[declindex]
        useop = useblock[declindex + 1]
        name = "local_reg_%s_%s" % (index, var)
        newdeclop = parse.LocalVarDeclaration(name, registers[var].typ, None)
        assert useop.value.resolved_type is not None
        newassignment = parse.Assignment(name, useop.value, resolved_type=useop.value.resolved_type)
        useop.value = parse.CastExpr(parse.Var(name, useop.value.resolved_type), useop.resolved_type)
        ops = [newdeclop, newassignment, declop]
        useblock[declindex] = ops

    # flatten
    for blockpc, block in blocks.iteritems():
        newcontent = []
        for op in block:
            if isinstance(op, list):
                newcontent.extend(op)
            else:
                newcontent.append(op)
        block[:] = newcontent

def identify_replacements(blocks, predefined=None, registers=None):
    if registers is None:
        registers = {}
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
        if any(len(defs[argvar]) != 1 or argvar in registers for argvar in defop.find_used_vars()):
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


def optimize_blocks(blocks, codegen, predefined=None, register_names=None):
    inline(blocks, codegen.inlinable_functions)
    move_regs_into_locals(blocks, register_names)
    do_replacements(identify_replacements(blocks, predefined))
    specialize_ops(blocks, codegen)
    optimize_gotos(blocks)


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

    def _make_int64_to_int(self, expr, sourcepos=None):
        return parse.OperationExpr(
            "zz5i64zDzKz5i", # int64_to_int
            [expr],
            types.Int(),
            sourcepos,
        )

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

    def visit_StructElementAssignment(self, assign):
       if assign.resolved_type != assign.value.resolved_type:
           value = parse.CastExpr(assign.value, assign.resolved_type)
           return parse.StructElementAssignment(assign.obj, assign.fields, value, assign.resolved_type, assign.sourcepos)

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
        assert isinstance(lhs, parse.RefAssignment)
        return parse.RefAssignment(lhs.ref, value, lhs.resolved_type, assign.sourcepos)

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

        arg1 = self._extract_number(arg1)
        arg2 = self._extract_number(arg2)
        width = arg1.number - arg2.number + 1
        if width > 64:
            return

        assert expr.resolved_type is types.GenericBitVector()
        try:
            arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        except NoMatchException:
            res = parse.OperationExpr(
                "@vector_subrange_o_i_i_unwrapped_res",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(width),
                expr.sourcepos,
            )
        else:
            res = parse.OperationExpr(
                "@vector_subrange_fixed_bv_i_i",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(width),
                expr.sourcepos,
            )
        return parse.CastExpr(
            res,
            expr.resolved_type,
        )

    def optimize_slice_o_i_i(self, expr):
        arg0, arg1, arg2 = expr.args
        arg1 = self._extract_machineint(arg1)
        arg2 = self._extract_number(arg2)
        length = arg2.number
        if length > 64:
            return

        try:
            assert expr.resolved_type is types.GenericBitVector()
            arg0, typ0 = self._extract_smallfixedbitvector(arg0)
        except NoMatchException:
            res = parse.OperationExpr(
                "@vector_slice_o_i_i_unwrapped_res",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(length),
                expr.sourcepos,
            )
        else:
            res = parse.OperationExpr(
                "@slice_fixed_bv_i_i",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(length),
                expr.sourcepos,
            )

        return parse.CastExpr(
            res,
            expr.resolved_type,
        )

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

    def optimize_zeros_i(self, expr):
        arg0, = expr.args
        arg0 = self._extract_number(arg0)
        if arg0.number > 64:
            return
        resconst = parse.BitVectorConstant("0b" + "0" * arg0.number, types.SmallFixedBitVector(arg0.number))
        res = parse.CastExpr(
            resconst,
            expr.resolved_type,
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
        width_as_num = parse.Number(typ0.width)
        if typ0.width < 64:
            # will always fit into a machine signed int
            res = parse.OperationExpr(
                "@unsigned_bv",
                [arg0, width_as_num],
                types.MachineInt(),
                expr.sourcepos,
            )
            return self._make_int64_to_int(res, expr.sourcepos)
        return parse.OperationExpr(
            "@unsigned_bv_wrapped_res",
            [arg0, width_as_num],
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
        try:
            arg0 = self._extract_number(arg0)
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            # can const-fold
            res = arg0.number + arg1.number
            if isinstance(res, int): # no overflow
                return self._make_int64_to_int(parse.Number(res), expr.sourcepos)
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return parse.OperationExpr(
            "@add_i_i_wrapped_res",
            [arg0, arg1],
            expr.resolved_type,
            expr.sourcepos,
        )

    def optimize_add_i_i_wrapped_res(self, expr):
        arg0, arg1 = expr.args
        arg0 = self._extract_number(arg0)
        arg1 = self._extract_number(arg1)
        # can const-fold
        res = arg0.number + arg1.number
        if isinstance(res, int): # no overflow
            return self._make_int64_to_int(parse.Number(res), expr.sourcepos)

    def optimize_sub_int(self, expr):
        arg0, arg1 = expr.args
        try:
            arg0 = self._extract_number(arg0)
            arg1 = self._extract_number(arg1)
        except NoMatchException:
            pass
        else:
            # can const-fold
            res = arg0.number - arg1.number
            if isinstance(res, int): # no overflow
                return self._make_int64_to_int(parse.Number(res), expr.sourcepos)
        arg0 = self._extract_machineint(arg0)
        arg1 = self._extract_machineint(arg1)
        return parse.OperationExpr(
            "@sub_i_i_wrapped_res",
            [arg0, arg1],
            expr.resolved_type,
            expr.sourcepos,
        )

    def optimize_sub_i_i_wrapped_res(self, expr):
        arg0, arg1 = expr.args
        arg0 = self._extract_number(arg0)
        arg1 = self._extract_number(arg1)
        # can const-fold
        res = arg0.number - arg1.number
        if isinstance(res, int): # no overflow
            return self._make_int64_to_int(parse.Number(res), expr.sourcepos)

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

    def optimize_length(self, expr):
        arg0, = expr.args
        res = parse.OperationExpr(
                "@length_unwrapped_res",
                [arg0],
                types.MachineInt(),
                expr.sourcepos,
        )
        if isinstance(arg0, parse.CastExpr):
            realtyp = arg0.expr.resolved_type
            if isinstance(realtyp, (types.SmallFixedBitVector, types.BigFixedBitVector)):
                res = parse.Number(realtyp.width)
        return self._make_int64_to_int(res, expr.sourcepos)

    def optimize_undefined_bitvector_i(self, expr):
        arg0, = expr.args
        num = self._extract_number(arg0)
        if num.number > 64:
            return
        return parse.CastExpr(
            parse.BitVectorConstant("0b" + "0" * num.number, types.SmallFixedBitVector(num.number)),
            expr.resolved_type,
            expr.sourcepos,
        )


# optimize_gotos


def collect_jump_to_jump(blocks):
    res = {}
    for num, block in blocks.iteritems():
        if num == 0 or len(block) > 1:
            continue
        (op,) = block
        if not isinstance(op, parse.Goto):
            continue
        res[num] = op.target
    for source, target in res.iteritems():
        while target in res:
            target = res[source] = res[target]
    return res


def optimize_gotos(blocks):
    jumps = collect_jump_to_jump(blocks)
    if not jumps:
        return
    for num, block in blocks.iteritems():
        for op in block:
            if not hasattr(op, "target"):
                continue
            if op.target in jumps:
                op.target = jumps[op.target]
    for useless in jumps:
        del blocks[useless]


def _get_successors(block):
    result = set()
    for op in block:
        if not hasattr(op, "target"):
            continue
        result.add(op.target)
    return result


def compute_predecessors(G):
    result = defaultdict(set)
    for num, succs in G.iteritems():
        for succ in succs:
            result[succ].add(num)
        result[num].add(num)
    return result


def _compute_dominators(G, start=0):
    preds = compute_predecessors(G)
    # initialize
    dominators = {}
    for node in G:
        dominators[node] = set(G)
    dominators[start] = {start}

    # fixpoint
    changed = True
    while changed:
        changed = False
        for node in G:
            if node == start:
                continue
            dom = set(G).intersection(*[dominators[x] for x in preds[node]])
            dom.add(node)
            if dom != dominators[node]:
                changed = True
                dominators[node] = dom
    return dominators


def immediate_dominators(G, start=0):
    if start not in G:
        return {}
    res = {}
    dominators = _compute_dominators(G, start)
    for node in G:
        if node == start:
            continue
        doms = dominators[node]
        for candidate in doms:
            if candidate == node:
                continue
            for otherdom in doms:
                if otherdom == node or otherdom == candidate:
                    continue
                if candidate in dominators[otherdom]:
                    break
            else:
                break
        res[node] = candidate
    return res

def _extract_graph(blocks):
    return {num: _get_successors(block) for (num, block) in blocks.iteritems()}

def immediate_dominators_blocks(blocks):
    G = _extract_graph(blocks)
    return immediate_dominators(G)

def bfs_graph(G, start=0):
    from collections import deque
    todo = deque([start])
    seen = set()
    res = []
    while todo:
        node = todo.popleft()
        if node in seen:
            continue
        seen.add(node)
        todo.extend(G[node])
        res.append(node)
    return res

def bfs_edges(G, start=0):
    from collections import deque
    todo = deque([start])
    seen = set()
    res = []
    while todo:
        node = todo.popleft()
        if node in seen:
            continue
        seen.add(node)
        todo.extend(G[node])
        for succ in G[node]:
            res.append((node, succ))
    return res

def view_blocks(blocks):
    from rpython.translator.tool.make_dot import DotGen
    from dotviewer import graphclient
    import pytest
    dotgen = DotGen('G')
    G = {num: _get_successors(block) for (num, block) in blocks.iteritems()}
    idom = immediate_dominators(G)
    for num, block in blocks.iteritems():
        label = [str(num)] + [str(op)[:100] for op in block]
        dotgen.emit_node(str(num), label="\n".join(label), shape="box")

    for start, succs in G.iteritems():
        for finish in succs:
            color = "green"
            dotgen.emit_edge(str(start), str(finish), color=color)
    for finish, start in idom.iteritems():
        color = "red"
        dotgen.emit_edge(str(start), str(finish), color=color)

    p = pytest.ensuretemp("pyparser").join("temp.dot")
    p.write(dotgen.generate(target=None))
    graphclient.display_dot_file(str(p))


# graph splitting

class CantSplitError(Exception):
    pass

def split_graph(blocks, min_size=6, start_node=0):
    G = _extract_graph(blocks)
    return_blocks = {num for (num, block) in blocks.iteritems() if isinstance(block[-1], parse.End)}
    end_blocks = {num for (num, block) in blocks.iteritems() if isinstance(block[-1], parse.FunctionEndingStatement)}
    return_edges = [(source, target) for (source, target) in bfs_edges(G, start_node) if target in return_blocks]
    return_edges.reverse()
    # split graph, starting from exit edges (ie an edge going to a block
    # ending with End)
    graph1 = {}
    last_working_graph1 = None
    while 1:
        # approach: from the edge going to the 'End' node, extend by adding
        # predecessors up to fixpoint
        source, target = return_edges.pop()
        preds = compute_predecessors(G)
        graph1[target] = blocks[target]
        todo = [source]
        while todo:
            node = todo.pop()
            if node in graph1:
                continue
            graph1[node] = blocks[node]
            todo.extend(preds[node])
        # add all end nodes that are reachable from the nodes in graph1.
        # also compute nodes where we need to transfer from graph1 to graph2
        transfer_nodes = set()
        for node in list(graph1):
            for succ in G[node]:
                if succ in graph1:
                    continue
                if succ in end_blocks:
                    graph1[succ] = blocks[succ]
                else:
                    transfer_nodes.add(succ)
        # try to remove some transfer nodes, if they are themselves only a
        # single block away from an end_blocks (happens with exceptions)
        for node in list(transfer_nodes):
            if len(G[node]) > 1:
                continue
            succ, = G[node]
            if succ not in end_blocks:
                continue
            graph1[node] = blocks[node]
            graph1[succ] = blocks[succ]
            transfer_nodes.remove(node)

        # if we only have a single transfer_node left, we have a potential
        # split
        if len(transfer_nodes) == 1:
            last_working_graph1 = graph1.copy()
            last_transfer_nodes = transfer_nodes.copy()
            if len(graph1) > min_size:
                break
        if len(graph1) == len(blocks) or not return_edges:
            # didn't manage to split
            if last_working_graph1:
                print "going back to earlier result, size", len(last_working_graph1)
                graph1 = last_working_graph1
                transfer_nodes = last_transfer_nodes
                break
            raise CantSplitError
    # compute graph2
    graph2 = {}
    for node in G:
        if node not in graph1:
            graph2[node] = blocks[node]
    # add reachable end nodes
    for node in list(graph2):
        for succ in G[node]:
            if succ in end_blocks:
                graph2[succ] = blocks[succ]
    # consistency check:
    for num, block in blocks.iteritems():
        assert num in graph1 or num in graph2
        if num in graph1 and num in graph2:
            assert num in end_blocks
    transferpc, = transfer_nodes
    assert transferpc not in graph1
    assert transferpc in graph2
    return graph1, graph2, transferpc
