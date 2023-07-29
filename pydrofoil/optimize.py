from pydrofoil import parse, makecode, types
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
            expr = parse.OperationExpr(defop.name, defop.args, defop.resolved_type)
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
    do_replacements(identify_replacements(blocks, predefined))
    specialize_ops(blocks, codegen, predefined)


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


def specialize_ops(blocks, codegen, predefined=None):
    if predefined is None:
        predefined = {}
    localtypes = predefined.copy()
    # find local var types
    for num, block in blocks.iteritems():
        for op in block:
            if isinstance(op, parse.LocalVarDeclaration):
                localtypes[op.name] = op.typ
    v = OptVisitor(localtypes, "zz5i64zDzKz5i")
    for num, block in blocks.iteritems():
        for i, op in enumerate(block):
            while 1:
                v.changed = False
                res = op.mutate_with(v)
                if res is not None:
                    block[i] = op = res
                elif not v.changed:
                    break


class OptVisitor(parse.Visitor):
    def __init__(self, localtypes, int64_to_int_name):
        self.localtypes = localtypes
        self.int64_to_int_name = int64_to_int_name

    def visit_CastExpr(self, cast):
        if isinstance(cast.expr, parse.CastExpr):
            return parse.CastExpr(cast.expr.expr, cast.typ)
        if isinstance(cast.expr, parse.OperationExpr) and cast.expr.typ == cast.typ:
            return cast.expr

    def visit_OperationExpr(self, expr):
        if expr.resolved_type is None:
            import pdb; pdb.set_trace()
            return None
        meth = getattr(self, "optimize_%s" % expr.name, None)
        if not meth:
            return None
        return meth(expr)

    def visit_Operation(self, operation):
        if operation.resolved_type is None:
            return
        if operation.name == "$zinternal_vector_update":
            return
        expr = parse.OperationExpr(operation.name, operation.args, operation.resolved_type)
        return parse.Assignment(
            operation.result, expr, operation.sourcepos
        )

    def visit_Assignment(self, expr):
        while isinstance(expr.value, parse.CastExpr):
            expr.value = expr.value.expr

    def visit_FieldAccess(self, expr):
        if not isinstance(expr.obj, parse.StructConstruction):
            return
        index = expr.obj.fieldnames.index(expr.element)
        return expr.obj.fieldvalues[index]

    def _gettyp(self, expr):
        if expr.resolved_type is None:
            import pdb; pdb.set_trace()
        return expr.resolved_type

    def optimize_zsubrange_bits(self, expr):
        arg0, arg1, arg2 = expr.args
        assert expr.typ.name == "%bv"

        if not isinstance(arg0, parse.CastExpr):
            return
        assert arg0.typ.name == "%bv"
        arg0 = arg0.expr
        typ = self._gettyp(arg0)
        if not isinstance(typ, types.SmallFixedBitVector):
            return

        if (
            not isinstance(arg1, parse.OperationExpr)
            or arg1.name != self.int64_to_int_name
        ):
            return
        if (
            not isinstance(arg2, parse.OperationExpr)
            or arg2.name != self.int64_to_int_name
        ):
            return
        (arg1,) = arg1.args
        if not isinstance(arg1, parse.Number):
            return
        (arg2,) = arg2.args
        if not isinstance(arg2, parse.Number):
            return
        width = arg1.number - arg2.number + 1

        res = parse.CastExpr(
            parse.OperationExpr(
                "@slice_fixed_bv_i_i",
                [arg0, arg1, arg2],
                types.SmallFixedBitVector(width),
            ),
            expr.resolved_type,
        )
        return res

    def optimize_zupdate_subrange_bits(self, expr):
        arg0, arg1, arg2, arg3 = expr.args
        if (
            not isinstance(arg1, parse.OperationExpr)
            or arg1.name != self.int64_to_int_name
        ):
            return
        if (
            not isinstance(arg2, parse.OperationExpr)
            or arg2.name != self.int64_to_int_name
        ):
            return
        (arg1,) = arg1.args
        if not isinstance(arg1, parse.Number):
            return
        (arg2,) = arg2.args
        if not isinstance(arg2, parse.Number):
            return
        width = arg1.number - arg2.number + 1
        return parse.OperationExpr(
            "@vector_update_subrange_o_i_i_o", [arg0, arg1, arg2, arg3], expr.resolved_type,
        )

    def optimize_zbitvector_access(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        if not isinstance(typ0, types.SmallFixedBitVector):
            return
        if (
            not isinstance(arg1, parse.OperationExpr)
            or arg1.name != self.int64_to_int_name
        ):
            return

        (arg1,) = arg1.args
        if not isinstance(arg1, parse.Number):
            return
        return parse.OperationExpr("@vector_access_bv_i", [arg0.expr, arg1], expr.resolved_type)

    def optimize_zeq_bits(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        if not isinstance(arg1, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        typ1 = self._gettyp(arg1.expr)
        if typ0 != typ1 or not isinstance(typ0, types.SmallFixedBitVector):
            return
        res = parse.OperationExpr("@eq_bits_bv_bv", [arg0.expr, arg1.expr], expr.resolved_type)
        return res

    def optimize_zneq_bits(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        if not isinstance(arg1, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        typ1 = self._gettyp(arg1.expr)
        if typ0 != typ1 or not isinstance(typ0, types.SmallFixedBitVector):
            return
        res = parse.OperationExpr("@neq_bits_bv_bv", [arg0.expr, arg1.expr], expr.resolved_type)
        return res

    def optimize_zbitvector_concat(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        if not isinstance(arg1, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        typ1 = self._gettyp(arg1.expr)
        if not isinstance(typ0, types.SmallFixedBitVector) or not isinstance(
            typ1, types.SmallFixedBitVector
        ):
            return
        reswidth = typ0.width + typ1.width
        if reswidth > 64:
            return
        res = parse.CastExpr(
            parse.OperationExpr(
                "@bitvector_concat_bv_bv",
                [arg0.expr, parse.Number(typ1.width), arg1.expr],
                types.SmallFixedBitVector(reswidth),
            ),
            expr.resolved_type,
        )
        return res

    def optimize_zeq_int(self, expr):
        arg0, arg1 = expr.args
        if (
            not isinstance(arg0, parse.OperationExpr)
            or arg0.name != self.int64_to_int_name
        ):
            return
        if (
            not isinstance(arg1, parse.OperationExpr)
            or arg1.name != self.int64_to_int_name
        ):
            return
        (arg0,) = arg0.args
        (arg1,) = arg1.args
        return parse.OperationExpr("@eq_int_i_i", [arg0, arg1], expr.resolved_type)

    def optimize_zz5i64zDzKz5i(self, expr):  # int64_to_int
        # int_to_int64
        (arg0,) = expr.args
        if not isinstance(arg0, parse.OperationExpr) or arg0.name != "zz5izDzKz5i64":
            return
        return arg0.args[0]

    def optimize_zz5izDzKz5i64(self, expr):
        (arg0,) = expr.args
        if not isinstance(arg0, parse.OperationExpr) or arg0.name != "zz5i64zDzKz5i":
            return
        return arg0.args[0]

    def optimize_zxor_vec(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        if not isinstance(arg1, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        typ1 = self._gettyp(arg1.expr)
        if not isinstance(typ0, types.SmallFixedBitVector) or typ0 is not typ1:
            return
        arg0 = arg0.expr
        arg1 = arg1.expr
        return parse.CastExpr(
            parse.OperationExpr(
                "@xor_vec_bv_bv", [arg0, arg1], typ0
            ),
            expr.resolved_type,
        )

    def optimize_zand_vec(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        if not isinstance(arg1, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        typ1 = self._gettyp(arg1.expr)
        if not isinstance(typ0, types.SmallFixedBitVector) or typ0 is not typ1:
            return
        arg0 = arg0.expr
        arg1 = arg1.expr
        return parse.CastExpr(
            parse.OperationExpr(
                "@and_vec_bv_bv", [arg0, arg1], typ0
            ),
            expr.resolved_type,
        )

    def optimize_zor_vec(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        if not isinstance(arg1, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        typ1 = self._gettyp(arg1.expr)
        if not isinstance(typ0, types.SmallFixedBitVector) or typ0 is not typ1:
            return
        arg0 = arg0.expr
        arg1 = arg1.expr
        return parse.CastExpr(
            parse.OperationExpr(
                "@or_vec_bv_bv", [arg0, arg1], typ0
            ),
            expr.resolved_type,
        )

    def optimize_znot_vec(self, expr):
        (arg0,) = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        if not isinstance(typ0, types.SmallFixedBitVector):
            return
        arg0 = arg0.expr
        return parse.CastExpr(
            parse.OperationExpr(
                "@not_vec_bv",
                [arg0, parse.Number(typ0.width)],
                typ0
            ),
            expr.resolved_type,
        )

    def optimize_zadd_bits(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        if not isinstance(arg1, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        typ1 = self._gettyp(arg1.expr)
        if not isinstance(typ0, types.SmallFixedBitVector) or typ0 is not typ1:
            return
        arg0 = arg0.expr
        arg1 = arg1.expr
        return parse.CastExpr(
            parse.OperationExpr(
                "@add_bits_bv_bv",
                [arg0, arg1],
                typ0
            ),
            expr.resolved_type,
        )

    def optimize_zsub_vec(self, expr):
        arg0, arg1 = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        if not isinstance(arg1, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        typ1 = self._gettyp(arg1.expr)
        if not isinstance(typ0, types.SmallFixedBitVector) or typ0 is not typ1:
            return
        arg0 = arg0.expr
        arg1 = arg1.expr
        return parse.CastExpr(
            parse.OperationExpr(
                "@sub_bits_bv_bv",
                [arg0, arg1],
                typ0
            ),
            expr.resolved_type,
        )

    def optimize_zsigned(self, expr):
        (arg0,) = expr.args
        if not isinstance(arg0, parse.CastExpr):
            return
        typ0 = self._gettyp(arg0.expr)
        if not isinstance(typ0, types.SmallFixedBitVector):
            return
        arg0 = arg0.expr
        return parse.CastExpr(
            parse.OperationExpr(
                "@signed_bv",
                [arg0, parse.Number(typ0.width)],
                types.MachineInt()
            ),
            expr.resolved_type,
        )
