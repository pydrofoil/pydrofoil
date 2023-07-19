from pydrofoil import parse, makecode, types
from collections import defaultdict


# optimize operation ASTs before generating code


def identify_replacements(blocks):
    decls, defs, uses = find_decl_defs_uses(blocks)
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
            expr = parse.OperationExpr(defop.name, defop.args, declop.typ)
        else:
            assert isinstance(defop, parse.Assignment)
            expr = parse.CastExpr(defop.value, declop.typ)
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


def optimize_blocks(blocks, codegen):
    do_replacements(identify_replacements(blocks.values()))
    specialize_ops(blocks, codegen)


def find_decl_defs_uses(blocks):
    defs = defaultdict(list)
    uses = defaultdict(list)
    decls = {}
    for block in blocks:
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


def specialize_ops(blocks, codegen):
    localtypes = {}
    # find local var types
    for num, block in blocks.iteritems():
        for op in block:
            if isinstance(op, parse.LocalVarDeclaration):
                localtypes[op.name] = op
    v = OptVisitor(localtypes, "zz5i64zDzKz5i")
    for num, block in blocks.iteritems():
        for i, op in enumerate(block):
            for _ in range(10):  # XXX terrible
                res = op.visit(v)
                if res is not None:
                    block[i] = op = res


class OptVisitor(parse.Visitor):
    def __init__(self, localtypes, int64_to_int_name):
        self.localtypes = localtypes
        self.int64_to_int_name = int64_to_int_name

    def visit_CastExpr(self, cast):
        if isinstance(cast.expr, parse.CastExpr):
            return parse.CastExpr(cast.expr.expr, cast.typ)

    def visit_OperationExpr(self, expr):
        meth = getattr(self, "optimize_%s" % expr.name, None)
        if not meth:
            return None
        return meth(expr)

    def visit_Operation(self, expr):
        if expr.result not in self.localtypes:
            return None
        typ = self.localtypes[expr.result].typ
        if expr.name == "$zinternal_vector_update":
            return
        return parse.Assignment(
            expr.result, parse.OperationExpr(expr.name, expr.args, typ), expr.sourcepos
        )

    def visit_Assignment(self, expr):
        while isinstance(expr.value, parse.CastExpr):
            expr.value = expr.value.expr

    def _gettyp(self, expr):
        try:
            if not isinstance(expr, parse.Var):
                return expr.gettyp(None)
            if not expr.name in self.localtypes:
                xxx
            decl = self.localtypes[expr.name]
            return decl.typ.resolve_type(None)
        except AttributeError:
            return None

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
            and arg1.name == self.int64_to_int_name
        ):
            return
        if (
            not isinstance(arg2, parse.OperationExpr)
            and arg2.name == self.int64_to_int_name
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
                parse.NamedType("%bv" + str(width)),
            ),
            expr.typ,
        )
        return res

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
        res = parse.OperationExpr("@eq_bits_bv_bv", [arg0.expr, arg1.expr], expr.typ)
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
                parse.NamedType("%bv" + str(reswidth)),
            ),
            expr.typ,
        )
        return res
