from rpython.tool.pairtype import extendabletype, pair, pairtype

from pydrofoil import types, parse

class __extend__(pairtype(types.Type, types.Type)):
    def convert((from_, to), expr, codegen):
        if from_ is to: # no conversion needed
            return expr
        raise TypeError("can't convert from %s to %s: %s" % (from_, to, expr))

class __extend__(pairtype(types.SmallFixedBitVector, types.GenericBitVector)):
    def convert((from_, to), expr, codegen):
        assert from_.width <= 64
        return "bitvector.from_ruint(%s, %s)" % (from_.width, expr)

class __extend__(pairtype(types.SmallFixedBitVector, types.SmallFixedBitVector)):
    def convert((from_, to), expr, codegen):
        if from_ is not to:
            return "supportcode.raise_type_error('can not convert bv%s to bv%s')" % (from_.width, to.width)
        return expr

class __extend__(pairtype(types.GenericBitVector, types.SmallFixedBitVector)):
    def convert((from_, to), expr, codegen):
        return "%s.touint(%s)" % (expr, to.width)

class __extend__(pairtype(types.GenericBitVector, types.BigFixedBitVector)):
    def convert((from_, to), expr, codegen):
        return "%s.check_size_and_return(%s)" % (expr, to.width)

class __extend__(pairtype(types.BigFixedBitVector, types.GenericBitVector)):
    def convert((from_, to), expr, codegen):
        return "%s.tell_jit_size_and_return(%s)" % (expr, from_.width)

class __extend__(pairtype(types.Int, types.SmallFixedBitVector)):
    def convert((from_, to), expr, codegen):
        assert to.width <= 64
        return "%s.touint()" % expr

class __extend__(pairtype(types.String, types.Int)):
    def convert((from_, to), expr, codegen):
        return "Integer.fromstr(%s)" % (expr, )

class __extend__(pairtype(types.MachineInt, types.Int)):
    def convert((from_, to), expr, codegen):
        if isinstance(expr, parse.Number):
            # XXX
            s = str(ast.number)
            s = s.replace('-', 'NEG_')
            with codegen.cached_declaration(("num", ast.number), "IntConst_" + s) as pyname:
                codegen.emit("%s = Integer.fromint(%s)" % (pyname, ast.to_code(codegen)))
            return pyname
        return "Integer.fromint(%s)" % expr

class __extend__(pairtype(types.Int, types.MachineInt)):
    def convert((from_, to), expr, codegen):
        return "%s.toint()" % expr

class __extend__(pairtype(types.Tuple, types.Tuple)):
    def convert((from_, to), expr, codegen):
        if from_ is to:
            return expr
        with codegen.cached_declaration((from_, to), "convert_%s_%s" % (from_.pyname, to.pyname)) as pyname:
            with codegen.emit_indent("def %s(t1):" % pyname), codegen.enter_scope(parse.Function(None, None, None)):
                codegen.add_local("t1", "t1", from_, None)
                codegen.emit("res = %s()" % (to.pyname, ))
                for i, (typfrom, typto) in enumerate(zip(from_.elements, to.elements)):
                    codegen.emit("res.ztup%s = %s" % (i, pair(typfrom, typto).convert(parse.FieldAccess(parse.Var("t1"), "ztup%s" % i), codegen)))
                codegen.emit("return res")
        return "%s(%s)" % (pyname, expr)

class __extend__(pairtype(types.Vec, types.FVec)):
    def convert((from_, to), expr, codegen):
        return expr

class __extend__(pairtype(types.FVec, types.Vec)):
    def convert((from_, to), expr, codegen):
        return expr
