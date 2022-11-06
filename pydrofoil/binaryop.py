from rpython.tool.pairtype import extendabletype, pair, pairtype

from pydrofoil import types, parse

class __extend__(pairtype(types.Type, types.Type)):
    def convert((from_, to), ast, codegen):
        if from_ is to: # no conversion needed
            return ast.to_code(codegen)
        raise TypeError("can't convert from %s to %s: %s" % (from_, to, ast))

class __extend__(pairtype(types.FixedBitVector, types.GenericBitVector)):
    def convert((from_, to), ast, codegen):
        assert from_.width <= 64
        return "bitvector.from_ruint(%s, %s)" % (from_.width, ast.to_code(codegen))

class __extend__(pairtype(types.FixedBitVector, types.FixedBitVector)):
    def convert((from_, to), ast, codegen):
        if from_ is to:
            return ast.to_code(codegen)
        return "supportcode.raise_type_error()" # I can't find what sail does here!

class __extend__(pairtype(types.SmallBitVector, types.GenericBitVector)):
    def convert((from_, to), ast, codegen):
        arg = ast.to_code(codegen)
        return arg # no conversion needed!

class __extend__(pairtype(types.SmallBitVector, types.FixedBitVector)):
    def convert((from_, to), ast, codegen):
        return "%s.touint()" % ast.to_code(codegen)

class __extend__(pairtype(types.FixedBitVector, types.SmallBitVector)):
    def convert((from_, to), ast, codegen):
        return "bitvector.from_ruint(%s, %s)" % (from_.width, ast.to_code(codegen))

class __extend__(pairtype(types.GenericBitVector, types.FixedBitVector)):
    def convert((from_, to), ast, codegen):
        return "%s.touint()" % ast.to_code(codegen)

class __extend__(pairtype(types.GenericBitVector, types.SmallBitVector)):
    def convert((from_, to), ast, codegen):
        return ast.to_code(codegen)

class __extend__(pairtype(types.Int, types.FixedBitVector)):
    def convert((from_, to), ast, codegen):
        assert to.width <= 64
        return "%s.touint()" % ast.to_code(codegen)

class __extend__(pairtype(types.String, types.Int)):
    def convert((from_, to), ast, codegen):
        return "Integer.fromstr(%s)" % (ast.to_code(codegen), )

class __extend__(pairtype(types.MachineInt, types.Int)):
    def convert((from_, to), ast, codegen):
        if isinstance(ast, parse.Number):
            s = str(ast.number)
            s = s.replace('-', 'NEG_')
            with codegen.cached_declaration(("num", ast.number), "IntConst_" + s) as pyname:
                codegen.emit("%s = Integer.fromint(%s)" % (pyname, ast.to_code(codegen)))
            return pyname
        return "Integer.fromint(%s)" % ast.to_code(codegen)

class __extend__(pairtype(types.Int, types.MachineInt)):
    def convert((from_, to), ast, codegen):
        return "%s.toint()" % ast.to_code(codegen)

class __extend__(pairtype(types.Tuple, types.Tuple)):
    def convert((from_, to), ast, codegen):
        if from_ is to:
            return ast.to_code(codegen)
        with codegen.cached_declaration((from_, to), "convert_%s_%s" % (from_.pyname, to.pyname)) as pyname:
            with codegen.emit_indent("def %s(t1):" % pyname), codegen.enter_scope(parse.Function(None, None, None)):
                codegen.add_local("t1", "t1", from_, None)
                codegen.emit("res = %s()" % (to.pyname, ))
                for i, (typfrom, typto) in enumerate(zip(from_.elements, to.elements)):
                    codegen.emit("res.ztup%s = %s" % (i, pair(typfrom, typto).convert(parse.FieldAccess(parse.Var("t1"), "ztup%s" % i), codegen)))
                codegen.emit("return res")
        return "%s(%s)" % (pyname, ast.to_code(codegen))

