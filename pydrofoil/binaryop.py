from rpython.tool.pairtype import extendabletype, pair, pairtype

from pydrofoil import types, parse

class __extend__(pairtype(types.Type, types.Type)):
    def convert((from_, to), ast, codegen):
        if from_ is to: # no conversion needed
            return ast.to_code(codegen)
        raise TypeError("can't convert from %s to %s: %s" % (from_, to, ast))

class __extend__(pairtype(types.SmallFixedBitVector, types.GenericBitVector)):
    def convert((from_, to), ast, codegen):
        assert from_.width <= 64
        if isinstance(ast, parse.BitVectorConstant):
            name = "bitvectorconstant%s" % ast.constant
            with codegen.cached_declaration(0, name) as pyname:
                codegen.emit("%s = bitvector.from_ruint(%s, %s)" % (
                    pyname, from_.width, ast.to_code(codegen)))
                return pyname
        if ast.is_constant(codegen):
            import pdb; pdb.set_trace()
        return "bitvector.from_ruint(%s, %s)" % (from_.width, ast.to_code(codegen))

class __extend__(pairtype(types.SmallFixedBitVector, types.SmallFixedBitVector)):
    def convert((from_, to), ast, codegen):
        if from_ is to:
            return ast.to_code(codegen)
        return "supportcode.raise_type_error()" # I can't find what sail does here!

class __extend__(pairtype(types.GenericBitVector, types.SmallFixedBitVector)):
    def convert((from_, to), ast, codegen):
        return "bitvector.bv_touint(%s)" % ast.to_code(codegen)

class __extend__(pairtype(types.GenericBitVector, types.BigFixedBitVector)):
    def convert((from_, to), ast, codegen):
        return "bitvector.bv_touint(%s)" % ast.to_code(codegen)

class __extend__(pairtype(types.BigFixedBitVector, types.GenericBitVector)):
    def convert((from_, to), ast, codegen):
        return "bitvector.from_bigint(%s, %s)" % (from_.width, ast.to_code(codegen))

class __extend__(pairtype(types.Int, types.SmallFixedBitVector)):
    def convert((from_, to), ast, codegen):
        assert to.width <= 64
        xxx
        return "%s.touint()" % ast.to_code(codegen)

class __extend__(pairtype(types.String, types.Int)):
    def convert((from_, to), ast, codegen):
        return "bitvector.int_fromstr(%s)" % (ast.to_code(codegen), )

class __extend__(pairtype(types.MachineInt, types.Int)):
    def convert((from_, to), ast, codegen):
        if isinstance(ast, parse.Number):
            s = str(ast.number)
            s = s.replace('-', 'NEG_')
            with codegen.cached_declaration(("num", ast.number), "IntConst_" + s) as pyname:
                codegen.emit("%s = bitvector.int_fromint(%s)" % (pyname, ast.to_code(codegen)))
            return pyname
        return "bitvector.int_fromint(%s)" % ast.to_code(codegen)

class __extend__(pairtype(types.Int, types.MachineInt)):
    def convert((from_, to), ast, codegen):
        return "bitvector.int_toint(%s)" % ast.to_code(codegen)

class __extend__(pairtype(types.Tuple, types.Tuple)):
    def convert((from_, to), ast, codegen):
        if from_ is to:
            return ast.to_code(codegen)
        with codegen.cached_declaration((from_, to), "convert_%s_%s" % (from_.pyname, to.pyname)) as pyname:
            codegen.emit("@objectmodel.always_inline")
            with codegen.emit_indent("def %s(t1):" % pyname), codegen.enter_scope(parse.Function(None, None, None)):
                codegen.add_local("t1", "t1", from_, None)
                codegen.add_local("res", "res", to, None)
                codegen.emit("res = %s()" % (to.pyname, ))
                for i, (typfrom, typto) in enumerate(zip(from_.elements, to.elements)):
                    converted = pair(typfrom, typto).convert(parse.FieldAccess(parse.Var("t1"), "ztup%s" % i), codegen)
                    # hack, use parse.Number because its argument is passed as a string into the resulting code
                    synthetic_ast = parse.TupleElementAssignment("res", i, parse.Number(converted))
                    synthetic_ast.make_op_code(codegen)
                codegen.emit("return res")
        return "%s(%s)" % (pyname, ast.to_code(codegen))

class __extend__(pairtype(types.Vec, types.FVec)):
    def convert((from_, to), ast, codegen):
        return ast.to_code(codegen)

class __extend__(pairtype(types.FVec, types.Vec)):
    def convert((from_, to), ast, codegen):
        return ast.to_code(codegen)
