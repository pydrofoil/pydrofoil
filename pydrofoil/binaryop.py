from rpython.tool.pairtype import extendabletype, pair, pairtype

from pydrofoil import types

class __extend__(pairtype(types.Type, types.Type)):
    def convert((from_, to), ast, codegen):
        if from_ is to: # no conversion needed
            return ast.to_code(codegen)
        raise TypeError("can't convert from %s to %s: %s" % (from_, to, ast))

class __extend__(pairtype(types.BitVector, types.GenericBitVector)):
    def convert((from_, to), ast, codegen):
         assert from_.width <= 64
         return "rbigint.fromrarith_int(%s)" % ast.to_code(codegen)

class __extend__(pairtype(types.GenericBitVector, types.BitVector)):
    def convert((from_, to), ast, codegen):
         assert to.width <= 64
         return "%s.touint()" % ast.to_code(codegen)


class __extend__(pairtype(types.Int, types.BitVector)):
    def convert((from_, to), ast, codegen):
         assert to.width <= 64
         return "%s.touint()" % ast.to_code(codegen)

