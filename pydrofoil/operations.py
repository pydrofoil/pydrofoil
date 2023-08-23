from rpython.tool.pairtype import extendabletype, pair, pairtype

from pydrofoil import types, parse

class __extend__(types.Type):
    def make_op_code_special_neq(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return "not (%s)" % (self.make_op_code_special_eq(ast, sargs, argtyps, restyp), )

    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        return "supportcode.raise_type_error() + %r + %r" % (sarg1, sarg2)

def ruint_mask(s, width):
    if width == 64:
        return s
    return "(%s) & r_uint(0x%x)" % (s, (1 << width) - 1)

class __extend__(types.SmallFixedBitVector):
    def checkwidths(self, argtyps):
        for typ in argtyps:
            assert typ.width == self.width

    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        self.checkwidths(argtyps)
        return "%s == %s" % (sarg1, sarg2)

class __extend__(types.GenericBitVector):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        return "%s.eq(%s)" % (sarg1, sarg2)

class __extend__(types.MachineInt):
    def machineintop(self, template, sargs, argtyps):
        for typ in argtyps:
            assert isinstance(typ, types.MachineInt)
        return "(%s)" % (template % tuple(sargs))

    def make_op_code_special_eq(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return self.machineintop("%s == %s", sargs, argtyps)

    def make_op_code_special_gt(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return self.machineintop("%s > %s", sargs, argtyps)

    def make_op_code_special_lt(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return self.machineintop("%s < %s", sargs, argtyps)

    def make_op_code_special_gteq(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return self.machineintop("%s >= %s", sargs, argtyps)

    def make_op_code_special_lteq(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return self.machineintop("%s <= %s", sargs, argtyps)

    def make_op_code_special_iadd(self, ast, sargs, argtyps, restyp):
        return self.machineintop("%s + %s", sargs, argtyps)

    def make_op_code_special_isub(self, ast, sargs, argtyps, restyp):
        return self.machineintop("%s - %s", sargs, argtyps)

class __extend__(types.Int):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        return "%s.eq(%s)" % (sarg1, sarg2)

class DummyAst(object):
    def __init__(self, s):
        self.s = s
    def to_code(self, codegen):
        return self.s

class __extend__(types.List):
    def make_op_code_special_hd(self, ast, sargs, argtyps, restyp):
        ast = DummyAst("%s.head" % (sargs[0], ))
        return pair(argtyps[0].typ.elements[0], restyp).convert(ast, None)

    def make_op_code_special_tl(self, ast, sargs, argtyps, restyp):
        assert argtyps[0] is restyp
        return "%s.tail" % (sargs[0], )

    def make_op_code_special_eq(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        if sargs[1] != "None":
            # no clue
            return "supportcode.raise_type_error()"
        return "%s is None" % (sargs[0], )

class __extend__(types.Bool):
    def make_op_code_special_not(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return "not %s" % (sargs[0], )

    def make_op_code_special_eq(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return "%s == %s" % (sargs[0], sargs[1])

class __extend__(types.Enum):
    def make_op_code_special_eq(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return "%s == %s" % (sargs[0], sargs[1])

class __extend__(types.Bit):
    def make_op_code_special_eq(self, ast, sargs, argtyps, restyp):
        assert restyp is types.Bool()
        return "%s == %s" % (sargs[0], sargs[1])

class __extend__(types.String):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        return "%s == %s" % (sarg1, sarg2)

class __extend__(types.Union):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        return "%s.eq(%s)" % (sarg1, sarg2)

class __extend__(types.Struct):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        return "%s.eq(%s)" % (sarg1, sarg2)

class __extend__(types.Tuple):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        return "%s.eq(%s)" % (sarg1, sarg2)


class __extend__(types.Unit):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        return "True"

class __extend__(types.Ref):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        assert restyp is types.Bool()
        return "supportcode.raise_type_error()"

class __extend__(types.Real):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps, restyp):
        return "supportcode.eq_real(machine, %s, %s)" % (sarg1, sarg2)

class __extend__(types.Vec):
    def make_op_code_special_vector_access_o_i(self, ast, sargs, argtyps, restyp):
        return "%s[%s]" % tuple(sargs)

    def make_op_code_special_vector_update_o_i_o(self, ast, sargs, argtyps, restyp):
        return "supportcode.helper_vector_update_list_o_i_o(machine, %s)" % ", ".join(sargs)
