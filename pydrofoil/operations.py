from rpython.tool.pairtype import extendabletype, pair, pairtype

from pydrofoil import types, parse

class __extend__(types.Type):
    def make_op_code_special_neq(self, ast, sargs, argtyps):
        return "not (%s)" % (self.make_op_code_special_eq(ast, sargs, argtyps), )


class __extend__(types.FixedBitVector):
    def checkwidths(self, argtyps):
        for typ in argtyps:
            assert typ.width == self.width

    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps):
        self.checkwidths(argtyps)
        return "%s == %s" % (sarg1, sarg2)

    def bvop(self, template, sargs, argtyps):
        self.checkwidths(argtyps)
        mask = "rarithmetic.r_uint(0x%x)" % ((1 << self.width) - 1)
        return "((%s) & %s)" % (template % tuple(sargs), mask)

    def make_op_code_special_bvnot(self, ast, sargs, argtyps):
        return self.bvop("~%s", sargs, argtyps)

    def make_op_code_special_bvsub(self, ast, sargs, argtyps):
        return self.bvop("%s - %s", sargs, argtyps)

    def make_op_code_special_bvadd(self, ast, sargs, argtyps):
        return self.bvop("%s + %s", sargs, argtyps)

    def make_op_code_special_bvand(self, ast, sargs, argtyps):
        return self.bvop("%s & %s", sargs, argtyps)

    def make_op_code_special_bvor(self, ast, sargs, argtyps):
        return self.bvop("%s | %s", sargs, argtyps)

    def make_op_code_special_bvxor(self, ast, sargs, argtyps):
        return self.bvop("%s ^ %s", sargs, argtyps)

    def make_op_code_special_bvaccess(self, ast, (sarg1, sarg2), argtyps):
        return "rarithmetic.r_uint(1) & supportcode.safe_rshift(%s, rarithmetic.r_uint(%s))" % (sarg1, sarg2)

    def make_op_code_special_concat(self, ast, (sarg1, sarg2), (argtyp1, argtyp2)):
        return "(%s << %s) | %s" % (sarg1, argtyp2.width, sarg2)

    # templated

    def make_op_code_templated_slice(self, ast, codegen):
        arg, num = ast.args
        assert isinstance(num, parse.Number)
        assert isinstance(ast.templateparam, parse.Number)
        width = ast.templateparam.number
        return "supportcode.safe_rshift(%s, %s) & rarithmetic.r_uint(0x%x)" % (arg.to_code(codegen), num.number, (1 << width) - 1)

    def make_op_code_templated_signed(self, ast, codegen):
        arg, = ast.args
        self = arg.gettyp(codegen)
        assert isinstance(ast.templateparam, parse.Number)
        width = ast.templateparam.number
        restyp = codegen.gettyp(ast.result)
        assert isinstance(restyp, types.MachineInt) and width == 64
        return "supportcode.fast_signed(%s, %s)" % (arg.to_code(codegen), self.width)

    def make_op_code_templated_unsigned(self, ast, codegen):
        arg, = ast.args
        self = arg.gettyp(codegen)
        assert isinstance(ast.templateparam, parse.Number)
        width = ast.templateparam.number
        restyp = codegen.gettyp(ast.result)
        assert isinstance(restyp, types.MachineInt) and width == 64
        result = codegen.gettarget(ast.result)
        return "rarithmetic.intmask(%s)" % (arg.to_code(codegen), )


class __extend__(types.SmallBitVector):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), argtyps):
        return "%s.val == %s.val" % (sarg1, sarg2)

    def make_op_code_templated_slice(self, ast, codegen):
        arg, num = ast.args
        assert isinstance(num, parse.Number)
        assert isinstance(ast.templateparam, parse.Number)
        width = ast.templateparam.number
        return "supportcode.safe_rshift(%s.val, %s) & rarithmetic.r_uint(0x%x)" % (arg.to_code(codegen), num.number, (1 << width) - 1)

class __extend__(types.MachineInt):
    def machineintop(self, template, sargs, argtyps):
        for typ in argtyps:
            assert isinstance(typ, types.MachineInt)
        return "(%s)" % (template % tuple(sargs))

    def make_op_code_special_eq(self, ast, sargs, argtyps):
        return self.machineintop("%s == %s", sargs, argtyps)

    def make_op_code_special_neq(self, ast, sargs, argtyps):
        return self.machineintop("%s != %s", sargs, argtyps)

    def make_op_code_special_gt(self, ast, sargs, argtyps):
        return self.machineintop("%s > %s", sargs, argtyps)

    def make_op_code_special_lt(self, ast, sargs, argtyps):
        return self.machineintop("%s < %s", sargs, argtyps)

    def make_op_code_special_gteq(self, ast, sargs, argtyps):
        return self.machineintop("%s >= %s", sargs, argtyps)

    def make_op_code_special_lteq(self, ast, sargs, argtyps):
        return self.machineintop("%s <= %s", sargs, argtyps)

    def make_op_code_special_iadd(self, ast, sargs, argtyps):
        return self.machineintop("%s + %s", sargs, argtyps)

    def make_op_code_special_isub(self, ast, sargs, argtyps):
        return self.machineintop("%s - %s", sargs, argtyps)


class __extend__(types.List):
    def make_op_code_special_hd(self, ast, sargs, argtyps):
        return "%s[0]" % (sargs[0], )

    def make_op_code_special_tl(self, ast, sargs, argtyps):
        return "%s[1]" % (sargs[0], )

class __extend__(types.Bool):
    def make_op_code_special_not(self, ast, sargs, argtyps):
        return "not %s" % (sargs[0], )

    def make_op_code_special_eq(self, ast, sargs, argtyps):
        return "%s == %s" % (sargs[0], sargs[1])

class __extend__(types.Enum):
    def make_op_code_special_eq(self, ast, sargs, argtyps):
        return "%s == %s" % (sargs[0], sargs[1])
