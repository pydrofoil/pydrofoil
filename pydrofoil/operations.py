from rpython.tool.pairtype import extendabletype, pair, pairtype

from pydrofoil import types, parse

class __extend__(types.FixedBitVector):
    def make_op_code_special_eq(self, ast, (sarg1, sarg2), (argtyp1, argtyp2)):
        arg1, arg2 = ast.args
        return "%s == %s" % (sarg1, sarg2)

    def bvop(self, template, sargs, argtyps):
        for typ in argtyps:
            assert typ.width == self.width
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
