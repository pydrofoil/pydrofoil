from rpython.tool.pairtype import pair

from pydrofoil import parse, types, binaryop
from contextlib import contextmanager

class NameInfo(object):
    def __init__(self, pyname, typ, ast):
        self.pyname = pyname
        self.typ = typ
        self.ast = ast

    def __repr__(self):
        return "NameInfo(%r, %r, %r)" % (self.pyname, self.typ, self.ast)


class Codegen(object):
    def __init__(self):
        self.declarations = []
        self.code = []
        self.level = 0
        self.last_enum = 0
        self.globalnames = {}
        self.namedtypes = {}
        self.localnames = None
        self.add_global("false", "False", types.Bool(), None)
        self.add_global("true", "True", types.Bool(), None)
        self.declared_types = set()

    def add_global(self, name, pyname, typ, ast):
        assert isinstance(typ, types.Type)
        assert name not in self.globalnames
        self.globalnames[name] = NameInfo(pyname, typ, ast)

    def add_named_type(self, name, pyname, typ, ast):
        assert isinstance(typ, types.Type)
        assert name not in self.namedtypes
        self.namedtypes[name] = NameInfo(pyname, typ, ast)

    def get_named_type(self, name):
        return self.namedtypes[name].typ

    def update_global_pyname(self, name, pyname):
        self.globalnames[name].pyname = pyname

    def add_local(self, name, pyname, typ, ast):
        assert isinstance(typ, types.Type)
        self.localnames[name] = NameInfo(pyname, typ, ast)

    def getname(self, name):
        if name not in self.localnames:
            return self.globalnames[name].pyname
        return name

    def getinfo(self, name):
        if name in self.localnames:
            return self.localnames[name]
        else:
            return self.globalnames[name]

    def gettarget(self, name):
        return self.getinfo(name).pyname

    def gettyp(self, name):
        return self.getinfo(name).typ

    @contextmanager
    def enter_scope(self, ast):
        old_localnames = self.localnames
        self.localnames = {}
        yield
        ast.localnames = self.localnames
        self.localnames = old_localnames

    @contextmanager
    def emit_indent(self, line):
        self.emit(line)
        self.level += 1
        yield
        self.level -= 1

    def emit(self, line=''):
        if not line.strip():
            self.code.append('')
        else:
            self.code.append("    " * self.level + line)

    def emit_declaration(self, line):
        self.declarations.append(line)

    def declare_tuple(self, typ):
        if typ in self.declared_types:
            return
        self.declared_types.add(typ)
        self.emit_declaration("class Tuple%s(object): pass" % (id(typ), ))

    def getcode(self):
        return "\n".join(self.declarations + self.code)


def parse_and_make_code(s):
    ast = parse.parser.parse(parse.lexer.lex(s))
    c = Codegen()
    c.emit("from rpython.rlib.rbigint import rbigint")
    c.emit("from rpython.rlib import rarithmetic")
    c.emit("import operator")
    c.emit("from pydrofoil.test import supportcode")
    c.emit("class Registers(object): pass")
    c.emit("r = Registers()")
    try:
        ast.make_code(c)
    except Exception:
        print c.getcode()
        raise
    return c.getcode()


# ____________________________________________________________
# declarations

class __extend__(parse.File):
    def make_code(self, codegen):
        for decl in self.declarations:
            decl.make_code(codegen)

class __extend__(parse.Declaration):
    def make_code(self, codegen):
        raise NotImplementedError("abstract base class")

class __extend__(parse.Enum):
    def make_code(self, codegen):
        name = "Enum_" + self.name
        self.pyname = name
        with codegen.emit_indent("class %s(object):" % name):
            for index, name in enumerate(self.names, start=codegen.last_enum):
                codegen.add_global(name, "%s.%s" % (self.pyname, name), types.Enum(self), self)
                codegen.emit("%s = %s" % (name, index))
            codegen.last_enum += len(self.names) + 1 # gap of 1
            codegen.add_named_type(self.name, self.pyname, types.Enum(self), self)
        codegen.emit()

class __extend__(parse.Union):
    def make_code(self, codegen):
        name = "Union_" + self.name
        self.pyname = name
        with codegen.emit_indent("class %s(object):" % name):
            codegen.emit("pass")
        self.pynames = []
        codegen.add_named_type(self.name, self.pyname, types.Union(self), self)
        for name, typ in zip(self.names, self.types):
            pyname = self.pyname + "_" + name
            codegen.add_global(name, pyname, types.Union(self), self)
            self.pynames.append(pyname)
            with codegen.emit_indent("class %s(%s):" % (pyname, self.pyname)):
                if isinstance(typ, parse.NamedType) and typ.name == "%unit":
                    codegen.emit("pass")
                    continue
                if isinstance(typ, parse.TupleType):
                    argtypes = typ.elements
                    fnarg = 't'
                    args = ["ztup%s" % i for i in range(len(argtypes))]
                    inits = ["t.ztup%s" % i for i in range(len(argtypes))]
                else:
                    argtypes = [typ]
                    args = inits = ["a"]
                    fnarg = 'a'
                with codegen.emit_indent("def __init__(self, %s):" % fnarg):
                    for arg, init, typ in zip(args, inits, argtypes):
                        codegen.emit("self.%s = %s # %s" % (arg, init, typ))
        codegen.emit()

class __extend__(parse.GlobalVal):
    def make_code(self, codegen):
        if self.definition is not None:
            name = eval(self.definition)
            if name == "not": name = "not_"
            codegen.add_global(self.name, "supportcode.%s" % (name, ), self.typ.resolve_type(codegen), self)
        else:
            codegen.add_global(self.name, None,  self.typ.resolve_type(codegen), self)

class __extend__(parse.Register):
    def make_code(self, codegen):
        codegen.emit("# %s" % (self, ))
        codegen.add_global(self.name, "r.%s" % self.name, self.typ.resolve_type(codegen), self)


class __extend__(parse.Function):
    def make_code(self, codegen):
        pyname = "func_" + self.name
        codegen.update_global_pyname(self.name, pyname)
        typ = codegen.globalnames[self.name].typ
        self.pyname = pyname
        args = self.args
        with codegen.emit_indent("def %s(%s):" % (pyname, ", ".join(args))):
            with codegen.enter_scope(self):
                codegen.add_local('return', 'return_', typ.restype, self)
                for i, arg in enumerate(args):
                    codegen.add_local(arg, arg, typ.argtype.elements[i], self)
                jumptargets = {0}
                for i, op in enumerate(self.body):
                    if isinstance(op, (parse.Goto, parse.ConditionalJump)):
                        jumptargets.add(op.target)
                if len(jumptargets) > 1:
                    codegen.emit("pc = 0")
                    codegen.emit("while 1:")
                    codegen.level += 2
                else:
                    jumptargets = set()
                for i, op in enumerate(self.body):
                    if i in jumptargets:
                        codegen.level -= 1
                        codegen.emit("if pc == %s:" % i)
                        codegen.level += 1
                    codegen.emit("# %s" % (op, ))
                    op.make_op_code(codegen)
                    if i + 1 in jumptargets:
                        # XXX remove two pc assignments
                        codegen.emit("pc = %s" % (i + 1, ))
                    op.make_op_jump(codegen, i)
                if len(jumptargets) > 1:
                    codegen.level -= 2
        codegen.emit()

# ____________________________________________________________
# operations

class __extend__(parse.Statement):
    def make_op_code(self, codegen):
        raise NotImplementedError

    def make_op_jump(self, codegen, i):
        pass


class __extend__(parse.LocalVarDeclaration):
    def make_op_code(self, codegen):
        codegen.emit("# %s: %s" % (self.name, self.typ))
        typ = self.typ.resolve_type(codegen)
        codegen.add_local(self.name, self.name, typ, self)
        if isinstance(typ, types.TupleType):
            assert self.value is None
            # need to make a tuple instance
            result = codegen.gettarget(self.name)
            codegen.declare_tuple(typ)
            codegen.emit("%s = Tuple%s()" % (result, id(typ)))
        elif self.value is not None:
            result = codegen.gettarget(self.name)
            othertyp = self.value.gettyp(codegen)
            rhs = pair(othertyp, typ).convert(self.value, codegen)
            codegen.emit("%s = %s" % (result, rhs))

class __extend__(parse.Operation):
    def make_op_code(self, codegen):
        name = self.name
        result = codegen.gettarget(self.result)
        if name.startswith("@"):
            if name == "@eq":
                op = "operator.eq"
                # XXX mess
                arg1, arg2 = self.args
                sarg1 = arg1.to_code(codegen)
                sarg2 = arg2.to_code(codegen)
                if isinstance(arg2, parse.Number):
                    typ = arg1.gettyp(codegen)
                    if isinstance(typ, types.BitVector):
                        sarg2 = "rarithmetic.r_uint(%s)" % (arg2.number, )
                    elif isinstance(typ, types.MachineInt):
                        sarg2 = str(arg2.number)
                    else:
                        assert 0
                codegen.emit("%s = %s == %s" % (result, sarg1, sarg2))
                return
            else:
                op = "XXX_" + name[1:]
        else:
            op = codegen.getname(name)
        if not self.args:
            args = '()'
        else:
            args = ", ".join([arg.to_code(codegen) for arg in self.args])
        codegen.emit("%s = %s(%s)" % (result, op, args))

class __extend__(parse.ConditionalJump):
    def make_op_code(self, codegen):
        pass

    def make_op_jump(self, codegen, i):
        with codegen.emit_indent("if %s:" % (self.condition.to_code(codegen))):
            codegen.emit("pc = %s" % (self.target, ))
            codegen.emit("continue")

class __extend__(parse.Goto):
    def make_op_code(self, codegen):
        pass

    def make_op_jump(self, codegen, i):
        codegen.emit("pc = %s" % (self.target, ))

class __extend__(parse.Assignment):
    def make_op_code(self, codegen):
        result = codegen.gettarget(self.result)
        typ = codegen.gettyp(self.result)
        othertyp = self.value.gettyp(codegen)
        rhs = pair(othertyp, typ).convert(self.value, codegen)
        codegen.emit("%s = %s" % (result, rhs))

class __extend__(parse.TupleElementAssignment):
    def make_op_code(self, codegen):
        codegen.emit("%s.ztup%s = %s" % (self.tup, self.index, self.value.to_code(codegen)))

class __extend__(parse.End):
    def make_op_code(self, codegen):
        codegen.emit("return return_")

    def make_op_jump(self, codegen, i):
        pass

class __extend__(parse.Failure):
    def make_op_code(self, codegen):
        codegen.emit("raise TypeError")

    def make_op_jump(self, codegen, i):
        pass

class __extend__(parse.TemplatedOperation):
    def make_op_code(self, codegen):
        if self.name == "@slice":
            arg, num = self.args
            typ = arg.gettyp(codegen)
            assert isinstance(typ, types.BitVector)
            assert isinstance(num, parse.Number)
            assert isinstance(self.templateparam, parse.Number)
            width = self.templateparam.number
            restyp = codegen.gettyp(self.result)
            assert isinstance(restyp, types.BitVector)
            result = codegen.gettarget(self.result)
            assert restyp.width == width
            codegen.emit("%s = (%s >> %s) & rarithmetic.r_uint(0x%x)" % (result, arg.to_code(codegen), num.number, (1 << width) - 1))
        elif self.name == "@signed":
            arg, = self.args
            typ = arg.gettyp(codegen)
            assert isinstance(typ, types.BitVector)
            assert isinstance(self.templateparam, parse.Number)
            width = self.templateparam.number
            restyp = codegen.gettyp(self.result)
            assert isinstance(restyp, types.MachineInt)
            result = codegen.gettarget(self.result)
            assert width <= 64
            codegen.emit("%s = supportcode.fast_signed(%s, %s)" % (result, arg.to_code(codegen), width))
        else:
            codegen.emit("XXX")

# ____________________________________________________________
# expressions

class __extend__(parse.Expression):
    def to_code(self, codegen):
        raise NotImplementedError

    def gettyp(self, codegen):
        raise NotImplementedError


class __extend__(parse.Var):
    def to_code(self, codegen):
        return codegen.getname(self.name)

    def gettyp(self, codegen):
        return codegen.gettyp(self.name)

class __extend__(parse.Number):
    def to_code(self, codegen):
        return "rbigint.fromint(%s)" % (self.number, )

    def gettyp(self, codegen):
        return types.Int()

class __extend__(parse.Unit):
    def to_code(self, codegen):
        return '()'

    def gettyp(self, codegen):
        return types.Unit()

class __extend__(parse.TupleElement):
    def to_code(self, codegen):
        return "%s.%s" % (self.tup.to_code(codegen), self.element)

    def gettyp(self, codegen):
        tuptyp = self.tup.gettyp(codegen)
        assert self.element.startswith("ztup")
        return tuptyp.elements[int(self.element[len('ztup'):])]

class __extend__(parse.Cast):
    def to_code(self, codegen):
        expr = self.expr.to_code(codegen)
        if self.field:
            field = self.field
        else:
            field = 'a'
        # XXX cleaner typeerror
        return "%s.%s if isinstance(%s, %s) else 1/0" % (expr, field, expr, codegen.getname(self.variant))

    def gettyp(self, codegen):
        # XXX clean up
        unionast = self.expr.gettyp(codegen).ast
        index = unionast.names.index(self.variant)
        typ = unionast.types[index].resolve_type(codegen)
        if self.field is not None:
            assert isinstance(typ, types.TupleType)
            assert self.field.startswith('ztup')
            return typ.elements[int(self.field[len('ztup'):])]
        else:
            return typ

# ____________________________________________________________
# conditions

class __extend__(parse.Condition):
    def to_code(self, codegen):
        raise NotImplementedError

class __extend__(parse.VarCondition):
    def to_code(self, codegen):
        return self.name

class __extend__(parse.Comparison):
    def to_code(self, codegen):
        op = self.operation
        if op.startswith("@"):
            if op == "@not":
                arg, = self.args
                return "not %s" % (arg.to_code(codegen), )
            op = "XXX_" + op[1:]
        return "%s(%s)" % (op, ", ".join([arg.to_code(codegen) for arg in self.args]))

class __extend__(parse.UnionVariantCheck):
    def to_code(self, codegen):
        return "type(%s) is not %s" % (self.var, codegen.getname(self.variant))

# ____________________________________________________________
# types


class __extend__(parse.Type):
    def resolve_type(self, codegen):
        raise NotImplementedError

class __extend__(parse.NamedType):
    def resolve_type(self, codegen):
        name = self.name
        if name == "%bool":
            return types.Bool()
        if name == "%i":
            return types.Int()
        if name == "%bv":
            return types.GenericBitVector()
        if name.startswith("%bv"):
            return types.BitVector(int(name[3:]))
        if name == "%unit":
            return types.Unit()
        if name == "%i64":
            return types.MachineInt()
        xxx

class __extend__(parse.EnumType):
    def resolve_type(self, codegen):
        return codegen.get_named_type(self.name)

class __extend__(parse.UnionType):
    def resolve_type(self, codegen):
        return codegen.get_named_type(self.name)

class __extend__(parse.FunctionType):
    def resolve_type(self, codegen):
        return types.FunctionType(self.argtype.resolve_type(codegen), self.restype.resolve_type(codegen))

class __extend__(parse.TupleType):
    def resolve_type(self, codegen):
        return types.TupleType(tuple([e.resolve_type(codegen) for e in self.elements]))
