from pydrofoil import parse, types
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
        self.code = []
        self.level = 0
        self.last_enum = 0
        self.globalnames = {}
        self.localnames = None
        self.add_global("false", "False", types.Bool(), None)
        self.add_global("true", "True", types.Bool(), None)

    def add_global(self, name, pyname, typ, ast):
        assert isinstance(typ, types.Type)
        assert name not in self.globalnames
        self.globalnames[name] = NameInfo(pyname, typ, ast)

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


def parse_and_make_code(s):
    from rpysail import parse
    ast = parse.parser.parse(parse.lexer.lex(s))
    c = Codegen()
    c.emit("import operator")
    c.emit("from rpysail.test import supportcode")
    c.emit("class Registers(object): pass")
    c.emit("r = Registers()")
    try:
        ast.make_code(c)
    except Exception:
        print "\n".join(c.code)
        raise
    return "\n".join(c.code)
    

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
            #codegen.add_global(self.name, self.pyname, types.Enum(self), self)
        codegen.emit()

class __extend__(parse.Union):
    def make_code(self, codegen):
        name = "Union_" + self.name
        self.pyname = name
        with codegen.emit_indent("class %s(object):" % name):
            codegen.emit("pass")
        self.pynames = []
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
                    args = ["a%s" % i for i in range(len(argtypes))]
                else:
                    argtypes = [typ]
                    args = ["a"]
                with codegen.emit_indent("def __init__(self, %s):" % (", ".join(args), )):
                    for arg, typ in zip(args, argtypes):
                        codegen.emit("self.%s = %s # %s" % (arg, arg, typ))
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
        codegen.add_local(self.name, self.name, self.typ.resolve_type(codegen), self)
        if self.value is not None:
            codegen.emit("%s = %s" % (self.name, self.value.to_code(codegen)))

class __extend__(parse.Operation):
    def make_op_code(self, codegen):
        name = self.name
        if name.startswith("@"):
            if name == "@eq":
                op = "operator.eq"
            else:
                op = "XXX_" + name[1:]
        else:
            op = codegen.getname(name)
        if not self.args:
            args = '()'
        else:
            args = ", ".join([arg.to_code(codegen) for arg in self.args])
        result = codegen.gettarget(self.result)
        codegen.emit("%s = %s(%s)" % (result, op, args))

class __extend__(parse.ConditionalJump):
    def make_op_code(self, codegen):
        pass

    def make_op_jump(self, codegen, i):
        with codegen.emit_indent("if not (%s):" % (self.condition.to_code(codegen))):
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
        codegen.emit("%s = %s" % (result, self.value.to_code(codegen)))

class __extend__(parse.TupleElementAssignment):
    def make_op_code(self, codegen):
        codegen.emit("%s.tup%s = %s" % (self.tup, self.index, self.value.to_code(codegen)))

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
        return str(self.number)

    def gettyp(self, codegen):
        return parse.NamedType('%i64')

class __extend__(parse.Unit):
    def to_code(self, codegen):
        return '()'

    def gettyp(self, codegen):
        return parse.NamedType('%unit')


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
            op = "XXX_" + op[1:]
        return "%s(%s)" % (op, ", ".join([arg.to_code(codegen) for arg in self.args]))

class __extend__(parse.UnionVariantCheck):
    def to_code(self, codegen):
        return "type(%s) is %s" % (self.var, codegen.getname(self.variant))

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
        xxx

class __extend__(parse.EnumType):
    def resolve_type(self, codegen):
        return codegen.get_named_type(self.name)

class __extend__(parse.FunctionType):
    def resolve_type(self, codegen):
        return types.FunctionType(self.argtype.resolve_type(codegen), self.restype.resolve_type(codegen))

class __extend__(parse.TupleType):
    def resolve_type(self, codegen):
        return types.TupleType(tuple([e.resolve_type(codegen) for e in self.elements]))
