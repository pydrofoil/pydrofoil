from rpysail import parse
from contextlib import contextmanager

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
                codegen.emit("%s = %s" % (index, name))
            codegen.last_enum += len(self.names) + 1 # gap of 1

class __extend__(parse.Union):
    def make_code(self, codegen):
        name = "Union_" + self.name.lstrip("z")
        self.pyname = name
        with codegen.emit_indent("class %s(object):" % name):
            codegen.emit("pass")
        self.pynames = []
        for name, typ in zip(self.names, self.types):
            pyname = self.pyname + "_" + name.lstrip("z")
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

class __extend__(parse.GlobalVal):
    def make_code(self, codegen):
        if self.definition is not None:
            codegen.emit("%s = 'XXX define me %s'" % (self.name, self.definition))

class __extend__(parse.Register):
    def make_code(self, codegen):
        codegen.emit("# %s" % (self, ))


class __extend__(parse.Function):
    def make_code(self, codegen):
        pyname = "func_" + self.name.lstrip("z")
        self.pyname = pyname
        args = self.args
        with codegen.emit_indent("def %s(%s):" % (pyname, ", ".join(args))):
            codegen.emit("pc = 0")
            with codegen.emit_indent("while 1:"):
                for i, op in enumerate(self.body):
                    with codegen.emit_indent("if pc == %s:" % i):
                        codegen.emit("# %s" % (op, ))
                        op.make_op_code(codegen, self.localtypes)
                        op.make_op_jump(codegen, i, self.localtypes)


class __extend__(parse.Statement):
    def make_op_code(self, codegen, local_namespace):
        raise NotImplementedError

    def make_op_jump(self, codegen, i, local_namespace):
        codegen.emit("pc = %s" % (i + 1, ))


class __extend__(parse.LocalVarDeclaration):
    def make_op_code(self, codegen, local_namespace):
        codegen.emit("# %s: %s" % (self.name, self.typ))
        if self.value is not None:
            codegen.emit("%s = %s" % (self.name, self.value.to_code(codegen, local_namespace)))

class __extend__(parse.Operation):
    def make_op_code(self, codegen, local_namespace):
        result = self.result
        if result == "return":
            result = "return_"
        codegen.emit("%s = %s(%s)" % (result, self.name, ", ".join([arg.to_code(codegen, local_namespace) for arg in self.args])))

class __extend__(parse.ConditionalJump):
    def make_op_code(self, codegen, local_namespace):
        pass

    def make_op_jump(self, codegen, i, local_namespace):
        with codegen.emit_indent("if %s:" % (self.condition.to_code(codegen, local_namespace))):
            codegen.emit("pc = %s" % (self.target, ))
        codegen.emit("pc = %s" % (i + 1, ))

class __extend__(parse.Goto):
    def make_op_code(self, codegen, local_namespace):
        pass

    def make_op_jump(self, codegen, i, local_namespace):
        codegen.emit("pc = %s" % (self.target, ))

class __extend__(parse.Assignment):
    def make_op_code(self, codegen, local_namespace):
        codegen.emit("%s = %s" % (self.result, self.value.to_code(codegen, local_namespace)))

class __extend__(parse.End):
    def make_op_code(self, codegen, local_namespace):
        codegen.emit("return return_")
    
    def make_op_jump(self, codegen, i, local_namespace):
        pass

class __extend__(parse.Failure):
    def make_op_code(self, codegen, local_namespace):
        codegen.emit("raise TypeError")
    
    def make_op_jump(self, codegen, i, local_namespace):
        pass


class __extend__(parse.Expression):
    def to_code(self, codegen, local_namespace):
        raise NotImplementedError

class __extend__(parse.Var):
    def to_code(self, codegen, local_namespace):
        return self.name

class __extend__(parse.Number):
    def to_code(self, codegen, local_namespace):
        return str(self.number)

class __extend__(parse.Condition):
    def to_code(self, codegen, local_namespace):
        raise NotImplementedError

class __extend__(parse.VarCondition):
    def to_code(self, codegen, local_namespace):
        return self.name

class __extend__(parse.Comparison):
    def to_code(self, codegen, local_namespace):
        return "%s(%s)" % (self.operation, ", ".join([arg.to_code(codegen, local_namespace) for arg in self.args]))


class Codegen(object):
    def __init__(self, namespaces):
        self.code = []
        self.level = 0
        self.last_enum = 0
        self.namespaces = namespaces

    @contextmanager
    def emit_indent(self, line):
        self.emit(line)
        self.level += 1
        yield
        self.level -= 1

    def emit(self, line):
        self.code.append("    " * self.level + line)

def parse_and_make_code(s):
    from rpysail import parse, addtypes
    ast = parse.parser.parse(parse.lexer.lex(s))
    visitor = addtypes.ResolveNamesVisitor()
    ast.visit(visitor)
    c = Codegen(visitor)
    c.emit("class Registers(object): pass")
    c.emit("r = Registers()")
    try:
        ast.make_code(c)
    except Exception:
        print "\n".join(c.code)
        raise
    return "\n".join(c.code)
    
