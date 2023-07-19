from rply import LexerGenerator, LexingError, ParserGenerator, ParsingError
from rply.token import BaseBox

from rpython.tool.pairtype import extendabletype

# ____________________________________________________________
# lexer

lg = LexerGenerator()

alltokens = []

def addtok(name, regex):
    alltokens.append(name)
    lg.add(name, regex)

def addkeyword(kw):
    addtok(kw.upper(), kw)

addkeyword('enum')
addkeyword('union')
addkeyword('struct')
addkeyword('val')
addkeyword('fn')
addkeyword('end')
addkeyword('arbitrary')
addkeyword('exit')
addkeyword('goto')
addkeyword('jump')
addkeyword('register')
addkeyword('is')
addkeyword('as')
addkeyword('let')
addkeyword('undefined')
addkeyword('files')

addtok('PERCENTENUM', r'%enum')
addtok('PERCENTUNION', r'%union')
addtok('PERCENTSTRUCT', r'%struct')
addtok('PERCENTVEC', r'%vec')
addtok('PERCENTFVEC', r'%fvec')
addtok('PERCENTLIST', r'%list')

addtok('BINBITVECTOR', r'0b[01]+')
addtok('HEXBITVECTOR', r'0x[0-9a-fA-F]+')
addtok('NUMBER', r'-?\d+')
addtok('NAME', r'[a-zA-Z_%@$][a-zA-Z_0-9]*')
addtok('STRING', r'"[^"]*"')
addtok('ARROW', r'->')
addtok('SOURCEPOS', r'`[^;]+')
addtok('LPAREN', r'[(]')
addtok('RPAREN', r'[)]')
addtok('LBRACE', r'[{]')
addtok('RBRACE', r'[}]')
addtok('COMMA', r'[,]')
addtok('COLON', r'[:]')
addtok('EQUAL', r'[=]')
addtok('SEMICOLON', r'[;]')
addtok('LT', r'[<]')
addtok('GT', r'[>]')
addtok('DOT', r'[.]')
addtok('AMPERSAND', r'[&]')
addtok('STAR', r'[*]')
addtok('HASH', r'#')

lg.ignore(r'[ \n]')

lexer = lg.build()


# ____________________________________________________________
# AST classes

class Visitor(object):
    def visit(self, ast):
        meth = getattr(self, "visit_%s" % type(ast).__name__, None)
        if meth is not None:
            return meth(ast)
        return self.default_visit(ast)

    def default_visit(self, ast):
        pass

class BaseAst(BaseBox):
    __metaclass__ = extendabletype

    def __eq__(self, other):
        if type(self) != type(other):
            return NotImplemented
        return self.__dict__ == other.__dict__

    def __ne__(self, other):
        if type(self) != type(other):
            return NotImplemented
        return self.__dict__ != other.__dict__

    def __repr__(self):
        return "%s(%s)" % (type(self).__name__, ", ".join(sorted("%s=%r" % (key, value) for key, value in self.__dict__.items())))

    def view(self):
        from rpython.translator.tool.make_dot import DotGen
        from dotviewer import graphclient
        import pytest
        dotgen = DotGen('G')
        self._dot(dotgen)
        p = pytest.ensuretemp("pyparser").join("temp.dot")
        p.write(dotgen.generate(target=None))
        graphclient.display_dot_file(str(p))

    def _dot(self, dotgen):
        arcs = []
        label = [type(self).__name__]
        for key, value in self.__dict__.items():
            if isinstance(value, BaseAst):
                arcs.append((value, key))
                value._dot(dotgen)
            elif isinstance(value, list) and value and isinstance(value[0], BaseAst):
                for index, item in enumerate(value):
                    arcs.append((item, "%s[%s]" % (key, index)))
                    item._dot(dotgen)
            else:
                label.append("%s = %r" % (key, value))
        dotgen.emit_node(str(id(self)), shape="box", label = "\n".join(label))
        for target, label in arcs:
            dotgen.emit_edge(str(id(self)), str(id(target)), label)

    def visit(self, visitor):
        result = visitor.visit(self)
        if result is not None:
            return result
        for key, value in self.__dict__.items():
            if isinstance(value, BaseAst):
                newvalue = value.visit(visitor)
                if newvalue is not None:
                    setattr(self, key, newvalue)
            elif isinstance(value, list) and value and isinstance(value[0], BaseAst):
                for i, item in enumerate(value):
                    newitem = item.visit(visitor)
                    if newitem is not None:
                        value[i] = newitem

class File(BaseAst):
    def __init__(self, declarations, sourcepos=None):
        self.declarations = declarations

class Declaration(BaseAst):
    pass

class Enum(Declaration):
    def __init__(self, name, names, sourcepos=None):
        self.name = name
        self.names = names

class Union(Declaration):
    def __init__(self, name, names, types, sourcepos=None):
        self.name = name
        self.names = names
        self.types = types

class Struct(Declaration):
    def __init__(self, name, names, types, sourcepos=None):
        self.name = name
        self.names = names
        self.types = types

class GlobalVal(Declaration):
    def __init__(self, name, definition, typ, sourcepos=None):
        self.name = name
        self.definition = definition
        self.typ = typ

class Register(Declaration):
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

class Let(Declaration):
    def __init__(self, name, typ, body):
        self.name = name
        self.typ = typ
        self.body = body

class Function(Declaration):
    def __init__(self, name, args, body, sourcepos=None):
        self.name = name
        self.args = args
        self.body = body
        self.localtypes = None

    def _dot(self, dotgen):
        arcs = []
        label = ["Function", "name = %r" % (self.name, ), "args = %r" % (self.args, )]
        for op in self.body:
            op._dot(dotgen)
        dotgen.emit_node(str(id(self)), shape="box", label = type(self).__name__ + "\n" + "\n".join(label))
        dotgen.emit_edge(str(id(self)), str(id(self.body[0])), "start")
        for index, op in enumerate(self.body):
            if isinstance(op, End):
                pass
            elif isinstance(op, Exit):
                pass
            elif isinstance(op, Goto):
                dotgen.emit_edge(str(id(op)), str(id(self.body[op.target])))
            elif isinstance(op, ConditionalJump):
                dotgen.emit_edge(str(id(op)), str(id(self.body[op.target])), "false")
                dotgen.emit_edge(str(id(op)), str(id(self.body[index + 1])), "true")
            else:
                dotgen.emit_edge(str(id(op)), str(id(self.body[index + 1])))

class Pragma(Declaration):
    def __init__(self, name, content):
        self.name = name
        self.content = content

class Files(Declaration):
    def __init__(self, filenames):
        self.filenames = filenames

class Type(BaseAst):
    pass

class NamedType(Type):
    def __init__(self, name, sourcepos=None):
        self.name = name

    def __repr__(self):
        return "NamedType(%r)" % self.name

class TupleType(Type):
    def __init__(self, elements):
        self.elements = elements

class EnumType(Type):
    def __init__(self, name):
        self.name = name

class UnionType(Type):
    def __init__(self, name):
        self.name = name

class StructType(Type):
    def __init__(self, name):
        self.name = name

class ListType(Type):
    def __init__(self, typ):
        self.typ = typ

class FunctionType(Type):
    def __init__(self, argtype, restype):
        self.argtype = argtype
        self.restype = restype

class RefType(Type):
    def __init__(self, refto):
        self.refto = refto

class VecType(Type):
    def __init__(self, of):
        self.of = of

class FVecType(Type):
    def __init__(self, number, of):
        self.number = number
        self.of = of

class Statement(BaseAst):
    end_of_block = False

    def find_used_vars(self):
        raise NotImplementedError

    def replace_var(self, var, expr):
        raise NotImplementedError

class StatementWithSourcePos(Statement):
    sourcepos = None
    def add_sourcepos(self, sourcepos):
        self.sourcepos = sourcepos
        return self

class LocalVarDeclaration(StatementWithSourcePos):
    def __init__(self, name, typ, value=None, sourcepos=None):
        self.name = name
        self.typ = typ
        self.value = value
        self.sourcepos = sourcepos

    def find_used_vars(self):
        if self.value:
            return self.value.find_used_vars()
        return set()

    def replace_var(self, var, expr):
        xxx

class Assignment(StatementWithSourcePos):
    def __init__(self, result, value, sourcepos=None):
        self.result = result
        self.value = value
        self.sourcepos = sourcepos

    def find_used_vars(self):
        return self.value.find_used_vars()

    def replace_var(self, var, expr):
        return Assignment(
            self.result,
            self.value.replace_var(var, expr),
            self.sourcepos
        )

class Operation(StatementWithSourcePos):
    def __init__(self, result, name, args, sourcepos=None):
        self.result = result
        self.name = name
        self.args = args
        self.sourcepos = sourcepos

    def find_used_vars(self):
        res = set()
        for val in self.args:
            res.update(val.find_used_vars())
        return res

    def replace_var(self, var, expr):
        newargs = [arg.replace_var(var, expr) for arg in self.args]
        return Operation(self.result, self.name, newargs)


class TemplatedOperation(StatementWithSourcePos):
    def __init__(self, result, name, templateparam, args):
        self.result = result
        self.name = name
        self.templateparam = templateparam
        self.args = args

    def find_used_vars(self):
        res = set()
        for val in self.args:
            res.update(val.find_used_vars())
        return res

    def replace_var(self, var, expr):
        xxx


class Goto(Statement):
    end_of_block = True
    def __init__(self, target):
        self.target = target

    def find_used_vars(self):
        return set()

class ConditionalJump(StatementWithSourcePos):
    def __init__(self, condition, target, sourcepos=None):
        self.condition = condition
        self.target = target
        self.sourcepos = sourcepos

    def find_used_vars(self):
        return self.condition.find_used_vars()

    def replace_var(self, var, expr):
        newcond = self.condition.replace_var(var, expr)
        return ConditionalJump(newcond, self.target, self.sourcepos)

class Condition(BaseAst):
    pass

class ExprCondition(Condition):
    def __init__(self, expr):
        self.expr = expr

    def find_used_vars(self):
        return self.expr.find_used_vars()

    def replace_var(self, var, expr):
        return ExprCondition(self.expr.replace_var(var, expr))

class Comparison(Condition):
    def __init__(self, operation, args):
        self.operation = operation
        self.args = args

    def find_used_vars(self):
        res = set()
        for val in self.args:
            res.update(val.find_used_vars())
        return res

    def replace_var(self, var, expr):
        newargs = [arg.replace_var(var, expr) for arg in self.args]
        return Comparison(self.operation, newargs)

class UnionVariantCheck(Condition):
    def __init__(self, var, variant):
        self.var = var
        self.variant = variant

    def find_used_vars(self):
        return self.var.find_used_vars()

    def replace_var(self, var, expr):
        xxx

class StructElementAssignment(StatementWithSourcePos):
    def __init__(self, obj, field, value, sourcepos=None):
        self.obj = obj
        self.field = field
        self.value = value
        self.sourcepos = sourcepos

    def find_used_vars(self):
        res = self.obj.find_used_vars()
        res.update(self.value.find_used_vars())
        return res

    def replace_var(self, var, expr):
        return StructElementAssignment(
            self.obj.replace_var(var, expr),
            self.field,
            self.value.replace_var(var, expr),
            self.sourcepos)


class RefAssignment(StatementWithSourcePos):
    def __init__(self, ref, value, sourcepos=None):
        self.ref = ref
        self.value = value
        self.sourcepos = sourcepos

    def find_used_vars(self):
        res = self.value.find_used_vars()
        res.add(self.ref)
        return res

    def replace_var(self, var, expr):
        xxx

class End(Statement):
    end_of_block = True

    def find_used_vars(self):
        return set()

    def replace_var(self, var, expr):
        xxx

class Exit(StatementWithSourcePos):
    end_of_block = True

    def __init__(self, kind, sourcepos=None):
        self.kind = kind
        self.sourcepos = sourcepos

    def find_used_vars(self):
        return set()

    def replace_var(self, var, expr):
        xxx

class Arbitrary(Statement):
    end_of_block = True

    def find_used_vars(self):
        return set()

    def replace_var(self, var, expr):
        xxx

class Expression(BaseAst):
    def find_used_vars(self):
        raise NotImplementedError

    def replace_var(self, var, expr):
        xxx

class Var(Expression):
    def __init__(self, name):
        self.name = name

    def find_used_vars(self):
        return {self.name}

    def replace_var(self, var, expr):
        if self.name == var:
            return expr
        return self


class Number(Expression):
    def __init__(self, number):
        self.number = number

    def find_used_vars(self):
        return set()

    def replace_var(self, var, expr):
        return self

class BitVectorConstant(Expression):
    def __init__(self, constant):
        self.constant = constant

    def find_used_vars(self):
        return set()

    def replace_var(self, var, expr):
        return self

class FieldAccess(Expression):
    def __init__(self, obj, element):
        self.obj = obj # expr
        self.element = element

    def find_used_vars(self):
        return self.obj.find_used_vars()

    def replace_var(self, var, expr):
        return FieldAccess(self.obj.replace_var(var, expr), self.element)

class Cast(Expression):
    def __init__(self, expr, variant):
        self.expr = expr
        self.variant = variant

    def find_used_vars(self):
        return self.expr.find_used_vars()

    def replace_var(self, var, expr):
        return Cast(self.expr.replace_var(var, expr), self.variant)

class RefOf(Expression):
    def __init__(self, expr):
        self.expr = expr

    def find_used_vars(self):
        return self.expr.find_used_vars()

    def replace_var(self, var, expr):
        return RefOf(self.expr.replace_var(var, expr))

class String(Expression):
    def __init__(self, string):
        self.string = string

    def find_used_vars(self):
        return set()

    def replace_var(self, var, expr):
        return self

class Unit(Expression):
    def find_used_vars(self):
        return set()

    def replace_var(self, var, expr):
        return self


class Undefined(Expression):
    def __init__(self, typ):
        self.typ = typ

    def find_used_vars(self):
        return set()

    def replace_var(self, var, expr):
        return self


class StructConstruction(Expression):
    def __init__(self, name, fieldnames, fieldvalues):
        self.name = name
        self.fieldnames = fieldnames
        self.fieldvalues = fieldvalues

    def find_used_vars(self):
        res = set()
        for val in self.fieldvalues:
            res.update(val.find_used_vars())
        return res

    def replace_var(self, var, expr):
        fieldvalues = [val.replace_var(var, expr) for val in self.fieldvalues]
        return StructConstruction(self.name, self.fieldnames, fieldvalues)

class StructField(BaseAst):
    def __init__(self, fieldname, fieldvalue):
        self.fieldname = fieldname
        self.fieldvalue = fieldvalue

# some ASTs only used during optimization

class OperationExpr(Expression):
    def __init__(self, name, args, typ):
        self.name = name
        self.args = args
        self.typ = typ

    def find_used_vars(self):
        res = set()
        for val in self.args:
            res.update(val.find_used_vars())
        return res

    def replace_var(self, var, expr):
        newargs = [arg.replace_var(var, expr) for arg in self.args]
        return OperationExpr(self.name, newargs, self.typ)

class CastExpr(Expression):
    def __init__(self, expr, typ):
        while isinstance(expr, CastExpr): # remove double cast
            expr = expr.expr
        self.expr = expr
        self.typ = typ

    def find_used_vars(self):
        return self.expr.find_used_vars()

    def replace_var(self, var, expr):
        expr = self.expr.replace_var(var, expr)
        return CastExpr(expr, self.typ)

# ____________________________________________________________
# parser

pg = ParserGenerator(alltokens)

@pg.production('file : declaration | file declaration')
def file(p):
    if len(p) == 1:
        return File(p)
    return File(p[0].declarations + [p[1]])

@pg.production('declaration : enum | union | struct | globalval | function | register | let | pragma | files')
def declaration(p):
    return p[0]

@pg.production('enum : ENUM NAME LBRACE enumcontent RBRACE')
def enum(p):
    p[3].name = p[1].value
    return p[3]

@pg.production('enumcontent : NAME | NAME COMMA enumcontent')
def enumcontent(p):
    if len(p) == 1:
        return Enum(None, [p[0].value])
    else:
        return Enum(None, [p[0].value] + p[2].names)

@pg.production('union : UNION NAME LBRACE unioncontent RBRACE')
def union(p):
    return Union(p[1].value, p[3].names, p[3].types)

@pg.production('struct : STRUCT NAME LBRACE unioncontent RBRACE')
def struct(p):
    return Struct(p[1].value, p[3].names, p[3].types)

@pg.production('unioncontent : NAME COLON type | NAME COLON type COMMA unioncontent')
def unioncontent(p):
    if len(p) == 3:
        return Union(None, [p[0].value], [p[2]])
    else:
        return Union(None, [p[0].value] + p[4].names, [p[2]] + p[4].types)

@pg.production('globalval : VAL NAME COLON type | VAL NAME EQUAL STRING COLON type')
def globalval(p):
    if len(p) == 4:
        return GlobalVal(p[1].value, None, p[3])
    else:
        return GlobalVal(p[1].value, p[3].value, p[5])

@pg.production('function : FN NAME LPAREN args RPAREN LBRACE operations RBRACE')
def function(p):
    return Function(p[1].value, p[3].args, p[6].body)

@pg.production('args : NAME | NAME COMMA args')
def args(p):
    if len(p) == 1:
        return Function(None, [p[0].value], None)
    else:
        return Function(None, [p[0].value] + p[2].args, None)

@pg.production('register : REGISTER NAME COLON type')
def register(p):
    return Register(p[1].value, p[3])

@pg.production('let : LET LPAREN NAME COLON type RPAREN LBRACE operations RBRACE')
def let(p):
    return Let(p[2].value, p[4], p[7].body)

@pg.production('pragma : HASH NAME pragmacontent')
def pragma(p):
    return Pragma(p[1].value, p[2].content)

@pg.production('pragmacontent : NAME | NAME pragmacontent')
def pragmacontent(p):
    if len(p) == 1:
        return Pragma(None, [p[0].value])
    else:
        return Pragma(None, [p[0].value] + p[1].content)

@pg.production('files : FILES filescontent')
def files(p):
    return p[1]

@pg.production('filescontent : STRING | STRING filescontent')
def filescontent(p):
    if len(p) == 1:
        return Files([p[0].value])
    else:
        return Files([p[0].value] + p[1].filenames)

@pg.production('operations : operation SEMICOLON | operation SEMICOLON operations')
def operations(p):
    if len(p) == 2:
        return Function(None, None, [p[0]])
    else:
        return Function(None, None, [p[0]] + p[2].body)

# operations

@pg.production('operation : operationwithposition SOURCEPOS | end | goto | arbitrary ')
def operation(p):
    if len(p) == 2:
        return p[0].add_sourcepos(p[1].value)
    else:
        return p[0]

@pg.production('operationwithposition : localvardeclaration | op | templatedop | conditionaljump | assignment | exit')
def operationwithposition(p):
    return p[0]

@pg.production('localvardeclaration : NAME COLON type | NAME COLON type EQUAL expr')
def localvardeclaration(p):
    if len(p) == 3:
        return LocalVarDeclaration(p[0].value, p[2])
    return LocalVarDeclaration(p[0].value, p[2], p[4])


@pg.production('op : NAME EQUAL NAME LPAREN opargs RPAREN')
def op(p):
    return Operation(p[0].value, p[2].value, p[4].args)

@pg.production('templatedop : NAME EQUAL NAME LT type GT LPAREN opargs RPAREN')
def op(p):
    return TemplatedOperation(p[0].value, p[2].value, p[4], p[7].args)

@pg.production('opargs : expr | expr COMMA opargs')
def opargs(p):
    if len(p) == 1:
        return Operation(None, None, [p[0]])
    else:
        return Operation(None, None, [p[0]] + p[2].args)

@pg.production('expr : NAME | STRING | NUMBER | BINBITVECTOR | HEXBITVECTOR | UNDEFINED COLON type | expr DOT NAME | LPAREN RPAREN | expr AS NAME | AMPERSAND expr | STRUCT structconstruction')
def expr(p):
    if len(p) == 1:
        if p[0].gettokentype() == "NAME":
            return Var(p[0].value)
        if p[0].gettokentype() == "STRING":
            return String(p[0].value)
        elif p[0].gettokentype() == "BINBITVECTOR":
            return BitVectorConstant(p[0].value)
        elif p[0].gettokentype() == "HEXBITVECTOR":
            return BitVectorConstant(p[0].value)
        elif p[0].gettokentype() == "NUMBER":
            return Number(int(p[0].value))
    elif len(p) == 2:
        if p[0].gettokentype() == "LPAREN":
            return Unit()
        elif p[0].gettokentype() == "AMPERSAND":
            return RefOf(p[1])
        elif p[0].gettokentype() == "STRUCT":
            return p[1]
    elif len(p) == 3:
        if p[1].gettokentype() == "COLON":
            return Undefined(p[2])
        elif p[1].gettokentype() == "DOT":
            return FieldAccess(p[0], p[2].value)
        elif p[1].gettokentype() == "AS":
            return Cast(p[0], p[2].value)
    assert 0

@pg.production('structconstruction : NAME LBRACE structconstructioncontent RBRACE')
def structconstruction(p):
    return StructConstruction(p[0].value, p[2].fieldnames, p[2].fieldvalues)

@pg.production('structconstructioncontent : structfield | structfield COMMA structconstructioncontent')
def structconstructioncontent(p):
    if len(p) == 1:
        return StructConstruction(None, [p[0].fieldname], [p[0].fieldvalue])
    else:
        return StructConstruction(None, [p[0].fieldname] + p[2].fieldnames, [p[0].fieldvalue] + p[2].fieldvalues)

@pg.production('structfield : NAME EQUAL expr')
def structfield(p):
    return StructField(p[0].value, p[2])


@pg.production('conditionaljump : JUMP condition GOTO NUMBER')
def conditionaljump(p):
    return ConditionalJump(p[1], int(p[3].value))

@pg.production('condition : expr | NAME LPAREN opargs RPAREN | expr IS NAME ')
def condition(p):
    if len(p) == 1:
        return ExprCondition(p[0])
    if len(p) == 4:
        return Comparison(p[0].value, p[2].args)
    return UnionVariantCheck(p[0], p[2].value)

@pg.production('goto : GOTO NUMBER')
def op(p):
    return Goto(int(p[1].value))

@pg.production('assignment : NAME EQUAL expr | NAME STAR EQUAL expr | NAME DOT NAME EQUAL expr')
def op(p):
    if len(p) == 3:
        return Assignment(p[0].value, p[2])
    if len(p) == 4:
        return RefAssignment(p[0].value, p[3])
    else:
        assert p[2].gettokentype() == "NAME"
        return StructElementAssignment(Var(p[0].value), p[2].value, p[4])


@pg.production('end : END')
def end(p):
    return End()

@pg.production('exit : EXIT NAME')
def exit(p):
    return Exit(p[1].value)

@pg.production('arbitrary : ARBITRARY')
def arbitrary(p):
    return Arbitrary()



# types

@pg.production('type : simpletype  | functiontype')
def typ(p):
    return p[0]

@pg.production('simpletype : namedtype | tupletype | enumtype | uniontype | structtype | reftype | vectype | fvectype | listtype')
def simpletype(p):
    return p[0]

@pg.production('namedtype : NAME')
def namedtype(p):
    return NamedType(p[0].value)

@pg.production('tupletype : LPAREN tupletypecontent RPAREN')
def tupletype(p):
    return p[1]

@pg.production('tupletypecontent : type | type COMMA tupletypecontent')
def tupletypecontent(p):
    if len(p) == 1:
        return TupleType([p[0]])
    else:
        return TupleType([p[0]] + p[2].elements)

@pg.production('enumtype : PERCENTENUM NAME')
def enumtype(p):
    return EnumType(p[1].value)

@pg.production('uniontype : PERCENTUNION NAME')
def uniontype(p):
    return UnionType(p[1].value)

@pg.production('structtype : PERCENTSTRUCT NAME')
def structtype(p):
    return StructType(p[1].value)

@pg.production('listtype : PERCENTLIST type')
def listtype(p):
    return ListType(p[1])

@pg.production('functiontype : simpletype ARROW simpletype')
def functiontype(p):
    return FunctionType(p[0], p[2])

@pg.production('reftype : AMPERSAND LPAREN structtype RPAREN')
def reftype(p):
    return RefType(p[2])

@pg.production('vectype : PERCENTVEC LPAREN simpletype RPAREN')
def vectype(p):
    return VecType(p[2])

@pg.production('fvectype : PERCENTFVEC LPAREN NUMBER COMMA simpletype RPAREN')
def fvectype(p):
    return FVecType(int(p[2].value), p[4])


def print_conflicts():
    if parser.lr_table.rr_conflicts:
        print("rr conflicts")
    for rule_num, token, conflict in parser.lr_table.rr_conflicts:
        print(rule_num, token, conflict)

    if parser.lr_table.sr_conflicts:
        print("sr conflicts")
    for rule_num, token, conflict in parser.lr_table.sr_conflicts:
        print(rule_num, token, conflict)

parser = pg.build()
print_conflicts()


