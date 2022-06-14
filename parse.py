from rply import LexerGenerator, LexingError, ParserGenerator
from rply.token import BaseBox

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
addkeyword('val')
addkeyword('fn')
addkeyword('end')
addkeyword('failure')
addkeyword('goto')
addkeyword('jump')

addtok('PERCENTENUM', r'%enum')
addtok('PERCENTUNION', r'%union')

addtok('NUMBER', r'(0b)?\d+')
addtok('NAME', r'[a-zA-Z_%@][a-zA-Z_0-9]*')
addtok('STRING', r'"[^"]*"')
addtok('ARROW', r'->')
addtok('BACKTICK', r'`')
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

lg.ignore(r'[ \n]')

lexer = lg.build()


# ____________________________________________________________
# AST classes

class BaseAst(BaseBox):
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

class File(BaseAst):
    def __init__(self, declarations, sourcepos=None):
        self.declarations = declarations

class Declaration(BaseAst):
    pass

class Enum(Declaration):
    def __init__(self, name, values, sourcepos=None):
        self.name = name
        self.values = values

    def __repr__(self):
        return "Enum(%r, %r)" % (self.name, self.values)


class Union(Declaration):
    def __init__(self, name, types, sourcepos=None):
        self.name = name
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

class Function(Declaration):
    def __init__(self, name, arguments, body, sourcepos=None):
        self.name = name
        self.arguments = arguments
        self.body = body

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

class FunctionType(Type):
    def __init__(self, argtype, restype):
        self.argtype = argtype
        self.restype = restype

class Function(Declaration):
    def __init__(self, name, args, body):
        self.name = name
        self.args = args
        self.body = body

class Statement(BaseAst):
    pass

class LocalVarDeclaration(Statement):
    def __init__(self, name, typ, value=None):
        self.name = name
        self.typ = typ
        self.value = value

class Operation(Statement):
    def __init__(self, result, name, args):
        self.result = result
        self.name = name
        self.args = args

class TemplatedOperation(Statement):
    def __init__(self, result, name, templateparam, args):
        self.result = result
        self.name = name
        self.templateparam = templateparam
        self.args = args

class Goto(Statement):
    def __init__(self, target):
        self.target = target

class ConditionalJump(Statement):
    def __init__(self, condition, target, sourcecomment):
        self.condition = condition
        self.target = target
        self.sourcecomment = sourcecomment

class ConditionalJumpComparison(Statement):
    def __init__(self, operation, args, target, sourcecomment):
        self.operation = operation
        self.args = args
        self.target = target
        self.sourcecomment = sourcecomment

class Assignment(Statement):
    def __init__(self, result, value):
        self.result = result
        self.value = value

class End(Statement):
    pass

class Failure(Statement):
    pass
        
class Expression(BaseAst):
    pass

class Var(Expression):
    def __init__(self, name):
        self.name = name

class Number(Expression):
    def __init__(self, number):
        self.number = number

class TupleElement(Expression):
    def __init__(self, name, number):
        self.name = name
        self.number = number

# ____________________________________________________________
# parser

pg = ParserGenerator(alltokens)

@pg.production('file : declaration | file declaration')
def file(p):
    if len(p) == 1:
        return File(p)
    return File(p[0].declarations + [p[1]])

@pg.production('declaration : enum | union | globalval | function')
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
        return Enum(None, [p[0].value] + p[2].values)

@pg.production('union : UNION NAME LBRACE unioncontent RBRACE')
def union(p):
    p[3].name = p[1].value
    return p[3]

@pg.production('unioncontent : NAME COLON type | NAME COLON type COMMA unioncontent')
def unioncontent(p):
    if len(p) == 3:
        return Union(None, [(p[0].value, p[2])])
    else:
        return Union(None, [(p[0].value, p[2])] + p[4].types)

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

@pg.production('operations : operation SEMICOLON | operation SEMICOLON operations')
def operations(p):
    if len(p) == 2:
        return Function(None, None, [p[0]])
    else:
        return Function(None, None, [p[0]] + p[2].body)

# operations

@pg.production('operation : localvardeclaration | op | templatedop | conditionaljump | goto | assignment | end | failure')
def operation(p):
    return p[0]

@pg.production('localvardeclaration : NAME COLON type | NAME COLON type EQUAL expr')
def localvardeclaration(p):
    if len(p) == 3:
        return LocalVarDeclaration(p[0].value, p[2])
    return LocalVarDeclaration(p[0].value, p[2], p[4])


@pg.production('op : NAME EQUAL NAME LPAREN opargs RPAREN')
def op(p):
    return Operation(p[0].value, p[2].value, p[4].args)

@pg.production('templatedop : NAME EQUAL NAME COLON COLON LT expr GT LPAREN opargs RPAREN')
def op(p):
    return TemplatedOperation(p[0].value, p[2].value, p[6], p[9].args)

@pg.production('opargs : LPAREN RPAREN | opargs_')
def opargs(p):
    if len(p) == 2:
        return Operation(None, None, [])
    return p[0]

@pg.production('opargs_ : expr | expr COMMA opargs_')
def opargs_(p):
    if len(p) == 1:
        return Operation(None, None, [p[0]])
    else:
        return Operation(None, None, [p[0]] + p[2].args)

@pg.production('expr : NAME | NUMBER')
def expr(p):
    if p[0].gettokentype() == "NAME":
        return Var(p[0].value)
    return Number(p[0].value)


@pg.production('conditionaljump : JUMP NAME GOTO NUMBER BACKTICK STRING | JUMP NAME LPAREN opargs RPAREN GOTO NUMBER BACKTICK STRING')
def op(p):
    if len(p) == 6:
        return ConditionalJump(p[1].value, int(p[3].value), p[5].value)
    return ConditionalJumpComparison(p[1].value, p[3].args, int(p[6].value), p[8].value)

@pg.production('goto : GOTO NUMBER')
def op(p):
    return Goto(int(p[1].value))

@pg.production('assignment : NAME EQUAL NAME')
def op(p):
    return Assignment(p[0].value, p[2].value)

@pg.production('lhs : NAME | NAME DOT NUMBER')
def op(p):
    if len(p) == 1:
        return Var(p[0].value)
    return TupleElement(p[0].value, int(p[2].value))

@pg.production('end : END')
def end(p):
    return End()

@pg.production('failure : FAILURE')
def failure(p):
    return Failure()



# types

@pg.production('type : namedtype | tupletype | enumtype | uniontype | functiontype')
def typ(p):
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

@pg.production('functiontype : type ARROW type')
def functiontype(p):
    return FunctionType(p[0], p[2])

parser = pg.build()
