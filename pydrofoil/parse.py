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
addkeyword('failure')
addkeyword('goto')
addkeyword('jump')
addkeyword('register')
addkeyword('is')
addkeyword('as')
addkeyword('let')
addkeyword('undefined')

addtok('PERCENTENUM', r'%enum')
addtok('PERCENTUNION', r'%union')
addtok('PERCENTSTRUCT', r'%struct')
addtok('PERCENTVEC', r'%vec')

addtok('BINBITVECTOR', r'0b[01]+')
addtok('HEXBITVECTOR', r'0x[0-9a-fA-F]+')
addtok('NUMBER', r'-?\d+')
addtok('NAME', r'[a-zA-Z_%@$][a-zA-Z_0-9]*')
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
addtok('AMPERSAND', r'[&]')
addtok('STAR', r'[*]')

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
        visitor.visit(self)
        for key, value in self.__dict__.items():
            if isinstance(value, BaseAst):
                value.visit(visitor)
            elif isinstance(value, list) and value and isinstance(value[0], BaseAst):
                for item in value:
                    item.visit(visitor)


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
            elif isinstance(op, Failure):
                pass
            elif isinstance(op, Goto):
                dotgen.emit_edge(str(id(op)), str(id(self.body[op.target])))
            elif isinstance(op, ConditionalJump):
                dotgen.emit_edge(str(id(op)), str(id(self.body[op.target])), "false")
                dotgen.emit_edge(str(id(op)), str(id(self.body[index + 1])), "true")
            else:
                dotgen.emit_edge(str(id(op)), str(id(self.body[index + 1])))


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

class Condition(BaseAst):
    pass

class VarCondition(Condition):
    def __init__(self, name):
        self.name = name

class Comparison(Condition):
    def __init__(self, operation, args):
        self.operation = operation
        self.args = args

class UnionVariantCheck(Condition):
    def __init__(self, var, variant):
        self.var = var
        self.variant = variant

class Assignment(Statement):
    def __init__(self, result, value):
        self.result = result
        self.value = value

class TupleElementAssignment(Statement):
    def __init__(self, tup, index, value):
        self.tup = tup
        self.index = index
        self.value = value

class StructElementAssignment(Statement):
    def __init__(self, obj, field, value):
        self.obj = obj
        self.field = field
        self.value = value

class RefAssignment(Statement):
    def __init__(self, ref, value):
        self.ref = ref
        self.value = value

class End(Statement):
    pass

class Failure(Statement):
    pass

class Arbitrary(Statement):
    pass

class Expression(BaseAst):
    pass

class Var(Expression):
    def __init__(self, name):
        self.name = name

class Number(Expression):
    def __init__(self, number):
        self.number = number

class BitVectorConstant(Expression):
    def __init__(self, constant):
        self.constant = constant

class TupleElement(Expression):
    def __init__(self, tup, element):
        self.tup = tup
        self.element = element

class Cast(Expression):
    def __init__(self, expr, variant, field=None):
        self.expr = expr
        self.variant = variant
        self.field = field

class RefOf(Expression):
    def __init__(self, expr):
        self.expr = expr

class String(Expression):
    def __init__(self, string):
        self.string = string

class Unit(Expression):
    pass

class Undefined(Expression):
    def __init__(self, typ):
        self.typ = typ


# ____________________________________________________________
# parser

pg = ParserGenerator(alltokens)

@pg.production('file : declaration | file declaration')
def file(p):
    if len(p) == 1:
        return File(p)
    return File(p[0].declarations + [p[1]])

@pg.production('declaration : enum | union | struct | globalval | function | register | let')
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

@pg.production('operations : operation SEMICOLON | operation SEMICOLON operations')
def operations(p):
    if len(p) == 2:
        return Function(None, None, [p[0]])
    else:
        return Function(None, None, [p[0]] + p[2].body)

# operations

@pg.production('operation : localvardeclaration | op | templatedop | conditionaljump | goto | assignment | end | failure | arbitrary')
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

@pg.production('opargs : expr | expr COMMA opargs')
def opargs(p):
    if len(p) == 1:
        return Operation(None, None, [p[0]])
    else:
        return Operation(None, None, [p[0]] + p[2].args)

@pg.production('expr : NAME | STRING | NUMBER | BINBITVECTOR | HEXBITVECTOR | UNDEFINED COLON type | NAME DOT NAME | LPAREN RPAREN | NAME AS NAME | NAME AS NAME DOT NAME | AMPERSAND NAME')
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
            return RefOf(p[0].value)
    elif len(p) == 3:
        if p[1].gettokentype() == "COLON":
            return Undefined(p[2])
        elif p[1].gettokentype() == "DOT":
            return TupleElement(Var(p[0].value), p[2].value)
        elif p[1].gettokentype() == "AS":
            return Cast(Var(p[0].value), p[2].value)
    elif len(p) == 5 and p[1].gettokentype() == "AS":
        return Cast(Var(p[0].value), p[2].value, p[4].value)
    assert 0

@pg.production('conditionaljump : JUMP condition GOTO NUMBER BACKTICK STRING')
def conditionaljump(p):
    return ConditionalJump(p[1], int(p[3].value), p[5].value)

@pg.production('condition : NAME | NAME LPAREN opargs RPAREN | expr IS NAME ')
def condition(p):
    if len(p) == 1:
        return VarCondition(p[0].value)
    if len(p) == 4:
        return Comparison(p[0].value, p[2].args)
    return UnionVariantCheck(p[0], p[2].value)

@pg.production('goto : GOTO NUMBER')
def op(p):
    return Goto(int(p[1].value))

@pg.production('assignment : NAME EQUAL expr | NAME STAR EQUAL expr | NAME DOT NUMBER EQUAL expr | NAME DOT NAME EQUAL expr')
def op(p):
    if len(p) == 3:
        return Assignment(p[0].value, p[2])
    if len(p) == 4:
        return RefAssignment(p[0].value, p[3])
    elif p[2].gettokentype() == "NUMBER":
        return TupleElementAssignment(p[0].value, int(p[2].value), p[4])
    else:
        assert p[2].gettokentype() == "NAME"
        return StructElementAssignment(p[0].value, p[2].value, p[4])


@pg.production('end : END')
def end(p):
    return End()

@pg.production('failure : FAILURE')
def failure(p):
    return Failure()

@pg.production('arbitrary : ARBITRARY')
def arbitrary(p):
    return Arbitrary()



# types

@pg.production('type : simpletype  | functiontype')
def typ(p):
    return p[0]

@pg.production('simpletype : namedtype | tupletype | enumtype | uniontype | structtype | reftype | vectype')
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

@pg.production('functiontype : simpletype ARROW simpletype')
def functiontype(p):
    return FunctionType(p[0], p[2])

@pg.production('reftype : AMPERSAND LPAREN structtype RPAREN')
def reftype(p):
    return RefType(p[2])

@pg.production('vectype : PERCENTVEC LPAREN simpletype RPAREN')
def vectype(p):
    return VecType(p[2])


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


