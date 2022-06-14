from rpysail.parse import Visitor

class Info(object):
    def __init__(self):
        self.typ = None
        self.value = None
        self.ast = None

class ResolveNamesVisitor(Visitor):
    def __init__(self):
        self.names = {} # string -> Info
        self.current_function = None

    def getinfo(self, name):
        return self.names[name]

    def addinfo(self, name):
        assert name not in self.names
        res = self.names[name] = Info()
        return res

    def visit_GlobalVal(self, ast):
        info = self.addinfo(ast.name)
        info.typ = ast.typ
        info.value = ast.definition
        info.ast = ast

    def visit_Enum(self, ast):
        info = self.addinfo(ast.name)
        info.typ = ast
        for index, name in enumerate(ast.names):
            info = self.addinfo(name)
            info.value = index
            info.ast = ast

    def visit_Union(self, ast):
        info = self.addinfo(ast.name)
        info.typ = ast
        info.ast = ast
        for name, typ in zip(ast.names, ast.types):
            info = self.addinfo(name)
            info.typ = typ
            info.ast = ast

    def visit_EnumType(self, ast):
        info = self.getinfo(ast.name)
        ast.definition = info

    def visit_UnionType(self, ast):
        info = self.getinfo(ast.name)
        ast.definition = info

    def visit_LocalVarDeclaration(self, ast):
        info = self.current_function.localtypes[ast.name] = Info()
        info.typ = ast.typ

    def visit_Function(self, ast):
        info = self.getinfo(ast.name)
        info.value = ast
        self.current_function = ast
        ast.localtypes = {}
        if ast.args:
            for typ, arg in zip(info.typ.argtype.elements, ast.args):
                info = ast.localtypes[arg] = Info()
                info.typ = typ


