from contextlib import contextmanager

from pydrofoil import parse, types

class TypingContext(object):
    def __init__(self):
        self.globalnames = {}
        self.namedtypes = {}
        self.tuplestruct = {}
        self.localnames = None
        self.add_global_name("false", types.Bool())
        self.add_global_name("true", types.Bool())
        self.add_global_name("bitzero", types.Bit())
        self.add_global_name("bitone", types.Bit())
        self.add_global_name("have_exception", types.Bool())
        self.add_global_name("NULL", types.NullType())
        self.add_global_name("throw_location", types.String())

    def add_named_type(self, name, typ):
        assert isinstance(typ, types.Type)
        assert name not in self.namedtypes
        self.namedtypes[name] = typ

    def get_named_type(self, name):
        return self.namedtypes[name]

    def add_global_name(self, name, typ):
        assert isinstance(typ, types.Type)
        self.globalnames[name] = typ

    def add_local_name(self, name, typ):
        assert isinstance(typ, types.Type)
        self.localnames[name] = typ

    def gettyp(self, name):
        if self.localnames is None or name not in self.localnames:
            return self.globalnames[name]
        return self.localnames[name]


    @contextmanager
    def enter_scope(self):
        old_localnames = self.localnames
        self.localnames = {}
        yield
        self.localnames = old_localnames


class TypeAttachingVisitor(parse.Visitor):
    def __init__(self, context):
        self.context = context

    def default_visit(self, ast):
        import pdb; pdb.set_trace()
        assert not isinstance(ast, parse.Expression) # need cases for all of these!
        return parse.Visitor.default_visit(self, ast)

    def visit_File(self, ast):
        for decl in ast.declarations:
            self.visit(decl)

    def visit_GlobalVal(self, ast):
        typ = ast.resolved_type = self.visit(ast.typ)
        self.context.add_global_name(ast.name, typ)

    def visit_Abstract(self, ast):
        typ = ast.resolved_type = self.visit(ast.typ)
        self.context.add_global_name(ast.name, typ)

    def visit_Let(self, ast):
        typ = ast.resolved_type = self.visit(ast.typ)
        self.context.add_global_name(ast.name, typ)
        with self.context.enter_scope():
            for stmt in ast.body:
                self.visit(stmt)

    def visit_Enum(self, ast):
        typ = ast.resolve_type(None)
        for name in ast.names:
            self.context.add_global_name(name, typ)
        self.context.add_named_type(ast.name, typ)

    def visit_Union(self, ast):
        uniontyp = types.Union(ast.name, tuple(ast.names), tuple(self.visit(typ) for typ in ast.types))
        self.context.add_named_type(ast.name, uniontyp)
        if ast.name == "zexception":
            self.context.add_global_name("current_exception", uniontyp)

    def visit_Struct(self, ast):
        tuplestruct = ast.name in self.context.tuplestruct
        structtyp = types.Struct(ast.name, tuple(ast.names), tuple(self.visit(typ) for typ in ast.types), tuplestruct)
        self.context.add_named_type(ast.name, structtyp)

    def visit_Pragma(self, ast):
        if ast.name == 'tuplestruct':
            self.context.tuplestruct[ast.content[0]] = ast

    def visit_Files(self, ast):
        pass

    def visit_Function(self, ast):
        with self.context.enter_scope():
            typ = self.context.globalnames[ast.name]
            ast.resolved_type = typ
            for arg, argtyp in zip(ast.args, typ.argtype.elements):
                self.context.add_local_name(arg, argtyp)
            self.context.add_local_name('return', typ.restype)
            for stmt in ast.body:
                self.visit(stmt)

    # statements

    def visit_LocalVarDeclaration(self, ast):
        typ = self.visit(ast.typ)
        ast.resolved_type = typ
        self.context.add_local_name(ast.name, typ)

    def visit_Assignment(self, ast):
        self.visit(ast.value)
        ast.resolved_type = self.context.gettyp(ast.result)

    def visit_Operation(self, ast):
        for arg in ast.args:
            self.visit(arg)
        ast.resolved_type = self.context.gettyp(ast.result)

    def visit_TemplatedOperation(self, ast):
        for arg in ast.args:
            self.visit(arg)
        ast.resolved_type = self.context.gettyp(ast.result)

    def visit_ConditionalJump(self, ast):
        self.visit(ast.condition)

    def visit_Register(self, ast):
        typ = self.visit(ast.typ)
        ast.resolved_type = typ
        self.context.add_global_name(ast.name, typ)
        if ast.body is not None:
            with self.context.enter_scope():
                for stmt in ast.body:
                    self.visit(stmt)

    def visit_StructElementAssignment(self, ast):
        self.visit(ast.obj)
        self.visit(ast.value)
        curr = ast.obj.resolved_type
        for field in ast.fields:
            curr = curr.fieldtyps[field]
        ast.resolved_type = curr

    def visit_RefAssignment(self, ast):
        self.visit(ast.ref)
        self.visit(ast.value)

    def visit_Goto(self, ast):
        pass

    def visit_End(self, ast):
        pass

    def visit_Exit(self, ast):
        pass

    def visit_Arbitrary(self, ast):
        pass

    def visit_GeneralAssignment(self, ast):
        lhs = ast.lhs # refassignment, structelementassignment with None as value
        if isinstance(lhs, parse.StructElementAssignment):
            self.visit(lhs.obj)
            curr = lhs.obj.resolved_type
            for field in lhs.fields:
                curr = curr.fieldtyps[field]
            lhs.resolved_type = curr
        elif isinstance(lhs, parse.RefAssignment):
            typ = self.visit(lhs.ref)
            lhs.resolved_type = typ.typ
        else:
            import pdb; pdb.set_trace()
        rhs = ast.rhs # Operation or TemplatedOperation (with None results)
        for arg in rhs.args:
            self.visit(arg)
        rhs.resolved_type = lhs.resolved_type # what about casts?

    # conditions

    def visit_Comparison(self, ast):
        for arg in ast.args:
            self.visit(arg)

    def visit_ExprCondition(self, ast):
        self.visit(ast.expr)

    def visit_UnionVariantCheck(self, ast):
        self.visit(ast.var)

    # expressions

    def visit_Var(self, ast):
        ast.resolved_type = self.context.gettyp(ast.name)
        return ast.resolved_type

    def visit_StructConstruction(self, ast):
        for expr in ast.fieldvalues:
            self.visit(expr)
        typ = self.context.namedtypes[ast.name]
        ast.resolved_type = typ
        return typ

    def visit_Cast(self, ast):
        self.visit(ast.expr)
        typ = ast.expr.resolved_type.variants[ast.variant]
        ast.resolved_type = typ
        return typ

    def visit_FieldAccess(self, ast):
        if isinstance(ast.obj, parse.StructConstruction):
            index = ast.obj.fieldnames.index(ast.element)
            restyp = self.visit(ast.obj.fieldvalues[index])
        else:
            typ = self.visit(ast.obj)
            restyp = typ.fieldtyps[ast.element]
        ast.resolved_type = restyp
        return restyp

    def visit_RefOf(self, ast):
        typ = types.Ref(self.visit(ast.expr))
        ast.resolved_type = typ
        return typ

    def visit_String(self, ast):
        ast.resolved_type = res = types.String()
        return res

    def visit_BitVectorConstant(self, ast):
        if ast.constant.startswith("0b"):
            size = len(ast.constant) - 2
        else:
            assert ast.constant.startswith("0x")
            size = (len(ast.constant) - 2) * 4
        if size <= 64:
            typ = types.SmallFixedBitVector(size)
        else:
            typ = types.BigFixedBitVector(size)
        ast.resolved_type = res = typ
        return res

    def visit_Number(self, ast):
        ast.resolved_type = res = types.MachineInt()
        return res

    def visit_Unit(self, ast):
        ast.resolved_type = res = types.Unit()
        return res

    # types

    def visit_NamedType(self, ast):
        name = ast.name
        if name == "%bool":
            return types.Bool()
        if name == "%i":
            return types.Int()
        if name == "%bv":
            return types.GenericBitVector()
        if name.startswith("%bv"):
            size = int(name[3:])
            if size <= 64:
                return types.SmallFixedBitVector(size)
            else:
                return types.BigFixedBitVector(size)
        if name == "%unit":
            return types.Unit()
        if name == "%i64":
            return types.MachineInt()
        if name == "%bit":
            return types.Bit()
        if name == "%string":
            return types.String()
        if name == "%real":
            return types.Real()
        assert False, "unknown type"

    def visit_EnumType(self, ast):
        return self.context.get_named_type(ast.name)

    def visit_UnionType(self, ast):
        return self.context.get_named_type(ast.name)

    def visit_StructType(self, ast):
        return self.context.get_named_type(ast.name)

    def visit_ListType(self, ast):
        return types.List(self.visit(ast.typ))

    def visit_FunctionType(self, ast):
        return types.Function(self.visit(ast.argtype), self.visit(ast.restype))

    def visit_RefType(self, ast):
        return types.Ref(self.visit(ast.refto))

    def visit_VecType(self, ast):
        return types.Vec(self.visit(ast.of))

    def visit_FVecType(self, ast):
        return types.FVec(ast.number, self.visit(ast.of))

    def visit_TupleType(self, ast):
        return types.Tuple(tuple([self.visit(e) for e in ast.elements]))


def infer(ast):
    context = TypingContext()
    v = TypeAttachingVisitor(context)
    v.visit(ast)
    return context

