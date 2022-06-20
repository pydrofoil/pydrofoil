from rpython.tool.pairtype import pair

from pydrofoil import parse, types, binaryop, operations
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
        self.runtimeinit = []
        self.code = []
        self.level = 0
        self.last_enum = 0
        self.globalnames = {}
        self.namedtypes = {}
        self.declarationcache = {}
        self.gensym = {} # prefix -> number
        self.localnames = None
        self.add_global("false", "False", types.Bool())
        self.add_global("true", "True", types.Bool())
        self.add_global("bitzero", "rarithmetic.r_uint(0)", types.Bit())
        self.add_global("bitone", "rarithmetic.r_uint(1)", types.Bit())
        self.add_global("$zupdate_fbits", "supportcode.update_fbits")
        self.add_global("have_exception", "l.have_exception", types.Bool())
        self.add_global("throw_location", "l.throw_location", types.String())
        self.add_global("zsail_assert", "supportcode.sail_assert")
        self.add_global("NULL", "None")
        self.declared_types = set()

    def add_global(self, name, pyname, typ=None, ast=None):
        assert isinstance(typ, types.Type) or typ is None
        if name in self.globalnames:
            assert isinstance(ast, parse.GlobalVal)
            assert ast == self.globalnames[name].ast
            return
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
        if ast:
            ast.localnames = self.localnames
        self.localnames = old_localnames

    @contextmanager
    def emit_indent(self, line):
        self.emit(line)
        self.level += 1
        yield
        self.level -= 1

    @contextmanager
    def emit_code_type(self, attr):
        oldlevel = self.level
        self.level = 0
        oldcode = self.code
        self.code = getattr(self, attr)
        yield
        assert self.level == 0
        self.code = oldcode
        self.level = oldlevel

    def emit(self, line=''):
        if not line.strip():
            self.code.append('')
        else:
            self.code.append("    " * self.level + line)

    def emit_declaration(self, line):
        self.declarations.append(line)

    @contextmanager
    def cached_declaration(self, key, nameprefix):
        tup = key, nameprefix
        if tup in self.declarationcache:
            self.dummy = []
            with self.emit_code_type("dummy"):
                yield self.declarationcache[tup]
        else:
            num = self.gensym.get(nameprefix, 0) + 1
            self.gensym[nameprefix] = num
            name = self.declarationcache[tup] = "%s_%s" % (nameprefix, num)
            with self.emit_code_type("declarations"):
                yield name

    def getcode(self):
        res = ["\n".join(self.declarations)]
        res.append("def model_init():\n    " + "\n    ".join(self.runtimeinit or ["pass"]))
        res.append("\n".join(self.code))
        return "\n\n\n".join(res)


def parse_and_make_code(s, supportcodename="supportcode"):
    ast = parse.parser.parse(parse.lexer.lex(s))
    c = Codegen()
    with c.emit_code_type("declarations"):
        c.emit("from rpython.rlib.rbigint import rbigint")
        c.emit("from rpython.rlib import rarithmetic")
        c.emit("import operator")
        c.emit("from pydrofoil.test import %s as supportcode" % supportcodename)
        c.emit("from pydrofoil import bitvector")
        c.emit("class Registers(object): pass")
        c.emit("r = Registers()")
        c.emit("class Lets(object): pass")
        c.emit("l = Lets()")
        c.emit("l.have_exception = False")
        c.emit("l.throw_location = None")
        c.emit("l.current_exception = None")
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
            codegen.emit()

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
            typ = types.Enum(self)
            codegen.add_named_type(self.name, self.pyname, typ, self)
            typ.uninitialized_value = "-1"

class __extend__(parse.Union):
    def make_code(self, codegen):
        name = "Union_" + self.name
        self.pyname = name
        for typ in self.types:
            typ.resolve_type(codegen) # pre-declare the types
        with codegen.emit_code_type("declarations"):
            with codegen.emit_indent("class %s(object):" % name):
                codegen.emit("pass")
            self.pynames = []
            uniontyp = types.Union(self)
            uniontyp.uninitialized_value = "%s()" % (self.pyname, )
            codegen.add_named_type(self.name, self.pyname, uniontyp, self)
            for name, typ in zip(self.names, self.types):
                pyname = self.pyname + "_" + name
                codegen.add_global(name, pyname, uniontyp, self)
                self.pynames.append(pyname)
                with codegen.emit_indent("class %s(%s):" % (pyname, self.pyname)):
                    rtyp = typ.resolve_type(codegen)
                    codegen.emit("a = %s" % (rtyp.uninitialized_value, ))
                    # XXX could special-case tuples here, and unit
                    with codegen.emit_indent("def __init__(self, a):"):
                        codegen.emit("self.a = a # %s" % (typ, ))
                    codegen.emit("@staticmethod")
                    with codegen.emit_indent("def convert(inst):"):
                        with codegen.emit_indent("if isinstance(inst, %s):" % pyname):
                            codegen.emit("return inst")
                        with codegen.emit_indent("else:"):
                            codegen.emit("raise TypeError")
        if self.name == "zexception":
            codegen.add_global("current_exception", "l.current_exception", uniontyp, self)

class __extend__(parse.Struct):
    def make_code(self, codegen):
        name = "Struct_" + self.name
        self.pyname = name
        structtyp = types.Struct(self)
        structtyp.fieldtyps = {}
        uninit_arg = []
        codegen.add_named_type(self.name, self.pyname, structtyp, self)
        with codegen.emit_code_type("declarations"), codegen.emit_indent("class %s(object):" % name):
            with codegen.emit_indent("def __init__(self, %s):" % ", ".join(self.names)):
                for arg, typ in zip(self.names, self.types):
                    codegen.emit("self.%s = %s # %s" % (arg, arg, typ))
                    fieldtyp = structtyp.fieldtyps[arg] = typ.resolve_type(codegen)
                    uninit_arg.append(fieldtyp.uninitialized_value)
            with codegen.emit_indent("def copy_into(self, res=None):"):
                codegen.emit("if res is None: res = type(self)()")
                for arg, typ in zip(self.names, self.types):
                    codegen.emit("res.%s = self.%s # %s" % (arg, arg, typ))
                codegen.emit("return res")
        structtyp.uninitialized_value = "%s(%s)" % (self.pyname, ", ".join(uninit_arg))

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
        typ = self.typ.resolve_type(codegen)
        pyname = "r.%s" % self.name
        codegen.add_global(self.name, pyname, typ, self)
        with codegen.emit_code_type("declarations"):
            codegen.emit("# %s" % (self, ))
            codegen.emit("%s = %s" % (pyname, typ.uninitialized_value))


class __extend__(parse.Function):
    def make_code(self, codegen):
        pyname = "func_" + self.name
        if codegen.globalnames[self.name].pyname is not None:
            print "duplicate!", self.name, codegen.globalnames[self.name].pyname
            return
        codegen.update_global_pyname(self.name, pyname)
        typ = codegen.globalnames[self.name].typ
        self.pyname = pyname
        args = self.args
        with codegen.emit_indent("def %s(%s):" % (pyname, ", ".join(args))):
            with codegen.enter_scope(self):
                codegen.add_local('return', 'return_', typ.restype, self)
                for i, arg in enumerate(args):
                    codegen.add_local(arg, arg, typ.argtype.elements[i], self)
                entrycounts = {0: 1} # pc, count
                for i, op in enumerate(self.body):
                    if isinstance(op, (parse.Goto, parse.ConditionalJump)):
                        entrycounts[op.target] = entrycounts.get(op.target, 0) + 1
                if entrycounts == {0: 1}:
                    assert self.body[-1].end_of_block
                    self.emit_block_ops(self.body, codegen)
                else:
                    blocks = {}
                    for i, op in enumerate(self.body):
                        if i in entrycounts:
                            blocks[i] = block = []
                        block.append(op)
                    for blockpc, block in sorted(blocks.items()):
                        lastop = block[-1]
                        if lastop.end_of_block:
                            continue
                        # insert goto at the end to make have no "fall throughs"
                        block.append(parse.Goto(blockpc + len(block)))
                    if self.detect_union_switch(blocks[0]) and entrycounts[0] == 1:
                        print "making method!", self.name
                        codegen.emit("return %s.meth_%s(%s)" % (self.args[0], self.name, ", ".join(self.args[1:])))
                        codegen.level -= 1
                        self._emit_methods(blocks, entrycounts, codegen)
                        codegen.level += 1
                        return
                    codegen.emit("pc = 0")
                    with codegen.emit_indent("while 1:"):
                        for blockpc, block in sorted(blocks.items()):
                            if block == [None]:
                                # inlined
                                continue
                            with codegen.emit_indent("if pc == %s:" % blockpc):
                                self.emit_block_ops(block, codegen, entrycounts, blockpc, blocks)
        codegen.emit()

    def _find_first_non_decl(self, block):
        # return first operation that's not a declaration
        for op in block:
            if isinstance(op, parse.LocalVarDeclaration):
                continue
            return op

    def detect_union_switch(self, block):
        # heuristic: if the function starts with a switch on the first
        # argument, turn it into a method
        op = self._find_first_non_decl(block)
        if (isinstance(op, parse.ConditionalJump) and 
                isinstance(op.condition, parse.UnionVariantCheck) and
                isinstance(op.condition.var, parse.Var) and
                op.condition.var.name == self.args[0]):
            return op
        else:
            return None

    def _emit_methods(self, blocks, entrycounts, codegen):
        uniontyp = codegen.gettyp(self.args[0])
        switches = []
        curr_block = blocks[0]
        curr_offset = 0
        while 1:
            op = self.detect_union_switch(curr_block)
            if op is None or entrycounts[op.target] != 1:
                switches.append((curr_block, None))
                break
            switches.append((curr_block, op))
            curr_block = blocks[op.target]
        for i, (block, cond) in enumerate(switches):
            copyblock = []
            # add all var declarations of all the previous blocks
            for prevblock, prevcond in switches[:i]:
                copyblock.extend(prevblock[:prevblock.index(prevcond)])
            # now add all operations except the condition
            b = block[:]
            if cond:
                del b[block.index(cond)]
            copyblock.extend(b)
            graph = self._find_reachable(copyblock, blocks)
            local_blocks = {k: v for k, v in graph}
            # recompute entrycounts
            local_entrycounts = {0: 1}
            for pc, block in graph:
                for op in block:
                    if isinstance(op, (parse.Goto, parse.ConditionalJump)):
                        local_entrycounts[op.target] = local_entrycounts.get(op.target, 0) + 1
            # emit
            pyname = self.name + "_" + (cond.condition.variant if cond else "default")
            with codegen.enter_scope(None), codegen.emit_indent("def %s(%s):" % (pyname, ", ".join(self.args))):
                typ = codegen.globalnames[self.name].typ
                codegen.add_local('return', 'return_', typ.restype, self)
                for i, arg in enumerate(self.args):
                    codegen.add_local(arg, arg, typ.argtype.elements[i], self)
                codegen.emit("pc = 0")
                with codegen.emit_indent("while 1:"):
                    for blockpc, block in graph:
                        if block == [None]:
                            # inlined
                            continue
                        with codegen.emit_indent("if pc == %s:" % blockpc):
                            self.emit_block_ops(block, codegen, local_entrycounts, blockpc, local_blocks)
            if cond is not None:
                clsname = codegen.getname(cond.condition.variant)
            else:
                clsname = uniontyp.ast.pyname
            codegen.emit("%s.meth_%s = %s" % (clsname, self.name, pyname))
        with codegen.emit_indent("def %s(%s):" % (self.pyname, ", ".join(self.args))):
            codegen.emit("return %s.meth_%s(%s)" % (self.args[0], self.name, ", ".join(self.args[1:])))

    def _find_reachable(self, block, blocks):
        def process(index, current):
            res.append((index, current[:]))
            for op in current:
                if isinstance(op, (parse.Goto, parse.ConditionalJump)):
                    if op.target not in added:
                        added.add(op.target)
                        todo.append(op.target)
        added = set()
        res = []
        todo = []
        process(0, block)
        while todo:
            index = todo.pop()
            current = blocks[index]
            process(index, current)
        return res


    def emit_block_ops(self, block, codegen, entrycounts=(), offset=0, blocks=None):
        for i, op in enumerate(block):
            if (isinstance(op, parse.LocalVarDeclaration) and
                    i + 1 < len(block) and
                    isinstance(block[i + 1], parse.Assignment) and
                    op.name == block[i + 1].result):
                op.make_op_code(codegen, False)
            elif isinstance(op, parse.ConditionalJump):
                with codegen.emit_indent("if %s:" % (op.condition.to_code(codegen))):
                    if entrycounts[op.target] == 1:
                        # can inline!
                        codegen.emit("# inline pc=%s" % op.target)
                        self.emit_block_ops(blocks[op.target], codegen, entrycounts, op.target, blocks)
                        blocks[op.target][:] = [None]
                    else:
                        codegen.emit("pc = %s" % (op.target, ))
                    codegen.emit("continue")
                continue
            elif isinstance(op, parse.Goto):
                codegen.emit("pc = %s" % (op.target, ))
                if op.target < i:
                    codegen.emit("continue")
                return
            else:
                codegen.emit("# %s" % (op, ))
                op.make_op_code(codegen)
            if op.end_of_block:
                return

class __extend__(parse.Let):
    def make_code(self, codegen):
        codegen.emit("# %s" % (self, ))
        codegen.add_global(self.name, "l.%s" % self.name, self.typ.resolve_type(codegen), self)
        with codegen.emit_code_type("runtimeinit"), codegen.enter_scope(self):
            codegen.emit(" # let %s : %s" % (self.name, self.typ, ))
            for i, op in enumerate(self.body):
                codegen.emit("# %s" % (op, ))
                op.make_op_code(codegen)
            codegen.emit()

# ____________________________________________________________
# operations

class __extend__(parse.Statement):
    def make_op_code(self, codegen):
        raise NotImplementedError

    def make_op_jump(self, codegen, i):
        pass


class __extend__(parse.LocalVarDeclaration):
    def make_op_code(self, codegen, need_default_init=True):
        codegen.emit("# %s: %s" % (self.name, self.typ))
        typ = self.typ.resolve_type(codegen)
        codegen.add_local(self.name, self.name, typ, self)
        if self.value is not None:
            result = codegen.gettarget(self.name)
            othertyp = self.value.gettyp(codegen)
            rhs = pair(othertyp, typ).convert(self.value, codegen)
            codegen.emit("%s = %s" % (result, rhs))
        elif need_default_init:
            assert self.value is None
            # need to make a tuple instance
            result = codegen.gettarget(self.name)
            codegen.emit("%s = %s" % (result, typ.uninitialized_value))

class __extend__(parse.Operation):
    def make_op_code(self, codegen):
        name = self.name
        result = codegen.gettarget(self.result)
        sargs = [arg.to_code(codegen) for arg in self.args]
        argtyps = [arg.gettyp(codegen) for arg in self.args]
        if name.startswith("@"):
            codegen.emit("%s = %s" % (result,
                getattr(argtyps[0], "make_op_code_special_" + name[1:])(self, sargs, argtyps)))
            return
        elif name.startswith("$zcons"): # magic list cons stuff
            restyp = codegen.gettyp(self.result)
            codegen.emit("%s = %s(%s, %s)" % (result, restyp.pyname, sargs[0], sargs[1]))
            return
        elif name.startswith("$zinternal_vector_init"): # magic vector stuff
            oftyp = codegen.localnames[self.result].typ.typ
            codegen.emit("%s = [%s] * %s" % (result, oftyp.uninitialized_value, sargs[0]))
            return
        elif name.startswith("$zinternal_vector_update"):
            codegen.emit("%s = supportcode.vector_update_inplace(%s, %s, %s, %s)" % (result, result, sargs[0], sargs[1], sargs[2]))
            return

        op = codegen.getname(name)
        if not sargs:
            args = '()'
        else:
            args = ", ".join(sargs)
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
        if self.target < i:
            codegen.emit("continue")

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

class __extend__(parse.StructElementAssignment):
    def make_op_code(self, codegen):
        typ = codegen.gettyp(self.obj).fieldtyps[self.field]
        othertyp = self.value.gettyp(codegen)
        rhs = pair(othertyp, typ).convert(self.value, codegen)
        codegen.emit("%s.%s = %s" % (self.obj, self.field, rhs))

class __extend__(parse.RefAssignment):
    def make_op_code(self, codegen):
        # XXX think long and hard about refs!
        codegen.emit("%s.copy_into(%s)" % (self.value.to_code(codegen), self.ref))

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

class __extend__(parse.Arbitrary):
    def make_op_code(self, codegen):
        codegen.emit("raise ValueError")

    def make_op_jump(self, codegen, i):
        pass

class __extend__(parse.TemplatedOperation):
    def make_op_code(self, codegen):
        typ = self.args[0].gettyp(codegen)
        name = self.name
        if name.startswith("@"):
            op = getattr(typ, "make_op_code_templated_" + name[1:])(self, codegen)
            result = codegen.gettarget(self.result)
            codegen.emit("%s = %s" % (result, op))
            return
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
        return str(self.number)

    def gettyp(self, codegen):
        return types.MachineInt()

class __extend__(parse.BitVectorConstant):
    def to_code(self, codegen):
        return "rarithmetic.r_uint(%s)" % (self.constant, )

    def gettyp(self, codegen):
        if self.constant.startswith("0b"):
            return types.FixedBitVector(len(self.constant) - 2)
        assert self.constant.startswith("0x")
        return types.FixedBitVector((len(self.constant) - 2) * 4)

class __extend__(parse.Unit):
    def to_code(self, codegen):
        return '()'

    def gettyp(self, codegen):
        return types.Unit()

class __extend__(parse.Undefined):
    def to_code(self, codegen):
        return 'xxx'

    def gettyp(self, codegen):
        return self.typ.resolve_type(codegen)

class __extend__(parse.FieldAccess):
    def to_code(self, codegen):
        return "%s.%s" % (self.obj.to_code(codegen), self.element)

    def gettyp(self, codegen):
        objtyp = self.obj.gettyp(codegen)
        if isinstance(objtyp, types.Tuple):
            assert self.element.startswith("ztup")
            return objtyp.elements[int(self.element[len('ztup'):])]
        return objtyp.fieldtyps[self.element]

class __extend__(parse.Cast):
    def to_code(self, codegen):
        expr = self.expr.to_code(codegen)
        return "(%s.convert(%s).a)" % (codegen.getname(self.variant), expr)

    def gettyp(self, codegen):
        # XXX clean up
        unionast = self.expr.gettyp(codegen).ast
        index = unionast.names.index(self.variant)
        typ = unionast.types[index].resolve_type(codegen)
        return typ

class __extend__(parse.RefOf):
    def to_code(self, codegen):
        expr = self.expr.to_code(codegen)
        assert isinstance(self.expr.gettyp(codegen), types.Struct)
        return expr

    def gettyp(self, codegen):
        return types.Ref(self.expr.gettyp(codegen))

class __extend__(parse.String):
    def to_code(self, codegen):
        return self.string

    def gettyp(self, codegen):
        return types.String()

# ____________________________________________________________
# conditions

class __extend__(parse.Condition):
    def to_code(self, codegen):
        raise NotImplementedError

class __extend__(parse.ExprCondition):
    def to_code(self, codegen):
        return self.expr.to_code(codegen)

class __extend__(parse.Comparison):
    def to_code(self, codegen):
        op = self.operation
        if op.startswith("@"):
            sargs = [arg.to_code(codegen) for arg in self.args]
            argtyps = [arg.gettyp(codegen) for arg in self.args]
            if hasattr(argtyps[0], "make_op_code_special_" + op[1:]):
                return getattr(argtyps[0], "make_op_code_special_" + op[1:])(self, sargs, argtyps)
            print "didn't find", op, argtyps, sargs
            op = "XXX_cmp_" + op[1:]
        return "%s(%s)" % (op, ", ".join([arg.to_code(codegen) for arg in self.args]))

class __extend__(parse.UnionVariantCheck):
    def to_code(self, codegen):
        return "type(%s) is not %s" % (self.var.to_code(codegen), codegen.getname(self.variant))

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
            return types.FixedBitVector(int(name[3:]))
        if name == "%unit":
            return types.Unit()
        if name == "%i64":
            return types.MachineInt()
        if name == "%bit":
            return types.Bit()
        if name == "%string":
            return types.String()
        if name.startswith("%sbv"):
            return types.SmallBitVector(int(name[len("%sbv"):]))
        xxx

class __extend__(parse.EnumType):
    def resolve_type(self, codegen):
        return codegen.get_named_type(self.name)

class __extend__(parse.UnionType):
    def resolve_type(self, codegen):
        return codegen.get_named_type(self.name)

class __extend__(parse.StructType):
    def resolve_type(self, codegen):
        return codegen.get_named_type(self.name)

class __extend__(parse.ListType):
    def resolve_type(self, codegen):
        typ = types.List(self.typ.resolve_type(codegen))
        with codegen.cached_declaration(typ, "List") as pyname:
            with codegen.emit_indent("class %s(object): # %s" % (pyname, self)):
                codegen.emit("_immutable_fields_ = ['head', 'tail']")
                codegen.emit("def __init__(self, head, tail): self.head, self.tail = head, tail")
            typ.pyname = pyname
        return typ

class __extend__(parse.FunctionType):
    def resolve_type(self, codegen):
        return types.Function(self.argtype.resolve_type(codegen), self.restype.resolve_type(codegen))

class __extend__(parse.RefType):
    def resolve_type(self, codegen):
        return types.Ref(self.refto.resolve_type(codegen))

class __extend__(parse.VecType):
    def resolve_type(self, codegen):
        return types.Vec(self.of.resolve_type(codegen))

class __extend__(parse.TupleType):
    def resolve_type(self, codegen):
        typ = types.Tuple(tuple([e.resolve_type(codegen) for e in self.elements]))
        with codegen.cached_declaration(typ, "Tuple") as pyname:
            codegen.emit("class %s(object): pass # %s" % (pyname, self))
            typ.pyname = pyname
        typ.uninitialized_value = "%s()" % (pyname, )
        return typ
