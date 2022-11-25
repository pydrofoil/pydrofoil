from rpython.tool.pairtype import pair

from pydrofoil import parse, types, binaryop, operations
from contextlib import contextmanager

import sys

parse.BaseAst.call_count = 0

assert sys.maxint == 2 ** 63 - 1, "only 64 bit platforms are supported!"

class NameInfo(object):
    def __init__(self, pyname, typ, ast):
        self.pyname = pyname
        self.typ = typ
        self.ast = ast

    def __repr__(self):
        return "NameInfo(%r, %r, %r)" % (self.pyname, self.typ, self.ast)


class Codegen(object):
    def __init__(self, promoted_registers=frozenset(), inline_functions=frozenset()):
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
        self.add_global("bitzero", "r_uint(0)", types.Bit())
        self.add_global("bitone", "r_uint(1)", types.Bit())
        self.add_global("$zupdate_fbits", "supportcode.update_fbits")
        self.add_global("have_exception", "machine.have_exception", types.Bool())
        self.add_global("throw_location", "machine.throw_location", types.String())
        self.add_global("zsail_assert", "supportcode.sail_assert")
        self.add_global("NULL", "None")
        self.declared_types = set()
        self.promoted_registers = promoted_registers
        self.inline_functions = inline_functions

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
        if self.localnames is None or name not in self.localnames:
            return self.globalnames[name].pyname
        return self.localnames[name].pyname

    def getinfo(self, name):
        if name in self.localnames:
            return self.localnames[name]
        else:
            return self.globalnames[name]

    def gettarget(self, name):
        res = self.getinfo(name).pyname
        # XXX stupid hack
        if res.startswith("jit.promote("):
            return res[len('jit.promote('):-1]
        return res

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
        if self.level == 0 and line.startswith(("def ", "class ")):
            self.code.append('')
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
        res.append("def model_init(machine):\n    " + "\n    ".join(self.runtimeinit or ["pass"]))
        res.append("\n".join(self.code))
        return "\n\n\n".join(res)

def is_bvtyp(typ):
    return isinstance(typ, types.SmallBitVector) or typ is types.GenericBitVector()


def parse_and_make_code(s, support_code, promoted_registers=frozenset(), inline_functions=frozenset()):
    ast = parse.parser.parse(parse.lexer.lex(s))
    c = Codegen(promoted_registers, inline_functions)
    with c.emit_code_type("declarations"):
        c.emit("from rpython.rlib import jit")
        c.emit("from rpython.rlib import objectmodel")
        c.emit("from rpython.rlib.rarithmetic import r_uint, intmask")
        c.emit("import operator")
        c.emit(support_code)
        c.emit("from pydrofoil import bitvector")
        c.emit("class Lets(object): pass")
        c.emit("class Machine(supportcode.RegistersBase):")
        c.emit("    def __init__(self): self.l = Lets(); model_init(self)")
        c.emit("UninitInt = bitvector.int_fromint(-0xfefee)")
    try:
        ast.make_code(c)
    except Exception:
        print c.getcode()
        raise
    #called = [d for d in ast.declarations if d.call_count]
    #called.sort(key=lambda d: d.call_count)
    #called.reverse()
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
        with codegen.emit_code_type("declarations"):
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
                codegen.emit("@objectmodel.always_inline")
                with codegen.emit_indent("def eq(self, other):"):
                    codegen.emit("return False")
            codegen.emit("%s.singleton = %s()" % (name, name))
            self.pynames = []
            uniontyp = types.Union(self)
            uniontyp.uninitialized_value = "%s.singleton" % (name, )
            codegen.add_named_type(self.name, self.pyname, uniontyp, self)
            for name, typ in zip(self.names, self.types):
                rtyp = typ.resolve_type(codegen)
                pyname = self.pyname + "_" + name
                codegen.add_global(name, pyname, uniontyp, self)
                self.pynames.append(pyname)
                with codegen.emit_indent("class %s(%s):" % (pyname, self.pyname)):
                    # default field values
                    if type(rtyp) is types.Tuple:
                        for fieldnum, fieldtyp in enumerate(rtyp.elements):
                            if fieldtyp is types.Int():
                                codegen.emit("utup%s_0 = -0xfefee" % (fieldnum, ))
                                codegen.emit("utup%s_1 = None" % (fieldnum, ))
                            elif is_bvtyp(fieldtyp):
                                codegen.emit("utup%s_0 = 0xdeadcafe" % (fieldnum, ))
                                codegen.emit("utup%s_1 = r_uint(-1)" % (fieldnum, ))
                                codegen.emit("utup%s_2 = None" % (fieldnum, ))
                            else:
                                codegen.emit("utup%s = %s" % (fieldnum, fieldtyp.uninitialized_value))
                    elif is_bvtyp(rtyp):
                        codegen.emit("bv_0 = 0xbebe")
                        codegen.emit("bv_1 = r_uint(-35)")
                        codegen.emit("bv_2 = None")
                    elif rtyp is not types.Unit():
                        codegen.emit("a = %s" % (rtyp.uninitialized_value, ))
                    self.make_init(codegen, rtyp, typ, pyname)
                    self.make_eq(codegen, rtyp, typ, pyname)
                    self.make_convert(codegen, rtyp, typ, pyname)
                if rtyp is types.Unit():
                    codegen.emit("%s.singleton = %s(())" % (pyname, pyname))
                if type(rtyp) is types.Enum:
                    # for enum union options, we make singletons
                    for enum_value in rtyp.ast.names:
                        subclassname = "%s_%s" % (pyname, enum_value)
                        with codegen.emit_indent("class %s(%s):" % (subclassname, pyname)):
                            codegen.emit("a = %s" % (codegen.getname(enum_value), ))
                        codegen.emit("%s.singleton = %s()" % (subclassname, subclassname))
        if self.name == "zexception":
            codegen.add_global("current_exception", "machine.current_exception", uniontyp, self)

    def make_init(self, codegen, rtyp, typ, pyname):
        if type(rtyp) is types.Enum:
            codegen.emit("@staticmethod")
            codegen.emit("@objectmodel.specialize.arg_or_var(0)")
            with codegen.emit_indent("def construct(a):"):
                for enum_value in rtyp.ast.names:
                    codegen.emit("if a == %s: return %s_%s.singleton" % (codegen.getname(enum_value), pyname, enum_value))
                codegen.emit("raise ValueError")
            return
        codegen.emit("@objectmodel.always_inline")
        with codegen.emit_indent("def __init__(self, a):"):
            if rtyp is types.Unit():
                codegen.emit("pass")
            elif type(rtyp) is types.Tuple:
                codegen.emit("# %s" % typ)
                written = False
                for fieldnum, fieldtyp in enumerate(rtyp.elements):
                    if fieldtyp is types.Unit():
                        continue
                    written = True
                    if fieldtyp is types.Int():
                        codegen.emit("self.utup%s_0 = a.ztup%s_0" % (fieldnum, fieldnum))
                        codegen.emit("self.utup%s_1 = a.ztup%s_1" % (fieldnum, fieldnum))
                    elif is_bvtyp(fieldtyp):
                        codegen.emit("self.utup%s_0 = a.ztup%s_0" % (fieldnum, fieldnum))
                        codegen.emit("self.utup%s_1 = a.ztup%s_1" % (fieldnum, fieldnum))
                        codegen.emit("self.utup%s_2 = a.ztup%s_2" % (fieldnum, fieldnum))
                    else:
                        codegen.emit("self.utup%s = a.ztup%s" % (fieldnum, fieldnum))
                if not written:
                    codegen.emit('pass')

            elif rtyp is types.Int():
                assert 0, "not implemented"
            elif is_bvtyp(rtyp):
                codegen.emit("self.bv_0 = a[0]")
                codegen.emit("self.bv_1 = a[1]")
                codegen.emit("self.bv_2 = a[2]")
            else:
                codegen.emit("self.a = a # %s" % (typ, ))

    def make_eq(self, codegen, rtyp, typ, pyname):
        codegen.emit("@objectmodel.always_inline")
        with codegen.emit_indent("def eq(self, other):"):
            codegen.emit("if type(self) is not type(other): return False")
            if rtyp is types.Unit():
                codegen.emit("return True")
                return
            elif type(rtyp) is types.Tuple:
                codegen.emit("# %s" % typ)
                for fieldnum, fieldtyp in enumerate(rtyp.elements):
                    expr = self.read_field(fieldnum, fieldtyp, 'self')
                    otherexpr = self.read_field(fieldnum, fieldtyp, 'other')
                    codegen.emit("if %s: return False # %s" % (
                        fieldtyp.make_op_code_special_neq(None, (expr, otherexpr), (fieldtyp, fieldtyp)),
                        typ.elements[fieldnum]))
            else:
                codegen.emit("if %s: return False # %s" % (
                    rtyp.make_op_code_special_neq(None, ('self.a', 'other.a'), (rtyp, rtyp)), typ))
            codegen.emit("return True")

    def make_convert(self, codegen, rtyp, typ, pyname):
        codegen.emit("@staticmethod")
        codegen.emit("@objectmodel.always_inline")
        with codegen.emit_indent("def convert(inst):"):
            with codegen.emit_indent("if isinstance(inst, %s):" % pyname):
                if rtyp is types.Unit():
                    codegen.emit("return ()")
                elif type(rtyp) is types.Tuple:
                    codegen.emit("res = %s" % rtyp.uninitialized_value)
                    for fieldnum, fieldtyp in enumerate(rtyp.elements):
                        if fieldtyp is types.Unit():
                            continue
                        if fieldtyp is types.Int():
                            codegen.emit("res.ztup%s_0 = inst.utup%s_0" % (fieldnum, fieldnum))
                            codegen.emit("res.ztup%s_1 = inst.utup%s_1" % (fieldnum, fieldnum))
                        elif is_bvtyp(fieldtyp):
                            codegen.emit("res.ztup%s_0 = inst.utup%s_0" % (fieldnum, fieldnum))
                            codegen.emit("res.ztup%s_1 = inst.utup%s_1" % (fieldnum, fieldnum))
                            codegen.emit("res.ztup%s_2 = inst.utup%s_2" % (fieldnum, fieldnum))
                        else:
                            codegen.emit("res.ztup%s = %s" % (fieldnum,
                                self.read_field(fieldnum, fieldtyp, 'inst')))
                    codegen.emit("return res")
                elif is_bvtyp(rtyp):
                    codegen.emit("return inst.bv_0, inst.bv_1, inst.bv_2")
                else:
                    codegen.emit("return inst.a")
            with codegen.emit_indent("else:"):
                codegen.emit("raise TypeError")
        if type(rtyp) is types.Tuple:
            for fieldnum, fieldtyp in enumerate(rtyp.elements):
                codegen.emit("@staticmethod")
                with codegen.emit_indent("def convert_ztup%s(inst):" % fieldnum):
                    with codegen.emit_indent("if isinstance(inst, %s):" % pyname):
                        codegen.emit("return %s" % self.read_field(fieldnum, fieldtyp, 'inst'))
                    with codegen.emit_indent("else:"):
                        codegen.emit("raise TypeError")

    def constructor(self, info, op, args, argtyps):
        if len(argtyps) == 1 and type(argtyps[0]) is types.Enum:
            return "%s.construct(%s)" % (op, args)
        if argtyps == [types.Unit()]:
            return "%s.singleton" % (op, )
        return "%s(%s)" % (op, args)

    def read_field(self, fieldnum, fieldtyp, selfvar='self'):
        if fieldtyp is types.Int():
            return "(%s.utup%s_0, %s.utup%s_1)" % (selfvar, fieldnum, selfvar, fieldnum)
        elif is_bvtyp(fieldtyp):
            return "(%s.utup%s_0, %s.utup%s_1, %s.utup%s_2)" % (selfvar, fieldnum, selfvar, fieldnum, selfvar, fieldnum)
        else:
            return "%s.utup%s" % (selfvar, fieldnum)

class __extend__(parse.Struct):
    def make_code(self, codegen):
        name = "Struct_" + self.name
        self.pyname = name
        structtyp = types.Struct(self)
        structtyp.fieldtyps = {}
        uninit_arg = []
        codegen.add_named_type(self.name, self.pyname, structtyp, self)
        for typ in self.types:
            typ.resolve_type(codegen) # pre-declare the types
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
            codegen.emit("@objectmodel.always_inline")
            with codegen.emit_indent("def eq(self, other):"):
                codegen.emit("assert isinstance(other, %s)" % (self.pyname, ))
                for arg, typ in zip(self.names, self.types):
                    rtyp = typ.resolve_type(codegen)
                    codegen.emit("if %s: return False # %s" % (
                        rtyp.make_op_code_special_neq(None, ('self.%s' % arg, 'other.%s' % arg), (rtyp, rtyp)), typ))
                codegen.emit("return True")
        structtyp.uninitialized_value = "%s(%s)" % (self.pyname, ", ".join(uninit_arg))

class __extend__(parse.GlobalVal):
    def make_code(self, codegen):
        if self.definition is not None:
            name = eval(self.definition)
            if name == "not": name = "not_"
            typ = self.typ.resolve_type(codegen)
            funcname = "supportcode.%s" % (name, )
            codegen.add_global(self.name, funcname, typ, self)
        else:
            codegen.add_global(self.name, None,  self.typ.resolve_type(codegen), self)

class __extend__(parse.Register):
    def make_code(self, codegen):
        self.pyname = "_reg_%s" % (self.name, )
        typ = self.typ.resolve_type(codegen)
        if self.name in codegen.promoted_registers:
            pyname = "jit.promote(machine.%s)" % self.pyname
        else:
            pyname = "machine.%s" % self.pyname
        codegen.add_global(self.name, pyname, typ, self)
        with codegen.emit_code_type("declarations"):
            codegen.emit("# %s" % (self, ))
            codegen.emit("Machine.%s = %s" % (self.pyname, typ.uninitialized_value))


class __extend__(parse.Function):
    def make_code(self, codegen):
        pyname = "func_" + self.name
        if codegen.globalnames[self.name].pyname is not None:
            print "duplicate!", self.name, codegen.globalnames[self.name].pyname
            return
        codegen.update_global_pyname(self.name, pyname)
        self.pyname = pyname
        blocks = self._prepare_blocks()
        entrycounts = self._compute_entrycounts(blocks)
        if self.detect_union_switch(blocks[0]) and entrycounts[0] == 1:
            print "making method!", self.name
            with self._scope(codegen, pyname):
                codegen.emit("return %s.meth_%s(machine, %s)" % (self.args[0], self.name, ", ".join(self.args[1:])))
            self._emit_methods(blocks, entrycounts, codegen)
            return
        with self._scope(codegen, pyname):
            if entrycounts == {0: 1}:
                assert self.body[-1].end_of_block
                self.emit_block_ops(self.body, codegen)
            else:
                self._emit_blocks(blocks, codegen, entrycounts, )
        codegen.emit()

    @contextmanager
    def _scope(self, codegen, pyname, method=False):
        typ = codegen.globalnames[self.name].typ
        args = []
        startlines = []
        for i, arg in enumerate(self.args):
            argtyp = typ.argtype.elements[i]
            if argtyp is types.Int():
                args.append("%s_0" % (arg, ))
                args.append("%s_1" % (arg, ))
            elif is_bvtyp(argtyp):
                args.append("%s_0" % (arg, ))
                args.append("%s_1" % (arg, ))
                args.append("%s_2" % (arg, ))
            else:
                args.append(arg)
        codegen.emit("# %s" % codegen.globalnames[self.name].ast.typ)
        if self.name[1:] in codegen.inline_functions:
            codegen.emit("@objectmodel.always_inline")

        if not method:
            first = "def %s(machine, %s):" % (pyname, ", ".join(args))
        else:
            # bit messy, need the self
            first = "def %s(%s, machine, %s):" % (pyname, self.args[0], ", ".join(args[1:]))
        with codegen.enter_scope(self), codegen.emit_indent(first):
            codegen.add_local('return', 'return_', typ.restype, self)
            for i, arg in enumerate(self.args):
                argtyp = typ.argtype.elements[i]
                if argtyp is types.Int():
                    pyname = "(%s_0, %s_1)" % (arg, arg)
                elif is_bvtyp(argtyp):
                    pyname = "(%s_0, %s_1, %s_2)" % (arg, arg, arg)
                else:
                    pyname = arg
                codegen.add_local(arg, pyname, typ.argtype.elements[i], self)
            for startline in startlines:
                codegen.emit(startline)
            yield

    def _prepare_blocks(self):
        # bring operations into a block format:
        # a dictionary {label-as-int: [list of operations]}
        # every list of operations ends with a goto, return or failure

        # first check which ops can be jumped to
        jumptargets = {getattr(op, 'target', 0) for op in self.body}

        # now split into blocks
        blocks = {}
        for i, op in enumerate(self.body):
            if i in jumptargets:
                blocks[i] = block = []
            block.append(op)

        # insert goto at the end to make have no "fall throughs"
        for blockpc, block in sorted(blocks.items()):
            lastop = block[-1]
            if lastop.end_of_block:
                continue
            block.append(parse.Goto(blockpc + len(block)))
        return blocks


    @staticmethod
    def _compute_entrycounts(blocks):
        entrycounts = {0: 1} # pc, count
        for pc, block in blocks.iteritems():
            for op in block:
                if isinstance(op, (parse.Goto, parse.ConditionalJump)):
                    entrycounts[op.target] = entrycounts.get(op.target, 0) + 1
        return entrycounts

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
        if self._is_union_switch(op):
            return op
        else:
            return None


    def _is_union_switch(self, op):
        return (isinstance(op, parse.ConditionalJump) and
                isinstance(op.condition, parse.UnionVariantCheck) and
                isinstance(op.condition.var, parse.Var) and
                op.condition.var.name == self.args[0])

    def _emit_methods(self, blocks, entrycounts, codegen):
        typ = codegen.globalnames[self.name].typ
        uniontyp = typ.argtype.elements[0]
        switches = []
        curr_offset = 0
        while 1:
            curr_block = blocks[curr_offset]
            op = self.detect_union_switch(curr_block)
            if op is None:
                switches.append((curr_block, curr_offset, None))
                break
            switches.append((curr_block, curr_offset, op))
            curr_offset = op.target
        generated_for_class = set()
        for i, (block, oldpc, cond) in enumerate(switches):
            if cond is not None:
                clsname = codegen.getname(cond.condition.variant)
                known_cls = cond.condition.variant
            else:
                clsname = uniontyp.ast.pyname
                known_cls = None
            if clsname in generated_for_class:
                continue
            generated_for_class.add(clsname)
            copyblock = []
            # add all var declarations of all the previous blocks
            for prevblock, _, prevcond in switches[:i]:
                copyblock.extend(prevblock[:prevblock.index(prevcond)])
            # now add all operations except the condition
            b = block[:]
            if cond:
                del b[block.index(cond)]
            copyblock.extend(b)
            local_blocks = self._find_reachable(copyblock, oldpc, blocks, known_cls)
            # recompute entrycounts
            local_entrycounts = self._compute_entrycounts(local_blocks)
            pyname = self.name + "_" + (cond.condition.variant if cond else "default")
            with self._scope(codegen, pyname, method=True):
                self._emit_blocks(local_blocks, codegen, local_entrycounts, startpc=oldpc)
            codegen.emit("%s.meth_%s = %s" % (clsname, self.name, pyname))

    def _find_reachable(self, block, blockpc, blocks, known_cls=None):
        # return all the blocks reachable from "block", where self.args[0] is
        # know to be an instance of known_cls
        def process(index, current):
            current = current[:]
            for i, op in enumerate(current):
                if self._is_union_switch(op):
                    if op.condition.variant == known_cls:
                        # always True: can remove
                        current[i] = None
                        continue
                    elif known_cls is not None:
                        # always false, replace with Goto
                        current[i] = parse.Goto(op.target)
                        del current[i+1:]
                if isinstance(op, (parse.Goto, parse.ConditionalJump)):
                    if op.target not in added:
                        added.add(op.target)
                        todo.append(op.target)
            res.append((index, [op for op in current if op is not None]))
        added = set()
        res = []
        todo = []
        process(blockpc, block)
        while todo:
            index = todo.pop()
            current = blocks[index]
            process(index, current)
        return {k: v for k, v in res}


    def _emit_blocks(self, blocks, codegen, entrycounts, startpc=0):
        codegen.emit("pc = %s" % startpc)
        with codegen.emit_indent("while 1:"):
            for blockpc, block in sorted(blocks.items()):
                if block == [None]:
                    # inlined by emit_block_ops
                    continue
                with codegen.emit_indent("if pc == %s:" % blockpc):
                    self.emit_block_ops(block, codegen, entrycounts, blockpc, blocks)

    def emit_block_ops(self, block, codegen, entrycounts=(), offset=0, blocks=None):
        for i, op in enumerate(block):
            if (isinstance(op, parse.LocalVarDeclaration) and
                    i + 1 < len(block) and
                    isinstance(block[i + 1], (parse.Assignment, parse.Operation)) and
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
            elif isinstance(op, parse.Arbitrary):
                codegen.emit("# arbitrary")
                codegen.emit("return %s" % (codegen.gettyp(self.name).restype.uninitialized_value, ))
            else:
                codegen.emit("# %s" % (op, ))
                op.make_op_code(codegen)
            if op.end_of_block:
                return

class __extend__(parse.Let):
    def make_code(self, codegen):
        codegen.add_global(self.name, "machine.l.%s" % self.name, self.typ.resolve_type(codegen), self)
        with codegen.emit_code_type("runtimeinit"), codegen.enter_scope(self):
            codegen.emit("# %s" % (self, ))
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
        if typ is types.Int():
            pyname = "(%s_1, %s_2)" % (self.name, self.name)
        elif is_bvtyp(typ):
            pyname = "(%s_1, %s_2, %s_3)" % (self.name, self.name, self.name)
        else:
            pyname = self.name
        codegen.add_local(self.name, pyname, typ, self)
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

def tupleindexread(stuple, index):
    # another terrible hack, but very expedient
    if stuple.startswith("(") and stuple.endswith(")") and index <= stuple.count(","):
        elements = stuple[1:-1].split(",")
        return elements[index]
    return "%s[%s]" % (stuple, index)

class __extend__(parse.Operation):
    def make_op_code(self, codegen):
        name = self.name
        result = codegen.gettarget(self.result)
        sargs = [arg.to_code(codegen) for arg in self.args]
        argtyps = [arg.gettyp(codegen) for arg in self.args]
        if name in codegen.globalnames and codegen.globalnames[name].pyname == "supportcode.eq_anything":
            name = "@eq"

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
            codegen.emit("%s = supportcode.vector_update_inplace(machine, %s, %s, %s, %s)" % (result, result, sargs[0], sargs[1], sargs[2]))
            return

        if not sargs:
            args = '()'
        else:
            args = ", ".join(sargs)
        op = codegen.getname(name)
        info = codegen.getinfo(name)
        if isinstance(info.typ, types.Function):
            if info.ast is not None:
                info.ast.call_count += 1

            expand_ints = not info.pyname.startswith("supportcode.")
            if expand_ints:
                newargs = []
                for index, (arg, argtyp) in enumerate(zip(sargs, argtyps)):
                    if argtyp is types.Int():
                        newargs.append(tupleindexread(arg, 0))
                        newargs.append(tupleindexread(arg, 1))
                    elif is_bvtyp(argtyp):
                        newargs.append(tupleindexread(arg, 0))
                        newargs.append(tupleindexread(arg, 1))
                        newargs.append(tupleindexread(arg, 2))
                    else:
                        newargs.append(arg)
                # pass machine, even to supportcode functions
            else:
                newargs = sargs
            codegen.emit("%s = %s(machine, %s)" % (result, op, ", ".join(newargs)))

        elif isinstance(info.typ, types.Union):
            codegen.emit("%s = %s" % (result, info.ast.constructor(info, op, args, argtyps)))
        else:
            # constructors etc don't get machine passed (yet)
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
        tuptyp = codegen.getinfo(self.tup).typ
        assert isinstance(tuptyp, types.Tuple)
        fieldtyp = tuptyp.elements[self.index]
        if fieldtyp is types.Unit():
            pass
        elif fieldtyp is types.Int():
            codegen.emit("%s.ztup%s_0, %s.ztup%s_1 = %s" % (self.tup, self.index, self.tup, self.index, self.value.to_code(codegen)))
        elif is_bvtyp(fieldtyp):
            codegen.emit("%s.ztup%s_0, %s.ztup%s_1, %s.ztup%s_2 = %s" % (self.tup, self.index, self.tup, self.index, self.tup, self.index, self.value.to_code(codegen)))
        else:
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
        return "r_uint(%s)" % (self.constant, )

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
        obj = self.obj
        if isinstance(obj, parse.Cast):
            return "%s.convert_%s(%s)" % (codegen.getname(obj.variant), self.element, obj.expr.to_code(codegen))
        objtyp = obj.gettyp(codegen)
        objstr = self.obj.to_code(codegen)
        if isinstance(objtyp, types.Tuple):
            assert self.element.startswith("ztup")
            index = int(self.element[4:])
            fieldtyp = objtyp.elements[index]
            if fieldtyp is types.Unit():
                return "()"
            elif fieldtyp is types.Int():
                return "(%s.ztup%s_0, %s.ztup%s_1)" % (objstr, index, objstr, index)
            elif is_bvtyp(fieldtyp):
                return "(%s.ztup%s_0, %s.ztup%s_1, %s.ztup%s_2)" % (objstr, index, objstr, index, objstr, index)
        res = "%s.%s" % (objstr, self.element)
        if isinstance(objtyp, types.Struct) and self.element in codegen.promoted_registers:
            return "jit.promote(%s)" % res
        return res

    def gettyp(self, codegen):
        objtyp = self.obj.gettyp(codegen)
        if isinstance(objtyp, types.Tuple):
            assert self.element.startswith("ztup")
            return objtyp.elements[int(self.element[len('ztup'):])]
        return objtyp.fieldtyps[self.element]

class __extend__(parse.Cast):
    def to_code(self, codegen):
        expr = self.expr.to_code(codegen)
        return "%s.convert(%s)" % (codegen.getname(self.variant), expr)

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
        return "not isinstance(%s, %s)" % (self.var.to_code(codegen), codegen.getname(self.variant))

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
            with codegen.emit_indent("class %s(object): # %s" % (pyname, self)):
                codegen.emit("@objectmodel.always_inline")
                with codegen.emit_indent("def eq(self, other):"):
                    codegen.emit("assert isinstance(other, %s)" % (pyname, ))
                    for index, fieldtyp in enumerate(self.elements):
                        rtyp = fieldtyp.resolve_type(codegen)
                        if rtyp is types.Unit():
                            continue
                        codegen.emit("if %s: return False # %s" % (
                            rtyp.make_op_code_special_neq(None, ('self.utup%s' % index, 'other.utup%s' % index), (rtyp, rtyp)), fieldtyp))
                    codegen.emit("return True")
            typ.pyname = pyname
        typ.uninitialized_value = "%s()" % (pyname, )
        return typ
