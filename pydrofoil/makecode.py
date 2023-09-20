import sys
from contextlib import contextmanager
from rpython.tool.pairtype import pair

from pydrofoil import parse, types, binaryop, operations, supportcode


assert sys.maxint == 2 ** 63 - 1, "only 64 bit platforms are supported!"

class NameInfo(object):
    def __init__(self, pyname, typ, ast, write_pyname=None):
        self.pyname = pyname
        self.typ = typ
        self.ast = ast
        self.write_pyname = write_pyname

    def __repr__(self):
        return "NameInfo(%r, %r, %r, %r)" % (self.pyname, self.typ, self.ast, self.write_pyname)


class Codegen(object):
    def __init__(self, promoted_registers=frozenset()):
        self.declarations = []
        self.runtimeinit = []
        self.code = []
        self.level = 0
        self.last_enum = 0
        self.globalnames = {}
        self.builtin_names = {}
        self.namedtypes = {}
        self.declarationcache = {}
        self.gensym = {} # prefix -> number
        self.localnames = None
        for name, (spec, unwrapped_name) in supportcode.all_unwraps.iteritems():
            self.add_global("@" + unwrapped_name, "supportcode." + unwrapped_name)
        self.add_global("false", "False", types.Bool())
        self.add_global("true", "True", types.Bool())
        self.add_global("bitzero", "r_uint(0)", types.Bit())
        self.add_global("bitone", "r_uint(1)", types.Bit())
        self.add_global("$zupdate_fbits", "supportcode.update_fbits")
        self.add_global("@vector_subrange_fixed_bv_i_i", "supportcode.vector_subrange_fixed_bv_i_i")
        self.add_global("@slice_fixed_bv_i_i", "supportcode.slice_fixed_bv_i_i")
        self.add_global("@vector_subrange_o_i_i_unwrapped_res", "supportcode.vector_subrange_o_i_i_unwrapped_res")
        self.add_global("@vector_slice_o_i_i_unwrapped_res", "supportcode.vector_slice_o_i_i_unwrapped_res")
        self.add_global("@eq_bits_bv_bv", "supportcode.eq_bits_bv_bv")
        self.add_global("@neq_bits_bv_bv", "supportcode.neq_bits_bv_bv")
        self.add_global("@eq_int_i_i", "supportcode.eq_int_i_i")
        self.add_global("@add_i_i_wrapped_res", "supportcode.add_i_i_wrapped_res")
        self.add_global("@sub_i_i_wrapped_res", "supportcode.sub_i_i_wrapped_res")
        self.add_global("@xor_vec_bv_bv", "supportcode.xor_vec_bv_bv")
        self.add_global("@or_vec_bv_bv", "supportcode.or_vec_bv_bv")
        self.add_global("@and_vec_bv_bv", "supportcode.and_vec_bv_bv")
        self.add_global("@not_vec_bv", "supportcode.not_vec_bv")
        self.add_global("@bitvector_concat_bv_bv", "supportcode.bitvector_concat_bv_bv")
        self.add_global("@signed_bv", "supportcode.signed_bv")
        self.add_global("@unsigned_bv_wrapped_res", "supportcode.unsigned_bv_wrapped_res")
        self.add_global("@unsigned_bv", "supportcode.unsigned_bv")
        self.add_global("@zero_extend_bv_i_i", "supportcode.zero_extend_bv_i_i")
        self.add_global("@vector_access_bv_i", "supportcode.vector_access_bv_i")
        self.add_global("@add_bits_bv_bv", "supportcode.add_bits_bv_bv")
        self.add_global("@add_bits_int_bv_i", "supportcode.add_bits_int_bv_i")
        self.add_global("@sub_bits_bv_bv", "supportcode.sub_bits_bv_bv")
        self.add_global("@shiftl_bv_i", "supportcode.shiftl_bv_i")
        self.add_global("@length_unwrapped_res", "supportcode.length_unwrapped_res")
        self.add_global("zsail_assert", "supportcode.sail_assert")
        self.add_global("UINT64_C", "supportcode.uint64c")
        self.add_global("NULL", "None")
        self.add_global("have_exception", "machine.have_exception", types.Bool(), write_pyname="machine.have_exception")
        self.add_global("throw_location", "machine.throw_location", types.String(), write_pyname="machine.throw_location")
        self.promoted_registers = promoted_registers
        self.all_registers = {}
        self.inlinable_functions = {}

    def add_global(self, name, pyname, typ=None, ast=None, write_pyname=None):
        assert isinstance(typ, types.Type) or typ is None
        if name in self.globalnames:
            assert isinstance(ast, parse.GlobalVal)
            assert ast == self.globalnames[name].ast
            return
        self.globalnames[name] = NameInfo(pyname, typ, ast, write_pyname)

    def add_named_type(self, name, pyname, typ, ast):
        assert isinstance(typ, types.Type)
        assert name not in self.namedtypes
        self.namedtypes[name] = NameInfo(pyname, typ, ast)

    def get_named_type(self, name):
        return self.namedtypes[name].typ

    def add_local(self, name, pyname, typ, ast):
        assert isinstance(typ, types.Type)
        self.localnames[name] = NameInfo(pyname, typ, ast, pyname)

    def getname(self, name):
        if self.localnames is None or name not in self.localnames:
            return self.globalnames[name].pyname
        return name

    def getinfo(self, name):
        if self.localnames is not None and name in self.localnames:
            return self.localnames[name]
        else:
            return self.globalnames[name]

    def write_to(self, name, result):
        target = self.getinfo(name).write_pyname
        assert target is not None
        if "%" not in target:
            self.emit("%s = %s" % (target, result))
        else:
            self.emit(target % (result, ))

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
        self.runtimeinit.append("func_zinitializze_registers(machine, ())")
        res.append("def model_init(machine):\n    " + "\n    ".join(self.runtimeinit or ["pass"]))
        res.append("\n".join(self.code))
        return "\n\n".join(res)


def parse_and_make_code(s, support_code, promoted_registers=set()):
    from pydrofoil.infer import infer
    ast = parse.parser.parse(parse.lexer.lex(s))
    context = infer(ast)
    c = Codegen(promoted_registers)
    with c.emit_code_type("declarations"):
        c.emit("from rpython.rlib import jit")
        c.emit("from rpython.rlib.rbigint import rbigint")
        c.emit("from rpython.rlib import objectmodel")
        c.emit("from rpython.rlib.rarithmetic import r_uint, intmask")
        c.emit("import operator")
        c.emit(support_code)
        c.emit("from pydrofoil import bitvector")
        c.emit("from pydrofoil.bitvector import Integer")
        c.emit("class Lets(supportcode.LetsBase): pass")
        c.emit("class Machine(supportcode.RegistersBase):")
        c.emit("    _immutable_fields_ = ['g']")
        c.emit("    def __init__(self):")
        c.emit("        self.l = Lets(); model_init(self)")
        c.emit("        self.g = supportcode.Globals()")
        c.emit("UninitInt = bitvector.Integer.fromint(-0xfefee)")
    try:
        ast.make_code(c)
    except Exception:
        print c.getcode()[:1024*1024*1024]
        raise
    return c.getcode()


# ____________________________________________________________
# declarations

class __extend__(parse.BaseAst):
    def is_constant(self, codegen):
        return False

class __extend__(parse.File):
    def make_code(self, codegen):
        import traceback
        failure_count = 0
        for index, decl in enumerate(self.declarations):
            print "\033[1K\rMAKING CODE FOR %s/%s" % (index, len(self.declarations)), type(decl).__name__, getattr(decl, "name", decl),
            sys.stdout.flush()
            try:
                decl.make_code(codegen)
            except Exception as e:
                import pdb; pdb.xpm()
                print failure_count, "COULDN'T GENERATE CODE FOR", index, getattr(decl, "name", decl)
                print(traceback.format_exc())
                failure_count += 1
                codegen.level = 0
            codegen.emit()

class __extend__(parse.Declaration):
    def make_code(self, codegen):
        raise NotImplementedError("abstract base class")

class __extend__(parse.Enum):
    def make_code(self, codegen):
        name = "Enum_" + self.name
        self.pyname = name
        with codegen.emit_code_type("declarations"):
            with codegen.emit_indent("class %s(supportcode.ObjectBase):" % name):
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
            with codegen.emit_indent("class %s(supportcode.ObjectBase):" % name):
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
                    if type(rtyp) is types.Struct:
                        for fieldname, fieldtyp in sorted(rtyp.fieldtyps.iteritems()):
                            codegen.emit("%s = %s" % (fieldname, fieldtyp.uninitialized_value))
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
            codegen.add_global("current_exception", "machine.current_exception", uniontyp, self, "machine.current_exception")

    def make_init(self, codegen, rtyp, typ, pyname):
        if type(rtyp) is types.Enum:
            codegen.emit("@staticmethod")
            codegen.emit("@objectmodel.specialize.arg_or_var(0)")
            with codegen.emit_indent("def construct(a):"):
                for enum_value in rtyp.ast.names:
                    codegen.emit("if a == %s: return %s_%s.singleton" % (codegen.getname(enum_value), pyname, enum_value))
                codegen.emit("raise ValueError")
            return
        with codegen.emit_indent("def __init__(self, a):"):
            if rtyp is types.Unit():
                codegen.emit("pass")
            elif type(rtyp) is types.Struct:
                codegen.emit("# %s" % typ)
                for fieldname, fieldtyp in sorted(sorted(rtyp.fieldtyps.iteritems())):
                    codegen.emit("self.%s = a.%s" % (fieldname, fieldname))
            else:
                codegen.emit("self.a = a # %s" % (typ, ))

    def make_eq(self, codegen, rtyp, typ, pyname):
        codegen.emit("@objectmodel.always_inline")
        with codegen.emit_indent("def eq(self, other):"):
            codegen.emit("if type(self) is not type(other): return False")
            if rtyp is types.Unit():
                codegen.emit("return True")
                return
            elif type(rtyp) is types.Struct:
                codegen.emit("# %s" % typ)
                for fieldname, fieldtyp in sorted(rtyp.fieldtyps.iteritems()):
                    codegen.emit("if %s: return False" % (
                        fieldtyp.make_op_code_special_neq(
                            None,
                            ('self.%s' % fieldname, 'other.%s' % fieldname),
                            (fieldtyp, fieldtyp), types.Bool())))
            else:
                codegen.emit("if %s: return False # %s" % (
                    rtyp.make_op_code_special_neq(None, ('self.a', 'other.a'), (rtyp, rtyp), types.Bool()), typ))
            codegen.emit("return True")

    def make_convert(self, codegen, rtyp, typ, pyname):
        codegen.emit("@staticmethod")
        codegen.emit("@objectmodel.always_inline")
        with codegen.emit_indent("def convert(inst):"):
            with codegen.emit_indent("if isinstance(inst, %s):" % pyname):
                if rtyp is types.Unit():
                    codegen.emit("return ()")
                elif type(rtyp) is types.Struct:
                    codegen.emit("res = %s" % rtyp.uninitialized_value)
                    for fieldname, fieldtyp in sorted(rtyp.fieldtyps.iteritems()):
                        codegen.emit("res.%s = inst.%s" % (fieldname, fieldname))
                    codegen.emit("return res")
                else:
                    codegen.emit("return inst.a")
            with codegen.emit_indent("else:"):
                codegen.emit("raise TypeError")
        if type(rtyp) is types.Struct:
            for fieldname, fieldtyp in sorted(rtyp.fieldtyps.iteritems()):
                codegen.emit("@staticmethod")
                with codegen.emit_indent("def convert_%s(inst):" % fieldname):
                    with codegen.emit_indent("if isinstance(inst, %s):" % pyname):
                        codegen.emit("return inst.%s" % (fieldname, ))
                    with codegen.emit_indent("else:"):
                        codegen.emit("raise TypeError")

    def constructor(self, info, op, args, argtyps):
        if len(argtyps) == 1 and type(argtyps[0]) is types.Enum:
            return "%s.construct(%s)" % (op, args)
        if argtyps == [types.Unit()]:
            return "%s.singleton" % (op, )
        return "%s(%s)" % (op, args)

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
        with codegen.emit_code_type("declarations"), codegen.emit_indent("class %s(supportcode.ObjectBase):" % name):
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
                        rtyp.make_op_code_special_neq(None, ('self.%s' % arg, 'other.%s' % arg), (rtyp, rtyp), types.Bool()), typ))
                codegen.emit("return True")
        structtyp.uninitialized_value = "%s(%s)" % (self.pyname, ", ".join(uninit_arg))

class __extend__(parse.GlobalVal):
    def make_code(self, codegen):
        typ = self.typ.resolve_type(codegen) # XXX should use self.resolve_type?
        if self.definition is not None:
            name = eval(self.definition)
            if "->" in name:
                if name == "%i->%i64":
                    name = "int_to_int64"
                elif name == "%i64->%i":
                    name = "int64_to_int"
                elif name == "%string->%i":
                    name = "string_to_int"
                elif name == "%string->%real":
                    name = "string_to_real"
                else:
                    import pdb; pdb.set_trace()
            if name == "not": name = "not_"
            funcname = "supportcode.%s" % (name, )
            codegen.add_global(self.name, funcname, typ, self)
            codegen.builtin_names[self.name] = name
        else:
            # a sail function, invent the name now
            pyname = "func_" + self.name
            codegen.add_global(self.name, pyname,  typ, self)

class __extend__(parse.Abstract):
    def make_code(self, codegen):
        typ = self.typ.resolve_type(codegen) # XXX should use self.resolve_type?
        pyname = "func_" + self.name
        codegen.add_global(self.name, pyname,  typ, self)
        codegen.emit("# %s" % self)
        codegen.emit("def %s(*args): return ()" % (pyname, ))

class __extend__(parse.Register):
    def make_code(self, codegen):
        from pydrofoil.optimize import optimize_blocks
        self.pyname = "_reg_%s" % (self.name, )
        typ = self.typ.resolve_type(codegen)
        read_pyname = write_pyname = "machine.%s" % self.pyname
        if self.name in codegen.promoted_registers:
            read_pyname = "jit.promote(%s)" % write_pyname
        elif isinstance(typ, types.GenericBitVector):
            names = "(%s_width, %s_val, %s_rval)" % (read_pyname, read_pyname, read_pyname)
            read_pyname = "bitvector.BitVector.unpack" + names
            write_pyname = "%s = %%s.pack()" % (names, )
        elif isinstance(typ, types.BigFixedBitVector):
            names = "(%s_val, %s_rval)" % (read_pyname, read_pyname)
            read_pyname = "bitvector.BitVector.unpack(%s, *%s)" % (typ.width, names)
            write_pyname = "%s = %%s.pack()[1:]" % (names, )
        elif isinstance(typ, types.Int):
            names = "(%s_val, %s_rval)" % (read_pyname, read_pyname)
            read_pyname = "bitvector.Integer.unpack" + names
            write_pyname = "%s = %%s.pack()" % (names, )
        codegen.all_registers[self.name] = self
        codegen.add_global(self.name, read_pyname, typ, self, write_pyname)
        #with codegen.emit_code_type("declarations"):
        #    codegen.emit("# %s" % (self, ))
        #    codegen.write_to(self.name, typ.uninitialized_value)

        if self.body is None:
            return
        with codegen.emit_code_type("runtimeinit"), codegen.enter_scope(self):
            codegen.emit(" # register %s : %s" % (self.name, self.typ, ))
            blocks = {0: self.body[:]}
            optimize_blocks(blocks, codegen)
            for i, op in enumerate(blocks[0]):
                codegen.emit("# %s" % (op, ))
                op.make_op_code(codegen)
            codegen.emit()

def iterblockops(blocks):
    for blockpc, block in sorted(blocks.items()):
        for op in block:
            yield blockpc, op


class __extend__(parse.Function):
    def make_code(self, codegen):
        from pydrofoil.optimize import optimize_blocks, CollectSourceVisitor, view_blocks
        from pydrofoil import optimize
        #vbefore = CollectSourceVisitor()
        #vbefore.visit(self)
        pyname = codegen.getname(self.name)
        assert pyname.startswith("func_")
        #if codegen.globalnames[self.name].pyname is not None:
        #    print "duplicate!", self.name, codegen.globalnames[self.name].pyname
        #    return
        self.pyname = pyname
        blocks = self._prepare_blocks()
        inlinable = len(blocks) == 1 and len(blocks[0]) <= 40
        typ = codegen.globalnames[self.name].ast.typ
        predefined = {arg: typ.argtype.elements[i] for i, arg in enumerate(self.args)}
        predefined["return"] = typ.restype
        optimize_blocks(blocks, codegen, predefined, codegen.all_registers)
        #vafter = CollectSourceVisitor()
        #for pc, block in blocks.iteritems():
        #    for op in block:
        #        vafter.visit(op)
        #if vafter.seen != vbefore.seen:
        #    import pdb; pdb.set_trace()
        if inlinable:
            codegen.inlinable_functions[self.name] = self, blocks
        entrycounts = self._compute_entrycounts(blocks)
        if self.detect_union_switch(blocks[0]) and entrycounts[0] == 1:
            print "making method!", self.name
            with self._scope(codegen, pyname):
                codegen.emit("return %s.meth_%s(machine, %s)" % (self.args[0], self.name, ", ".join(self.args[1:])))
            self._emit_methods(blocks, entrycounts, codegen)
            return
        if len(blocks) > 340:
            print "splitting", self.name
            try:
                self._split_function(blocks, entrycounts, codegen)
                codegen.emit()
                return
            except optimize.CantSplitError:
                print "didn't manage"

        with self._scope(codegen, pyname):
            if entrycounts == {0: 1}:
                assert self.body[-1].end_of_block
                self.emit_block_ops(blocks[0], codegen)
            else:
                self._emit_blocks(blocks, codegen, entrycounts, )
        codegen.emit()

    @contextmanager
    def _scope(self, codegen, pyname, method=False, extra_args=None):
        # extra_args is a list of tuples (name, typ)
        args = self.args
        if extra_args:
            args = args[:]
            for name, _ in extra_args:
                args.append(name)
        if not method:
            first = "def %s(machine, %s):" % (pyname, ", ".join(args))
        else:
            # bit messy, need the self
            first = "def %s(%s, machine, %s):" % (pyname, args[0], ", ".join(args[1:]))
        typ = codegen.globalnames[self.name].typ
        with codegen.enter_scope(self), codegen.emit_indent(first):
            if self.name in codegen.inlinable_functions:
                codegen.emit("# inlinable")
            codegen.add_local('return', 'return_', typ.restype, self)
            for i, arg in enumerate(self.args):
                codegen.add_local(arg, arg, typ.argtype.elements[i], self)
            if extra_args:
                for name, typ in extra_args:
                    codegen.add_local(name, name, typ, self)
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
                        assert op.target in blocks
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

    def _split_function(self, blocks, entrycounts, codegen):
        from pydrofoil import optimize
        blocks = {pc: ops[:] for (pc, ops) in blocks.iteritems()}
        with self._scope(codegen, self.pyname):
            args = self.args
            next_func_name = self.pyname + "_next_0"
            codegen.emit("return %s(machine, %s)" % (next_func_name, ", ".join(args)))
        args = self.args
        prev_extra_args = []
        startpc = 0
        while len(blocks) > 150:
            g1, g2, transferpc = optimize.split_graph(blocks, 120, start_node=startpc)
            print "previous size", len(blocks), "afterwards:", len(g1), len(g2)
            # compute the local variables that are declared in g1 and used in g2,
            # they become extra arguments
            declared_variables_g1 = {}
            for blockpc, op in iterblockops(g1):
                if isinstance(op, parse.LocalVarDeclaration):
                    declared_variables_g1[op.name] = op.typ.resolve_type(codegen)
            for argname, typ in prev_extra_args:
                declared_variables_g1[argname] = typ
            needed_args = set()
            assignment_targets = set()
            for blockpc, op in iterblockops(g2):
                needed_args.update(op.find_used_vars())
                if isinstance(op, parse.Assignment):
                    assignment_targets.add(op.result)
            extra_args_names = sorted(needed_args.intersection(declared_variables_g1))
            extra_args = [(name, declared_variables_g1[name]) for name in extra_args_names]

            # which variables are declared in g1, and also assigned to in g2,
            # but aren't arguments?
            need_declaration = assignment_targets.intersection(declared_variables_g1) - set(args) - set(extra_args_names)
            assert not need_declaration
            # make a copy to not mutate blocks
            #transferstartblock = g2[transferpc] = g2[transferpc][:]
            #for declvar in need_declaration:
            #    transferstartblock.insert(0, declared_variables_g1[declvar])

            with self._scope(codegen, next_func_name, extra_args=prev_extra_args):
                callargs = args + extra_args_names
                next_func_name = self.pyname + "_next_" + str(transferpc)
                next_call = "return %s(machine, %s)" % (next_func_name, ", ".join(callargs))
                g1[transferpc] = [next_call]
                self._emit_blocks(g1, codegen, entrycounts, startpc=startpc)
            prev_extra_args = extra_args
            blocks = g2
            startpc = transferpc
        with self._scope(codegen, next_func_name, extra_args=extra_args):
            self._emit_blocks(g2, codegen, entrycounts, startpc=transferpc)

    def _emit_blocks(self, blocks, codegen, entrycounts, startpc=0):
        codegen.emit("pc = %s" % startpc)
        with codegen.emit_indent("while 1:"):
            prefix = ''
            for blockpc, block in sorted(blocks.items()):
                if block == [None]:
                    # inlined by emit_block_ops
                    continue
                with codegen.emit_indent("%sif pc == %s:" % (prefix, blockpc)):
                    self.emit_block_ops(block, codegen, entrycounts, blockpc, blocks)
                #prefix = 'el'
            #with codegen.emit_indent("else:"):
            #    codegen.emit("assert 0, 'should be unreachable'")

    def emit_block_ops(self, block, codegen, entrycounts=(), offset=0, blocks=None):
        if isinstance(block[0], str):
            # bit hacky: just emit it
            assert len(block) == 1
            codegen.emit(block[0])
            return
        for i, op in enumerate(block):
            if (isinstance(op, parse.LocalVarDeclaration) and
                    i + 1 < len(block) and
                    isinstance(block[i + 1], (parse.Assignment, parse.Operation)) and
                    op.name == block[i + 1].result and op.name not in block[i + 1].find_used_vars()):
                op.make_op_code(codegen, False)
            elif isinstance(op, parse.ConditionalJump):
                codegen.emit("# %s" % (op, ))
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

class __extend__(parse.Pragma):
    def make_code(self, codegen):
        codegen.emit("# %s" % (self, ))

class __extend__(parse.Files):
    def make_code(self, codegen):
        codegen.emit("# %s" % (self, ))

class __extend__(parse.Let):
    def make_code(self, codegen):
        from pydrofoil.optimize import optimize_blocks
        codegen.emit("# %s" % (self, ))
        pyname = "machine.l.%s" % self.name
        codegen.add_global(self.name, pyname, self.typ.resolve_type(codegen), self, pyname)
        with codegen.emit_code_type("runtimeinit"), codegen.enter_scope(self):
            codegen.emit(" # let %s : %s" % (self.name, self.typ, ))
            blocks = {0: self.body[:]}
            optimize_blocks(blocks, codegen)
            for i, op in enumerate(blocks[0]):
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
            othertyp = self.value.gettyp(codegen)
            rhs = pair(othertyp, typ).convert(self.value, codegen)
            codegen.write_to(self.name, rhs)
        elif need_default_init:
            assert self.value is None
            # need to make a tuple instance
            codegen.write_to(self.name, typ.uninitialized_value)

class __extend__(parse.Operation):
    def make_op_code(self, codegen):
        name = self.name
        assert name == "$zinternal_vector_update"
        result = codegen.getname(self.result)
        sargs = [arg.to_code(codegen) for arg in self.args]
        codegen.write_to(self.result,
            "supportcode.vector_update_inplace(machine, %s, %s, %s, %s)" % (result, sargs[0], sargs[1], sargs[2]))

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
        result = codegen.getname(self.result)
        typ = codegen.gettyp(self.result)
        othertyp = self.value.gettyp(codegen)
        rhs = pair(othertyp, typ).convert(self.value, codegen)
        # hack to make array updates not do a copy
        if rhs.startswith("supportcode.helper_vector_update_list_o_i_o(machine, " + result):

            assert rhs.endswith(")")
            rhs = rhs[:-1] + ", res=%s)" % (result, )
            codegen.emit(rhs) # the function mutates, no need to do the assignment
        else:
            codegen.write_to(self.result, rhs)

class __extend__(parse.StructElementAssignment):
    def make_op_code(self, codegen):
        typ = self.obj.gettyp(codegen)
        for field in self.fields:
            typ = typ.fieldtyps[field]
        othertyp = self.value.gettyp(codegen)
        rhs = pair(othertyp, typ).convert(self.value, codegen)
        codegen.emit("%s.%s = %s" % (self.obj.to_code(codegen), ".".join(self.fields), rhs))

class __extend__(parse.RefAssignment):
    def make_op_code(self, codegen):
        # XXX think long and hard about refs!
        codegen.emit("%s.copy_into(%s)" % (self.value.to_code(codegen), self.ref.to_code(codegen)))

class __extend__(parse.End):
    def make_op_code(self, codegen):
        codegen.emit("return return_")

    def make_op_jump(self, codegen, i):
        pass

class __extend__(parse.Exit):
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
        import pdb; pdb.set_trace()
        result = codegen.gettarget(self.result)
        if name == '$zcons':
            restyp = codegen.gettyp(self.result)
            sargs = [arg.to_code(codegen) for arg in self.args]
            codegen.emit("%s = %s(%s, %s)" % (result, restyp.pyname, sargs[0], sargs[1]))
        else:
            import pdb; pdb.set_trace()
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
    def is_constant(self, codegen):
        return True

    def to_code(self, codegen):
        return str(self.number)

    def gettyp(self, codegen):
        return types.MachineInt()

class __extend__(parse.BitVectorConstant):
    def is_constant(self, codegen):
        return True

    def to_code(self, codegen):
        return "r_uint(%s)" % (self.constant, )

    def gettyp(self, codegen):
        if self.constant.startswith("0b"):
            size = len(self.constant) - 2
        else:
            assert self.constant.startswith("0x")
            size = (len(self.constant) - 2) * 4
        if size <= 64:
            return types.SmallFixedBitVector(size)
        else:
            return types.BigFixedBitVector(size)

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


class __extend__(parse.StructConstruction):
    def to_code(self, codegen):
        typ = self.gettyp(codegen)
        ast_type = typ.ast
        sargs = []
        for name, arg in zip(self.fieldnames, self.fieldvalues):
            fieldtyp = typ.fieldtyps[name]
            valuetyp = arg.gettyp(codegen)
            sargs.append(pair(valuetyp, fieldtyp).convert(arg, codegen))
        assert self.fieldnames == ast_type.names
        return "%s(%s)" % (ast_type.pyname, ", ".join(sargs))

    def gettyp(self, codegen):
        return codegen.get_named_type(self.name)

class __extend__(parse.FieldAccess):
    def to_code(self, codegen):
        obj = self.obj
        if isinstance(self.obj, parse.StructConstruction):
            index = self.obj.fieldnames.index(self.element)
            return self.obj.fieldvalues[index].to_code(codegen)
        if isinstance(obj, parse.Cast):
            return "%s.convert_%s(%s)" % (codegen.getname(obj.variant), self.element, obj.expr.to_code(codegen))
        objtyp = obj.gettyp(codegen)
        res = "%s.%s" % (self.obj.to_code(codegen), self.element)
        if isinstance(objtyp, types.Struct) and self.element in codegen.promoted_registers:
            return "jit.promote(%s)" % res
        return res

    def gettyp(self, codegen):
        if isinstance(self.obj, parse.StructConstruction):
            index = self.obj.fieldnames.index(self.element)
            return self.obj.fieldvalues[index].gettyp(codegen)
        objtyp = self.obj.gettyp(codegen)
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
        if isinstance(self.expr.gettyp(codegen), types.Struct):
            return expr
        assert isinstance(self.expr, parse.Var)
        return repr("crashmenow")

    def gettyp(self, codegen):
        return types.Ref(self.expr.gettyp(codegen))

class __extend__(parse.String):
    def to_code(self, codegen):
        return self.string

    def gettyp(self, codegen):
        return types.String()

class __extend__(parse.OperationExpr):
    def gettyp(self, codegen):
        return self.resolved_type

    def to_code(self, codegen):
        name = self.name
        sargs = [arg.to_code(codegen) for arg in self.args]
        argtyps = [arg.gettyp(codegen) for arg in self.args]
        restyp = self.gettyp(codegen)
        if name in codegen.globalnames:
            n = codegen.globalnames[name].pyname
            if "eq_string" in name:
                name = "@eq"
            elif name == "znot_bool":
                name = "@not"
            elif n == "supportcode.eq_anything":
                name = "@eq"
            elif n == "supportcode.cons":
                return "%s(%s, %s)" % (restyp.pyname, sargs[0], sargs[1])


        if name.startswith("@"):
            meth = getattr(argtyps[0], "make_op_code_special_" + name[1:], None)
            if meth:
                return meth(self, sargs, argtyps, restyp)
        elif name.startswith("$zinternal_vector_init"): # magic vector stuff
            oftyp = restyp.typ
            return "[%s] * %s" % (oftyp.uninitialized_value, sargs[0])

        if not sargs:
            args = '()'
        else:
            args = ", ".join(sargs)
        op = codegen.getname(name)
        info = codegen.getinfo(name)
        if isinstance(info.typ, types.Function):
            if (op.startswith("supportcode.") and
                    all(arg.is_constant(codegen) for arg in self.args) and
                    can_constfold(op)):
                folded_result = constfold(op, sargs, self, codegen)
                return folded_result
            else:
                # pass machine, even to supportcode functions
                return "%s(machine, %s)" % (op, args)
        elif isinstance(info.typ, types.Union):
            return info.ast.constructor(info, op, args, argtyps)
        elif name.startswith(("@", "$")):
            return "%s(machine, %s)" % (op, args)
        else:
            # constructors etc don't get machine passed (yet)
            return "%s(%s)" % (op, args)

class __extend__(parse.CastExpr):
    def gettyp(self, codegen):
        return self.resolved_type

    def to_code(self, codegen):
        typ = self.gettyp(codegen)
        expr = self.expr
        while isinstance(expr, parse.CastExpr):
            expr = expr.expr
        othertyp = expr.gettyp(codegen)
        return pair(othertyp, typ).convert(expr, codegen)

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
                return getattr(argtyps[0], "make_op_code_special_" + op[1:])(self, sargs, argtyps, types.Bool())
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
            with codegen.emit_indent("class %s(supportcode.ObjectBase): # %s" % (pyname, self)):
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

class __extend__(parse.FVecType):
    def resolve_type(self, codegen):
        return types.FVec(self.number, self.of.resolve_type(codegen))

class __extend__(parse.TupleType):
    def resolve_type(self, codegen):
        typ = types.Tuple(tuple([e.resolve_type(codegen) for e in self.elements]))
        with codegen.cached_declaration(typ, "Tuple") as pyname:
            with codegen.emit_indent("class %s(supportcode.ObjectBase): # %s" % (pyname, self)):
                codegen.emit("@objectmodel.always_inline")
                with codegen.emit_indent("def eq(self, other):"):
                    codegen.emit("assert isinstance(other, %s)" % (pyname, ))
                    for index, fieldtyp in enumerate(self.elements):
                        rtyp = fieldtyp.resolve_type(codegen)
                        codegen.emit("if %s: return False # %s" % (
                            rtyp.make_op_code_special_neq(None, ('self.utup%s' % index, 'other.utup%s' % index), (rtyp, rtyp), types.Bool()), fieldtyp))
                    codegen.emit("return True")
            typ.pyname = pyname
        typ.uninitialized_value = "%s()" % (pyname, )
        return typ


def can_constfold(op):
    return op in {"supportcode.int64_to_int"}

def constfold(op, sargs, ast, codegen):
    if op == "supportcode.int64_to_int":
        name = "smallintconst%s" % sargs[0]
        name = name.replace("-", "_minus_")
        with codegen.cached_declaration(sargs[0], name) as pyname:
            codegen.emit("%s = bitvector.SmallInteger(%s)" % (pyname, sargs[0]))
        return pyname
    else:
        assert 0
