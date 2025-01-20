import os
import sys
import time
from contextlib import contextmanager
from rpython.tool.pairtype import pair

from pydrofoil import parse, types, binaryop, operations, supportcode, specialize
from pydrofoil.emitfunction import emit_function_code


assert sys.maxint == 2 ** 63 - 1, "only 64 bit platforms are supported!"

class NameInfo(object):
    def __init__(self, pyname, typ, ast, write_pyname=None):
        self.pyname = pyname
        self.typ = typ
        self.ast = ast
        self.write_pyname = write_pyname

    def __repr__(self):
        return "NameInfo(%r, %r, %r, %r)" % (self.pyname, self.typ, self.ast, self.write_pyname)


class Codegen(specialize.FixpointSpecializer):
    def __init__(self, promoted_registers=frozenset(), should_inline=None, entrypoints=None):
        specialize.FixpointSpecializer.__init__(self, entrypoints=entrypoints)
        self.declarations = []
        self.runtimeinit = []
        self.code = []
        self.level = 0
        self.last_enum = 0
        self.globalnames = {}
        self.builtin_names = {}
        self.namedtypes = {}
        self.tuplestruct = {}
        # seen typs
        self.seen_typs = set()
        self.declarationcache = {}
        self.gensym = {} # prefix -> number
        self.localnames = None
        for name, (spec, unwrapped_name) in supportcode.all_unwraps.iteritems():
            self.add_global("@" + unwrapped_name, "supportcode." + unwrapped_name)
        self.add_global("false", "False", types.Bool())
        self.add_global("true", "True", types.Bool())
        self.add_global("bitzero", "r_uint(0)", types.Bit())
        self.add_global("bitone", "r_uint(1)", types.Bit())
        self.add_global("$zupdate_fbits", "supportcode.zupdate_fbits")
        self.add_global("@vector_subrange_fixed_bv_i_i", "supportcode.vector_subrange_fixed_bv_i_i")
        self.add_global("@vector_update_subrange_fixed_bv_i_i_bv", "supportcode.vector_update_subrange_fixed_bv_i_i_bv")
        self.add_global("@slice_fixed_bv_i_i", "supportcode.slice_fixed_bv_i_i")
        self.add_global("@vector_subrange_o_i_i_unwrapped_res", "supportcode.vector_subrange_o_i_i_unwrapped_res")
        self.add_global("@vector_slice_o_i_i_unwrapped_res", "supportcode.vector_slice_o_i_i_unwrapped_res")
        self.add_global("@helper_vector_update_inplace_o_i_o", "supportcode.helper_vector_update_inplace_o_i_o")
        self.add_global("@eq_bits", "supportcode.eq_bits")
        self.add_global("@eq_bits_bv_bv", "supportcode.eq_bits_bv_bv")
        self.add_global("@neq_bits_bv_bv", "supportcode.neq_bits_bv_bv")
        self.add_global("@eq_int_o_i", "supportcode.eq_int_o_i")
        self.add_global("@eq_int_i_i", "supportcode.eq_int_i_i")
        self.add_global("@add_i_i_wrapped_res", "supportcode.add_i_i_wrapped_res")
        self.add_global("@add_i_i_must_fit", "supportcode.add_i_i_must_fit")
        self.add_global("@add_o_i_wrapped_res", "supportcode.add_o_i_wrapped_res")
        self.add_global("@add_unsigned_bv64_unsigned_bv64_wrapped_res", "supportcode.add_unsigned_bv64_unsigned_bv64_wrapped_res")
        self.add_global("@lteq_add4_unsigned_bv64", "supportcode.lteq_add4_unsigned_bv64")
        self.add_global("@sub_i_i_wrapped_res", "supportcode.sub_i_i_wrapped_res")
        self.add_global("@sub_i_i_must_fit", "supportcode.sub_i_i_must_fit")
        self.add_global("@sub_o_i_wrapped_res", "supportcode.sub_o_i_wrapped_res")
        self.add_global("@sub_i_o_wrapped_res", "supportcode.sub_i_o_wrapped_res")
        self.add_global("@mult_i_i_wrapped_res", "supportcode.mult_i_i_wrapped_res")
        self.add_global("@mult_i_i_must_fit", "supportcode.mult_i_i_must_fit")
        self.add_global("@mult_o_i_wrapped_res", "supportcode.mult_o_i_wrapped_res")
        self.add_global("@ediv_int_i_ipos", "supportcode.ediv_int_i_ipos")
        self.add_global("@tdiv_int_i_i", "supportcode.tdiv_int_i_i")
        self.add_global("@unsigned_bv64_rshift_int_result", "supportcode.unsigned_bv64_rshift_int_result")
        self.add_global("@shl_int_i_i_wrapped_res", "supportcode.shl_int_i_i_wrapped_res")
        self.add_global("@shl_int_i_i_must_fit", "supportcode.shl_int_i_i_must_fit")
        self.add_global("@get_slice_int_i_o_i_unwrapped_res", "supportcode.get_slice_int_i_o_i_unwrapped_res")
        self.add_global("@get_slice_int_i_i_i", "supportcode.get_slice_int_i_i_i")
        self.add_global("@xor_vec_bv_bv", "supportcode.xor_vec_bv_bv")
        self.add_global("@or_vec_bv_bv", "supportcode.or_vec_bv_bv")
        self.add_global("@and_vec_bv_bv", "supportcode.and_vec_bv_bv")
        self.add_global("@not_vec_bv", "supportcode.not_vec_bv")
        self.add_global("@bitvector_concat_bv_bv", "supportcode.bitvector_concat_bv_bv")
        self.add_global("@bitvector_concat_bv_gbv_wrapped_res", "supportcode.bitvector_concat_bv_gbv_wrapped_res")
        self.add_global("@bitvector_concat_bv_n_zeros_wrapped_res", "supportcode.bitvector_concat_bv_n_zeros_wrapped_res")
        self.add_global("@bitvector_concat_bv_gbv_truncate_to", "supportcode.bitvector_concat_bv_gbv_truncate_to")
        self.add_global("@bitvector_concat_bv_bv_n_zeros_truncate", "supportcode.bitvector_concat_bv_bv_n_zeros_truncate")
        self.add_global("@ones_zero_extended_unwrapped_res", "supportcode.ones_zero_extended_unwrapped_res")
        self.add_global("@signed_bv", "supportcode.signed_bv")
        self.add_global("@unsigned_bv_wrapped_res", "supportcode.unsigned_bv_wrapped_res")
        self.add_global("@unsigned_bv", "supportcode.unsigned_bv")
        self.add_global("@zero_extend_bv_i_i", "supportcode.zero_extend_bv_i_i")
        self.add_global("@zero_extend_o_i_unwrapped_res", "supportcode.zero_extend_o_i_unwrapped_res")
        self.add_global("@sign_extend_bv_i_i", "supportcode.sign_extend_bv_i_i")
        self.add_global("@sign_extend_o_i_unwrapped_res", "supportcode.sign_extend_o_i_unwrapped_res")
        self.add_global("@vector_access_bv_i", "supportcode.vector_access_bv_i")
        self.add_global("@add_bits_bv_bv", "supportcode.add_bits_bv_bv")
        self.add_global("@add_bits_int_bv_i", "supportcode.add_bits_int_bv_i")
        self.add_global("@sub_bits_bv_bv", "supportcode.sub_bits_bv_bv")
        self.add_global("@sub_bits_int_bv_i", "supportcode.sub_bits_int_bv_i")
        self.add_global("@shiftl_bv_i", "supportcode.shiftl_bv_i")
        self.add_global("@shiftr_bv_i", "supportcode.shiftr_bv_i")
        self.add_global("@arith_shiftr_bv_i", "supportcode.arith_shiftr_bv_i")
        self.add_global("@length_unwrapped_res", "supportcode.length_unwrapped_res")
        self.add_global("@vec_length_unwrapped_res", "supportcode.vec_length_unwrapped_res")
        self.add_global("@truncate_unwrapped_res", "supportcode.truncate_unwrapped_res")
        self.add_global("@truncate_bv_i", "supportcode.truncate_bv_i")
        self.add_global("@replicate_bv_i_i", "supportcode.replicate_bv_i_i")
        self.add_global("@platform_read_mem_o_i_bv_i", "supportcode.platform_read_mem_o_i_bv_i")
        self.add_global("@fast_read_mem_i_bv_i_isfetch_isexclusive", "supportcode.fast_read_mem_i_bv_i_isfetch_isexclusive")
        self.add_global("@lt_unsigned64", "supportcode.lt_unsigned64")
        self.add_global("@lteq_unsigned64", "supportcode.lteq_unsigned64")
        self.add_global("@gteq_unsigned64", "supportcode.gteq_unsigned64")
        self.add_global("@pack_smallfixedbitvector", "supportcode.pack_smallfixedbitvector")
        self.add_global("@pack_machineint", "supportcode.pack_machineint")
        self.add_global("@packed_field_cast_smallfixedbitvector", "supportcode.packed_field_cast_smallfixedbitvector")
        self.add_global("@packed_field_int_to_int64", "supportcode.packed_field_int_to_int64")
        self.add_global("zsail_assert", "supportcode.sail_assert")
        self.add_global("UINT64_C", "supportcode.uint64c")
        self.add_global("NULL", "None")
        self.add_global("have_exception", "machine.have_exception", types.Bool(), write_pyname="machine.have_exception")
        self.add_global("throw_location", "machine.throw_location", types.String(), write_pyname="machine.throw_location")
        self.promoted_registers = promoted_registers
        self.all_registers = {}
        self.inlinable_functions = {}
        # a function that returns True, False or None
        self.should_inline = should_inline if should_inline is not None else lambda name: None
        self.let_values = {}
        # (graphs, funcs, args, kwargs) to emit at the end
        self._all_graphs = []

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
    def emit_indent(self, line=None):
        if line is not None:
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
        self.finish_graphs()
        res = ["\n".join(self.declarations)]
        res.append("def let_init(machine):\n    " + "\n    ".join(self.runtimeinit or ["pass"]))
        res.append("\n".join(self.code))
        res.append("let_init(Machine)")
        return "\n\n".join(res)

    def emit_extra_graph(self, graph, functyp):
        pyname = "func_" + graph.name
        self.add_global(graph.name, pyname, functyp)
        args = [arg.name for arg in graph.args]
        first = "def %s(machine, %s):" % (pyname, ", ".join(args))
        def emit_extra(graph, codegen):
            with self.emit_indent(first):
                emit_function_code(graph, None, codegen)
        self.add_graph(graph, emit_extra)

    def add_graph(self, graph, emit_function, *args, **kwargs):
        self.schedule_graph_specialization(graph)
        self._all_graphs.append((graph, emit_function, args, kwargs))

    def finish_graphs(self):
        self.print_persistent_msg("============== FINISHING ==============")
        from pydrofoil.ir import print_stats
        t1 = time.time()
        self.specialize_all()
        unspecialized_graphs = []
        if self.program_entrypoints is None:
            program_entrypoints = [g for g, _, _, _ in self._all_graphs]
        else:
            program_entrypoints = self.program_entrypoints + ["zinitializze_registers"]
            program_entrypoints = [self.all_graph_by_name[name] for name in program_entrypoints]
        extra_graphs = self.extract_needed_extra_graphs(program_entrypoints)
        graphs_to_emit = set(program_entrypoints)
        for graph, typ in extra_graphs:
            if typ is not None:
                self.emit_extra_graph(graph, typ)
            graphs_to_emit.add(graph)
        for graph, func, args, kwargs in self._all_graphs:
            if graph in graphs_to_emit:
                func(graph, self, *args, **kwargs)
        t2 = time.time()
        self.print_persistent_msg("DONE, took seconds", round(t2 - t1, 2))
        print_stats()

    def add_struct_type(self, name, pyname, structtyp, ast=None):
        if structtyp in self.seen_typs:
            return
        self.seen_typs.add(structtyp)
        #if sum(bits_needed(typ) for typ in structtyp.typs) <= 64:
        #    import pdb;pdb.set_trace()
        self.add_named_type(name, pyname, structtyp, ast)
        uninit_arg = []
        with self.emit_code_type("declarations"), self.emit_indent("class %s(supportcode.ObjectBase):" % pyname):
            self.emit("@objectmodel.always_inline")
            with self.emit_indent("def __init__(self, %s):" % ", ".join(structtyp.names)):
                for arg, fieldtyp in zip(structtyp.names, structtyp.internaltyps):
                    fieldname = "self." + arg
                    self.emit(fieldtyp.packed_field_write(fieldname, arg, bare=True))
                    uninit_arg.append(fieldtyp.uninitialized_value)
            #self.emit("@objectmodel.always_inline")
            with self.emit_indent("def copy_into(self, machine, res=None):"):
                self.emit("if res is None: res = objectmodel.instantiate(self.__class__)")
                for arg, fieldtyp in zip(structtyp.names, structtyp.typs):
                    self.emit(fieldtyp.packed_field_copy("res.%s" % arg, "self.%s" % arg))
                self.emit("return res")
            self.emit("@objectmodel.always_inline")
            with self.emit_indent("def eq(self, other):"):
                self.emit("assert isinstance(other, %s)" % (pyname, ))
                for arg, fieldtyp in zip(structtyp.names, structtyp.typs):
                    leftfield = fieldtyp.packed_field_read('self.%s' % arg)
                    rightfield = fieldtyp.packed_field_read('other.%s' % arg)
                    self.emit("if %s: return False" % (
                        fieldtyp.make_op_code_special_neq(None, (leftfield, rightfield), (fieldtyp, fieldtyp), types.Bool())))
                self.emit("return True")
        structtyp.uninitialized_value = "%s(%s)" % (pyname, ", ".join(uninit_arg))

def parse_and_make_code(s, support_code, promoted_registers=set(), should_inline=None, entrypoints=None):
    from pydrofoil.infer import infer
    t1 = time.time()
    ast = parse.parser.parse(parse.lexer.lex(s))
    t2 = time.time()
    print "parsing took", round(t2 - t1, 2)
    context = infer(ast)
    t3 = time.time()
    print "infer took", round(t3 - t2, 2)
    c = Codegen(promoted_registers, should_inline=should_inline, entrypoints=entrypoints)
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
        c.emit("    l = Lets()")
        c.emit("    def __init__(self):")
        c.emit("        self.l  = Machine.l; func_zinitializze_registers(self, ())")
        c.emit("        self.g = supportcode.Globals()")
        c.emit("UninitInt = bitvector.Integer.fromint(-0xfefee)")
    ast.make_code(c)
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
        t1 = time.time()
        for index, decl in enumerate(self.declarations):
            codegen.print_highlevel_task("MAKING IR FOR %s/%s" % (index, len(self.declarations)), type(decl).__name__, getattr(decl, "name", decl))
            try:
                decl.make_code(codegen)
            except Exception as e:
                import pdb
                if os.getenv("GITHUB_ACTIONS") is None and hasattr(pdb, 'xpm'):
                    pdb.xpm()
                print failure_count, "COULDN'T GENERATE CODE FOR", index, getattr(decl, "name", decl)
                print(traceback.format_exc())
                failure_count += 1
                codegen.level = 0
            codegen.emit()
        t2 = time.time()
        codegen.print_persistent_msg("AST WALKING DONE, took seconds:", round(t2 - t1, 2))

class __extend__(parse.Declaration):
    def make_code(self, codegen):
        raise NotImplementedError("abstract base class")

class __extend__(parse.Enum):
    def resolve_type(self, codegen):
        return types.Enum(self.name, tuple(self.names))

    def make_code(self, codegen):
        name = "Enum_" + self.name
        typ = self.resolve_type(codegen)
        self.pyname = name
        codegen.add_global(self.name, self.pyname, typ, self)
        with codegen.emit_code_type("declarations"):
            with codegen.emit_indent("class %s(supportcode.ObjectBase):" % name):
                for index, name in enumerate(self.names, start=codegen.last_enum):
                    codegen.add_global(name, "%s.%s" % (self.pyname, name), typ, self)
                    codegen.emit("%s = %s" % (name, index))
                codegen.emit("@staticmethod")
                with codegen.emit_indent("def convert_to_uint(e):"):
                    codegen.emit("return r_uint(e - %s.%s)" % (self.pyname, self.names[0]))

                codegen.emit("@staticmethod")
                with codegen.emit_indent("def convert_from_uint(u):"):
                    codegen.emit("res = intmask(u) + %s.%s" % (self.pyname, self.names[0]))
                    codegen.emit("assert res <= %s.%s" % (self.pyname, self.names[-1]))
                    codegen.emit("return res")

                codegen.last_enum += len(self.names) + 1 # gap of 1
                codegen.add_named_type(self.name, self.pyname, typ, self)

class __extend__(parse.Union):
    def make_code(self, codegen):
        name = "Union_" + self.name
        self.pyname = name
        # pre-declare the types
        rtyps = [typ.resolve_type(codegen) for typ in self.types]
        with codegen.emit_code_type("declarations"):
            self.pynames = []
            names = tuple(self.names)
            uniontyp = types.Union(self.name, names, tuple(rtyps))
            codegen.add_named_type(self.name, self.pyname, uniontyp, self)
            uniontyp.compact_union = False
            bits = bits_needed(uniontyp) 
            if bits <= 64:
                uniontyp.compact_union = True
                self._implement_compact_union(codegen, uniontyp)
                return
            with codegen.emit_indent("class %s(supportcode.ObjectBase):" % name):
                codegen.emit("@objectmodel.always_inline")
                with codegen.emit_indent("def eq(self, other):"):
                    codegen.emit("return False")
            codegen.emit("%s.singleton = %s()" % (name, name))
            uniontyp.uninitialized_value = "%s.singleton" % (name, )
            for name, typ in zip(self.names, self.types):
                rtyp = typ.resolve_type(codegen)
                pyname = self.pyname + "_" + name
                codegen.add_global(name, pyname, uniontyp, self)
                self.pynames.append(pyname)
                with codegen.emit_indent("class %s(%s):" % (pyname, self.pyname)):
                    # default field values
                    if type(rtyp) is types.Struct:
                        for fieldname, fieldtyp in sorted(rtyp.internalfieldtyps.iteritems()):
                            codegen.emit(fieldtyp.packed_field_write(fieldname, fieldtyp.uninitialized_value, bare=True))
                    elif rtyp is not types.Unit():
                        codegen.emit("a = %s" % (rtyp.uninitialized_value, ))
                    self.make_init(codegen, rtyp, typ, pyname)
                    self.make_eq(codegen, rtyp, typ, pyname)
                    self.make_convert(codegen, rtyp, typ, pyname)
                    self.make_check_variant(codegen, rtyp, typ, pyname)
                if rtyp is types.Unit():
                    codegen.emit("%s.singleton = %s(())" % (pyname, pyname))
                if type(rtyp) is types.Enum:
                    # for enum union options, we make singletons
                    for enum_value in rtyp.elements:
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
                for enum_value in rtyp.elements:
                    codegen.emit("if a == %s: return %s_%s.singleton" % (codegen.getname(enum_value), pyname, enum_value))
                codegen.emit("raise ValueError")
            return
        with codegen.emit_indent("def __init__(self, a):"):
            if rtyp is types.Unit():
                codegen.emit("pass")
            elif type(rtyp) is types.Struct:
                codegen.emit("# %s" % typ)
                for fieldname, fieldtyp in sorted(rtyp.fieldtyps.iteritems()):
                    codegen.emit(fieldtyp.packed_field_copy("self.%s" % fieldname, "a.%s" % (fieldname, )))
            else:
                codegen.emit("self.a = a # %s" % (typ, ))

    def make_eq(self, codegen, rtyp, typ, pyname):
        codegen.emit("@objectmodel.always_inline")
        with codegen.emit_indent("def eq(self, other):"):
            codegen.emit("if type(self) is not type(other): return False")
            codegen.emit("assert isinstance(other, %s)" % pyname)
            if rtyp is types.Unit():
                codegen.emit("return True")
                return
            elif type(rtyp) is types.Struct:
                codegen.emit("# %s" % typ)
                for fieldname, fieldtyp in sorted(rtyp.fieldtyps.iteritems()):
                    codegen.emit("if %s: return False" % (
                        fieldtyp.make_op_code_special_neq(
                            None,
                            (rtyp.packed_field_read('self.%s' % fieldname), rtyp.packed_field_read('other.%s' % fieldname)),
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
                        codegen.emit(fieldtyp.packed_field_copy("res.%s" % fieldname, "inst.%s" % (fieldname, )))
                    codegen.emit("return res")
                else:
                    codegen.emit("return inst.a")
            with codegen.emit_indent("else:"):
                codegen.emit("raise TypeError")

    def make_check_variant(self, codegen, rtyp, typ, pyname):
        codegen.emit("@staticmethod")
        codegen.emit("@objectmodel.always_inline")
        with codegen.emit_indent("def check_variant(inst):"):
            codegen.emit("return isinstance(inst, %s)" % pyname)

    def constructor(self, info, op, args, argtyps):
        if info.typ.compact_union or (len(argtyps) == 1 and type(argtyps[0]) is types.Enum):
            return "%s.construct(%s)" % (op, args)
        if argtyps == [types.Unit()]:
            return "%s.singleton" % (op, )
        return "%s(%s)" % (op, args)

    def _implement_compact_union(self, codegen, uniontyp):
        from rpython.rlib.rarithmetic import r_uint
        bits_tag = len(uniontyp.typs).bit_length()
        with codegen.emit_indent("class %s(object): # only used as namespace" % self.pyname):
            codegen.emit("SHIFT = %s" % (bits_tag, ))
            codegen.emit("TAG_MASK = 0x%x" % ((1 << bits_tag) - 1, ))

            for number, (name, typ) in enumerate(zip(self.names, self.types)):
                codegen.emit("%s_tag = r_uint(0x%x)" % (name, number))
            number += 1
            uninitialized_value = r_uint(hash(str(uniontyp))) # deterministic and based on the type
            uninitialized_value = (uninitialized_value << bits_tag) | number
            codegen.emit("UNINIT = r_uint(0x%x)" % (uninitialized_value, ))
        uniontyp.uninitialized_value = "%s.UNINIT" % (self.pyname, )
        for name, typ in zip(self.names, self.types):
            rtyp = typ.resolve_type(codegen)
            pyname = self.pyname + "_" + name
            codegen.add_global(name, pyname, uniontyp, self)
            self.pynames.append(pyname)
            with codegen.emit_indent("class %s(%s):" % (pyname, self.pyname)):
                codegen.emit("# typ: %s" % rtyp)
                codegen.emit("@staticmethod")
                codegen.emit("@objectmodel.specialize.arg_or_var(0)")
                with codegen.emit_indent("def construct(a):"):
                    codegen.emit("tag = %s.%s_tag" % (self.pyname, name))
                    converted = to_uint_bits(codegen, rtyp, 'a')
                    codegen.emit("return (%s << %s.SHIFT) | tag" % (converted, self.pyname))
                codegen.emit()
                codegen.emit("@staticmethod")
                codegen.emit("@objectmodel.specialize.arg_or_var(0)")
                with codegen.emit_indent("def check_variant(a):"):
                    codegen.emit("tag = %s.%s_tag" % (self.pyname, name))
                    codegen.emit("return a & %s.TAG_MASK == tag" % (self.pyname, ))
                codegen.emit()
                codegen.emit("@staticmethod")
                codegen.emit("@objectmodel.specialize.arg_or_var(0)")
                with codegen.emit_indent("def convert(u):"):
                    codegen.emit("tag = %s.%s_tag" % (self.pyname, name))
                    codegen.emit("assert u & %s.TAG_MASK == tag" % (self.pyname, ))
                    codegen.emit("u >>= %s.SHIFT" % (self.pyname, ))
                    converted = from_uint_bits(codegen, rtyp, 'u')
                    codegen.emit("return %s" % (converted, ))

def to_uint_bits(codegen, typ, name):
    if isinstance(typ, types.Enum):
        typname = codegen.getname(typ.name)
        return '%s.convert_to_uint(%s)' % (typname, name)
    elif isinstance(typ, types.SmallFixedBitVector):
        return name
    elif isinstance(typ, types.Unit):
        return '0'
    elif isinstance(typ, types.Bool):
        return 'r_uint(%s)' % name
    elif isinstance(typ, types.Union):
        assert typ.compact_union
        return name
    else:
        assert 0

def from_uint_bits(codegen, typ, name):
    if isinstance(typ, types.Enum):
        typname = codegen.getname(typ.name)
        return '%s.convert_from_uint(%s)' % (typname, name)
    elif isinstance(typ, types.SmallFixedBitVector):
        return 'supportcode.debug_check_bv_fits(%s, %s)'  % (name, typ.width)
    elif isinstance(typ, types.Unit):
        return ()
    elif isinstance(typ, types.Bool):
        return 'bool(%s)' % name
    elif isinstance(typ, types.Union):
        assert typ.compact_union
        return name
    else:
        assert 0

def bits_needed(typ):
    if isinstance(typ, types.Enum):
        return len(typ.elements).bit_length()
    elif isinstance(typ, types.SmallFixedBitVector):
        return typ.width
    elif isinstance(typ, types.Unit):
        return 1
    elif isinstance(typ, types.Bool):
        return 1
    #elif isinstance(typ, types.Struct):
    #    return sum(bits_needed(typ) for typ in typ.typs)
    elif isinstance(typ, types.Union):
        bits_tag = len(typ.typs).bit_length() # over-approximation
        return max(bits_needed(typ) for typ in typ.typs) + bits_tag
    #elif isinstance(typ, (types.String, types.GenericBitVector, types.Int)):
    #    return sys.maxint
    return sys.maxint

class __extend__(parse.Struct):
    def make_code(self, codegen):
        name = self.name
        pyname = "Struct_" + name
        self.pyname = pyname
        # predeclare types
        typs = [typ.resolve_type(codegen) for typ in self.types]
        tuplestruct = name in codegen.tuplestruct
        structtyp = types.Struct(name, tuple(self.names), tuple(typs), tuplestruct)
        codegen.add_struct_type(name, pyname, structtyp, ast=self)


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
                elif name == "%vec(%bv)->%vec(%bv8)":
                    name = "vec_gbv_to_vec_bv8"
                elif name == "%vec(%bv)->%vec(%bv16)":
                    name = "vec_gbv_to_vec_bv16"
                else:
                    import pdb; pdb.set_trace()
            if name == "not": name = "not_"
            if name == "print": name = "print_"
            funcname = "supportcode.%s" % (name, )

            if name == "cons":
                funcname = self.resolved_type.restype.pyname
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
        from pydrofoil.ir import construct_ir
        self.pyname = "_reg_%s" % (self.name, )
        typ = self.typ.resolve_type(codegen)
        read_pyname = write_pyname = "machine.%s" % self.pyname
        if self.name in codegen.promoted_registers:
            read_pyname = "jit.promote(%s)" % write_pyname
        elif isinstance(typ, types.Struct):
            register_ref_name = self.make_register_ref(codegen, read_pyname)
            read_pyname = "%s.deref(machine)" % (register_ref_name, )
            write_pyname = "%s.update_with(machine, %%s)" % (register_ref_name, )
        else:
            read_pyname = typ.packed_field_read(read_pyname)
            write_pyname = typ.packed_field_write(write_pyname, '%s') # bit too much string processing magic
        codegen.all_registers[self.name] = self
        codegen.add_global(self.name, read_pyname, typ, self, write_pyname)
        with codegen.emit_code_type("declarations"):
            codegen.emit("Machine.%s = %s" % (self.pyname, typ.uninitialized_value))

        if self.body is None:
            return
        with codegen.emit_code_type("runtimeinit"), codegen.enter_scope(self):
            graph = construct_ir(self, codegen, singleblock=True)
            emit_function_code(graph, self, codegen)

    def make_register_ref(self, codegen, read_pyname=None):
        if hasattr(self, 'register_ref_name'):
            return self.register_ref_name
        if read_pyname is None:
            read_pyname = codegen.globalnames[self.name].pyname
        typ = self.typ.resolve_type(codegen)
        name = "ref_%s" % (self.pyname, )
        with codegen.cached_declaration(self.name, name) as pyname:
            with codegen.emit_indent("class %s(supportcode.RegRef):" % (pyname, )):
                with codegen.emit_indent("def deref(self, machine):"):
                    codegen.emit("return %s" % (read_pyname, ))
                with codegen.emit_indent("def update_with(self, machine, res):"):
                    if isinstance(typ, types.Struct):
                        codegen.emit("res.copy_into(machine, machine.%s)" % (self.pyname, ))
                    else:
                        codegen.emit("assert 0, 'not implemented'")
            codegen.emit("%s = %s() # singleton" % (pyname, pyname))
            self.register_ref_name = pyname
        return pyname

def iterblockops(blocks):
    for blockpc, block in sorted(blocks.items()):
        for op in block:
            yield blockpc, op


class __extend__(parse.Function):
    def make_code(self, codegen):
        from pydrofoil.ir import construct_ir, should_inline
        from pydrofoil.specialize import Specializer, usefully_specializable
        from pydrofoil.splitgraph import split_completely
        pyname = codegen.getname(self.name)
        assert pyname.startswith("func_")
        #if codegen.globalnames[self.name].pyname is not None:
        #    print "duplicate!", self.name, codegen.globalnames[self.name].pyname
        #    return
        self.pyname = pyname
        typ = codegen.globalnames[self.name].ast.typ
        blocks = self._prepare_blocks()
        if self.detect_union_switch(blocks[0]):
            codegen.print_debug_msg("making method!", self.name)
            self._emit_methods(blocks, codegen)
            return
        codegen.print_debug_msg("making SSA IR")
        graph = construct_ir(self, codegen)
        inlinable = should_inline(graph, codegen.should_inline)
        if inlinable:
            codegen.inlinable_functions[self.name] = graph
        elif not graph.has_loop and graph.has_more_than_n_blocks(150):
            codegen.print_debug_msg("splitting", self.name)
            functyp = codegen.globalnames[self.name].typ
            for graph2, graph2typ in split_completely(graph, self, functyp, codegen):
                codegen.add_global(graph2.name, graph2.name, graph2typ)
                codegen.add_graph(graph2, self.emit_regular_function, graph2.name)
        else:
            if usefully_specializable(graph):
                codegen.specialization_functions[self.name] = Specializer(graph, codegen)

        codegen.add_graph(graph, self.emit_regular_function, pyname)
        del self.body # save memory, don't need to keep the parse tree around

    def emit_regular_function(self, graph, codegen, pyname):
        with self._scope(codegen, pyname, actual_args=graph.args):
            emit_function_code(graph, self, codegen)
        codegen.emit()

    @contextmanager
    def _scope(self, codegen, pyname, method=False, actual_args=None):
        # extra_args is a list of tuples (name, typ)
        if actual_args is not None:
            args = [arg.name for arg in actual_args]
        else:
            args = self.args
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
            if actual_args:
                for arg in actual_args:
                    codegen.add_local(arg.name, arg.name, arg.resolved_type, self)
            yield

    def _prepare_blocks(self):
        # bring operations into a block format:
        # a dictionary {label-as-int: [list of operations]}
        # every list of operations ends with a goto, return or failure

        # first check which ops can be jumped to
        jumptargets = {getattr(op, 'target', 0) for op in self.body}
        for i, op in enumerate(self.body):
            if isinstance(op, parse.ConditionalJump):
                jumptargets.add(i + 1)

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

    def _emit_methods(self, blocks, codegen):
        from pydrofoil.ir import build_ssa
        typ = codegen.globalnames[self.name].typ
        uniontyp = typ.argtype.elements[0]
        # make the implementations
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
        generated_for_class = {}
        for i, (block, oldpc, cond) in enumerate(switches):
            if cond is not None:
                clsname = codegen.getname(cond.condition.variant)
                known_cls = cond.condition.variant
            else:
                clsname = codegen.namedtypes[uniontyp.name].pyname
                known_cls = None
            if clsname in generated_for_class:
                continue
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
            propername = self.name
            try:
                self.name += "_" + (cond.condition.variant if cond else "default")
                graph = build_ssa(local_blocks, self, self.args, codegen, startpc=oldpc)
                pyname = self.name
            finally:
                self.name = propername
            generated_for_class[clsname] = pyname, known_cls
            codegen.add_graph(graph, self.emit_method, pyname, clsname)
            if codegen.program_entrypoints:
                codegen.program_entrypoints.append(graph.name)
        # make method calling function
        with self._scope(codegen, self.pyname):
            if uniontyp.compact_union:
                # ouch, need to implement tag-based dispatch
                default = None
                basename = codegen.namedtypes[uniontyp.name].pyname
                codegen.emit("tag = %s & %s.TAG_MASK" % (self.args[0], basename, ))
                prefix = ''
                for clsname, (pyname, known_cls) in generated_for_class.iteritems():
                    if not known_cls:
                        default = pyname
                        continue
                    with codegen.emit_indent("%sif tag == %s.%s_tag:" % (prefix, basename, known_cls)):
                        codegen.emit("return %s(%s, machine, %s)"  % (pyname, self.args[0], ", ".join(self.args[1:])))
                    prefix = 'el'
                if default:
                    with codegen.emit_indent("else:"):
                        codegen.emit("return %s(%s, machine, %s)"  % (default, self.args[0], ", ".join(self.args[1:])))
                codegen.emit("assert 0, 'should be unreachable'")
            else:
                basename = codegen.namedtypes[uniontyp.name].pyname
                codegen.emit("return %s.meth_%s(machine, %s)" % (self.args[0], self.name, ", ".join(self.args[1:])))


    def emit_method(self, graph, codegen, pyname, clsname):
        with self._scope(codegen, pyname, method=True):
            emit_function_code(graph, self, codegen)
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

    def _emit_blocks(self, blocks, codegen, entrycounts, startpc=0):
        UNUSED
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
        UNUSED
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
        if self.name == 'tuplestruct':
            codegen.tuplestruct[self.content[0]] = self


class __extend__(parse.Files):
    def make_code(self, codegen):
        codegen.emit("# %s" % (self, ))

class __extend__(parse.Let):
    def make_code(self, codegen):
        from pydrofoil.ir import construct_ir, extract_global_value
        pyname = "machine.l.%s" % self.name
        if isinstance(self.resolved_type, types.Struct):
            read_pyname = pyname + ".copy_into(machine)"
        else:
            read_pyname = pyname
        codegen.add_global(self.name, read_pyname, self.typ.resolve_type(codegen), self, pyname)
        with codegen.emit_code_type("runtimeinit"), codegen.enter_scope(self):
            codegen.emit(" # let %s : %s" % (self.name, self.typ, ))
            graph = construct_ir(self, codegen, singleblock=True)
            emit_function_code(graph, self, codegen)
            value = extract_global_value(graph, self.name)
            if value is not None:
                codegen.let_values[self.name] = value


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
                codegen.emit("def __init__(self, machine, head, tail): self.head, self.tail = head, tail")
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
