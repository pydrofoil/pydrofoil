import sys
from rpython.rlib import jit
from rpython.rlib import objectmodel
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
from rpython.rlib.unroll import unrolling_iterable
from pypy.interpreter.baseobjspace import W_Root
from pypy.interpreter.error import oefmt, oefmt_attribute_error, OperationError
from pypy.interpreter.typedef import (TypeDef, interp2app, GetSetProperty,
    descr_get_dict, make_weakref_descr)
from pypy.interpreter.gateway import unwrap_spec, interpindirect2app, applevel
from pypy.interpreter.module import Module

from riscv import supportcoderiscv

from pydrofoil import mem as mem_mod
from pydrofoil.bitvector import BitVector, ruint_mask
from pydrofoil import types

def _patch_machineclasses(machinecls64=None, machinecls32=None, space=None):
    from riscv import supportcoderiscv
    from riscv.targetriscv import _make_code
    if "machinecls64" in globals():
        return
    if machinecls64 is None:
        if "--dont-regen" in sys.argv:
            from riscv.generated import outriscv as mod64
        else:
            mod64 = _make_code(True)
        machinecls64 = supportcoderiscv.get_main(mod64, True)._machinecls
    if machinecls32 is None:
        if "--dont-regen" in sys.argv:
            from riscv.generated import outriscv32 as mod32
        else:
            mod32 = _make_code(False)
        machinecls32 = supportcoderiscv.get_main(mod32, False)._machinecls
    globals()["machinecls64"] = machinecls64
    globals()["machinecls32"] = machinecls32
    _init_register_names(W_RISCV64, machinecls64._all_register_names)
    _init_register_names(W_RISCV32, machinecls32._all_register_names)
    _init_types(W_RISCV64, machinecls64._all_type_names)
    _init_types(W_RISCV32, machinecls32._all_type_names)
    _init_functions(W_RISCV64, machinecls64._all_functions)
    _init_functions(W_RISCV32, machinecls32._all_functions)
    space.fromcache(W_RISCV64.TypesCache)
    space.fromcache(W_RISCV32.TypesCache)

def wrap_fn(fn):
    def wrapped_fn(space, machine, *args):
        try:
            res = fn(machine, *args)
        except supportcoderiscv.SailError as e:
            w_module = space.getbuiltinmodule('_pydrofoil')
            w_error = space.getattr(w_module, space.newtext('SailAssertionError'))
            raise OperationError(w_error, space.newtext(e.msg))
        except OperationError:
            raise
        except Exception as e:
            if not objectmodel.we_are_translated():
                import pdb; pdb.xpm()
            raise oefmt(space.w_SystemError, "internal error, please report a bug: %s", str(e))
        if machine.have_exception:
            raise oefmt(space.w_SystemError, "sail exception")
        return res
    wrapped_fn.func_name = "wrap_" + fn.func_name
    return wrapped_fn

load_sail = wrap_fn(supportcoderiscv.load_sail)
init_mem = wrap_fn(supportcoderiscv.init_mem)
init_sail = wrap_fn(supportcoderiscv.init_sail)

@wrap_fn
def run_sail(machine, insn_limit, do_show_times):
    machine.run_sail(insn_limit, do_show_times)

@wrap_fn
def initialize_registers(machine):
    machine.initialize_registers()


def _init_register_names(cls, _all_register_names):
    assert cls is not MachineAbstractBase
    """ NOT_RPYTHON """
    def make_getter(attrname, name, convert_to_pypy):
        def getter(space, machine):
            return convert_to_pypy(space, getattr(machine, attrname))
        getter.func_name += "_" + name
        return getter
    def make_setter(attrname, name, convert_from_pypy):
        def setter(space, machine, w_value):
            setattr(machine, attrname, convert_from_pypy(space, w_value))
        setter.func_name += "_" + name
        return setter
    register_info = []
    applevel_register_info = []
    for (attrname, name, convert_to_pypy, convert_from_pypy, sail_type_repr) in _all_register_names:
        sail_type = eval(sail_type_repr, types.__dict__)
        name = name.lower()
        getter = make_getter(attrname, name, convert_to_pypy)
        setter = make_setter(attrname, name, convert_from_pypy)
        register_info.append((attrname, name, getter, setter, sail_type))
        applevel_register_info.append((name, sail_type))

    unrolling_register_info = unrolling_iterable(register_info)
    @staticmethod
    @jit.elidable
    def lookup_register(space, name):
        for attrname, pyname, getter, setter, sail_type in unrolling_register_info:
            if pyname == name:
                assert sail_type is not None
                return getter, setter, sail_type
        raise oefmt(space.w_ValueError, "register not found")
    cls._lookup_register = lookup_register

    def get_register_value(self, name):
        machine = self.machine
        space = self.space
        getter, _, sail_type = self._lookup_register(space, name)
        try:
            return getter(space, self.machine)
        except ValueError:
            if not objectmodel.we_are_translated():
                import pdb; pdb.xpm()
            raise oefmt(space.w_TypeError, "could not convert register value to Python object (Sail type %S)", sail_type)
    cls._get_register_value = get_register_value

    def set_register_value(self, name, w_value):
        machine = self.machine
        space = self.space
        _, setter, sail_type = self._lookup_register(space, name)
        try:
            setter(space, self.machine, w_value)
        except ValueError:
            if not objectmodel.we_are_translated():
                import pdb; pdb.xpm()
            raise oefmt(space.w_TypeError, "could not convert Python object to register value (Sail type %S)", sail_type)
    cls._set_register_value = set_register_value

    class State:
        def __init__(self, space):
            self.w_register_info = space.wrap(applevel_register_info)

    def _get_register_info(self, space):
        return space.fromcache(State).w_register_info
    cls._get_register_info = _get_register_info

def _init_types(cls, all_type_info):
    class TypesCache(object):
        def __init__(self, space):
            self.all_type_info = all_type_info
            w_mod = Module(space, space.newtext("<%s.types>" % cls.__name__[2:]))
            for type_info in all_type_info:
                if type_info[0].startswith("Union_"):
                    invent_python_cls_union(space, w_mod, type_info, cls)
                else:
                    assert type_info[0].startswith("Struct_")
                    invent_python_cls_struct(space, w_mod, type_info, cls)
            self.w_mod = w_mod
    cls.TypesCache = TypesCache

def is_valid_identifier(s):
    from pypy.objspace.std.unicodeobject import _isidentifier
    return _isidentifier(s)

def invent_python_cls_union(space, w_mod, type_info, machinecls):
    pyname, sail_name, cls, sail_type_repr = type_info
    sail_type = eval(sail_type_repr, types.__dict__)
    assert pyname.startswith("Union_")
    cls._pypy_union_number_fields = -1
    cls.typedef = TypeDef(sail_name,
        __len__=_make_union_len(space, machinecls, cls),
        __repr__=_make_union_repr(space, machinecls, cls),
        __eq__=_make_union_eq(space, machinecls, cls),
        __hash__=_make_union_hash(space, machinecls, cls),
        sail_type = sail_type
    )
    cls.typedef.acceptable_as_base_class = False
    space.setattr(w_mod, space.newtext(sail_name), space.gettypefor(cls))
    for subclass_info in cls._all_subclasses:
        sub_pyname, sub_sail_name, subcls = subclass_info
        subcls._pypy_union_number_fields = len(subcls._field_info)
        subcls.typedef = TypeDef(sub_sail_name,
            cls.typedef,
            __new__=_make_union_new(space, machinecls, subcls, sub_sail_name),
            __getitem__=_make_union_getitem(space, machinecls, subcls, sail_type),
        )
        subcls.typedef.acceptable_as_base_class = False
        space.setattr(w_mod, space.newtext(sub_sail_name), space.gettypefor(subcls))

def invent_python_cls_struct(space, w_mod, type_info, machinecls):
    pyname, sail_name, cls, sail_type_repr = type_info
    sail_type = eval(sail_type_repr, types.__dict__)
    def bind(convert, fieldname):
        if isinstance(sail_type.internalfieldtyps[fieldname], types.Packed):
            def get_field(self, space):
                raise oefmt(space.w_SystemError, 'reading packed field is not supported yet')
        else:
            def get_field(self, space):
                assert isinstance(self, cls)
                return convert(space, getattr(self, fieldname))
        return get_field
    kwargs = {}
    for index, (fieldname, convert_to, convert_from, sail_repr, sail_fieldname) in enumerate(cls._field_info):
        kwargs[sail_fieldname] = GetSetProperty(bind(convert_to, fieldname), cls=cls)
    cls.typedef = TypeDef(sail_name,
        __new__=_make_union_new(space, machinecls, cls, sail_type.name),
        __repr__=_make_struct_repr(space, machinecls, cls),
        sail_type = sail_type,
        **kwargs
    )
    cls.typedef.acceptable_as_base_class = False
    space.setattr(w_mod, space.newtext(sail_name), space.gettypefor(cls))

def _interp2app_unique_name(func, machinecls, *strings):
    func.func_name += "_".join(['', machinecls.__name__] + list(strings))
    return interp2app(func)

def _interp2app_unique_name_as_method(func, machinecls, subcls, *strings):
    func.func_name += "_".join(['', machinecls.__name__, subcls.__name__] + list(strings))
    return interp2app(func.__get__(None, subcls))

def _make_union_new(space, machinecls, subcls, name):
    length = len(subcls._field_info)
    if length == 1 and hasattr(subcls, 'construct'):
        convert = subcls._field_info[0][2]
        def descr_new(space, w_typ, w_arg):
            enum_value = convert(space, w_arg)
            return subcls.construct(enum_value)
    else:
        unroll_fields = unrolling_iterable(
            [(index, info[0], info[2]) for index, info in enumerate(subcls._field_info)])
        def descr_new(space, w_typ, args_w):
            if len(args_w) != length:
                raise oefmt(space.w_TypeError,
                            "expected exactly %d arguments, got %d", length,
                            len(args_w))
            self = objectmodel.instantiate(subcls)
            # XXX can reuse the adaptors probably? with a function that does the setting
            for index, fieldname, convert in unroll_fields:
                setattr(self, fieldname, convert(space, args_w[index]))
            return self
    return _interp2app_unique_name(descr_new, machinecls, name)

def _make_union_len(space, machinecls, basecls):
    def descr_len(self, space):
        return space.newint(self._pypy_union_number_fields)
    return _interp2app_unique_name_as_method(descr_len, machinecls, basecls)

def _make_union_repr(space, machinecls, basecls):
    def descr_repr(self, space):
        return app_repr_union(space, self)
    return _interp2app_unique_name_as_method(descr_repr, machinecls, basecls)

def _make_union_eq(space, machinecls, basecls):
    def descr_eq(self, space, w_other):
        if not isinstance(w_other, basecls):
            return space.w_NotImplemented
        return space.newbool(self.eq(w_other))
    return _interp2app_unique_name_as_method(descr_eq, machinecls, basecls)

def _make_union_hash(space, machinecls, basecls):
    def descr_hash(self, space):
        return app_hash_union(space, self)
    return _interp2app_unique_name_as_method(descr_hash, machinecls, basecls)

def _make_union_getitem(space, machinecls, subcls, sail_type):
    unroll_get_fields = unrolling_iterable(
        [(index, info[0], info[1], info[5]) for index, info in enumerate(subcls._field_info)])
    @unwrap_spec(index='index')
    def descr_getitem(self, space, index):
        assert isinstance(self, subcls)
        for i, fieldname, convert, getter in unroll_get_fields:
            if index == i:
                if getter is not None:
                    val = getter(self)
                else:
                    val = getattr(self, fieldname)
                return convert(space, val)
        raise oefmt(space.w_IndexError, "index out of bound")
    return _interp2app_unique_name_as_method(descr_getitem, machinecls, subcls)

def _make_struct_repr(space, machinecls, basecls):
    def descr_repr(self, space):
        return app_repr_struct(space, self)
    return _interp2app_unique_name_as_method(descr_repr, machinecls, basecls)

class W_BoundSailFunction(W_Root):
    def __init__(self, w_machine, func):
        self.func = func # an instance of SailFunctionAdaptor
        self.w_machine = w_machine

    def descr_call(self, space, args_w):
        return self.func.call(space, self.w_machine, args_w)

    def descr_repr(self, space):
        return space.newtext("<bound sail function .lowlevel.%s of %s>" % (
            self.func.sail_name, space.text_w(space.repr(self.w_machine))))

    def descr_doc(self, space):
        return space.newtext("""\
Sail function
%s
""" % (self.func.sail_name, ))

    def descr_sail_type(self, space):
        return self.func.sail_type


W_BoundSailFunction.typedef = TypeDef("sail-function",
    __call__ = interp2app(W_BoundSailFunction.descr_call),
    __doc__ = GetSetProperty(W_BoundSailFunction.descr_doc),
    __repr__ = interp2app(W_BoundSailFunction.descr_repr),
    sail_type = GetSetProperty(W_BoundSailFunction.descr_sail_type),
)

def _init_functions(machinecls, functions):
    d = {}
    function_info_dict = {}
    for function_info in functions:
        function_info_dict[function_info[1]] = function_info
        _make_function(function_info, d, machinecls)

    #for sail_name in list(d):
    #    if not sail_name.endswith('_backwards'):
    #        continue
    #    name = sail_name[:-len('_backwards')]
    #    forwards_name = name + '_forwards'
    #    if forwards_name not in d:
    #        continue
    #    if name in d:
    #        continue
    #    _make_forwards_backwards_function(

    @jit.elidable
    def get_sail_func(name):
        return d.get(name, None)

    class W_Lowlevel(W_Root):
        def __init__(self, space, w_machine):
            assert isinstance(w_machine, machinecls)
            self.w_machine = w_machine

        def descr_getattr(self, space, w_name):
            name = space.text_w(w_name)
            func = get_sail_func(name)
            if func is None:
                raise oefmt_attribute_error(space, self, w_name, "'%T' object has no attribute %R")
            return W_BoundSailFunction(self.w_machine, func)
        descr_getattr.func_name += "_" + machinecls.__name__

        def descr_dir(self, space):
            return space.newlist([space.newtext(name) for name in d])
        descr_dir.func_name += "_" + machinecls.__name__

    l = ["Exports the Sail functions of the model directly. The following functions are exported:"]
    l.extend(sorted(d))
    doc = "\n".join(l)

    W_Lowlevel.typedef = TypeDef("lowlevel",
        __getattr__ = interp2app(W_Lowlevel.descr_getattr),
        __dir__ = interp2app(W_Lowlevel.descr_dir),
    )
    W_Lowlevel.typedef.doc = doc
    machinecls.W_Lowlevel = W_Lowlevel

def _make_function(function_info, d, machinecls):
    pyname, sail_name, func, argument_converters, result_converter, sail_type_repr = function_info
    sail_type = eval(sail_type_repr, types.__dict__)
    if sail_type.argtype.elements == (types.Unit(), ):
        argument_converters = [] # if it's exactly unit, turn it into a zero-argument function
    adaptor_class = _make_function_adaptor(argument_converters, machinecls)
    def py(space, *args):
        res = func(*args)
        return result_converter(space, res)
    py.func_name += pyname
    adaptor = d[sail_name] = adaptor_class(py, sail_name, sail_type)


class SailFunctionAdaptor(object):
    num_args = -1
    sail_name = ''
    _immutable_ = True
    _attrs_ = ['num_args', 'sail_name', 'sail_type']

    def call(self, space, w_machine, args_w):
        if len(args_w) != self.num_args:
            raise oefmt(space.w_TypeError, "Sail function %s takes exactly %d arguments, got %d",
                        self.sail_name, self.num_args, len(args_w))
        try:
            return self._call(space, w_machine, args_w)
        except supportcoderiscv.SailError as e:
            w_module = space.getbuiltinmodule('_pydrofoil')
            w_error = space.getattr(w_module, space.newtext('SailAssertionError'))
            raise OperationError(w_error, space.newtext(e.msg))
        except OperationError:
            raise
        except Exception as e:
            if not objectmodel.we_are_translated():
                import pdb; pdb.xpm()
            raise oefmt(space.w_SystemError, "internal error, please report a bug: %s", str(e))

def _make_function_adaptor(argument_converters, machinecls, cache={}):
    key = tuple(argument_converters + [machinecls])

    if key in cache:
        return cache[key]

    _convert_args = _make_argument_converter_func(argument_converters)

    class Adaptor(SailFunctionAdaptor):
        _immutable_ = True
        num_args = len(argument_converters)

        def __init__(self, func, sail_name, sail_type):
            self.func = func
            self.sail_name = sail_name
            self.sail_type = sail_type

        def _call(self, space, w_machine, args_w):
            assert isinstance(w_machine, machinecls)
            args = _convert_args(space, args_w)
            res = self.func(space, w_machine.machine, *args)
            if w_machine.machine.have_exception:
                raise oefmt(space.w_SystemError, "sail exception")
            return res

    cache[key] = Adaptor
    return Adaptor

def _make_argument_converter_func(argument_converters, cache={}):
    key = tuple(argument_converters)
    if key in cache:
        return cache[key]
    converters = unrolling_iterable(argument_converters)
    noargs = argument_converters == []
    def convert(space, args_w):
        args = ()
        i = 0
        for conv in converters:
            args += (conv(space, args_w[i]), )
            i += 1
        if noargs:
            # unit argument case:
            args += ((), )
        return args
    cache[key] = convert
    return convert

class MachineAbstractBase(object):
    def __init__(self, space, elf=None, dtb=False, w_callbacks=None):
        if w_callbacks is not None:
            w_callbacks = space.interp_w(W_Callbacks, w_callbacks)
        else:
            w_callbacks = None
        self._init_machine()
        self.space = space
        self.elf = elf
        if dtb:
            self.machine.g._create_dtb()
        init_mem(space, self.machine, MemoryObserver)
        if w_callbacks:
            mem = ApplevelCallbackMemory(space, w_callbacks.w_mem_read8_intercept,
                                         w_callbacks.w_mem_write8_intercept)
            observer = self.machine.g.mem
            assert isinstance(observer, MemoryObserver)
            observer.wrapped = mem
        if elf is not None:
            entry = load_sail(space, self.machine, elf)
            write_reset_vector = True
        else:
            entry = self.machine.g.rv_ram_base
            write_reset_vector = dtb # don't write reset vector, unless we want a dtb
        self.reset_pc = init_sail(space, self.machine, entry, write_reset_vector)
        self.machine.set_pc(self.reset_pc)
        self.machine.g._init_ranges()

        self._step_no = 0
        self._insn_cnt = 0 # used to check whether a tick has been reached
        self._tick = False # should the next step tick

    def reset(self):
        initialize_registers(self.space, self.machine)
        self.machine.set_pc(self.reset_pc)

    def step(self):
        """ Execute a single instruction. """
        from pydrofoil.bitvector import Integer
        if self._tick:
            self.machine.tick_clock()
            self.machine.tick_platform()
            self._tick = False
        stepped = self.machine.step(Integer.fromint(self._step_no))
        if stepped:
            self._step_no += 1
            self._insn_cnt += 1
            if self._insn_cnt == self.machine.g.rv_insns_per_tick:
                self._tick = True

    def step_monitor_mem(self):
        """ EXPERIMENTAL: Execute a single instruction and monitor memory
        access while doing so. Returns a list of tuples of memory accesses the
        instruction executed. Every tuple has the format:

        (kind_of_access, start_address, number_of_bytes, memory_value)

        kind_of_access is a string, either "read", "read_executable", or
        "write". """
        mem = self.machine.g.mem
        assert isinstance(mem, MemoryObserver)
        result = mem.memory_observer = []
        try:
            self.step()
        finally:
            mem.memory_observer = None
        space = self.space
        res_w = []
        for kind, start_addr, num_bytes, value in result:
            res_w.append(space.newtuple([
                space.newtext(kind),
                space.newint(start_addr),
                space.newint(num_bytes),
                space.newint(value),
            ]))
        return space.newlist(res_w)

    @unwrap_spec(name="text")
    def read_register(self, name):
        """ read the value of register name """
        name = name.lower()
        return self._get_register_value(name)

    @unwrap_spec(name="text")
    def write_register(self, name, w_value):
        """ set the value of register name to value"""
        name = name.lower()
        return self._set_register_value(name, w_value)

    def get_register_info(self, space):
        """ Returns information about all available registers of the Sail
        model. The result is a list of tuples of the form

        (name, sail_type)

        of all the registers.
        """
        return self._get_register_info(space)

    @unwrap_spec(address=r_uint, width=int)
    def read_memory(self, address, width=8):
        """ Read width bytes of memory at address """
        if not (width == 1 or width == 2 or width == 4 or width == 8):
            raise oefmt(self.space.w_ValueError, "width can only be 1, 2, 4, or 8")
        try:
            return self.space.newint(self.machine.g.mem.read(address, width))
        except ValueError:
            raise oefmt(self.space.w_IndexError, "memory access out of bounds")

    @unwrap_spec(address=r_uint, value=r_uint, width=int)
    def write_memory(self, address, value, width=8):
        """ Write width bytes of memory at address. """
        if not (width == 1 or width == 2 or width == 4 or width == 8):
            raise oefmt(self.space.w_ValueError, "width can only be 1, 2, 4, or 8")
        try:
            self.machine.g.mem.write(address, width, value)
        except ValueError:
            raise oefmt(self.space.w_IndexError, "memory access out of bounds")

    def memory_info(self):
        """ Return information about the emulated memory of the model. Returns
        a list of tuples of the form

        (address_start, address_end)

        for all the parts of the address space that are currently backend by
        emulated memory. """
        space = self.space
        res = self.machine.g.mem.memory_info()
        if res is None:
            return space.w_None
        res_w = []
        for from_, to in res:
            res_w.append(space.newtuple2(space.newint(from_), space.newint(to)))
        w_res = space.newlist(res_w)
        space.call_method(w_res, "sort")
        return w_res

    @unwrap_spec(limit=int)
    def run(self, limit=0):
        """ Run the emulator, either for a given number of steps if limit is
        set, or indefinitely. """
        from rpython.rlib.nonconst import NonConstant
        if NonConstant(True):
            do_show_times = True
        else:
            do_show_times = False
        run_sail(self.space, self.machine, limit, do_show_times)

    @unwrap_spec(verbosity=bool)
    def set_verbosity(self, verbosity):
        """ Set the verbosity of the Sail emulation. """
        self.machine.g.config_print_instr = verbosity
        self.machine.g.config_print_reg = verbosity
        self.machine.g.config_print_mem_access = verbosity
        self.machine.g.config_print_platform = verbosity

    def disassemble_last_instruction(self):
        return self.space.newtext(self.machine.disassemble_last_instruction())

    def descr_get_types(self, space):
        return space.fromcache(self.TypesCache).w_mod

    def descr_get_lowlevel(self, space):
        return self.W_Lowlevel(space, self)

    @unwrap_spec(start=r_uint, size=r_uint)
    def descr_set_sail_memory_bounds(self, space, start, size):
        if start + size < start:
            raise oefmt(space.w_ValueError, "end point of memory bounds outside of 64-bit")
        self.machine.g.rv_ram_base = start
        self.machine.g.rv_ram_size = size



class MemoryObserver(mem_mod.MemBase):
    _immutable_fields_ = ['wrapped']

    def __init__(self, wrapped):
        self.wrapped = wrapped
        self.memory_observer = None

    def read(self, start_addr, num_bytes, executable_flag=False):
        result = self.wrapped.read(start_addr, num_bytes, executable_flag)
        if self.memory_observer is not None:
            if executable_flag:
                kind = "read_executable"
            else:
                kind = "read"
            self.memory_observer.append((kind, start_addr, num_bytes, result))
        return result

    def write(self, start_addr, num_bytes, value):
        if self.memory_observer is not None:
            self.memory_observer.append(("write", start_addr, num_bytes, value))
        return self.wrapped.write(start_addr, num_bytes, value)

    def close(self):
        return self.wrapped.close()

    def memory_info(self):
        return self.wrapped.memory_info()


class ApplevelCallbackMemory(mem_mod.MemBase):
    def __init__(self, space, w_read, w_write):
        self.space = space
        self.w_read = w_read
        self.w_write = w_write
        self.min_addr = r_uint(2 ** 64 - 1)
        self.max_addr = r_uint(0)

    def _split_addr(self, start_addr, num_bytes):
        mem_offset = start_addr >> 3
        inword_addr = start_addr & 0b111
        # little endian
        if num_bytes == 8:
            mask = r_uint(-1)
        else:
            mask = (r_uint(1) << (num_bytes * 8)) - 1
        return mem_offset, inword_addr, mask

    def _aligned_read(self, start_addr, num_bytes, executable_flag):
        mem_offset, inword_addr, mask = self._split_addr(start_addr, num_bytes)
        data = self._read_word(mem_offset)
        if num_bytes == 8:
            assert inword_addr == 0
            return data
        return (data >> (inword_addr * 8)) & mask

    def _aligned_write(self, start_addr, num_bytes, value):
        self.min_addr = min(start_addr, self.min_addr)
        self.max_addr = max(start_addr + num_bytes - 1, self.max_addr)
        mem_offset, inword_addr, mask = self._split_addr(start_addr, num_bytes)
        if num_bytes == 8:
            assert inword_addr == 0
            self._write_word(mem_offset, value)
            return
        assert value & ~mask == 0
        olddata = self._read_word(mem_offset)
        mask <<= inword_addr * 8
        value <<= inword_addr * 8
        self._write_word(mem_offset, (olddata & ~mask) | value)

    def _read_word(self, addr):
        w_res = self.space.call_function(self.w_read, BitVector.from_ruint(64, addr))
        res = self.space.interp_w(BitVector, w_res)
        return res.touint(64)

    def _write_word(self, addr, value):
        w_addr = BitVector.from_ruint(64, addr)
        w_value = BitVector.from_ruint(64, value)
        self.space.call_function(self.w_write, w_addr, w_value)

    def memory_info(self):
        return [(self.min_addr, self.max_addr)]


class W_RISCV64(W_Root):
    """ Emulator for a RISC-V 64-bit CPU """
    objectmodel.import_from_mixin(MachineAbstractBase)

    def _init_machine(self):
        self.machine = machinecls64()


@unwrap_spec(elf="text_or_none", dtb=bool)
def riscv64_descr_new(space, w_subtype, elf=None, dtb=False, w_callbacks=None):
    """ Create a RISC-V 64-bit CPU. Load elf if given, and create a device tree
    binary if the flag dtb is set. """
    w_res = space.allocate_instance(W_RISCV64, w_subtype)
    W_RISCV64.__init__(w_res, space, elf, dtb, w_callbacks)
    return w_res


W_RISCV64.typedef = TypeDef("_pydrofoil.RISCV64",
    __new__ = interp2app(riscv64_descr_new),
    reset = interp2app(W_RISCV64.reset),
    step = interp2app(W_RISCV64.step),
    step_monitor_mem = interp2app(W_RISCV64.step_monitor_mem),
    read_register = interp2app(W_RISCV64.read_register),
    write_register = interp2app(W_RISCV64.write_register),
    register_info = interp2app(W_RISCV64.get_register_info),
    read_memory = interp2app(W_RISCV64.read_memory),
    write_memory = interp2app(W_RISCV64.write_memory),
    memory_info = interp2app(W_RISCV64.memory_info),
    run = interp2app(W_RISCV64.run),
    set_verbosity = interp2app(W_RISCV64.set_verbosity),
    disassemble_last_instruction = interp2app(W_RISCV64.disassemble_last_instruction),
    types = GetSetProperty(W_RISCV64.descr_get_types),
    lowlevel = GetSetProperty(W_RISCV64.descr_get_lowlevel),
    _set_sail_memory_bounds = interp2app(W_RISCV64.descr_set_sail_memory_bounds),
)


class W_RISCV32(W_Root):
    """ Emulator for a RISC-V 32-bit CPU """
    objectmodel.import_from_mixin(MachineAbstractBase)

    def _init_machine(self):
        self.machine = machinecls32()


@unwrap_spec(elf="text_or_none", dtb=bool)
def riscv32_descr_new(space, w_subtype, elf=None, dtb=False, w_callbacks=None):
    """ Create a RISC-V 32-bit CPU. Load elf if given, and create a device tree
    binary if the flag dtb is set. """
    w_res = space.allocate_instance(W_RISCV32, w_subtype)
    W_RISCV32.__init__(w_res, space, elf, dtb, w_callbacks)
    return w_res


W_RISCV32.typedef = TypeDef("_pydrofoil.RISCV32",
    __new__ = interp2app(riscv32_descr_new),
    reset = interp2app(W_RISCV32.reset),
    step = interp2app(W_RISCV32.step),
    step_monitor_mem = interp2app(W_RISCV32.step_monitor_mem),
    read_register = interp2app(W_RISCV32.read_register),
    write_register = interp2app(W_RISCV32.write_register),
    register_info = interp2app(W_RISCV32.get_register_info),
    read_memory = interp2app(W_RISCV32.read_memory),
    write_memory = interp2app(W_RISCV32.write_memory),
    memory_info = interp2app(W_RISCV32.memory_info),
    run = interp2app(W_RISCV32.run),
    set_verbosity = interp2app(W_RISCV32.set_verbosity),
    disassemble_last_instruction = interp2app(W_RISCV32.disassemble_last_instruction),
    types = GetSetProperty(W_RISCV32.descr_get_types),
    lowlevel = GetSetProperty(W_RISCV32.descr_get_lowlevel),
    _set_sail_memory_bounds = interp2app(W_RISCV32.descr_set_sail_memory_bounds),
)

# bitvector support

class __extend__(BitVector):
    def descr_repr(self, space):
        s = "bitvector(%s, %s)" % (self.size(), self.string_of_bits())
        return space.newutf8(s, len(s)) # ascii

    def _pypy_coerce(self, space, w_other, masking_allowed=False):
        """ coerce w_other to a BitVector with size of self. return None if not
        possible. if mask=True too large ints will be masked """
        if isinstance(w_other, BitVector):
            if self.size() != w_other.size():
                raise oefmt(space.w_ValueError, "can't operate on bitvectors with differing sizes %d and %d", self.size(), w_other.size())
            return w_other
        try:
            w_other = space.index(w_other)
        except OperationError as e:
            if not e.match(space, space.w_TypeError):
                raise
            return None
        try:
            val = r_uint(space.int_w(w_other))
        except OperationError as e:
            if not e.match(space, space.w_OverflowError):
                raise
            value = space.bigint_w(w_other)
            bv = BitVector.from_bigint(self.size(), value)
            if masking_allowed or bv.tobigint().eq(value):
                return bv
        else:
            if self.size() > 64:
                masked_val = val
            else:
                masked_val = ruint_mask(self.size(), val)
            if masking_allowed or masked_val == val:
                return BitVector.from_ruint(self.size(), val)
        return None

    def descr_len(self, space):
        return space.newint(self.size())

    def descr_getitem(self, space, w_index):
        from pypy.objspace.std.sliceobject import W_SliceObject
        if isinstance(w_index, W_SliceObject):
            start, stop, step = w_index.unpack(space)
            if step > 1:
                raise oefmt(space.w_ValueError, "slice length %d > 1 not supported yet", step)
            start, stop, step, slicelength =  w_index.adjust_indices(start, stop, step, self.size())
            assert slicelength >= 0
            if slicelength == 0:
                # XXX support me
                raise oefmt(space.w_ValueError, "slice result would have length 0")
            return self.subrange(stop-1, start)
        index = space.getindex_w(w_index, space.w_IndexError, "bitvector")
        if index < 0:
            index += self.size()
        if not 0 <= index < self.size():
            raise oefmt(space.w_IndexError, "bitvector index out of range")
        if self.read_bit(index):
            return space.newint(1)
        else:
            return space.newint(0)

    def descr_eq(self, space, w_other):
        if not isinstance(w_other, BitVector):
            w_other = self._pypy_coerce(space, w_other)
        if w_other is None:
            return space.w_NotImplemented
        if self.size() != w_other.size():
            return space.w_False
        return space.newbool(self.eq(w_other))

    def descr_or(self, space, w_other):
        w_other = self._pypy_coerce(space, w_other, masking_allowed=True)
        if w_other is None:
            return space.w_NotImplemented
        return self.or_(w_other)

    def descr_ror(self, space, w_other):
        return self.descr_or(space, w_other)

    def descr_and(self, space, w_other):
        w_other = self._pypy_coerce(space, w_other, masking_allowed=True)
        if w_other is None:
            return space.w_NotImplemented
        return self.and_(w_other)

    def descr_rand(self, space, w_other):
        return self.descr_and(space, w_other)

    def descr_xor(self, space, w_other):
        w_other = self._pypy_coerce(space, w_other, masking_allowed=True)
        if w_other is None:
            return space.w_NotImplemented
        return self.xor(w_other)

    def descr_rxor(self, space, w_other):
        return self.descr_xor(space, w_other)

    def descr_add(self, space, w_other):
        w_other = self._pypy_coerce(space, w_other, masking_allowed=True)
        if w_other is None:
            return space.w_NotImplemented
        return self.add_bits(w_other)

    def descr_radd(self, space, w_other):
        return self.descr_add(space, w_other)

    def descr_sub(self, space, w_other):
        w_other = self._pypy_coerce(space, w_other, masking_allowed=True)
        if w_other is None:
            return space.w_NotImplemented
        return self.sub_bits(w_other)

    def descr_rsub(self, space, w_other):
        w_other = self._pypy_coerce(space, w_other, masking_allowed=True)
        if w_other is None:
            return space.w_NotImplemented
        return w_other.sub_bits(self)

    def descr_matmul(self, space, w_other):
        """ Concatenate two bitvectors """
        if not isinstance(w_other, BitVector):
            return space.w_NotImplemented
        return self.append(w_other)

    def _check_shift(self, space, shift):
        if shift < 0:
            raise oefmt(space.w_ValueError, "negative shift count")
        return shift

    @unwrap_spec(shift=int)
    def descr_lshift(self, space, shift):
        """ Shift bitvector to the left. """
        return self.lshift(self._check_shift(space, shift))

    def descr_rshift(self, space, w_other):
        """rshift is not implemented. use .arithmetic_rshift() or .logical_rshift()."""
        raise oefmt(space.w_TypeError, "rshift is not implemented. use .arithmetic_rshift() or .logical_rshift().")

    @unwrap_spec(shift=int)
    def descr_logical_rshift(self, space, shift):
        """Perform a logical right shift, i.e. shift in zeros."""
        return self.rshift(self._check_shift(space, shift))

    @unwrap_spec(shift=int)
    def descr_arithmetic_rshift(self, space, shift):
        """Perform a logical right shift, i.e. shift in zeros."""
        return self.arith_rshift(self._check_shift(space, shift))

    def descr_neg(self, space):
        # implement as 0 - self
        return BitVector.from_ruint(self.size(), r_uint(0)).sub_bits(self)

    def descr_invert(self, space):
        return self.invert()

    def descr_signed(self, space):
        """ Turn the bitvector into an integer by interpreting it as two's
        complement. """
        res = self.signed()
        return supportcoderiscv.convert_to_pypy_int(space, res)

    def descr_unsigned(self, space):
        """ Turn the bitvector into an integer by interpreting it as an
        unsigned integer."""
        res = self.unsigned()
        return supportcoderiscv.convert_to_pypy_int(space, res)

    @unwrap_spec(target_size=int)
    def descr_zero_extend(self, space, target_size):
        """ Zero-extend the bitvector to width target_size. """
        return self.zero_extend(target_size)

    @unwrap_spec(target_size=int)
    def descr_sign_extend(self, space, target_size):
        """ Sign-extend the bitvector to width target_size. """
        return self.sign_extend(target_size)

    def descr_index(self, space):
        """ Interpret the bitvector as an integer """
        return self.descr_unsigned(space)

    def descr_hash(self, space):
        return space.newint(self.tobigint().hash() ^ self.size())

    def descr_bool(self, space):
        return space.newbool(self.tobool())


@unwrap_spec(width=int)
def bitvector_descr_new(w_type, space, width, w_value):
    if width < 0:
        raise oefmt(space.w_ValueError, "width must not be negative")
    try:
        value = space.uint_w(w_value)
    except OperationError as e:
        if not e.match(space, space.w_TypeError) and not e.match(space, space.w_OverflowError):
            raise
    else:
        return BitVector.from_ruint(width, value)
    try:
        return BitVector.from_bigint(width, space.bigint_w(w_value))
    except OperationError as e:
        if not e.match(space, space.w_TypeError):
            raise
        raise oefmt(space.w_TypeError, "bitvector value must be integer")


BitVector.typedef = TypeDef("bitvector",
    __new__ = interp2app(bitvector_descr_new),
    __repr__ = interp2app(BitVector.descr_repr),
    __len__ = interp2app(BitVector.descr_len),
    __getitem__ = interp2app(BitVector.descr_getitem),

    __eq__ = interp2app(BitVector.descr_eq),
    __or__ = interp2app(BitVector.descr_or),
    __ror__ = interp2app(BitVector.descr_ror),
    __and__ = interp2app(BitVector.descr_and),
    __rand__ = interp2app(BitVector.descr_rand),
    __xor__ = interp2app(BitVector.descr_xor),
    __rxor__ = interp2app(BitVector.descr_rxor),

    __add__ = interp2app(BitVector.descr_add),
    __radd__ = interp2app(BitVector.descr_radd),
    __sub__ = interp2app(BitVector.descr_sub),
    __rsub__ = interp2app(BitVector.descr_rsub),

    __rshift__ = interp2app(BitVector.descr_rshift),
    __lshift__ = interp2app(BitVector.descr_lshift),
    arithmetic_rshift = interp2app(BitVector.descr_arithmetic_rshift),
    logical_rshift = interp2app(BitVector.descr_logical_rshift),

    __matmul__ = interp2app(BitVector.descr_matmul),

    __neg__ = interp2app(BitVector.descr_neg),
    __invert__ = interp2app(BitVector.descr_invert),

    __index__ = interp2app(BitVector.descr_index),
    __hash__ = interp2app(BitVector.descr_hash),

    __bool__ = interp2app(BitVector.descr_bool),

    signed = interp2app(BitVector.descr_signed),
    unsigned = interp2app(BitVector.descr_unsigned),

    zero_extend = interp2app(BitVector.descr_zero_extend),
    sign_extend = interp2app(BitVector.descr_sign_extend),
)
BitVector.typedef.acceptable_as_base_class = False

# ________________________________________________

import os
appfile = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'app_helpers.py')

with open(appfile, "r") as f:
    content = f.read()

app = applevel(content, filename=__file__)
app_repr_union = app.interphook('repr_union')
app_repr_struct = app.interphook('repr_struct')
app_hash_union = app.interphook('hash_union')

# ________________________________________________

class W_Callbacks(W_Root):
    _immutable_fields_ = ['w_mem_read8_intercept', 'w_mem_write8_intercept']

    def __init__(self, w_mem_read8_intercept, w_mem_write8_intercept):
        self.w_mem_read8_intercept = w_mem_read8_intercept
        self.w_mem_write8_intercept = w_mem_write8_intercept

    def descr_repr(self, space):
        res = ["_pydrofoil.Callbacks("]
        if self.w_mem_read8_intercept:
            res.append("mem_read8_intercept=")
            res.append(space.text_w(self.w_mem_read8_intercept))
        if self.w_mem_write8_intercept:
            res.append("mem_write8_intercept=")
            res.append(space.text_w(self.w_mem_write8_intercept))
        res.append(")")
        return space.newtext(''.join(res))

def callbacks_descr_new(space, w_subtype, __kwonly__, w_mem_read8_intercept=None, w_mem_write8_intercept=None):
    return W_Callbacks(w_mem_read8_intercept, w_mem_write8_intercept)

W_Callbacks.typedef = TypeDef("_pydrofoil.Callbacks",
    __new__ = interp2app(callbacks_descr_new),
    __repr__ = interp2app(W_Callbacks.descr_repr),
)
W_Callbacks.acceptable_as_base_class = False
