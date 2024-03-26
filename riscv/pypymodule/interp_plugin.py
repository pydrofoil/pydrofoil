from rpython.rlib import jit
from rpython.rlib import objectmodel
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
from pypy.interpreter.baseobjspace import W_Root
from pypy.interpreter.error import oefmt
from pypy.interpreter.typedef import (TypeDef, interp2app, GetSetProperty,
    descr_get_dict, make_weakref_descr)
from pypy.interpreter.gateway import unwrap_spec

from riscv import supportcoderiscv

from pydrofoil import mem as mem_mod

def _patch_machineclasses(machinecls64=None, machinecls32=None):
    from riscv import supportcoderiscv
    from riscv.targetriscv import _make_code
    if "machinecls64" in globals():
        return
    if machinecls64 is None:
        mod64 = _make_code(True)
        machinecls64 = supportcoderiscv.get_main(mod64, True)._machinecls
    if machinecls32 is None:
        mod32 = _make_code(False)
        machinecls32 = supportcoderiscv.get_main(mod32, False)._machinecls
    globals()["machinecls64"] = machinecls64
    globals()["machinecls32"] = machinecls32
    _init_register_names(W_RISCV64, machinecls64._all_register_names)
    _init_register_names(W_RISCV32, machinecls32._all_register_names)

def wrap_fn(fn):
    def wrapped_fn(space, *args):
        try:
            return fn(*args)
        except Exception as e:
            if not objectmodel.we_are_translated():
                import pdb; pdb.xpm()
            raise oefmt(space.w_SystemError, "internal error, please report a bug: %s", str(e))
    wrapped_fn.func_name = "wrap_" + fn.func_name
    return wrapped_fn

load_sail = wrap_fn(supportcoderiscv.load_sail)
init_mem = wrap_fn(supportcoderiscv.init_mem)
init_sail = wrap_fn(supportcoderiscv.init_sail)

@wrap_fn
def run_sail(machine, insn_limit, do_show_times):
    machine.run_sail(insn_limit, do_show_times)


def _init_register_names(cls, _all_register_names):
    assert cls is not AbstractBase
    """ NOT_RPYTHON """
    from rpython.rlib.unroll import unrolling_iterable
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
    for (attrname, name, convert_to_pypy, convert_from_pypy, sailrepr) in _all_register_names:
        name = name.lower()
        getter = make_getter(attrname, name, convert_to_pypy)
        setter = make_setter(attrname, name, convert_from_pypy)
        register_info.append((attrname, name, getter, setter, sailrepr))
        applevel_register_info.append((name, sailrepr))

    unrolling_register_info = unrolling_iterable(register_info)
    @staticmethod
    @jit.elidable
    def lookup_register(space, name):
        for attrname, pyname, getter, setter, sailrepr in unrolling_register_info:
            if pyname == name:
                return getter, setter, sailrepr
        raise oefmt(space.w_ValueError, "register not found")
    cls._lookup_register = lookup_register

    def get_register_value(self, name):
        machine = self.machine
        space = self.space
        getter, _, sailrepr = self._lookup_register(space, name)
        try:
            return getter(space, self.machine)
        except ValueError:
            raise oefmt(space.w_TypeError, "could not convert register value to Python object (Sail type %s)", sailrepr)
    cls._get_register_value = get_register_value

    def set_register_value(self, name, w_value):
        machine = self.machine
        space = self.space
        _, setter, sailrepr = self._lookup_register(space, name)
        try:
            setter(space, self.machine, w_value)
        except ValueError:
            raise oefmt(space.w_TypeError, "could not convert Python object to register value (Sail type %s)", sailrepr)
    cls._set_register_value = set_register_value

    class State:
        def __init__(self, space):
            self.w_register_info = space.wrap(applevel_register_info)

    def _get_register_info(self, space):
        return space.fromcache(State).w_register_info
    cls._get_register_info = _get_register_info


class AbstractBase(object):
    def __init__(self, space, elf=None, dtb=False):
        self._init_machine()
        self.space = space
        self.elf = elf
        if dtb:
            self.machine.g._create_dtb()
        init_mem(space, self.machine, MemoryObserver)
        if elf is not None:
            entry = load_sail(space, self.machine, elf)
        else:
            entry = self.machine.g.rv_ram_base
        init_sail(space, self.machine, entry)
        self._step_no = 0
        self._insn_cnt = 0 # used to check whether a tick has been reached
        self._tick = False # should the next step tick

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
        result = self.machine.g.mem.memory_observer = []
        try:
            self.step()
        finally:
            self.machine.g.mem.memory_observer = None
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


class W_RISCV64(W_Root):
    """ Emulator for a RISC-V 64-bit CPU """
    objectmodel.import_from_mixin(AbstractBase)

    def _init_machine(self):
        self.machine = machinecls64()


@unwrap_spec(elf="text_or_none", dtb=bool)
def riscv64_descr_new(space, w_subtype, elf=None, dtb=False):
    """ Create a RISC-V 64-bit CPU. Load elf if given, and create a device tree
    binary if the flag dtb is set. """
    w_res = space.allocate_instance(W_RISCV64, w_subtype)
    W_RISCV64.__init__(w_res, space, elf, dtb)
    return w_res


W_RISCV64.typedef = TypeDef("_pydrofoil.RISCV64",
    __new__ = interp2app(riscv64_descr_new),
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
)


class W_RISCV32(W_Root):
    """ Emulator for a RISC-V 32-bit CPU """
    objectmodel.import_from_mixin(AbstractBase)

    def _init_machine(self):
        self.machine = machinecls32()


@unwrap_spec(elf="text_or_none", dtb=bool)
def riscv32_descr_new(space, w_subtype, elf=None, dtb=False):
    """ Create a RISC-V 32-bit CPU. Load elf if given, and create a device tree
    binary if the flag dtb is set. """
    w_res = space.allocate_instance(W_RISCV32, w_subtype)
    W_RISCV32.__init__(w_res, space, elf, dtb)
    return w_res


W_RISCV32.typedef = TypeDef("_pydrofoil.RISCV32",
    __new__ = interp2app(riscv32_descr_new),
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
)
