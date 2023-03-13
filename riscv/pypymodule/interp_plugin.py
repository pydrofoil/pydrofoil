from rpython.rlib import jit
from rpython.rlib import objectmodel
from rpython.rlib.rarithmetic import r_uint, intmask, ovfcheck
from pypy.interpreter.baseobjspace import W_Root
from pypy.interpreter.error import oefmt
from pypy.interpreter.typedef import (TypeDef, interp2app, GetSetProperty,
    descr_get_dict, make_weakref_descr)
from pypy.interpreter.gateway import unwrap_spec

from riscv import supportcoderiscv

def _patch_machineclasses(machinecls64=None, machinecls32=None):
    from riscv import supportcoderiscv
    from riscv.targetriscv import _make_code
    if "machinecls64" in globals():
        return
    if machinecls64 is None:
        mod64 = _make_code(True)
        machinecls64 = supportcoderiscv.get_main(mod64, True)._machinecls
    elif machinecls32 is None:
        mod32 = _make_code(False)
        machinecls32 = supportcoderiscv.get_main(mod32, False)._machinecls
    globals()["machinecls64"] = machinecls64
    globals()["machinecls32"] = machinecls32
    W_RISCV64._init_register_names(machinecls64._all_register_names)

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

class W_RISCV64(W_Root):
    def __init__(self, space, elf=None):
        self.space = space
        self.elf = elf
        self.machine = machinecls64()
        init_mem(space, self.machine)
        if elf is not None:
            entry = load_sail(space, self.machine, elf)
        else:
            entry = self.machine.g.rv_ram_base
        init_sail(space, self.machine, entry)
        self.rv_insns_per_tick = 100 # TODO: make configurable
        self._step_no = 0

    @classmethod
    def _init_register_names(cls, _all_register_names):
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
        for (attrname, name, convert_to_pypy, convert_from_pypy) in _all_register_names:
            name = name.lower().lstrip("z")
            getter = make_getter(attrname, name, convert_to_pypy)
            setter = make_setter(attrname, name, convert_from_pypy)
            register_info.append((attrname, name, getter, setter))

        unrolling_register_info = unrolling_iterable(register_info)
        @staticmethod
        @jit.elidable
        def lookup_register(space, name):
            for attrname, pyname, getter, setter in unrolling_register_info:
                if pyname == name:
                    return getter, setter
            raise oefmt(space.w_ValueError, "register not found")
        cls._lookup_register = lookup_register

        def get_register_value(self, name):
            machine = self.machine
            space = self.space
            getter, _ = self._lookup_register(space, name)
            try:
                return getter(space, self.machine)
            except ValueError:
                raise oefmt(space.w_TypeError, "could not convert register value to Python object")
        cls._get_register_value = get_register_value

        def set_register_value(self, name, w_value):
            machine = self.machine
            space = self.space
            _, setter = self._lookup_register(space, name)
            try:
                setter(space, self.machine, w_value)
            except ValueError:
                raise oefmt(space.w_TypeError, "could not convert Python object to register value")
        cls._set_register_value = set_register_value

    def step(self):
        from pydrofoil.bitvector import Integer
        stepped = self.machine.step(Integer.fromint(self._step_no))
        self._step_no += 1

    @unwrap_spec(name="text")
    def read_register(self, name):
        name = name.lower()
        return self._get_register_value(name)

    @unwrap_spec(name="text")
    def write_register(self, name, w_value):
        name = name.lower()
        return self._set_register_value(name, w_value)

    @unwrap_spec(address=r_uint, width=int)
    def read_memory(self, address, width=8):
        if not (width == 1 or width == 2 or width == 4 or width == 8):
            raise oefmt(self.space.w_ValueError, "width can only be 1, 2, 4, or 8")
        try:
            return self.space.newint(self.machine.g.mem.read(address, width))
        except ValueError:
            raise oefmt(self.space.w_IndexError, "memory access out of bounds")

    @unwrap_spec(address=r_uint, value=r_uint, width=int)
    def write_memory(self, address, value, width=8):
        if not (width == 1 or width == 2 or width == 4 or width == 8):
            raise oefmt(self.space.w_ValueError, "width can only be 1, 2, 4, or 8")
        try:
            self.machine.g.mem.write(address, width, value)
        except ValueError:
            raise oefmt(self.space.w_IndexError, "memory access out of bounds")

    @unwrap_spec(limit=int)
    def run(self, limit=0):
        from rpython.rlib.nonconst import NonConstant
        if NonConstant(True):
            do_show_times = True
        else:
            do_show_times = False
        run_sail(self.space, self.machine, limit, do_show_times)


@unwrap_spec(elf="text_or_none")
def riscv64_descr_new(space, w_subtype, elf=None):
    w_res = space.allocate_instance(W_RISCV64, w_subtype)
    W_RISCV64.__init__(w_res, space, elf)
    return w_res


W_RISCV64.typedef = TypeDef("_pydrofoil.RISCV64",
    __new__ = interp2app(riscv64_descr_new),
    step = interp2app(W_RISCV64.step),
    read_register = interp2app(W_RISCV64.read_register),
    write_register = interp2app(W_RISCV64.write_register),
    read_memory = interp2app(W_RISCV64.read_memory),
    write_memory = interp2app(W_RISCV64.write_memory),
    run = interp2app(W_RISCV64.run),
)
