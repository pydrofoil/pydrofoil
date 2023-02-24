from rpython.rlib import jit
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

def wrap_fn(fn):
    def wrapped_fn(space, *args, **kwargs):
        try:
            return fn(*args, **kwargs)
        except Exception as e:
            raise oefmt(space.w_SystemError, "internal error, please report a bug: %s", str(e))
    wrapped_fn.func_name = "wrap_" + fn.func_name
    return wrapped_fn

load_sail = wrap_fn(supportcoderiscv.load_sail)
init_sail = wrap_fn(supportcoderiscv.init_sail)


class W_RISCV64(W_Root):
    def __init__(self, space, elf):
        self.space = space
        self.elf = elf
        self.machine = machinecls64()
        entry = load_sail(space, self.machine, elf)
        init_sail(space, self.machine, entry)
        self.rv_insns_per_tick = 100 # TODO: make configurable
        self._step_no = 0

    def step(self):
        from pydrofoil.bitvector import Integer
        stepped = self.machine.step(Integer.fromint(self._step_no))
        self._step_no += 1


@unwrap_spec(elf="text")
def riscv64_descr_new(space, w_subtype, elf):
    w_res = space.allocate_instance(W_RISCV64, w_subtype)
    W_RISCV64.__init__(w_res, space, elf)
    return w_res


W_RISCV64.typedef = TypeDef("pydrofoil.RISCV64",
    __new__ = interp2app(riscv64_descr_new),
    step = interp2app(W_RISCV64.step),
)
