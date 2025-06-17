from _pydrofoilcapi_cffi import ffi
import _pydrofoil

all_cpu_handles = []

class C:
    def __init__(self, n=None):
        self.arg = n
        self.reset()

    def step(self):
        self.steps += 1
        self.cpu.step()

    def reset(self):
        self.cpu = _pydrofoil.RISCV64(self.arg)
        self.steps = 0

@ffi.def_extern()
def pydrofoil_allocate_cpu(s):
    if s:
        filename = ffi.string(s).decode('utf-8')
    else:
        filename = None
    print(filename)

    all_cpu_handles.append(res := ffi.new_handle(C(filename)))
    return res

@ffi.def_extern()
def pydrofoil_free_cpu(i):
    try:
        all_cpu_handles.remove(i)
    except Exception:
        return -1
    return 0

@ffi.def_extern()
def pydrofoil_cpu_simulate(i, steps):
    cpu = ffi.from_handle(i)
    for i in range(steps):
        cpu.step()
    return steps

@ffi.def_extern()
def pydrofoil_cpu_cycles(i):
    cpu = ffi.from_handle(i)
    return cpu.steps

@ffi.def_extern()
def pydrofoil_cpu_pc(i):
    cpu = ffi.from_handle(i)
    return cpu.cpu.read_register('pc')

@ffi.def_extern()
def pydrofoil_cpu_reset(i):
    cpu = ffi.from_handle(i)
    cpu.reset()
    return 0

@ffi.def_extern()
def pydrofoil_cpu_set_verbosity(i, v):
    cpu = ffi.from_handle(i)
    cpu.cpu.set_verbosity(bool(v))
    return 0
