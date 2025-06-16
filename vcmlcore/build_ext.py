import cffi
ffibuilder = cffi.FFI()


# steps:
# download artifact.zip from github to pydrofoil/ folder and unzip it
# then run build.sh

with open('pydrofoilcapi.h') as f:
    # read .h and pass it to embedding_api(), manually
    # removing the '#' directives
    data = ''.join([line for line in f if not line.startswith('#')])
    data = data.replace('CFFI_DLLEXPORT', '')
    ffibuilder.embedding_api(data)

ffibuilder.set_source("_pydrofoilcapi_cffi", r'''
    #include "pydrofoilcapi.h"
''')

ffibuilder.embedding_init_code("""
    from _pydrofoilcapi_cffi import ffi
    import _pydrofoil

    all_cpus = {}

    class C:
        def __init__(self, n=None):
            self.cpu = _pydrofoil.RISCV64(n)
            self.steps = 0

        def step(self):
            self.steps += 1
            self.cpu.step()

    @ffi.def_extern()
    def pydrofoil_allocate_cpu(s):
        if s:
            filename = ffi.string(s).decode('utf-8')
        else:
            filename = None
        print(filename)
        index = len(all_cpus)
        all_cpus[index] = C(filename)
        return ffi.new_handle(index)

    @ffi.def_extern()
    def pydrofoil_simulate_cpu(i, steps):
        cpu = all_cpus[ffi.from_handle(i)]
        for i in range(steps):
            cpu.step()
        return steps

    @ffi.def_extern()
    def pydrofoil_cycles_cpu(i):
        cpu = all_cpus[ffi.from_handle(i)]
        return cpu.steps

    @ffi.def_extern()
    def pydrofoil_free_cpu(i):
        try:
            del all_cpus[ffi.from_handle(i)]
        except Exception:
            return -1
        return 0

""")

ffibuilder.emit_c_code("_pydrofoilcapi_cffi.c")
