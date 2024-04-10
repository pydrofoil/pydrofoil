from pypy.interpreter.mixedmodule import MixedModule

class Module(MixedModule):
    applevel_name = '_pydrofoil'

    appleveldefs = {
    }

    interpleveldefs = {
        'RISCV64': 'interp_plugin.W_RISCV64',
        'RISCV32': 'interp_plugin.W_RISCV32',
        'bitvector': 'interp_plugin.BitVector',
    }

    def __init__(self, space, w_name):
        from riscv.pypymodule import interp_plugin
        MixedModule.__init__(self, space, w_name)
        interp_plugin._patch_machineclasses()
