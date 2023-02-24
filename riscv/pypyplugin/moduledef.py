from pypy.interpreter.mixedmodule import MixedModule

class Module(MixedModule):
    applevel_name = '_pydrofoil'

    appleveldefs = {
    }

    interpleveldefs = {
        'RISCV64': 'interp_plugin.W_RISCV64',
    }

    def __init__(self, space, w_name):
        from riscv.pypyplugin import interp_plugin
        MixedModule.__init__(self, space, w_name)
        interp_plugin._patch_machineclasses()
