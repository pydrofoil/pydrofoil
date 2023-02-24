# Package initialisation
from pypy.interpreter.mixedmodule import MixedModule

class Module(MixedModule):
    applevel_name = '_pydrofoil'

    appleveldefs = {
    }

    interpleveldefs = {
        'RISCV64': 'interp_plugin.W_RISCV64',
    }

