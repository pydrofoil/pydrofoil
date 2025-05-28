from pypy.interpreter.mixedmodule import MixedModule

class TypesModule(MixedModule):
    """ Pydrofoil Sail types """
    applevel_name = '_pydrofoil.sailtypes'

    interpleveldefs = {
        'SailType': 'interp_types.Type',
        'Function': 'interp_types.Function',
        'FixedBitVector': 'interp_types.FixedBitVector',
        'SmallFixedBitVector': 'interp_types.SmallFixedBitVector',
        'BigFixedBitVector': 'interp_types.BigFixedBitVector',
        'GenericBitVector': 'interp_types.GenericBitVector',
        'Union': 'interp_types.Union',
        'String': 'interp_types.String',
        'Struct': 'interp_types.RegularStruct',
        'Tuple': 'interp_types.TupleStruct',
        'Bool': 'interp_types.Bool',
        'Enum': 'interp_types.Enum',
        'Real': 'interp_types.Real',
        'Int': 'interp_types.Int',
        'MachineInt': 'interp_types.MachineInt',
        'Unit': 'interp_types.Unit',
    }

    appleveldefs = {}


class Module(MixedModule):
    """ Pydrofoil scripting API """

    applevel_name = '_pydrofoil'

    appleveldefs = {
        'SailAssertionError': 'app_plugin.SailAssertionError',
        'SailException': 'app_plugin.SailException',
    }

    interpleveldefs = {
        'RISCV64': 'interp_plugin.W_RISCV64',
        'RISCV32': 'interp_plugin.W_RISCV32',
        'bitvector': 'interp_plugin.BitVector',
    }

    submodules = {
        "sailtypes": TypesModule,
    }

    def __init__(self, space, w_name):
        from riscv.pypymodule import interp_plugin
        MixedModule.__init__(self, space, w_name)
        interp_plugin._patch_machineclasses(space=space)
