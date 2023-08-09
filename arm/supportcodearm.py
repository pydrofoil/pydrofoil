from pydrofoil.supportcode import *

def make_dummy(name):
    def dummy(machine, *args):
        if objectmodel.we_are_translated():
            print "not implemented!", name
            raise ValueError
        import pdb; pdb.set_trace()
        return 123
    dummy.func_name += name
    globals()[name] = dummy


def sail_get_verbosity(machine, _):
    return 0 # XXX for now

def platform_branch_announce(machine, *args):
    return ()

def reset_registers(machine, *args):
    return ()
