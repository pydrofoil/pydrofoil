from pydrofoil import mem as mem_mod
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

class Globals(object):
    def __init__(self):
        self.mem = mem_mod.BlockMemory()

def load_raw(machine, offsets, filenames):
    machine.g = Globals()
    assert len(offsets) == len(filenames)
    for i in range(len(offsets)):
        offset = offsets[i]
        fn = filenames[i]
        f = open(fn, 'rb')
        content = f.read()
        for i, byte in enumerate(content):
            machine.g.mem.write(offset + i, 1, r_uint(ord(byte)))
