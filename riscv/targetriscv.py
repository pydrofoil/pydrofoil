import sys
sys.setrecursionlimit(2**31-1)

from pydrofoil.makecode import *

import os

thisdir = os.path.dirname(__file__)

riscvirs = [os.path.join(thisdir, "riscv_model_RV32.ir"), os.path.join(thisdir, "riscv_model_RV64.ir")]
outriscvpys = [os.path.join(thisdir, "generated/outriscv32.py"), os.path.join(thisdir, "generated/outriscv.py")]

def should_inline(name):
    if "zextensionEnabled" in name:
        return True
    if "zmatch_TLB_Entry" in name:
        return True

def _make_code(rv64=True):
    print "making python code"
    with open(riscvirs[rv64], "rb") as f:
        s = f.read()
    support_code = "from riscv import supportcoderiscv as supportcode"
    entrypoints = "ztick_clock ztick_platform zinit_model zphys_mem_read zstep zext_decode".split()
    res = parse_and_make_code(s, support_code, {'zPC', 'znextPC', 'zMisa_chunk_0', 'zcur_privilege', 'zMstatus_chunk_0', }, entrypoints=entrypoints, should_inline=should_inline)
    with open(outriscvpys[rv64], "w") as f:
        f.write(res)
    if rv64:
        from riscv.generated import outriscv
    else:
        from riscv.generated import outriscv32 as outriscv
    return outriscv

def make_code(rv64=True):
    from riscv import supportcoderiscv
    outriscv = _make_code(rv64)
    return supportcoderiscv.get_main(outriscv, rv64)

def make_code_combined():
    from riscv import supportcoderiscv
    mod64 = _make_code(True)
    machinecls64 = supportcoderiscv.get_main(mod64, True)._machinecls
    mod32 = _make_code(False)
    machinecls32 = supportcoderiscv.get_main(mod32, False)._machinecls
    def bound_main(argv):
        return supportcoderiscv.main(argv, machinecls64, machinecls32)
    return bound_main
    

def target(*args):
    import py
    main = make_code_combined()
    print "translating to C!"
    return main

if __name__ == '__main__':
    import sys
    try:
        target()(sys.argv)
    except:
        import pdb;pdb.xpm()
        raise
