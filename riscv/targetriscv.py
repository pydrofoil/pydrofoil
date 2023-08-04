import sys
sys.setrecursionlimit(2**31-1)

from pydrofoil.makecode import *

import os

thisdir = os.path.dirname(__file__)

riscvirs = [os.path.join(thisdir, "riscv_model_RV32.ir"), os.path.join(thisdir, "riscv_model_RV64.ir")]
outriscvpys = [os.path.join(thisdir, "generated/outriscv32.py"), os.path.join(thisdir, "generated/outriscv.py")]

def _make_code(rv64=True):
    print "making python code"
    with open(riscvirs[rv64], "rb") as f:
        s = f.read()
    support_code = "from riscv import supportcoderiscv as supportcode"
    res = parse_and_make_code(s, support_code, {'zPC', 'znextPC', 'zMisa_chunk_0', 'zcur_privilege', 'zMstatus_chunk_0', })
    ## XXX horrible hack, they should be fixed in the model!
    assert res.count("def func_zread_ram(machine, zrk") == 1
    res = res.replace("def func_zread_ram(machine, zrk", "def func_zread_ram(machine, executable_flag, zrk")
    assert res.count("func_zread_ram(machine, U") == 1
    res = res.replace("func_zread_ram(machine, U", "func_zread_ram(machine, (type(zt) is Union_zAccessTypezIuzK_zExecutezIuzK), U")
    assert res.count("platform_read_mem") == 1
    res = res.replace("platform_read_mem(machine, ", "platform_read_mem(machine, executable_flag, ")
    bits = 64 if rv64 else 32

    ## another one of them:
    #target = "return_ = Union_zExt_DataAddr_CheckzIuzK_zExt_DataAddr_OKzIuzK(supportcode.add_bits_bv_bv(func_zrX(machine, supportcode.int_to_int64(machine, supportcode.sail_unsigned(machine, bitvector.from_ruint(5, zbase)))), zoffset, %s))" % bits
    #assert res.count(target) == 1
    #res = res.replace(target, "zaddr_lz30 = supportcode.add_bits_bv_bv(func_zrX(machine, supportcode.int_to_int64(machine, supportcode.sail_unsigned(machine, bitvector.from_ruint(5, zbase)))), zoffset, %s); supportcode.promote_addr_region(machine, zaddr_lz30, zwidth, zoffset, (type(zacc) is Union_zAccessTypezIuzK_zExecutezIuzK)); return_ = Union_zExt_DataAddr_CheckzIuzK_zExt_DataAddr_OKzIuzK(zaddr_lz30)" % bits)
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
