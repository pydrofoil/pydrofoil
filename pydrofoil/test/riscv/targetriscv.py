import sys
sys.setrecursionlimit(2**31-1)

from pydrofoil.makecode import *

import os

thisdir = os.path.dirname(__file__)

riscvirs = [os.path.join(thisdir, "riscv_model_RV32.ir"), os.path.join(thisdir, "riscv_model_RV64.ir")]
outriscvpys = [os.path.join(thisdir, "generated/outriscv32.py"), os.path.join(thisdir, "generated/outriscv.py")]

def make_code(rv64=True):
    print "making python code"
    with open(riscvirs[rv64], "rb") as f:
        s = f.read()
    support_code = "from pydrofoil.test.riscv import supportcoderiscv as supportcode"
    res = parse_and_make_code(s, support_code, {'zPC', 'znextPC', 'zMisa_chunk_0', 'zcur_privilege', 'zMstatus_chunk_0', })
    # XXX horrible hack, they should be fixed in the model!
    assert res.count("func_zread_ram(machine, zrk") == 2
    res = res.replace("def func_zread_ram(machine, zrk", "def func_zread_ram(machine, executable_flag, zrk")
    res = res.replace("func_zread_ram(machine, zrk", "func_zread_ram(machine, (type(zt) is Union_zAccessType_zExecute), zrk")
    assert res.count("platform_read_mem") == 1
    res = res.replace("platform_read_mem(", "platform_read_mem(executable_flag, ")

    # another one of them:
    assert res.count("return_ = Union_zExt_DataAddr_Check_zExt_DataAddr_OK(zaddr_lz30") == 1
    res = res.replace("return_ = Union_zExt_DataAddr_Check_zExt_DataAddr_OK(zaddr_lz30", "supportcode.promote_addr_region(machine, zaddr_lz30, zwidth, zoffset, (type(zacc) is Union_zAccessType_zExecute)); return_ = Union_zExt_DataAddr_Check_zExt_DataAddr_OK(zaddr_lz30")
    with open(outriscvpys[rv64], "w") as f:
        f.write(res)
    if rv64:
        from pydrofoil.test.riscv.generated import outriscv
    else:
        from pydrofoil.test.riscv.generated import outriscv32 as outriscv
    from pydrofoil.test.riscv import supportcoderiscv
    supportcoderiscv.g.rv64 = rv64
    return outriscv, supportcoderiscv

def target(*args):
    import py
    outriscv, supportcoderiscv = make_code()
    print "translating to C!"
    from pydrofoil.test.riscv.supportcoderiscv import get_main
    main = get_main()
    return main

if __name__ == '__main__':
    import sys
    try:
        target()(sys.argv)
    except:
        import pdb;pdb.xpm()
        raise
