import sys
sys.setrecursionlimit(2**31-1)

from pydrofoil.makecode import *

import os

riscvir = os.path.join(os.path.dirname(__file__), "riscv_model_RV64.ir")
outriscvpy = os.path.join(os.path.dirname(__file__), "generated/outriscv.py")

def make_code():
    print "making python code"
    with open(riscvir, "rb") as f:
        s = f.read()
    support_code = "from pydrofoil.test.riscv import supportcoderiscv as supportcode"
    res = parse_and_make_code(s, support_code, {'zPC', 'znextPC', 'zMisa_chunk_0', 'zcur_privilege', 'zMstatus_chunk_0', })
    # XXX horrible hack, they should be fixed in the model!
    assert res.count("func_zread_ram(zrk") == 2
    res = res.replace("def func_zread_ram(zrk", "def func_zread_ram(executable_flag, zrk")
    res = res.replace("func_zread_ram(zrk", "func_zread_ram((type(zt) is Union_zAccessType_zExecute), zrk")
    assert res.count("platform_read_mem") == 1
    res = res.replace("platform_read_mem(", "platform_read_mem(executable_flag, ")

    # another one of them:
    assert res.count("return_ = Union_zExt_DataAddr_Check_zExt_DataAddr_OK(zaddr_lz30") == 1
    res = res.replace("return_ = Union_zExt_DataAddr_Check_zExt_DataAddr_OK(zaddr_lz30", "supportcode.promote_addr_region(zaddr_lz30, zwidth, zoffset, (type(zacc) is Union_zAccessType_zExecute)); return_ = Union_zExt_DataAddr_Check_zExt_DataAddr_OK(zaddr_lz30")
    with open(outriscvpy, "w") as f:
        f.write(res)
    from pydrofoil.test.riscv.generated import outriscv
    from pydrofoil.test.riscv import supportcoderiscv
    return outriscv, supportcoderiscv

def target(*args):
    import py
    outriscv, supportcoderiscv = make_code()
    print "translating to C!"
    from pydrofoil.test.riscv.supportcoderiscv import get_main, g
    main = get_main()
    return main

if __name__ == '__main__':
    import sys
    try:
        target()(sys.argv)
    except:
        import pdb;pdb.xpm()
        raise
