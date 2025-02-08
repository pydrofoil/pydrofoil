import sys
sys.setrecursionlimit(2**31-1)

from pydrofoil.makecode import *

import os

thisdir = os.path.dirname(__file__)

cheriotir = os.path.join(thisdir, "cheriot_model_rv32.ir")
outcheriotpy = os.path.join(thisdir, "generated/outcheriot32.py")

def _make_code():
    print "making python code"
    with open(cheriotir, "rb") as f:
        s = f.read()
    support_code = "from cheriot import supportcodecheriot as supportcode"
    entrypoints = "ztick_clock ztick_platform zword_width_bytes zinit_model zstep zext_decode zcapToBits zcapToString zcapBitsToCapability".split()
    res = parse_and_make_code(s, support_code, {'zPC', 'znextPC', 'zMisa_chunk_0', 'zcur_privilege', 'zMstatus_chunk_0', }, entrypoints=entrypoints)
    with open(outcheriotpy, "w") as f:
        f.write(res)
    from cheriot.generated import outcheriot32 as outcheriot
    return outcheriot

def make_code():
    from cheriot import supportcodecheriot
    outcheriot = _make_code()
    return supportcodecheriot.get_main(outcheriot)


def target(driver, cmdlineargs):
    import py
    if driver is not None:
        driver.config.translation.suggest(output="pydrofoil-cheriot")
    main = make_code()
    print "translating to C!"
    return main

if __name__ == '__main__':
    import sys
    try:
        target()(sys.argv)
    except:
        import pdb;pdb.xpm()
        raise
