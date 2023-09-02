import sys
import os
from os.path import dirname
from pydrofoil.makecode import parse_and_make_code
toplevel = dirname(dirname(__file__))
armir = os.path.join(toplevel, "arm", "armv9.ir")
outarm = os.path.join(toplevel, "arm", "generated", "outarm.py")

sys.setrecursionlimit(20000) # otherwise jitcode writing fails

PROMOTED_REGISTERS = set("""
zTCR_EL1
z__empam_implemented
zMAIR_EL3
zMPAMIDR_EL1
z__mpam_implemented
zSCTLR_EL3
zTCR_EL3
zDBGEN
z_EDSCR_0_28
z_EDSCR_31_31
zMDCCSR_EL0
zMPAM3_EL3
zOSLSR_EL1
z__supported_pa_sizze
zTSTATE
zCNTCR
zCNTHP_CTL_EL2
zCNTHPS_CTL_EL2
zCNTHV_CTL_EL2
zCNTHVS_CTL_EL2
zCNTP_CTL_EL0
zCNTPS_CTL_EL1
zMDCR_EL2
zPSTATE
zMDSCR_EL1
zHCR_EL2
zSCR_EL3
""".split())

def make_code(regen=True):
    from arm import supportcodearm
    outarm = _make_code(regen)
    return supportcodearm.get_main(outarm)

def _make_code(regen=True):
    print "making python code"
    if regen:
        with open(armir, "rb") as f:
            s = f.read()
        support_code = "from arm import supportcodearm as supportcode"
        res = parse_and_make_code(s, support_code, PROMOTED_REGISTERS)
        with open(outarm, "w") as f:
            f.write(res)
        print "written file", outarm, "importing now"
    else:
        print "skipping regeneration, importing"
    from arm.generated import outarm as mod
    print "done"
    return mod

def target(driver, cmdlineargs):
    main = make_code(regen="--no-arm-regen" not in cmdlineargs)
    print "translating to C!"
    return main

if __name__ == '__main__':
    import sys
    try:
        target(None, [])(sys.argv)
    except:
        import pdb;pdb.xpm()
        raise
