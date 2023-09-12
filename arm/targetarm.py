import sys
import os
from os.path import dirname
from pydrofoil.makecode import parse_and_make_code
toplevel = dirname(dirname(__file__))
armir = os.path.join(toplevel, "arm", "armv9.ir")
outarm = os.path.join(toplevel, "arm", "generated", "outarm.py")

sys.setrecursionlimit(20000) # otherwise jitcode writing fails

PROMOTED_REGISTERS = set("""
z__empam_implemented
z__mpam_implemented
z__supported_pa_sizze
z__block_bbm_implemented
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
    if driver is not None:
        driver.config.translation.suggest(jit_opencoder_model="big")
        driver.config.translation.suggest(withsmallfuncsets=0)
        driver.config.translation.suggest(output="pydrofoil-arm")
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
