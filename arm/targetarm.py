import os
from os.path import dirname
from pydrofoil.makecode import parse_and_make_code
toplevel = dirname(dirname(__file__))
armir = os.path.join(toplevel, "arm", "armv9.ir")
outarm = os.path.join(toplevel, "arm", "generated", "outarm.py")

def make_code():
    print "making python code"
    with open(armir, "rb") as f:
        s = f.read()
    support_code = "from arm import supportcodearm as supportcode"
    res = parse_and_make_code(s, support_code)
    with open(outarm, "w") as f:
        f.write(res)
    print "written file", outarm, "importing now"
    from arm.generated import outarm as mod
    print "done"
    def main(argv):
        return mod.func_zmain()
    main.mod = mod
    return main

def target(*args):
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
