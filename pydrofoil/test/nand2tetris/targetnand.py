import os
from rpython.rlib import rarithmetic
from pydrofoil.test.nand2tetris import supportcodenand
from pydrofoil.test.nand2tetris.supportcodenand import load_rom 
from pydrofoil.makecode import *

nandir = os.path.join(os.path.dirname(__file__), "generated/nand2tetris.jib")
outnandpy = os.path.join(os.path.dirname(__file__), "generated/nand_rpython.py")

def make_code():
    print "making rpython code"
    with open(nandir, "rb") as f:
        s = f.read()
    support_code = "from pydrofoil.test.nand2tetris import supportcodenand as supportcode"
    res = parse_and_make_code(s, support_code)
    with open(outnandpy, "w") as f:
        f.write(res)
    from pydrofoil.test.nand2tetris.generated import nand_rpython
    return nand_rpython, supportcodenand

def target(*args):
    make_code()
    return main

def main(argv):
    from pydrofoil.test.nand2tetris.generated.nand_rpython import func_zmymain
    if len(argv) != 4:
        print "usage: %s <binary> <maxcycle> <debug>" % (argv[0], )
        return -1
    load_rom(argv[1])
    func_zmymain(rarithmetic.r_uint(int(argv[2])), int(argv[3]))
    return 0


if __name__ == '__main__':
    import sys
    try:
        target()(sys.argv)
    except Exception as e:
        print e
        import pdb;pdb.xpm()
        raise
