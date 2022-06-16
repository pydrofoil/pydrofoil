from rpython.rlib import rarithmetic
from pydrofoil.test.supportcode import load_rom

def target(*args):
    return main

def main(argv):
    from pydrofoil.test.out import func_zmain
    if len(argv) != 3:
        print "usage: %s <binary> <maxcycle>" % (argv[0], )
        return -1
    load_rom(argv[1])
    func_zmain(rarithmetic.r_uint(int(argv[2])))
    return 0


if __name__ == '__main__':
    import sys
    main(sys.argv)
