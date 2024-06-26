import os
from rpython.rlib import rarithmetic, jit
from rpython.rlib.rarithmetic import r_uint, intmask
from pydrofoil.test.nand2tetris import supportcodenand
from pydrofoil.test.nand2tetris.supportcodenand import load_rom, my_print_debug, my_read_rom
from pydrofoil.makecode import *
from rpython.rlib.jit import JitDriver

nandir = os.path.join(os.path.dirname(__file__), "generated/nand2tetris.jib")
outnandpy = os.path.join(os.path.dirname(__file__), "generated/nand_rpython.py")

def get_printable_location(pc, debug):
    return str(pc) + ' ' + str(debug) + ' ' + hex(my_read_rom(pc))

driver = JitDriver(
    get_printable_location=get_printable_location,
    greens=['pc', 'debug'],
    reds='auto')


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
    from pydrofoil.supportcode import parse_args
    jitarg = parse_args(argv, "--jit")
    if jitarg:
        jit.set_user_param(None, jitarg)
    if len(argv) != 4:
        print "usage: %s <binary> <maxcycle> <debug>" % (argv[0], )
        return -1
    load_rom(argv[1])
    #func_zmymain(rarithmetic.r_uint(int(argv[2])), int(argv[3]))
    jit_run(int(argv[2]), int(argv[3]))
    return 0

def jit_run(limit, debug):
    from pydrofoil.test.nand2tetris.generated import nand_rpython
    r = nand_rpython.r
    r.zPC = r_uint(0)
    r.zA = r_uint(0)
    r.zD = r_uint(0)
    cycle_count = 0
    cont = True
    while cont:
        driver.jit_merge_point(pc=r.zPC, debug=debug)
        cont = False
        if debug:
            my_print_debug(cycle_count, r.zPC, r.zA, r.zD)
        if nand_rpython.func_zfetch_decode_execute(()):
            cont = cycle_count < limit
        cycle_count += 1


if __name__ == '__main__':
    import sys
    try:
        target()(sys.argv)
    except Exception as e:
        print e
        import pdb;pdb.xpm()
        raise
