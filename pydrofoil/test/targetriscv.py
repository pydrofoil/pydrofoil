from pydrofoil.makecode import *

import os

riscvir = os.path.join(os.path.dirname(__file__), "riscv_model_RV64.ir")
outriscvpy = os.path.join(os.path.dirname(__file__), "outriscv.py")



def target(*args):
    import py
    print "making python code"
    with open(riscvir, "rb") as f:
        s = f.read()
    res = parse_and_make_code(s, "supportcoderiscv")
    with open(outriscvpy, "w") as f:
        f.write(res)
    print "translating to C!"
    return main

def main(argv):
    from pydrofoil.test.supportcoderiscv import main
    return main(argv)


if __name__ == '__main__':
    import sys
    main(sys.argv)
