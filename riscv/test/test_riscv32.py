import pytest
from pydrofoil.makecode import *

import os
from os.path import dirname

toplevel = dirname(dirname(dirname(__file__)))
elfdir = os.path.join(toplevel, "riscv/input")

elfs = """
rv32ui-p-addi.elf
"""

elfs = [os.path.join(elfdir, fn) for fn in elfs.split()]


@pytest.fixture(scope='session')
def riscvmain():
    from riscv.targetriscv import make_code
    return make_code(rv64=False)

@pytest.mark.parametrize("elf", elfs)
def test_full_riscv(riscvmain, elf):
    riscvmain(['executable', elf])

