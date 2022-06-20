import sys
sys.setrecursionlimit(2**31-1)
from rpython import conftest

class o:
    view = False
    viewloops = True
conftest.option = o

from rpython.jit.metainterp.test.support import LLJitMixin
import os

elffile = os.path.join(os.path.dirname(__file__), "rv64um-v-mulhu.elf")

from pydrofoil.test.supportcoderiscv import *

class TestNandJIT(LLJitMixin):
    def test_sum(self):
        from pydrofoil.test import outriscv
        get_main()
        g.config_print_instr = False
        g.config_print_reg = False
        g.config_print_mem_access = False
        g.config_print_platform = False
        argv = ['executable', elffile]
        outriscv.model_init()
        entry = load_sail(elffile)
        init_sail(entry)
        def f():
            run_sail()
        self.meta_interp(f, [], listcomp=True, listops=True, backendopt=True)
