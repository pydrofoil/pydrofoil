import pytest
import os
import z3
from pydrofoil import z3backend
from rpython.rlib.rarithmetic import r_uint 

@pytest.fixture(scope='session')
def riscv_first_shared_state():
    from riscv.targetriscv import make_codegen
    c = make_codegen()  
    registers = {name: c.globalnames[name].typ for name in c.all_registers}
    return z3backend.SharedState(c.all_graph_by_name.copy(), registers)

@pytest.fixture(scope='function')
def riscvsharedstate(riscv_first_shared_state):
    return riscv_first_shared_state.copy()


def test_decode(riscvsharedstate):
    graph = riscvsharedstate.funcs['zencdec_backwards']
    interp = z3backend.RiscvInterpreter(graph, [z3backend.Constant(r_uint(0b1100))], riscvsharedstate.copy())
    res = interp.run()
    assert isinstance(res, z3backend.UnionConstant)
    assert res.variant == "zC_D"