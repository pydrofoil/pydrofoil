import pytest
import os
import time
import z3

from pydrofoil.z3backend import z3backend, z3btypes, graph_util, knownbits
from pydrofoil.z3backend import z3backend_executor, readangr, readvexingz3
from rpython.rlib.rarithmetic import r_uint 

RISCV_INSTRUCTION_SIZE = 32

##### copied from test_z3riscv #####

@pytest.fixture(scope='session')
def riscv_first_shared_state():
    return graph_util.generate_shared_state_riscv64()

@pytest.fixture(scope='function')
def riscvsharedstate(riscv_first_shared_state):
    return riscv_first_shared_state.copy()

####################################

def _set_init_registers(riscvsharedstate, interp):
    interp.registers["zmisa"] = z3backend_executor.get_rv64_usermode_misa_w_value(riscvsharedstate)
    interp.registers["zmstatus"] = z3backend_executor.get_rv64_usermode_mstatus_w_value(riscvsharedstate)
    interp.registers["zsatp"] = z3btypes.ConstantSmallBitVector(0, 64)
    interp.registers["zcur_privilege"] = z3backend_executor.get_rv64_usermode_cur_privilege_w_value(riscvsharedstate)
    interp.registers["zmie"] = z3backend_executor.get_rv64_mie_0_w_value(riscvsharedstate)
    interp.registers["zmip"] = z3backend_executor.get_rv64_mip_0_w_value(riscvsharedstate)
    interp.registers["zmtime"] = z3backend_executor.get_rv64_mtime_0_value(riscvsharedstate)
    interp.registers["zmtimecmp"] =  z3backend_executor.get_rv64_mtimecmp_0_value(riscvsharedstate)
    interp.registers["zmedeleg"] = z3backend_executor.get_rv64_medeleg_0_w_value(riscvsharedstate)
    # do we need mideleg?

class DummyGraph(object):
    def __init__(self):
        self.has_loop = False
        self.args = []

def test_execute_addi_abstract_target_reg(riscvsharedstate):
    """ Execute a addi xn, x7, 117 execution with abstract target register """
    decode_graph = riscvsharedstate.funcs['zencdec_backwards']

    #                                 117       x7   opc  xn?    opc                only xn? unknown
    #                           0b000001110101_00111_000_00000_0010011, 0b000000000000_00000_000_11111_0000000
    known = knownbits.KnownBits(0b00000111010100111000000000010011, 0b00000000000000000000111110000000)
    opcode = z3btypes.Z3SmallBitVector(z3.BitVec("z3mergez3var", 32), known)
    #

    interp = z3backend.RiscvInterpreter(decode_graph, [opcode], riscvsharedstate.copy())
    _set_init_registers(riscvsharedstate, interp)

    start = time.time()
    instr_ast = interp.run()
    print "decoding took %s seconds" % str(time.time()- start)

    execute_graphs = riscvsharedstate.mthds["zexecute"]

    assert str(instr_ast) == "zITYPE(<StructConstant [117, 7, Extract(11, 7, z3mergez3var), zRISCV_ADDI] ztuplez3z5bv12_z5bv5_z5bv5_z5enumz0zziop>)"

    interp = z3backend.RiscvInterpreter(DummyGraph(), [], riscvsharedstate.copy(), {}) # cant execute methods as interpreter graph arg
    _set_init_registers(riscvsharedstate, interp)

    init_x7 = interp.registers["zx7"]
    
    start = time.time()
    res = interp._concrete_method_call(execute_graphs, [instr_ast])
    print "executing took %s seconds" % str(time.time()- start)

    assert str(res) == "zRETIRE_SUCCESS"

    for i in range(1,32):
        register = "zx%d" % i
        value = interp.registers[register]

        solver = z3.Solver()
        solver.add(z3.Extract(11, 7, opcode.toz3()) == z3.BitVecVal(i, 5)) # 11, 7
        solver.add(init_x7.toz3() == 115)
        slv = solver.check(value.toz3() != 115 + 117)
        # TODO: check  that other regs are unchanged
        assert slv == z3.unsat

def test_execute_addi_abstract_source_reg(riscvsharedstate):
    """ Execute a addi x7, xn, 115 execution with abstract target register """
    decode_graph = riscvsharedstate.funcs['zencdec_backwards']

    #                                 115       xn?   opc   x7    opc                only xn? unknown
    #                           0b000001110011_00000_000_00111_0010011, 0b000000000000_11111_000_00000_0000000
    known = knownbits.KnownBits(0b00000111001100000000001110010011,     0b00000000000011111000000000000000)
    opcode = z3btypes.Z3SmallBitVector(z3.BitVec("z3mergez3var", 32), known)
    #

    interp = z3backend.RiscvInterpreter(decode_graph, [opcode], riscvsharedstate.copy())
    _set_init_registers(riscvsharedstate, interp)

    start = time.time()
    instr_ast = interp.run()
    print "decoding took %s seconds" % str(time.time()- start)

    execute_graphs = riscvsharedstate.mthds["zexecute"]

    assert str(instr_ast) == "zITYPE(<StructConstant [115, Extract(19, 15, z3mergez3var), 7, zRISCV_ADDI] ztuplez3z5bv12_z5bv5_z5bv5_z5enumz0zziop>)"

    interp = z3backend.RiscvInterpreter(DummyGraph(), [], riscvsharedstate.copy(), {}) # cant execute methods as interpreter graph arg
    _set_init_registers(riscvsharedstate, interp)

    init_regs = {"zx%d" % i: interp.registers["zx%d" % i] for i in range(1,32)}
    
    start = time.time()
    res = interp._concrete_method_call(execute_graphs, [instr_ast])
    print "executing took %s seconds" % str(time.time() - start)

    x7_value = interp.registers["zx7"]

    assert str(res) == "zRETIRE_SUCCESS"

    for i in range(1,32):
        register = "zx%d" % i
        init_name = init_regs[register]

        solver = z3.Solver()
        solver.add(z3.Extract(19, 15, opcode.toz3()) == z3.BitVecVal(i, 5))
        solver.add(init_name.toz3() == 117)
        slv = solver.check(x7_value.toz3() != 115 + 117)

        assert slv == z3.unsat