import os
from pydrofoil.z3backend import readvexingz3, readangr

def test_calling_vexingz3_works():
    opcode = 0x027383b3 # mul x7, x7, x7
    executions = readvexingz3.run_vexingz3_opcodes([opcode], "riscv64")

    assert readangr.get_code_from_execution(executions[0]) == [0x027383b3]
    assert "(bvmul x7 x7)" == readangr.get_result_regs_from_execution(executions[0])["x7"]