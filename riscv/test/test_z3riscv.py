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


def test_decode_and_execute_addi(riscvsharedstate):
    graph = riscvsharedstate.funcs['zencdec_backwards']
    interp = z3backend.RiscvInterpreter(graph, [z3backend.ConstantSmallBitVector(r_uint(0xfe0f0f13))], riscvsharedstate.copy(), _64bit=True)
    ast = interp.run()
    assert isinstance(ast, z3backend.UnionConstant)
    assert ast.variant_name == "zITYPE"
    assert str(ast.w_val) == "<StructConstant [4064, 30, 30, zRISCV_ADDI] ztuplez3z5bv12_z5bv5_z5bv5_z5enumz0zziop>"

    print("start executing", ast)
    graph = riscvsharedstate.funcs['zexecute_zITYPE']
    interp = z3backend.RiscvInterpreter(graph, [ast], riscvsharedstate.copy(), _64bit=True)
    res = interp.run()
    assert str(res) == "zRETIRE_SUCCESS"
    #assert str(interp.registers['zx30']).startswith("18446744073709551584 + init_zx30!"

    print("start executing", ast)
    graph = riscvsharedstate.funcs['zexecute_zITYPE']
    ast.w_val.vals_w[1] = z3backend.Z3Value(z3.FreshConst(z3.BitVecSort(5)))
    ast.w_val.vals_w[2] = z3backend.Z3Value(z3.FreshConst(z3.BitVecSort(5)))
    interp = z3backend.RiscvInterpreter(graph, [ast], riscvsharedstate.copy(), _64bit=True)
    res = interp.run()
    #import pdb;pdb.set_trace()

def test_prove_itype_cant_switch_mode(riscvsharedstate):
    graph = riscvsharedstate.funcs['zexecute_zITYPE']
    union_typ = graph.args[0].resolved_type
    struct_typ = union_typ.variants['zITYPE']
    z3_struct = riscvsharedstate.get_abstract_struct_const_of_type(struct_typ, '')
    z3_union_typ = riscvsharedstate.convert_type_to_z3_type(union_typ)
    arg = z3backend.UnionConstant('zITYPE', z3backend.Z3Value(z3_struct), union_typ, z3_union_typ)
    interp = z3backend.RiscvInterpreter(graph, [arg], riscvsharedstate.copy(), _64bit=True)
    registers_old = interp.registers.copy()
    interp.run()
    solver = z3.Solver()
    res = solver.check(z3.Not(registers_old['zcur_privilege'].toz3() == interp.registers['zcur_privilege'].toz3()))
    assert res == z3.unsat

#def test_invalid_opcode(riscvsharedstate):
#    graph = riscvsharedstate.funcs['zencdec_backwards']
#    print("start executing", graph)
#    interp = z3backend.RiscvInterpreter(graph, [z3backend.ConstantSmallBitVector(r_uint(0x65))], riscvsharedstate.copy(), _64bit=True)
#    res = interp.run()
#    assert isinstance(res, z3backend.Z3Value)
#    assert str(res) == "?"

