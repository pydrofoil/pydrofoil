import pytest
import os
import z3
from pydrofoil import graphalgorithms
from pydrofoil import ir
from pydrofoil.z3backend import z3backend
from rpython.rlib.rarithmetic import r_uint 

@pytest.fixture(scope='session')
def riscv_first_shared_state():
    from riscv import targetriscv
    p = os.path.join(os.path.dirname(os.path.abspath(targetriscv.__file__)), "generated", "riscvgraphs.py")
    if not os.path.exists(p):
        print "generating graphs"
        c = targetriscv.make_codegen()
        s = dump_graphs_and_registers(c)
        with open(p, "w") as f:
            f.write(s)
    import time
    t1 = time.time()
    from riscv.generated import riscvgraphs
    riscvsharedstate = z3backend.SharedState(
        {name: func() for name, func in riscvgraphs.funcs.iteritems()},
        riscvgraphs.registers
    )
    ### We assume that every graph only has one return; thus we must compute every singe return graph here ### 
    for name, graph in riscvsharedstate.funcs.iteritems():
        riscvsharedstate.funcs[name] = graphalgorithms.compute_single_return_graph(graph)
    t2 = time.time()
    print "loaded in %ss" % round(t2 - t1, 2)
    return riscvsharedstate

def dump_graphs_and_registers(c):
    code = ["from pydrofoil.ir import *",
            "from pydrofoil.types import *",
            "funcs = {}"]
    for name, graph in c.all_graph_by_name.iteritems():
        code.append("def %s():" % name)
        for line in ir.print_graph_construction(graph):
            code.append("    " + line)
        code.append("    return graph")
        code.append("funcs[%r] = %s" % (name, name))
        code.append("")
    registers = {name: c.globalnames[name].typ for name in c.all_registers}
    code.append("registers = {}")
    for name, typ in registers.iteritems():
        code.append("registers[%r] = %s" % (name, typ))
    return "\n".join(code)

@pytest.fixture(scope='function')
def riscvsharedstate(riscv_first_shared_state):
    return riscv_first_shared_state.copy()


def test_decode_and_execute_addi(riscvsharedstate):
    #assert "zeq_anythingzIEArchitecturez5zK" in riscvsharedstate.funcs
    graph = riscvsharedstate.funcs['zencdec_backwards']
    #graph.view()
    interp = z3backend.RiscvInterpreter(graph, [z3backend.ConstantSmallBitVector(r_uint(0xfe0f0f13), 64)], riscvsharedstate.copy())
    ast = interp.run()
    assert isinstance(ast, z3backend.UnionConstant)
    assert ast.variant_name == "zITYPE"
    assert str(ast.w_val) == "<StructConstant [4064, 30, 30, zRISCV_ADDI] ztuplez3z5bv12_z5bv5_z5bv5_z5enumz0zziop>"

    print("start executing", ast)
    graph = riscvsharedstate.funcs['zexecute_zITYPE']
    interp = z3backend.RiscvInterpreter(graph, [ast], riscvsharedstate.copy())
    res = interp.run()
    assert str(res) == "zRETIRE_SUCCESS"
    #assert str(interp.registers['zx30']).startswith("18446744073709551584 + init_zx30!"

    print("start executing", ast)
    graph = riscvsharedstate.funcs['zexecute_zITYPE']
    ast.w_val.vals_w[1] = z3backend.Z3Value(z3.FreshConst(z3.BitVecSort(5)))
    ast.w_val.vals_w[2] = z3backend.Z3Value(z3.FreshConst(z3.BitVecSort(5)))
    interp = z3backend.RiscvInterpreter(graph, [ast], riscvsharedstate.copy())
    res = interp.run()

    #import pdb;pdb.set_trace()

def test_prove_itype_cant_switch_mode(riscvsharedstate):
    graph = riscvsharedstate.funcs['zexecute_zITYPE']
    union_typ = graph.args[0].resolved_type
    struct_typ = union_typ.variants['zITYPE']
    z3_struct = riscvsharedstate.get_abstract_struct_const_of_type(struct_typ, '')
    z3_union_typ = riscvsharedstate.convert_type_to_z3_type(union_typ)
    arg = z3backend.UnionConstant('zITYPE', z3backend.Z3Value(z3_struct), union_typ, z3_union_typ)
    interp = z3backend.RiscvInterpreter(graph, [arg], riscvsharedstate.copy())
    registers_old = interp.registers.copy()
    interp.run()
    solver = z3.Solver()
    res = solver.check(z3.Not(registers_old['zcur_privilege'].toz3() == interp.registers['zcur_privilege'].toz3()))
    assert res == z3.unsat

def test_invalid_opcode(riscvsharedstate):
    graph = riscvsharedstate.funcs['zencdec_backwards']
    print("start executing", graph)
    interp = z3backend.RiscvInterpreter(graph, [z3backend.ConstantSmallBitVector(r_uint(0x65), 32)], riscvsharedstate.copy())
    res = interp.run()
    assert isinstance(res, z3backend.Z3Value)
    #assert str(res) == "?" # TODO: check for invalid opcode, after we use correct misa and mstatus values

def test_decode_all(riscvsharedstate):
    graph = riscvsharedstate.funcs['zencdec_backwards']
    print("start executing", graph)
    inst = z3.BitVec("inst", 32)
    interp = z3backend.RiscvInterpreter(graph, [z3backend.Z3Value(inst)], riscvsharedstate.copy())
    res = interp.run()

    assert isinstance(res, z3backend.Z3Value)

    res_sub = z3.substitute(res.toz3(), (inst, z3.BitVecVal(0xfe0f0f13, 32)))
    res_simple = z3.simplify(res_sub)
    assert str(res_simple) == "zITYPE(a(4064, 30, 30, zRISCV_ADDI))"

def test_decode_execute_itype(riscvsharedstate):# func_zstep
    graph = riscvsharedstate.funcs['zencdec_backwards']
    print("start executing", graph)
    interp = z3backend.RiscvInterpreter(graph, [z3backend.ConstantSmallBitVector(r_uint(0xfe0f0f13), 32)], riscvsharedstate.copy())
    instr_ast = interp.run()

    assert str(instr_ast.toz3()) == "zITYPE(a(4064, 30, 30, zRISCV_ADDI))" # 4064 in 12 bit bv = 111111100000 = -32

    graph = riscvsharedstate.funcs['zexecute_zITYPE']
    print("start executing", graph)
    interp = z3backend.RiscvInterpreter(graph, [instr_ast], riscvsharedstate.copy())
    interp.run()
    assert str(interp.registers["zx30"]).startswith("init_zx30!")
    assert str(interp.registers["zx30"]).endswith("+ 18446744073709551584") #  18446744073709551584L = -32 


def test_decode_execute_all_abstract(riscvsharedstate):
    """ run all execute_xxx funcs with abstract argument """

    graph = riscvsharedstate.funcs['zencdec_backwards']
    print("start executing", graph)
    interp = z3backend.RiscvInterpreter(graph, [z3backend.Z3Value(z3.BitVec("z3mergez3var", 32))], riscvsharedstate.copy())
    instr_ast = interp.run()

    assert isinstance(instr_ast, z3backend.Z3Value)

    for name, func in riscvsharedstate.funcs.iteritems():
        #if not "zexecute_zSHIFTIOP" == name: continue
        if not "zexecute_" in name: continue
        interp = z3backend.RiscvInterpreter(func, [instr_ast], riscvsharedstate.copy())
        res = interp.run()
        assert isinstance(res, z3backend.Enum) or isinstance(res, z3backend.Z3Value)

