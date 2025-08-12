import pytest
import os
import z3
from pydrofoil import graphalgorithms
from pydrofoil import ir
from pydrofoil.z3backend import z3backend, z3btypes
from pydrofoil.z3backend import z3backend_executor, readpy3angr
from rpython.rlib.rarithmetic import r_uint 


RISCV_INSTRUCTION_SIZE = 32

##### copied from test_z3riscv #####

@pytest.fixture(scope='session')
def riscv_first_shared_state():
    from riscv import targetriscv
    pf = os.path.join(os.path.dirname(os.path.abspath(targetriscv.__file__)), "generated", "riscvgraphs_functions.py")
    pm = os.path.join(os.path.dirname(os.path.abspath(targetriscv.__file__)), "generated", "riscvgraphs_methods.py")
    if not os.path.exists(pf) or not os.path.exists(pm): 
        print "generating graphs"
        c = targetriscv.make_codegen()
        s = dump_graphs_and_registers(c)
        with open(pf, "w") as f:
            f.write(s)
        s = dump_methods(c)
        with open(pm, "w") as f:
            f.write(s)
    import time
    t1 = time.time()
    from riscv.generated import riscvgraphs_functions, riscvgraphs_methods
    riscvsharedstate = z3backend.SharedState(
        {name: func() for name, func in riscvgraphs_functions.funcs.iteritems()},
        riscvgraphs_functions.registers,
        {name: {mname: mthd() for mname, mthd in mthds.iteritems()} for name, mthds in riscvgraphs_methods.mthds.iteritems()},
    )
    ### We assume that every graph only has one return; thus we must compute every singe return graph here ### 
    for name, graph in riscvsharedstate.funcs.iteritems():
        riscvsharedstate.funcs[name] = graphalgorithms.compute_single_return_graph(graph)
    for name, graphs in riscvsharedstate.mthds.iteritems():
        for mname, graph in graphs.iteritems():
            riscvsharedstate.mthds[name][mname] = graphalgorithms.compute_single_return_graph(graph)
    t2 = time.time()
    print "loaded in %ss" % round(t2 - t1, 2)
    return riscvsharedstate

def dump_methods(c):
    code = ["from pydrofoil.ir import *",
            "from pydrofoil.types import *",
            "mthds = {}"]
    for name, graphs in c.method_graphs_by_name.iteritems():
        code.append("%s_methods = {}" % name)
        for m_name, graph in graphs.iteritems():
            if m_name == None:
                m_name = "___default___" # TODO: is this naming ok?
            code.append("def %s():" % m_name)
            for line in ir.print_graph_construction(graph):
                code.append("    " + line)
            code.append("    return graph")
            code.append("%s_methods[%r] = %s" % (name, m_name, m_name))
        code.append("mthds[%r] = %s_methods" % (name, name))
        code.append("")
    return "\n".join(code)


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

####################################

def test_decode_and_execute_addi_li(riscvsharedstate):
    #assert "zeq_anythingzIEArchitecturez5zK" in riscvsharedstate.funcs
    graph_decode = riscvsharedstate.funcs['zencdec_backwards']
    graph_execute = riscvsharedstate.funcs['zexecute_zITYPE']
    code = [
        0xfe0f0f13,
        0x7300613 # li x12, 115 ~ addi x12 x0 115
    ]

    last_interp = z3backend_executor.execute_machine_code(code, 32, z3backend.RiscvInterpreter, riscvsharedstate,
                                                           graph_decode, graph_execute, False, {}, {})
  

    assert "+" in str(last_interp.registers["zx30"])
    assert str(last_interp.registers["zx12"]) == "115"

def test_load_angr_executions_wrap_regs(riscvsharedstate):
    executions = readpy3angr.load_executions("riscv.generated.executionsrv64")

    #assert len(executions) == 7

    w_regs_0, init_name_to_z3_mapping_0 = readpy3angr.create_wrapped_init_register_values_rv64(executions[0])

    assert w_regs_0["x0"].toz3().size() == 64
    assert w_regs_0["pc"].toz3().size() == 64

    assert w_regs_0["x7"].__class__ == z3btypes.Z3Value
    assert w_regs_0["pc"].__class__ == z3btypes.ConstantSmallBitVector

    assert w_regs_0["pc"].value == 0

    w_regs_1, init_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(executions[1])

    assert w_regs_1["x0"].toz3().size() == 64
    assert w_regs_1["pc"].toz3().size() == 64

    assert w_regs_1["x7"].__class__ == z3btypes.Z3Value
    assert w_regs_1["pc"].__class__ == z3btypes.ConstantSmallBitVector

    assert w_regs_1["pc"].value == 0

def test_complete(riscvsharedstate):
    executions = readpy3angr.load_executions("riscv.generated.executionsrv64")

    #riscvsharedstate.funcs["zstep"].view()
    #riscvsharedstate.mthds["zexecute"].view()

    graph_decode = riscvsharedstate.funcs['zencdec_backwards']
    #graph_execute = riscvsharedstate.funcs["zexecute_zITYPE"]
    graph_execute = riscvsharedstate.mthds["zexecute"]
    mthd = True # True

    for execution in executions:
        w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)
        code  = readpy3angr.get_code_from_execution(execution)

        interp = z3backend_executor.execute_machine_code(code, RISCV_INSTRUCTION_SIZE, z3backend.RiscvInterpreter,
                                                          riscvsharedstate, graph_decode, graph_execute, mthd, w_regs, {})
        
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp)
        angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib, angr_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib, angr_regs_smtlib)

        reg_init_name_mapping = readpy3angr.get_init_reg_names_from_execution(execution)

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, reg_init_name_mapping,  init_reg_name_to_z3_mapping)

        z3backend_executor.solve_assert_z3_unequality_exprs(exprs, False)

def test_gen_code_run_angr_and_compare(riscvsharedstate):
    executions = readpy3angr.gen_code_run_angr(num_ops=2**7)
    # failed:         0xd4158413, 0xf48f3413, 0x9acb413, 0x98d68413, 0x7e6e413, 0x5ab10413, 0x40987413
    # reg_50:         0xa2944c13, 0x6e942113, 0x68847593, 0x843293, 0xbab42a93
    # ReferenceError: 0x13007379, 0xef206093, 0x0xfffa8013

    graph_decode = riscvsharedstate.funcs['zencdec_backwards']
    #graph_execute = riscvsharedstate.funcs["zexecute_zITYPE"]
    graph_execute = riscvsharedstate.mthds["zexecute"]

    mthd = True # True

    for execution in executions:
        w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)
        code = readpy3angr.get_code_from_execution(execution)

        interp = z3backend_executor.execute_machine_code(code, RISCV_INSTRUCTION_SIZE, z3backend.RiscvInterpreter,
                                                          riscvsharedstate, graph_decode, graph_execute, mthd, w_regs, {})
        
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp)
        angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib, angr_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib, angr_regs_smtlib)

        reg_init_reg_name_mapping = readpy3angr.get_init_reg_names_from_execution(execution)

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, reg_init_reg_name_mapping,  init_reg_name_to_z3_mapping)

        z3backend_executor.solve_assert_z3_unequality_exprs(exprs, failfast=False, verbose=True)
