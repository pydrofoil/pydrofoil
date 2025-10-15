import pytest
import os
import time
import z3
from pydrofoil import graphalgorithms
from pydrofoil import ir
from pydrofoil.z3backend import z3backend, z3btypes
from pydrofoil.z3backend import z3backend_executor, readangr, readvexingz3
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
        _, backedges = graphalgorithms.find_loopheaders_backedges(graph)
        riscvsharedstate.backedges[graph] = backedges
    for name, graphs in riscvsharedstate.mthds.iteritems():
        for mname, graph in graphs.iteritems():
            riscvsharedstate.mthds[name][mname] = graphalgorithms.compute_single_return_graph(graph)
            _, backedges = graphalgorithms.find_loopheaders_backedges(graph)
            riscvsharedstate.backedges[graph] = backedges
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

def set_default_registers(riscvsharedstate, w_regs):
    w_regs["misa"] = z3backend_executor.get_rv64_usermode_misa_w_value(riscvsharedstate)
    w_regs["mstatus"] = z3backend_executor.get_rv64_usermode_mstatus_w_value(riscvsharedstate)
    w_regs["cur_privilege"] = z3backend_executor.get_rv64_usermode_cur_privilege_w_value(riscvsharedstate)
    w_regs["satp"] = z3btypes.ConstantSmallBitVector(0, 64)
    w_regs["mie"] = z3backend_executor.get_rv64_mie_0_w_value(riscvsharedstate)
    w_regs["mip"] = z3backend_executor.get_rv64_mip_0_w_value(riscvsharedstate)
    w_regs["mtime"] = z3backend_executor.get_rv64_mtime_0_value(riscvsharedstate)
    w_regs["mtimecmp"] = z3backend_executor.get_rv64_mtimecmp_0_value(riscvsharedstate)
    w_regs["medeleg"] = z3backend_executor.get_rv64_medeleg_0_w_value(riscvsharedstate)
    # do we need mideleg?

def get_rv64_mem_base_size():
    return 0x80000000, 0x4000000

def build_reg_memory_acc_constraints(regs, reg_z3_mapping):
    constraints = []
    ram_base, ram_size = get_rv64_mem_base_size()
    for reg in regs:
        constraints.append(ram_base <= reg_z3_mapping[reg] )<= (ram_base + ram_size)
        constraints.append(reg_z3_mapping[reg] <= (ram_base + ram_size))
        constraints.append(reg_z3_mapping[reg] % 4 == 0)
    return constraints

def run_angr_opcode_assert_equal(riscvsharedstate, opcode, pcode=False):
    executions = readangr.run_angr_opcodes(opcodes=[opcode], pcode=pcode, verbosity=1)
    execution = executions[0]

    if pcode:
        readangr.rename_execution_registers_xn_pcode_rv64(execution)

    w_regs, init_reg_name_z3_mapping = readangr.create_wrapped_init_register_values_rv64(execution)
    init_mem = z3backend_executor.create_memory("memory", 8, 1)
    #init_mem = readangr.create_init_memory(execution) # angr does not fully support abstract memory
    code = readangr.get_code_from_execution(execution)

    set_default_registers(riscvsharedstate, w_regs)

    interp, _ = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, init_mem, 0)
    
    branch_size = readangr.get_branch_size_from_execution(execution)
    z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)

    registers_size = readangr.get_arch_from_execution(execution).registers_size
    z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
    angr_regs_smtlib = readangr.get_result_regs_from_execution(execution)

    z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

    unreach_error_consts = interp.sharedstate._unreachable_error_constants
    unreach_error_consts["memory"] = init_mem

    z3types = interp.sharedstate._build_type_dict()

    exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_z3_mapping, unreach_error_consts, z3types)

    solvertime = z3backend_executor.solve_assert_z3_unequality_exprs(exprs, constraints=[], failfast=False, verbosity=1)
    print "z3solver used %f s for solving" % solvertime

def run_vexingz3_opcode_assert_equal(riscvsharedstate, opcode, regs_mem_constraint=[]):
    start = time.time()
    executions = readvexingz3.run_vexingz3_opcodes(opcodes=[opcode], arch="rv64", verbosity=1)
    execution = executions[0]

    w_regs, init_reg_name_z3_mapping = readangr.create_wrapped_init_register_values_rv64(execution)
    init_mem = readvexingz3.create_init_memory(execution, 8, 1)


    set_default_registers(riscvsharedstate, w_regs)

    code = readangr.get_code_from_execution(execution)

    interp, _ = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, init_mem, 0)

    registers_size = readangr.get_arch_from_execution(execution).registers_size
    z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
    vexingz3_regs_smtlib = readangr.get_result_regs_from_execution(execution)

    z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

    unreach_error_consts = interp.sharedstate._unreachable_error_constants
    unreach_error_consts["memory"] = init_mem

    z3b_mem_smt = z3backend_executor.extract_mem_smtlib2(interp)
    vexingz3_mem_smtlib = readangr.get_result_mem_from_execution(execution)

    z3types = interp.sharedstate._build_type_dict()

    exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, vexingz3_regs_smtlib, init_reg_name_z3_mapping, unreach_error_consts, z3types)
    expr_mem = z3backend_executor.build_assertion_mem(z3b_mem_smt, vexingz3_mem_smtlib, init_reg_name_z3_mapping, unreach_error_consts, z3types)
    exprs["memory"] = expr_mem

    memory_constraints = build_reg_memory_acc_constraints(regs_mem_constraint,init_reg_name_z3_mapping)

    solvertime = z3backend_executor.solve_assert_z3_unequality_exprs(exprs, constraints=memory_constraints, failfast=False, verbosity=1)

    print "z3 solver took %f seconds for checking %d * 32 assertions" % (solvertime, len(executions))
    print "z3backend took %f seconds of %f" % (time.time() - start - solvertime, time.time() - start)

####################################

def test_decode_and_execute_addi_li(riscvsharedstate):

    code = [
        0xfe0f0f13, # addi x30, x30, -32
        0x7300613 # li x12, 115 ~ addi x12 x0 115
    ]

    last_interp, _ = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, {}, None, 0)
  
    assert "+" in str(last_interp.registers["zx30"])
    assert str(last_interp.registers["zx12"]) == "115"

def test_load_angr_executions_wrap_regs(riscvsharedstate):
    executions = readangr.load_executions("riscv.generated.executionsrv64")

    w_regs_0, _ = readangr.create_wrapped_init_register_values_rv64(executions[0])

    assert w_regs_0["x0"].toz3().size() == 64
    assert w_regs_0["pc"].toz3().size() == 64

    assert w_regs_0["x7"].__class__ == z3btypes.Z3Value
    assert w_regs_0["pc"].__class__ == z3btypes.ConstantSmallBitVector

    assert w_regs_0["pc"].value == 0

    w_regs_1, _ = readangr.create_wrapped_init_register_values_rv64(executions[1])

    assert w_regs_1["x0"].toz3().size() == 64
    assert w_regs_1["pc"].toz3().size() == 64

    assert w_regs_1["x7"].__class__ == z3btypes.Z3Value
    assert w_regs_1["pc"].__class__ == z3btypes.ConstantSmallBitVector

    assert w_regs_1["pc"].value == 0

def test_complete_pregenerated_executions(riscvsharedstate):
    executions = readangr.load_executions("riscv.generated.executionsrv64")

    for execution in executions:
        w_regs, init_reg_name_z3_mapping = readangr.create_wrapped_init_register_values_rv64(execution)
        init_mem = z3backend_executor.create_memory("memory", 8, 1)
        #init_mem = readangr.create_init_memory(execution) # angr does not fully support abstract memory

        code  = readangr.get_code_from_execution(execution)

        set_default_registers(riscvsharedstate, w_regs)

        interp, _ = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, init_mem, 0)
        
        branch_size = readangr.get_branch_size_from_execution(execution)
        z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
        
        registers_size = readangr.get_arch_from_execution(execution).registers_size
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
        angr_regs_smtlib = readangr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

        unreach_error_consts = interp.sharedstate._unreachable_error_constants
        unreach_error_consts["memory"] = init_mem

        z3types = interp.sharedstate._build_type_dict()

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_z3_mapping, unreach_error_consts, z3types)

        z3backend_executor.solve_assert_z3_unequality_exprs(exprs, [], False)

def test_gen_code_run_vexingz3_all_types(riscvsharedstate):
    
    start = time.time()
    executions, gentime = readvexingz3.gen_code_run_vexingz3(num_ops=2**7, arch="rv64", verbosity=0)

    solvertime = 0

    z3backend_times = []
    opcodes = []

    for execution in executions:
        w_regs, init_reg_name_z3_mapping = readangr.create_wrapped_init_register_values_rv64(execution)
        init_mem = readvexingz3.create_init_memory(execution, 8, 1)

        set_default_registers(riscvsharedstate, w_regs)

        code = readangr.get_code_from_execution(execution)
        opcodes.append(code)

        interp, z3backend_time = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, init_mem, 0)
        z3backend_times.append(z3backend_time)

        registers_size = readangr.get_arch_from_execution(execution).registers_size
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
        vexingz3_regs_smtlib = readangr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

        unreach_error_consts = interp.sharedstate._unreachable_error_constants
        unreach_error_consts["memory"] = init_mem

        z3b_mem_smt = z3backend_executor.extract_mem_smtlib2(interp)
        vexingz3_mem_smtlib = readangr.get_result_mem_from_execution(execution)

        z3types = interp.sharedstate._build_type_dict()

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, vexingz3_regs_smtlib, init_reg_name_z3_mapping, unreach_error_consts, z3types)
        expr_mem = z3backend_executor.build_assertion_mem(z3b_mem_smt, vexingz3_mem_smtlib, init_reg_name_z3_mapping, unreach_error_consts, z3types)
        exprs["memory"] = expr_mem

        solvertime += z3backend_executor.solve_assert_z3_unequality_exprs(exprs, constraints=[], failfast=False, verbosity=0)

    # must sync the write, as multiple processes may write
    #z3backend_executor._sync_dump(z3backend_executor.BENCHMARK_FILE, z3backend_times, opcodes)
    
    print "hypothesis & vexingz3 took %f seconds for generating & simulating %d instructions" % (gentime, len(executions))
    print "z3 solver took %f seconds for checking %d * 32 assertions" % (solvertime, len(executions))
    print "z3backend took %f seconds of %f" % (time.time() - start - solvertime - gentime, time.time() - start)

def test_gen_code_run_angr_vex_all_types(riscvsharedstate):
    start = time.time()
    executions, gentime = readangr.gen_code_run_angr_single(num_ops=2**7, pcode=False, verbosity=0)

    solvertime = 0

    for execution in executions:
        w_regs, init_reg_name_z3_mapping = readangr.create_wrapped_init_register_values_rv64(execution)
        init_mem = z3backend_executor.create_memory("memory", 8, 1)
        #init_mem = readangr.create_init_memory(execution) # angr does not fully support abstract memory

        set_default_registers(riscvsharedstate, w_regs)

        code = readangr.get_code_from_execution(execution)

        interp, _ = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, init_mem, 0)
        
        branch_size = readangr.get_branch_size_from_execution(execution)
        z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
        
        registers_size = readangr.get_arch_from_execution(execution).registers_size
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
        angr_regs_smtlib = readangr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

        unreach_error_consts = interp.sharedstate._unreachable_error_constants
        unreach_error_consts["memory"] = init_mem

        z3types = interp.sharedstate._build_type_dict()

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_z3_mapping, unreach_error_consts, z3types)

        solvertime += z3backend_executor.solve_assert_z3_unequality_exprs(exprs, constraints=[], failfast=False, verbosity=0)
    
    print "hypothesis & angr took %f seconds for generating & simulating %d instructions" % (gentime, len(executions))
    print "z3 solver took %f seconds for checking %d * 31 assertions" % (solvertime, len(executions))
    print "z3backend took approx. %f seconds of %f" % (time.time() - start - solvertime - gentime, time.time() - start)

def test_gen_code_run_angr_pypcode_all_types(riscvsharedstate):
    start = time.time()
    executions, gentime = readangr.gen_code_run_angr_single(num_ops=2**7, pcode=True, verbosity=0)

    solvertime = 0

    for execution in executions:
        readangr.rename_execution_registers_xn_pcode_rv64(execution) # pypcode use abi names e.g. 'zero' instead of 'x0'

        w_regs, init_reg_name_z3_mapping = readangr.create_wrapped_init_register_values_rv64(execution)
        init_mem = z3backend_executor.create_memory("memory", 8, 1)
        #init_mem = readangr.create_init_memory(execution) # angr does not fully support abstract memory

        set_default_registers(riscvsharedstate, w_regs)

        code = readangr.get_code_from_execution(execution)

        interp, _ = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, init_mem, 0)
        
        branch_size = readangr.get_branch_size_from_execution(execution)
        z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
        
        registers_size = readangr.get_arch_from_execution(execution).registers_size
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
        angr_regs_smtlib = readangr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

        unreach_error_consts = interp.sharedstate._unreachable_error_constants
        unreach_error_consts["memory"] = init_mem

        z3types = interp.sharedstate._build_type_dict()

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_z3_mapping, unreach_error_consts, z3types)

        solvertime += z3backend_executor.solve_assert_z3_unequality_exprs(exprs, constraints=[], failfast=False, verbosity=0)
    
    print "hypothesis & angr took %f seconds for generating & simulating %d instructions" % (gentime, len(executions))
    print "z3 solver took %f seconds for checking %d * 32 assertions" % (solvertime, len(executions))
    print "z3backend took approx. %f seconds of %f" % (time.time() - start - solvertime - gentime, time.time() - start)


def test_angr_clui_vs_lui_x0_7_angr_error(riscvsharedstate):
    opcode_lui_x0 = 0x7037 # LUI x0 7
    opcode_clui_x1 = 0x609d # clui x1 1
    opcode_clui_x0 = 0x601d # cLUI x0 7
    run_angr_opcode_assert_equal(riscvsharedstate, opcode_lui_x0)
    run_angr_opcode_assert_equal(riscvsharedstate, opcode_clui_x1)
    run_angr_opcode_assert_equal(riscvsharedstate, opcode_clui_x0)

def test_z3backend_clz_x5_x6(riscvsharedstate):
    opcode = 0x60029313

    registers = {}

    registers["misa"] = z3backend_executor.get_rv64_usermode_misa_w_value(riscvsharedstate)
    registers["mstatus"] = z3backend_executor.get_rv64_usermode_mstatus_w_value(riscvsharedstate)
    registers["satp"] = z3btypes.ConstantSmallBitVector(0, 64)
    registers["cur_privilege"] = z3backend_executor.get_rv64_usermode_cur_privilege_w_value(riscvsharedstate)
    registers["mie"] = z3backend_executor.get_rv64_mie_0_w_value(riscvsharedstate)
    registers["mip"] = z3backend_executor.get_rv64_mip_0_w_value(riscvsharedstate)
    registers["x5"] = z3btypes.ConstantSmallBitVector(3, 64)

    interp, _ = z3backend_executor.execute_machine_code_rv64([opcode], riscvsharedstate, True, registers, None, 1)
    
    assert int(str(z3.simplify(interp.registers["zx6"].toz3()))) == 62

###### memory related failures ########

def test_vexingz3_storew_x7_0_x7(riscvsharedstate):
    opcode = 0x0073a023
    run_vexingz3_opcode_assert_equal(riscvsharedstate, opcode, ["x7"])

##############################

### currently failing, because of a bug that is not here in pydrofoil / z3backend ###

def test_angr_pcode_srliw_x31_x5_31(riscvsharedstate):
    opcode = 0x1f2df9b
    run_angr_opcode_assert_equal(riscvsharedstate, opcode, pcode=False)
    run_angr_opcode_assert_equal(riscvsharedstate, opcode, pcode=True)

def test_angr_c_addi_x5_0_angr_error(riscvsharedstate):
    # rv64 isa manual unprivileged architecture chapter 27.5.2 Integer Register-Immediate Operations 
    # c_addi xn_0 is a hint, but angr crashes (standard, NOT costum)
    opcode = 0x028d
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_angr_c_srli64_x8_angr_error(riscvsharedstate):
    # costum hint: rv64 isa manual unprivileged architecture chapter 27.7 HINT instructions
    opcode = 0x8001
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_angr_c_srli64_x11(riscvsharedstate):
    # TODO: check if this is a hint
    opcode = 0x8181
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)