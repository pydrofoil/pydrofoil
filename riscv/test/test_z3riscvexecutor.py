import pytest
import os
import time
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

def run_angr_opcode_assert_equal(riscvsharedstate, opcode, pcode=False):
    executions = readpy3angr.run_angr_opcodes(opcodes=[opcode], pcode=pcode, verbosity=1)
    execution = executions[0]

    if pcode:
        readpy3angr.rename_execution_registers_xn_pcode_rv64(execution)

    w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)
    code = readpy3angr.get_code_from_execution(execution)


    set_default_registers(riscvsharedstate, w_regs)

    interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, {}, 0)
    
    branch_size = readpy3angr.get_branch_size_from_execution(execution)
    z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)

    registers_size = readpy3angr.get_arch_from_execution(execution).registers_size
    z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
    angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

    z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

    unreach_error_consts = interp.sharedstate._unreachable_error_constants
    unreach_error_consts["memory"] = init_mem

    z3types = interp.sharedstate._build_type_dict()

    exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_to_z3_mapping, unreach_error_consts, z3types)

    solvertime = z3backend_executor.solve_assert_z3_unequality_exprs(exprs, failfast=False, verbosity=1)
    print "z3solver used %f s for solving" % solvertime

####################################

def test_decode_and_execute_addi_li(riscvsharedstate):

    code = [
        0xfe0f0f13,
        0x7300613 # li x12, 115 ~ addi x12 x0 115
    ]

    last_interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, {}, {}, 0)
  

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

    for execution in executions:
        w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)
        code  = readpy3angr.get_code_from_execution(execution)

        set_default_registers(riscvsharedstate, w_regs)

        interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, {}, 0)
        
        branch_size = readpy3angr.get_branch_size_from_execution(execution)
        z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
        
        registers_size = readpy3angr.get_arch_from_execution(execution).registers_size
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
        angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

        unreach_error_consts = interp.sharedstate._unreachable_error_constants
        unreach_error_consts["memory"] = init_mem

        z3types = interp.sharedstate._build_type_dict()

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_to_z3_mapping, unreach_error_consts, z3types)

        z3backend_executor.solve_assert_z3_unequality_exprs(exprs, False)

def test_gen_code_run_angr_vex_all_types(riscvsharedstate):
    start = time.time()
    executions, gentime = readpy3angr.gen_code_run_angr_single(num_ops=2**7, pcode=False, verbosity=0)

    solvertime = 0

    for execution in executions:
        w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)

        set_default_registers(riscvsharedstate, w_regs)

        code = readpy3angr.get_code_from_execution(execution)


        interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, {}, 0)
        
        branch_size = readpy3angr.get_branch_size_from_execution(execution)
        z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
        
        registers_size = readpy3angr.get_arch_from_execution(execution).registers_size
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
        angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

        unreach_error_consts = interp.sharedstate._unreachable_error_constants
        unreach_error_consts["memory"] = init_mem

        z3types = interp.sharedstate._build_type_dict()

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_to_z3_mapping, unreach_error_consts, z3types)

        solvertime += z3backend_executor.solve_assert_z3_unequality_exprs(exprs, failfast=False, verbosity=0)
    
    print "hypothesis & angr took %f seconds for generating & simulating %d instructions" % (gentime, len(executions))
    print "z3 solver took %f seconds for checking %d * 32 assertions" % (solvertime, len(executions))
    print "z3backend took approx. %f seconds of %f" % (time.time() - start - solvertime - gentime, time.time() - start)

def test_gen_code_run_angr_pypcode_all_types(riscvsharedstate):
    start = time.time()
    executions, gentime = readpy3angr.gen_code_run_angr_single(num_ops=2**7, pcode=True, verbosity=0)

    solvertime = 0

    for execution in executions:
        readpy3angr.rename_execution_registers_xn_pcode_rv64(execution)
        w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)

        set_default_registers(riscvsharedstate, w_regs)

        code = readpy3angr.get_code_from_execution(execution)


        interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, {}, 0)
        
        branch_size = readpy3angr.get_branch_size_from_execution(execution)
        z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
        
        registers_size = readpy3angr.get_arch_from_execution(execution).registers_size
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
        angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

        reg_init_reg_name_mapping = readpy3angr.get_init_reg_names_from_execution(execution)

        unreach_error_consts = interp.sharedstate._unreachable_error_constants
        unreach_error_consts["memory"] = init_mem

        z3types = interp.sharedstate._build_type_dict()

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_to_z3_mapping, unreach_error_consts, z3types)

        solvertime += z3backend_executor.solve_assert_z3_unequality_exprs(exprs, failfast=False, verbosity=0)
    
    print "hypothesis & angr took %f seconds for generating & simulating %d instructions" % (gentime, len(executions))
    print "z3 solver took %f seconds for checking %d * 32 assertions" % (solvertime, len(executions))
    print "z3backend took approx. %f seconds of %f" % (time.time() - start - solvertime - gentime, time.time() - start)


def test_gen_code_run_angr_pypcode_bit_manipulation(riscvsharedstate):
    start = time.time()
    typs = ["RISCV_CLMULH", ] # "ZBA_RTYPE", "ZBA_RTYPEW", "ZBS_RTYPE", "ZBS_IOP", "ZBB_RTYPEW", "ZBB_RTYPE", "RISCV_CLMULR",  "RISCV_CLMUL"
    # not implemented in pypcode: sh3addu.w (zba?)   sbclr (zbs?)    ror(zbb?)     clmulr        clmulh
    #opcodes:                     0x21de6cbb         0x492298b3      0x60cfd2b3    0xb27a6b3     0xad337b3
    executions, gentime = readpy3angr.gen_code_run_angr_single(num_ops=2**0, pcode=True, verbosity=1, instr_types=typs)

    solvertime = 0

    for execution in executions:
        readpy3angr.rename_execution_registers_xn_pcode_rv64(execution)
        w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)


        set_default_registers(riscvsharedstate, w_regs)

        code = readpy3angr.get_code_from_execution(execution)

        interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, {}, 0)
        
        branch_size = readpy3angr.get_branch_size_from_execution(execution)
        z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
        
        registers_size = readpy3angr.get_arch_from_execution(execution).registers_size
        z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
        angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

        z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

        unreach_error_consts = interp.sharedstate._unreachable_error_constants
        unreach_error_consts["memory"] = init_mem

        z3types = interp.sharedstate._build_type_dict()

        exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_to_z3_mapping, unreach_error_consts, z3types)

        solvertime += z3backend_executor.solve_assert_z3_unequality_exprs(exprs, failfast=False, verbosity=1)
    
    print "hypothesis & angr took %f seconds for generating & simulating %d instructions" % (gentime, len(executions))
    print "z3 solver took %f seconds for checking %d * 32 assertions" % (solvertime, len(executions))
    print "z3backend took approx. %f seconds of %f" % (time.time() - start - solvertime - gentime, time.time() - start)

def test_srli_x1_x2_0_unsolvable_pypcode(riscvsharedstate):
    opcode = 0x15093
    run_angr_opcode_assert_equal(riscvsharedstate, opcode, pcode=True)

def test_run_angr_slt_unsolvable(riscvsharedstate):
    opcode = 0x003120b3# 0x00002033 #0x0010a0b3 # slt x1 x1 x1

    executions =  readpy3angr.run_angr_opcodes(opcodes=[opcode], pcode=False)
    execution = executions[0]

    w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)
    code = readpy3angr.get_code_from_execution(execution)

    set_default_registers(riscvsharedstate, w_regs)

    interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, {}, 0)
    
    branch_size = readpy3angr.get_branch_size_from_execution(execution)
    z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)

    registers_size = readpy3angr.get_arch_from_execution(execution).registers_size
    z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
    angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

    z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

    reg_init_reg_name_mapping = readpy3angr.get_init_reg_names_from_execution(execution)

    unreach_error_consts = interp.sharedstate._unreachable_error_constants
    unreach_error_consts["memory"] = init_mem

    z3types = interp.sharedstate._build_type_dict()

    exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_to_z3_mapping, unreach_error_consts, z3types)

    z3backend_executor.solve_assert_z3_unequality_exprs(exprs, failfast=False, verbosity=1)


def test_run_angr_reg50_error(riscvsharedstate):
    opcode = 0xa2944c13 # xori x24 x8 -1495
    opcode = 0xff44c13
    executions =  readpy3angr.run_angr_opcodes(opcodes=[opcode], verbosity=1, pcode=False)
    execution = executions[0]

    w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)
    code = readpy3angr.get_code_from_execution(execution)

    set_default_registers(riscvsharedstate, w_regs)

    interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, {}, 0)
    
    branch_size = readpy3angr.get_branch_size_from_execution(execution)
    z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
    
    registers_size = readpy3angr.get_arch_from_execution(execution).registers_size
    z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
    angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

    z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

    unreach_error_consts = interp.sharedstate._unreachable_error_constants
    unreach_error_consts["memory"] = init_mem

    z3types = interp.sharedstate._build_type_dict()

    exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_to_z3_mapping, unreach_error_consts, z3types)

    z3backend_executor.solve_assert_z3_unequality_exprs(exprs, failfast=False, verbosity=1)


def test_run_angr_reference_error(riscvsharedstate):
    opcode = 0xef206093 # xori x1 x0 -270

    executions = readpy3angr.run_angr_opcodes(opcodes=[opcode], pcode=False)
    execution = executions[0]

    w_regs, init_reg_name_to_z3_mapping = readpy3angr.create_wrapped_init_register_values_rv64(execution)
    code = readpy3angr.get_code_from_execution(execution)

    set_default_registers(riscvsharedstate, w_regs)

    interp, init_mem = z3backend_executor.execute_machine_code_rv64(code, riscvsharedstate, True, w_regs, {}, 0)
    
    branch_size = readpy3angr.get_branch_size_from_execution(execution)
    z3backend_executor._rv64_patch_pc_for_angr_jump(interp, branch_size, code)
    
    registers_size = readpy3angr.get_arch_from_execution(execution).registers_size
    z3b_regs_smtlib = z3backend_executor.extract_regs_smtlib2(interp, registers_size)
    angr_regs_smtlib = readpy3angr.get_result_regs_from_execution(execution)

    z3b_regs_smtlib = z3backend_executor.filter_unpatch_rv64_registers(z3b_regs_smtlib)

    unreach_error_consts = interp.sharedstate._unreachable_error_constants
    unreach_error_consts["memory"] = init_mem

    z3types = interp.sharedstate._build_type_dict()

    exprs = z3backend_executor.build_assertions_regs(z3b_regs_smtlib, angr_regs_smtlib, init_reg_name_to_z3_mapping, unreach_error_consts, z3types)

    z3backend_executor.solve_assert_z3_unequality_exprs(exprs, failfast=False, verbosity=1)

def test_run_angr_missing_pc_reg(riscvsharedstate):
    opcode = 0x417 # AUIPC x8 0 ~ x8 = pc + (0 << 12)
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_run_angr_clui_vs_lui_x0_7_angr_error(riscvsharedstate):
    opcode_lui_x0 = 0x7037 # LUI x0 7
    opcode_clui_x1 = 0x609d # clui x1 1
    opcode_clui_x0 = 0x601d # cLUI x0 7
    run_angr_opcode_assert_equal(riscvsharedstate, opcode_lui_x0)
    run_angr_opcode_assert_equal(riscvsharedstate, opcode_clui_x1)
    run_angr_opcode_assert_equal(riscvsharedstate, opcode_clui_x0)

def test_z3backend_clz_x5_x6(riscvsharedstate):
    opcode = 0x60029313

    misa = z3backend_executor.get_rv64_usermode_misa_w_value(riscvsharedstate)
    mstatus = z3backend_executor.get_rv64_usermode_mstatus_w_value(riscvsharedstate)
    satp = z3btypes.ConstantSmallBitVector(0, 64)
    cur_privilege = z3backend_executor.get_rv64_usermode_cur_privilege_w_value(riscvsharedstate)
    mie = z3backend_executor.get_rv64_mie_0_w_value(riscvsharedstate)
    mip = z3backend_executor.get_rv64_mip_0_w_value(riscvsharedstate)

    registers = {}

    registers["misa"] = misa
    registers["mstatus"] = mstatus
    registers["satp"] = satp
    registers["cur_privilege"] = cur_privilege
    registers["mie"] = mie
    registers["mip"] = mip

    interp, init_mem = z3backend_executor.execute_machine_code_rv64([opcode], riscvsharedstate, True, registers, {}, 1)


"""def test_load_x17_m120_x17_failed(riscvsharedstate):
    # angr cannot load abstract addrs
    opcode = 0xf888a883
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)"""

### regression tests, TODO: move into separate file
### keep these tests, to not repeat the same mistakes again

def test_rtype_mul(riscvsharedstate):
    opcode = 0x027383b3 # mul x7, x7, x7
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_sra_generic_bv_error(riscvsharedstate):
    opcode = 0x400050b3 # sra x0, x0, x1
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_srai_x1_x1_0_failed(riscvsharedstate):
    opcode = 0x4000d093
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_srli_x1_x2_0_unsolvable(riscvsharedstate):
    opcode = 0x15093
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_srai_x2_x1_1_failed(riscvsharedstate):
    opcode = 0x40115093
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_srli_x16_x12_31_failed(riscvsharedstate):
    opcode = 0x1f65813
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_slti_x18_x20_m1908_failed(riscvsharedstate):
    opcode = 0x88ca2913
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_srli_x2_x18_36_failed(riscvsharedstate):
    opcode = 0x2495113
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_generic_bv_shiftr_o_i_error(riscvsharedstate):
    opcode = 0x418d53b3
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_srli_x8_x11_13_failed(riscvsharedstate):
    opcode = 0x49395037
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_sll_x22_x14_x6_failed(riscvsharedstate):
    opcode = 0x671b33
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_run_sraw_rshift_error(riscvsharedstate):
    opcode = 0x403cdbbb
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_sllw_x15_x18_x1_failed(riscvsharedstate):
    opcode = 0x1917bb
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_sra_x7_x11_x27_failed(riscvsharedstate):
    opcode = 0x41b5d3b3
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_srli_x22_x13_45_failed(riscvsharedstate):
    opcode = 0x2d6db13
    run_angr_opcode_assert_equal (riscvsharedstate, opcode)

def test_sllw_x27_x21_x4_failed(riscvsharedstate):
    opcode = 0x4a9dbb
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_addiw_x6_x19_2009_angr_weird_formula(riscvsharedstate):
    opcode = 0x7d99831b
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_addiw_x10_x20_x9_unsolvable(riscvsharedstate):
    opcode = 0xaa24b3
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_c_addi_x9_m3_failed(riscvsharedstate):
    opcode = 0x14f5
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_c_addi_x26_m22_failed(riscvsharedstate):
    opcode = 0x1d29
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_run_z3backend_illegal_c_lui(riscvsharedstate):
    opcode = 0x7075 # cLUI HINT
    graph_decode_compressed = riscvsharedstate.funcs['zencdec_compressed_backwards']
    interp = z3backend.RiscvInterpreter(graph_decode_compressed, [z3btypes.ConstantSmallBitVector(opcode, 32)],
                                         riscvsharedstate.copy())
    
    interp.registers["zmisa"] = z3backend_executor.get_rv64_usermode_misa_w_value(riscvsharedstate)
    interp.registers["zmstatus"] = z3backend_executor.get_rv64_usermode_mstatus_w_value(riscvsharedstate)
    interp.registers["zsatp"] = z3btypes.ConstantSmallBitVector(0, 64)

    ast = interp.run()
    assert "HINT" in str(ast)

def test_btype_generic_bv_simplify_occurence(riscvsharedstate):
    """ problem in comparison logic.
    angr returns valeus of false branch after any branch; thuspc is 4 """
    opcode = 0x649eeb63 # BLTU x29 x9 1622
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_jal_x1_8_failed(riscvsharedstate):
    opcode = 0x008000ef
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_c_addi_x5_0_angr_error(riscvsharedstate):
    # rv64 isa manual unprivileged architecture chapter 27.5.2 Integer Register-Immediate Operations 
    # c_addi xn_0 is a hint, but angr crashes (standard, NOT costum)
    opcode = 0x028d
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_c_srli64_x8_angr_error(riscvsharedstate):
    # costum hint: rv64 isa manual unprivileged architecture chapter 27.7 HINT instructions
    opcode = 0x8001
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_c_srli64_x11(riscvsharedstate):
    opcode = 0x8181
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_c_sltu_x12_x0_x0(riscvsharedstate):
    opcode = 0x3633
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)

def test_bltu_x29_x9_1622(riscvsharedstate):
    """ problem in comparison logic.
        angr returns values of false branch after any branch; thus pc is 4 """
    opcode = 0x649eeb63
    run_angr_opcode_assert_equal(riscvsharedstate, opcode)
