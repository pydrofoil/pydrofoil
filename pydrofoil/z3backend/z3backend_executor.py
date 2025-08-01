import z3
from pydrofoil.z3backend.z3btypes import ConstantSmallBitVector, UnionConstant

## registers used for comparison between angr and z3backend

# rv64: x0 is not allowed (hardwired 0?)
RV64REGISTERS = {"x1","x2","x3","x4","x5","x6","x7","x8","x9","x10","x11","x12","x13","x14","x15",
                 "x16","x17","x18","x19","x20","x21","x22","x23","x24","x25","x26","x27","x28","x29","x30","x31"}
ARM9_4REGISTERS = {}


def patch_name(name):
    """ append a 'z' to the name """
    return "z" + name

def prepare_interpreter(interp, registers_w, memory_w):
    """ set registers and memory """
    for regname, w_val in registers_w.iteritems():
        pydrofoil_regname = patch_name(regname)
        interp.registers[pydrofoil_regname] = w_val
    mem = interp.memory
    for addr, val in memory_w.iteritems():
        mem = z3.Store(mem, addr, val)
    interp.memory = mem

def execute_machine_code(code, code_bits, interp_class, shared_State, decode_graph, execute_graph, ismthd, init_regs_w, init_mem_w):
    decoder = interp_class(decode_graph, [ConstantSmallBitVector(code[0], code_bits)], shared_State.copy()) #  must init correctly
    ast = decoder.run()
    ### executor must only be used via _method_call or _func_call ###
    executor = interp_class(decode_graph, [ast], shared_State.copy()) # must init with 'normal graph'
    prepare_interpreter(executor, init_regs_w, init_mem_w)
    ### actual decode-execute  loop ###
    for instr in code:
        print "###  decoding: %s " % str(hex(instr))
        decoder = interp_class(decode_graph, [ConstantSmallBitVector(instr, code_bits)], shared_State.copy())
        ast = decoder.run()

        executor._reset_env()
        print "###  executing: %s " % str(ast)
        if ismthd:
            if isinstance(ast, UnionConstant):
                _ = executor._concrete_method_call(execute_graph, [ast])
            else:
                _ = executor._abstract_method_call(execute_graph, [ast], execute_graph["___default___"].args[0].resolved_type)
        else:
            _, call_mem, call_regs = executor._func_call(execute_graph, [ast])
            executor.memory = call_mem
            executor.registers = call_regs

    # return executing interpreter to access its registers and memory
    return executor

def extract_regs_smtlib2(interp):
    """ returns mapping register_name: smtlib2_expression_for_register """
    smt_regs = {}
    for regname, value in interp.registers.iteritems():
        smt_regs[regname] = value.toz3().sexpr()
    return smt_regs

def extract_mem_smtlib2(interp):
    """ returns mapping addr: smtlib2_expression_for_memory[addr] """
    smt_mem = {}
    # TODO
    assert 0, "implement memory"
    return smt_mem

def filter_unpatch_rv64_registers(pydrofoil_smt_regs, other_smt_regs):
    f_pydrofoil_regs, f_other_regs = {}, {} 
    for reg in RV64REGISTERS:
        f_pydrofoil_regs[reg] = pydrofoil_smt_regs[patch_name(reg)]
        #f_other_regs[reg] = other_smt_regs[reg]
    return f_pydrofoil_regs, other_smt_regs

def build_assertions_regs(pydrofoil_smt_regs, other_smt_regs, reg_to_init_reg_name, init_reg_name_to_z3):
    """ returns z3 expressions for register inequality e.g. x12_smt_regs0 != x12_smt_regs1
        those can then be passed into solver. unsat meaning equality """
    #assert set(smt_regs0.keys()) == set(smt_regs1.keys()), "can only compare within the same ISA"
    exprs = {}
    for regname in pydrofoil_smt_regs:
        #### smtlib example: (assert(distinct init_zx1 lr_4_64)) ####
        smtlib_expr = "(assert(distinct %s %s))" % (pydrofoil_smt_regs[regname], other_smt_regs[regname])
        exprs[regname] = z3.parse_smt2_string(smtlib_expr, decls=init_reg_name_to_z3)
    return exprs

def build_assertions_mem(smt_mem0, smt_mem1, init_mem_to_z3var):
    assert set(smt_mem0.keys()) == set(smt_mem1.keys()), "can only compare within the same ISA"
    exprs = {}
    #TODO
    assert 0, "implement memory"
    return exprs


def solve_assert_z3_unequality_exprs(exprs, failfast=True, verbose=True):
    """ gets dict of exprs e.g. {'x1': x1_a != x1_b, ...} and checks for unsat.
        unsat meaning x1_a and x1_b are equal """
    ok = True
    if verbose: 
        print "============== checking registers/memory =============="
    for name, value in exprs.iteritems():
        solver = z3.Solver()
        res = solver.check(value)
        if failfast:
            assert res == z3.unsat, "assertion %s:%s failed" % (name, str(value))
        elif res != z3.unsat:
            print "failed: %s:%s == z3.unsat" % (name, str(value))
            ok = False
        elif verbose:
            print "ok: %s:%s == z3.unsat" % (name, str(value))
    if ok and verbose: 
        print "==============    registers/memory ok    =============="
    print ""
    assert ok
