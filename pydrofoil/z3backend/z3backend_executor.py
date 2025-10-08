import z3
import time
from pydrofoil import types
from pydrofoil.types import *
from pydrofoil.z3backend.z3btypes import ConstantSmallBitVector, UnionConstant, StructConstant, Z3Value
from pydrofoil.z3backend import z3btypes
from pydrofoil.z3backend.z3backend import RiscvInterpreter

## registers used for comparison between angr and z3backend

# rv64: x0 is not allowed (hardwired 0?)
RV64REGISTERS = {"x1","x2","x3","x4","x5","x6","x7","x8","x9","x10","x11","x12","x13","x14","x15",
                 "x16","x17","x18","x19","x20","x21","x22","x23","x24","x25","x26","x27","x28","x29",
                 "x30","x31", "pc"}
ARM9_4REGISTERS = {}

RISCV_INSTRUCTION_SIZE = 32


def patch_name(name):
    """ append a 'z' to the name """
    if name == "pc": return "zPC" # for some reason pc is uppercase in sail
    if name == "nextpc": return "znextPC"
    if name == "have_exception": return name
    return "z" + name

def unpatch_name(name):
    """ remove a 'z' from the name """
    if name == "zPC": return "pc" # for some reason pc is uppercase in sail
    if name == "znextpc": return "nextPC"
    assert name[0] == "z"
    return name[1:]

def prepare_interpreter(interp, registers_w, memory_w):
    """ set registers and memory """
    for regname, w_val in registers_w.iteritems():
        pydrofoil_regname = patch_name(regname)
        interp.registers[pydrofoil_regname] = w_val
    init_mem = interp._init_mem()
    mem = interp.memory
    for addr, val in memory_w.iteritems():
        mem = z3.Store(mem, addr, val)
    interp.memory = mem
    return init_mem

#######################################################
# rv64 init register values
# TODO: move into a seperate file

def get_rv64_usermode_misa_w_value(riscvsharedstate):
    misa = types.Struct('zMisa', ('zbits',), (types.SmallFixedBitVector(64),))
    misa_z3type = riscvsharedstate.get_z3_struct_type(misa)
    value = 0b1000000000000000000000000000000000000000001101000001000100101111 # 0x800000000034112F
    # xlen  0b10 = 2 => 64 bit
    # reserved? 000000000000000000000000000000000000
    # extensions                                    00001101000001000100101111
    return StructConstant([ConstantSmallBitVector(value, 64)], misa, misa_z3type)

def get_rv64_usermode_mstatus_w_value(riscvsharedstate):
    mstatus = types.Struct('zMstatus', ('zbits',), (types.SmallFixedBitVector(64),))
    mstatus_z3type = riscvsharedstate.get_z3_struct_type(mstatus)
    value = 0x0000000A00000000
    return StructConstant([ConstantSmallBitVector(value, 64)], mstatus, mstatus_z3type)

def get_rv64_usermode_cur_privilege_w_value(riscvsharedstate):
    riscvsharedstate.register_enum('zPrivilege', ('zUser', 'zSupervisor', 'zMachine'))
    return riscvsharedstate.get_w_enum("zPrivilege", "zUser")

def get_rv64_medeleg_0_w_value(riscvsharedstate):
    medeleg = types.Struct('zMedeleg', ('zbits',), (SmallFixedBitVector(64),))
    medeleg_z3type = riscvsharedstate.get_z3_struct_type(medeleg)
    return StructConstant([ConstantSmallBitVector(0x0, 64)], medeleg, medeleg_z3type)

def get_rv64_mideleg_0_w_value(riscvsharedstate):
    minterupts = Struct('zMinterrupts', ('zbits',), (SmallFixedBitVector(64),)) # struct for mideleg
    minterupts_z3type = riscvsharedstate.get_z3_struct_type(minterupts)
    return StructConstant([ConstantSmallBitVector(0x0, 64)], minterupts, minterupts_z3type)

def get_rv64_mie_0_w_value(riscvsharedstate):
    mie = Struct('zMinterrupts', ('zbits',), (SmallFixedBitVector(64),))
    mie_z3type = riscvsharedstate.get_z3_struct_type(mie)
    return StructConstant([ConstantSmallBitVector(0x0, 64)], mie, mie_z3type)

def get_rv64_mip_0_w_value(riscvsharedstate):
    mip = Struct('zMinterrupts', ('zbits',), (SmallFixedBitVector(64),))
    mip_z3type = riscvsharedstate.get_z3_struct_type(mip)
    return StructConstant([ConstantSmallBitVector(0x0, 64)], mip, mip_z3type)

def get_rv64_mtime_0_value(riscvsharedstate):
    return ConstantSmallBitVector(0x0, 64)

def get_rv64_mtimecmp_0_value(riscvsharedstate):
    return ConstantSmallBitVector(0x0, 64)

#######################################################

class DummyGraph(object):
    def __init__(self):
        self.has_loop = False
        self.args = []

def _rv64_ends_bb(code):
    """ check wheter an rv64 instruction is a jump/branch """
    ends = False
    ends |= ((code & 0b1100011) == 0b1100011) & ((code &0b111000000000000) != 0b010) # btype
    ends |= (code & 0b1101111) == 0b1101111 # jal
    ends |= (code & 0b1100111) == 0b1100111 # jalr
    if ends: print "%s seems to end the bb" % str(code)
    return ends

def _rv64_patch_pc_for_angr_jump(interp, branch_size, code):
    # if a branch/jump was executed, bb ended and we dont need to do anything
    for c in code:
        if _rv64_ends_bb(c): return
    # otherwise angr executes a jump that is not a part of the executed code to end the bb
    # as the condition of the jump is always false, the pc is just incremented by the jump isntructions size
    if isinstance(interp.registers["zPC"], z3btypes.ConstantSmallBitVector):
        pc_val = interp.registers["zPC"].value
        interp.registers["zPC"] = z3btypes.ConstantSmallBitVector(pc_val + branch_size, 64)
    else:
        pc_val = interp.registers["zPC"].toz3()
        interp.registers["zPC"] = z3btypes.Z3Value(pc_val + z3.BitVecVal(branch_size, pc_val.sort().size()))

def execute_machine_code_rv64(code, rv64sharedstate, ismthd, init_regs_w, init_mem_w, verbosity=0):
    ### executor must only be used via _method_call or _func_call ###

    decode_graph = rv64sharedstate.funcs['zencdec_backwards']
    decode_compressed_graph = rv64sharedstate.funcs['zencdec_compressed_backwards']
    execute_graph = rv64sharedstate.mthds["zexecute"]
    tick_pc_graph = rv64sharedstate.funcs["ztick_pc"]
    
    executor = RiscvInterpreter(DummyGraph(), [], rv64sharedstate.copy(), {}) # init with dummy graph => do NOT call run() on this interpreter
    init_mem = prepare_interpreter(executor, init_regs_w, init_mem_w)
    # TODO: decoder and executor MUST use the same z3 array as init memory, and decoder mem must be passed on to executor and so on
    #  
    executor.set_verbosity(verbosity)
    ### actual decode-execute loop ###
    for instr in code:
        if instr & 0b11 == 0b11:
            print "###  decoding: %s " % str(hex(instr))
            decoder = RiscvInterpreter(decode_graph, [ConstantSmallBitVector(instr, RISCV_INSTRUCTION_SIZE)], rv64sharedstate.copy())
            opcode_size = 0x4 
        else:
            print "###  decoding compressed: %s " % str(hex(instr))
            decoder = RiscvInterpreter(decode_compressed_graph, [ConstantSmallBitVector(instr, RISCV_INSTRUCTION_SIZE)], rv64sharedstate.copy())
            opcode_size = 0x2

        decoder.set_verbosity(verbosity)
        prepare_interpreter(decoder, init_regs_w, init_mem_w)
        ast = decoder.run()

        if "ILLEGAL" in str(ast):
            assert 0, "Illegal Instruction %s" % str(instr)

        if not isinstance(ast, UnionConstant):
            import pdb; pdb.set_trace()

        # increment nextPC by opcode size
        if isinstance(executor.registers["zPC"], ConstantSmallBitVector):
            pc_val = executor.registers["zPC"].value
            executor.registers["znextPC"] = ConstantSmallBitVector(pc_val + opcode_size, 64)
        else:
            pc_val = executor.registers["zPC"].toz3()
            executor.registers["znextPC"] = Z3Value(pc_val + z3.BitVecVal(opcode_size, pc_val.sort().size()))

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

        _, call_mem, call_regs = executor._func_call(tick_pc_graph, [z3btypes.UnitConstant(rv64sharedstate._z3_unit)])
        executor.memory = call_mem
        executor.registers = call_regs

    # return executing interpreter to access its registers and memory
    return executor, init_mem

def extract_regs_smtlib2(interp, registers_size):
    """ returns mapping register_name: smtlib2_expression_for_register """
    smt_regs = {}
    for regname, value in interp.registers.iteritems():
        if isinstance(value, z3btypes.ConstantGenericBitVector):
            size = registers_size[unpatch_name(regname)] * 8
            smt_regs[regname] = value.toz3bv(size).sexpr()
        elif isinstance(value, z3btypes.Z3GenericBitVector):
            smt_regs[regname] = value.value.sexpr()
        else:
            smt_regs[regname] = value.toz3().sexpr()
    # handle sail registers manually
    smt_regs["have_exception"] = interp.registers["have_exception"].toz3().sexpr()
    # TODO: htif reg?
    return smt_regs

def extract_mem_smtlib2(interp):
    """ returns mapping addr: smtlib2_expression_for_memory[addr] """
    smt_mem = {}
    # TODO
    assert 0, "implement memory"
    return smt_mem

def filter_unpatch_rv64_registers(pydrofoil_smt_regs):
    f_pydrofoil_regs = {}
    for reg in RV64REGISTERS:
        f_pydrofoil_regs[reg] = pydrofoil_smt_regs[patch_name(reg)]
    return f_pydrofoil_regs

def build_assertions_regs(pydrofoil_smt_regs, other_smt_regs, init_reg_name_to_z3, other_z3_decls, z3types):
    """ returns z3 expressions for register inequality e.g. x12_smt_regs0 != x12_smt_regs1
        those can then be passed into solver. unsat meaning equality """
    #assert set(smt_regs0.keys()) == set(smt_regs1.keys()), "can only compare within the same ISA"
    exprs = {}
    regs_and_other_decls = {}
    regs_and_other_decls.update(init_reg_name_to_z3)
    regs_and_other_decls.update(other_z3_decls) # containes e.g. error_in_typecast_... or unreachable_const_of_....
    for regname in pydrofoil_smt_regs:
        #### smtlib example: (assert(distinct init_zx1 lr_4_64)) ####
        smtlib_expr = "(assert(distinct %s %s))" % (pydrofoil_smt_regs[regname], other_smt_regs[regname])
        exprs[regname] = z3.parse_smt2_string(smtlib_expr, decls=regs_and_other_decls, sorts=z3types)
    return exprs

def build_assertions_mem(smt_mem0, smt_mem1, init_mem_to_z3var):
    exprs = {}
    #TODO
    assert 0, "implement memory"
    return exprs


def solve_assert_z3_unequality_exprs(exprs, failfast=True, verbosity=0):
    """ gets dict of exprs e.g. {'x1': x1_a != x1_b, ...} and checks for unsat.
        unsat means that x1_a and x1_b are equal """
    ok = True
    print "============== checking registers/memory =============="
    start = time.time()
    for name, value in exprs.iteritems():
        solver = z3.Solver()
        solver.set("timeout", 777)
        res = solver.check(value)
        if res == z3.unknown:
            print "==============        timeout        =============="
            print value
            print "==============        timeout        =============="
            print "==============      skipped test     =============="
            return time.time() - start
        if failfast:
            if res != z3.unsat: print(solver.model())
            assert res == z3.unsat, "assertion %s:%s failed" % (name, str(value))
        elif res != z3.unsat:
            print "failed: %s:%s == z3.unsat" % (name, str(value))
            print "model:", solver.model()
            ok = False
        elif verbosity > 0:
            print "ok:     %s:%s == z3.unsat" % (name, str(value))
    if ok: 
        print "==============    registers/memory ok    =============="
    print ""
    assert ok
    return time.time() - start

