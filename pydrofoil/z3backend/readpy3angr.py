from pydrofoil.z3backend.z3btypes import Z3Value, ConstantSmallBitVector
import z3
import os, subprocess, tempfile
import shutil

RV64_REGISTER_ABI_NAMES = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0",
                           "s1", "a0", "a1", "a2", "a3", "a4", "a5", "a6",  "a7",
                           "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10",
                           "s11", "t3", "t4", "t5", "t6"]


def load_executions(filename):
    """ load angr simulated 'executions' from file """
    d = {}
    eval(compile("from %s import executions" % filename, "<string>", 'exec'), d)
    return d["executions"]

def load_code(filename):
    """ load generated instructions from file """
    d = {}
    eval(compile("from %s import code" % filename, "<string>", 'exec'), d)
    return d["code"]

def gen_code_run_angr_single(num_ops=128, arch="rv64", verbose=False, pcode=False):
    """ Generate random instructions, simulate each with angr in single subprocess and load the execution objects """
    assert "PYDROFOILANGR" in os.environ, "cant find py3 with pydrofoil and angr in environment"
    file = tempfile.NamedTemporaryFile(suffix=".py")
    cmd = [os.environ["PYDROFOILANGR"], "-m", "angrsmtdump", "-arch", arch, "-file", file.name, "-numops", str(num_ops), "-generate"]
    if verbose:
        cmd.append("-verbose")
    if pcode:
        cmd.append("-pypcode")
    subprocess.check_call(" ".join(cmd),shell=True, env=os.environ)
    copy_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), str(file.name)[1:])
    shutil.copy(file.name, copy_path)
    code = load_code("pydrofoil.z3backend%s" % file.name.replace("/", ".")[:-3])
    if os.path.exists(copy_path):
        os.remove(copy_path)
    if os.path.exists(copy_path + "c"):
        os.remove(copy_path + "c") 
    executions = []
    while code:
        instrs = [code.pop() for _ in range(min(128, len(code)))] # TODO: remove this and just run all at once
        excs = run_angr_opcodes(instrs, arch, verbose)
        while excs is None: excs = run_angr_opcodes(instrs, arch, verbose)
        executions.extend(excs)
    file.close()
    return executions

def gen_code_run_angr(num_ops=128, arch="rv64", verbose=False, pcode=False):
    """ Generate random instructions, simulate with angr and load the execution objects """
    #assert "CPY3ANGR" in os.environ, "cant find cpy3 with angr in environment " 
    assert "PYDROFOILANGR" in os.environ, "cant find py3 with pydrofoil and angr in environment"
    outfile_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "temp.py")
    cmd = [os.environ["PYDROFOILANGR"], "-m", "angrsmtdump", "-arch", arch, "-file", outfile_path, "-numops", str(num_ops)]
    if verbose:
        cmd.append("-verbose")
    if pcode:
        cmd.append("-pypcode")
    subprocess.check_call(" ".join(cmd),shell=True, env=os.environ)
    executions = load_executions("pydrofoil.z3backend.temp")
    if os.path.exists(outfile_path):
        os.remove(outfile_path)
    if os.path.exists(outfile_path + "c"):
        os.remove(outfile_path + "c") 
    return executions

def run_angr_opcodes(opcodes=[], arch="rv64", verbose=False, pcode=False):
    """ simulate opcodes with angr and load the execution objects """
    assert "CPY3ANGR" in os.environ, "cant find cpy3 with angr in environment " 
    assert "PYDROFOILANGR" in os.environ, "cant find py3 with pydrofoil and angr in environment"
    opcodes = [str(opc) for opc in opcodes]
    file = tempfile.NamedTemporaryFile(suffix=".py")
    cmd = [os.environ["PYDROFOILANGR"], "-m", "angrsmtdump", "-arch", arch, "-file", file.name]
    if verbose:
        cmd.append("-verbose")
    if pcode:
        cmd.append("-pypcode")
    cmd.append("-opcodes")
    cmd.append(str(" ".join(opcodes)))
    try:
        subprocess.check_call(" ".join(cmd),shell=True, env=os.environ)
    except subprocess.CalledProcessError as cpe:
        #print "CalledProcessError"
        #if "ReferenceError" in str(cpe.output): 
        #    print "ReferenceError"
        #else:
        #    print cpe.output
        file.close()
        return None
    copy_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), str(file.name)[1:])
    shutil.copy(file.name, copy_path)
    executions = load_executions("pydrofoil.z3backend%s" % file.name.replace("/", ".")[:-3])
    if os.path.exists(copy_path):
        os.remove(copy_path)
    if os.path.exists(copy_path + "c"):
        os.remove(copy_path + "c") 
    file.close()
    return executions

#############################

def create_wrapped_init_register_values(execution, pc_ip_reg_size=None): # TODO: move this intoz3backend_executor.py
    """ create z3 Bitvecs for registers and wrap them in z3Backend wrapper classes """
    arch = get_arch_from_execution(execution)
    init_regs = get_init_reg_names_from_execution(execution)
    w_regs = {}
    init_name_z3_mapping = {}

    all_regs = set(arch.registers_size.keys())

    for registername, aliaslist in arch.register_aliases.iteritems():
        if not registername in all_regs: continue

        rval = z3.BitVec(init_regs[registername], 8 * arch.registers_size[registername]) # registers_size is in bytes, z3 in bits
        init_name_z3_mapping[init_regs[registername]] = rval
        w_regs[registername] = Z3Value(rval)

        for alias in aliaslist:
            init_name_z3_mapping[init_regs[alias]] = rval
            w_regs[alias] = Z3Value(rval)
            all_regs.remove(alias)

        all_regs.remove(registername)

    assert len(all_regs) == 0

    if pc_ip_reg_size != None:
        regname, regsize = pc_ip_reg_size
        w_regs[pc_ip_reg_size[0]] = ConstantSmallBitVector(get_load_addr_from_execution(execution), regsize)
        init_name_z3_mapping[init_regs[regname]] = w_regs[regname].toz3()

        for alias in arch.register_aliases[regname]:
            w_regs[alias] = ConstantSmallBitVector(get_load_addr_from_execution(execution), regsize)
            init_name_z3_mapping[init_regs[alias]] = w_regs[alias].toz3()
    
    return w_regs, init_name_z3_mapping

def init_rv64_zero_reg(w_regs, init_name_z3_mapping, init_regs):
    w_regs["zero"] = ConstantSmallBitVector(0, 64)
    w_regs["x0"] = w_regs["zero"] 
    init_name_z3_mapping[init_regs["zero"]] = w_regs["zero"].toz3()
    init_name_z3_mapping[init_regs["x0"]] = w_regs["x0"].toz3()

def create_wrapped_init_register_values_rv64(execution):
    """ create z3 Bitvecs for registers and wrap them in z3Backend wrapper classes for rv64 """
    w_regs, init_name_z3_mapping = create_wrapped_init_register_values(execution, ("pc", 8 * 8))
    init_rv64_zero_reg(w_regs, init_name_z3_mapping, get_init_reg_names_from_execution(execution))
    return w_regs, init_name_z3_mapping

def rename_w_registers_xn_pcode_rv64(registers):
    """ when using pypcode in angr, regs are not refered to as x0, x1, ... but as zero, ra, ...
        creates mappings for the xnames by copying the abi entries e.g. mapping["x1"] = mapping["ra"], ..."""
    # x8 has two aliases: s0, fp
    if "s0" in registers:
        registers["fp"] = registers["s0"]
    else:
        registers["s0"] = registers["fp"]

    for i in range(32):
        registers["x%d" % i] = registers[RV64_REGISTER_ABI_NAMES[i]]

def create_wrapped_memory_values(execution):
    """ TODO """
    arch = get_arch_from_execution(execution)
    init_mem = get_result_mem_from_execution(execution)
    w_mem = {}
    assert 0, "implement memory"
    return w_mem


#### Execution field access ####
# Execution class may change

def get_code_from_execution(execution):
    """ returns list of executed machine code """
    return execution.code

def get_arch_from_execution(execution):
    """ returns correpsonding isa class """
    return execution.arch

def get_init_reg_names_from_execution(execution):
    """ returns mapping register_name:init_register_bitvec_name e.g. 'x12': 'bitvec_x12_1233245' """
    return execution.init_registers

def get_result_regs_from_execution(execution):
    """ returns mapping register_name: smtlib2 expr e.g. 'x12':'(bvadd #x0000000000000073 (concat #x00000000000000 zero_267_8))' """
    return execution.result_reg_values

def get_init_mem_names_from_execution(execution):
    """ returns mapping addr:init_mem_bitvec_name e.g. '12345': bitvec_12345_6767846 """
    return execution.init_memory

def get_result_mem_from_execution(execution):
    """ returns mapping addr:smtlib2 expr e.g. '12345':'(bvadd #x0000000000000073 (concat #x00000000000000 bitvec_12345_6767846))' """
    return execution.result_memory_values

def get_mem_from_execution(execution):
    """ TODO """
    return execution.init_memory, execution.result_memory_values

def get_load_addr_from_execution(execution):
    """ Get load addr, i.e., pc/ip value for first instruction in memory """
    return execution.load_addr
