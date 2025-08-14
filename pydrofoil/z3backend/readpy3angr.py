from pydrofoil.z3backend.z3btypes import Z3Value, ConstantSmallBitVector
import z3
import os, subprocess, tempfile


def load_executions(filename):
    """ load angr simulated 'executions' from file """
    d = {}
    #eval("from %s import executions" % filename, d)
    eval(compile("from %s import executions" % filename, "<string>", 'exec'), d)
    return d["executions"]

def gen_code_run_angr(num_ops=128, arch="rv64"):
    """ Generate random instructions, simulate with angr abd load the execution objects """
    assert "PYDROFOILANGR" in os.environ, "cant find py3 with pydrofoil and angr in environment"
    outfile_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "temp.py")
    cmd = [os.environ["PYDROFOILANGR"], "-m", "angrsmtdump", "-arch", arch, "-file", outfile_path, "-numops", str(num_ops)]
    subprocess.check_call(" ".join(cmd),shell=True)
    executions = load_executions("pydrofoil.z3backend.temp")
    if os.path.exists(outfile_path):
        os.remove(outfile_path)
    return executions

def run_angr_opcodes(opcodes=[], arch="rv64", verbose=False):
    """ simulate opcodes with angr abd load the execution objects """
    assert "PYDROFOILANGR" in os.environ, "cant find py3 with pydrofoil and angr in environment"
    opcodes = [str(opc) for opc in opcodes]
    outfile_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "temp.py")
    cmd = [os.environ["PYDROFOILANGR"], "-m", "angrsmtdump", "-arch", arch, "-file", outfile_path]
    if verbose:
        cmd.append("-verbose")
    cmd.append("-opcodes")
    cmd.append(str(" ".join(opcodes)))
    subprocess.check_call(" ".join(cmd),shell=True)
    executions = load_executions("pydrofoil.z3backend.temp")
    if os.path.exists(outfile_path):
        os.remove(outfile_path)
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
