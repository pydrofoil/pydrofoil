import os, subprocess, tempfile
import shutil
import time

#####################################
# copied from readangr.py
# TODO: could be moved into helper 'util' class

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


#####################################
# TODO: most of this could be moved into helper 'util' class
# and then be used by readangr and readvexingz3

def gen_code_run_vexingz3(num_ops=128, arch="rv64", verbosity=0, instr_types=None):
    """ Generate random instructions, simulate each with vexingz3 in single subprocess and load the execution objects """
    assert "PYDROFOILANGR" in os.environ, "cant find py3 with pydrofoil and angr-z3-converter in environment"
    start = time.time()
    file = tempfile.NamedTemporaryFile(suffix=".py")
    cmd = [os.environ["PYDROFOILANGR"], "-m", "angrsmtdump", "", "-arch", arch, "-file", file.name, "-numops", str(num_ops), "-generate"]
    # TODO: refactor angr-z3-converter into seperate packages for executing with angr (angrsmtdump) and generating instructions (generate)
    # ATM just generate via calling angrsmtdummp -generate
    if verbosity > 0:
        cmd.append("-verbose")
    if instr_types: # tell angrsmtdump to generate only instructions  of certain types, instead of the ones currently allowed in angrsmtdump
        cmd.append("-types")
        cmd.extend(instr_types)
    subprocess.check_call(" ".join(cmd),shell=True, env=os.environ)
    copy_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), str(file.name)[1:])
    shutil.copy(file.name, copy_path)
    code = load_code("pydrofoil.z3backend%s" % file.name.replace("/", ".")[:-3])
    if os.path.exists(copy_path):
        os.remove(copy_path)
    if os.path.exists(copy_path + "c"):
        os.remove(copy_path + "c") 
    executions = run_vexingz3_opcodes(code, arch, verbosity)
    if executions == None: assert 0, "run_angr_opcodes error"
    file.close()
    return executions, (time.time() - start)


def run_vexingz3_opcodes(opcodes=[], arch="rv64", verbosity=0):
    """ simulate opcodes with vexingz3 and load the execution objects """
    assert "PYDROFOILANGR" in os.environ, "cant find py3 with pydrofoil and vexingz3 in environment"
    opcodes = [str(opc) for opc in opcodes]
    file = tempfile.NamedTemporaryFile(suffix=".py")
    cmd = [os.environ["PYDROFOILANGR"], "-m", "vexingz3", "-arch", arch, "-file", file.name]
    #if verbosity > 0:
    #    cmd.append("-verbose")
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
