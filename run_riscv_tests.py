import sys
import time
import glob
import os
import subprocess
import junit_xml

base_test_path = os.path.join(os.getenv('RISCVMODELCHECKOUT'), 'test', 'riscv-tests')
print base_test_path


def run(cmd, fn, test_cases):
    print cmd,
    sys.stdout.flush()
    t1 = time.time()
    p = subprocess.Popen(cmd, shell=True,
              stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, close_fds=True)
    status = p.wait()
    t2 = time.time()
    success = status == 0
    stdout = p.stdout.read()
    stderr = p.stderr.read()
    case = junit_xml.TestCase(fn, elapsed_sec=t2 - t1, stdout=stdout, stderr=stderr)
    test_cases.append(case)
    if not success:
        case.add_failure_info("failed")
        print "FAILED"
        print stdout
        print stderr
    else:
        print "SUCESS"
    p.stdout.close()
    p.stderr.close()


def main():
    test_cases = []
    for fn in glob.glob(base_test_path + "/rv32*.elf"):
        cmd = "./pydrofoil-riscv --rv32 %s" % (fn, )
        run(cmd, fn, test_cases)
    ts32 = junit_xml.TestSuite("pydrofoild-riscv-32", test_cases)


    test_cases = []
    for fn in glob.glob(base_test_path + "/rv64*.elf"):
        cmd = "./pydrofoil-riscv %s" % (fn, )
        run(cmd, fn, test_cases)

    ts64 = junit_xml.TestSuite("pydrofoild-riscv-64", test_cases)
    with open("pydrofoil-riscv-tests.xml", "w") as f:
        f.write(junit_xml.TestSuite.to_xml_string([ts32, ts64]))

if __name__ == '__main__':
    main()
