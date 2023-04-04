from gdb_pydrofoil import start_gdb_server, stop_gdb_server
import os
import threading
import time
import subprocess

PORT = 12345
EXECUTABLE = os.path.join(os.path.dirname(__file__), "../../../../sail-riscv/test/riscv-tests/rv64ui-p-add.elf")
GDB = "/opt/riscv/bin/riscv64-unknown-elf-gdb"

def start_server():
    start_gdb_server(EXECUTABLE, PORT)

def test_real_gdb():
    server = threading.Thread(target=start_server)
    server.start()

    # wait for server to start
    time.sleep(0.25)

    gdb = subprocess.run([GDB, 
        "-batch",
        "-ex", "target remote :" + str(PORT),
        "-ex", "info registers pc",
        "-ex", "si",
        "-ex", "info registers pc"], 
        stdout=subprocess.PIPE)
    
    assert b"0x1000" in gdb.stdout
    assert b"0x1004" in gdb.stdout

    stop_gdb_server()
    server.join()
    