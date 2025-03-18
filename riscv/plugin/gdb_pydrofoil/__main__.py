from gdb_pydrofoil import start_gdb_server
import sys

if len(sys.argv) < 3:
    print("usage: gdb_pydrofoil <elf> <port>")
else:
    start_gdb_server(sys.argv[1], int(sys.argv[2]))