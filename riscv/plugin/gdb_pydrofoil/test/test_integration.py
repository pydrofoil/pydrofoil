from gdb_pydrofoil import start_gdb_server, stop_gdb_server
import socket
import os
import threading
import time

PORT = 12345
EXECUTABLE = os.path.join(os.path.dirname(__file__), "../../../../sail-riscv/test/riscv-tests/rv64ui-p-add.elf")

def start_server():
    start_gdb_server(EXECUTABLE, PORT)

def test_real_socket():
    server = threading.Thread(target=start_server)
    server.start()

    # wait for server to start
    time.sleep(0.25)

    clientsock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        clientsock.connect(("localhost", PORT))
        try:
            clientsock.sendall(b"+$g#67")
            resp = clientsock.recv(4096)
            print("Test", resp)
            assert resp[2:-3][32*16:32*16+16] == b"0010000000000000"

            clientsock.sendall(b"+$s#73")
            resp = clientsock.recv(4096)
            assert resp[2:-3] == b"S05"

            clientsock.sendall(b"+$g#67")
            resp = clientsock.recv(4096)
            assert resp[2:-3][32*16:32*16+16] == b"0410000000000000"
        finally:
            clientsock.close()
    finally:
        clientsock.close()

    stop_gdb_server()
    server.join()