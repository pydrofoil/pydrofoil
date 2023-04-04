import gdb_pydrofoil
from gdb_pydrofoil import GDBPacket, GDBServer
import pytest

def test_parse_gdb_packet():
    packet = b"$vMustReplyEmpty#3a"
    res = gdb_pydrofoil._parse_gdb_packet(packet)
    assert res.command == "vMustReplyEmpty"

def test_parse_gdb_packet_checksum_wrong():
    packet = b"$vMustReplyEmpty#00"
    with pytest.raises(ValueError):
        gdb_pydrofoil._parse_gdb_packet(packet)

def test_parse_gdb_packet_ack():
    packet = b"+$vMustReplyEmpty#3a"
    res = gdb_pydrofoil._parse_gdb_packet(packet)
    assert res.command == "vMustReplyEmpty"

def test_parse_gdb_packet_ack2():
    packet = b"-$vMustReplyEmpty#3a"
    res = gdb_pydrofoil._parse_gdb_packet(packet)
    assert res.command == "vMustReplyEmpty"
        
def test_get_command_s():
    command = gdb_pydrofoil._parse_command(b"s")
    assert command == "s"
    
def test_get_command_qSupported():
    command = gdb_pydrofoil._parse_command(b"qSupported")
    assert command == "qSupported"
    
def test_get_command_s_attributes():
    command = gdb_pydrofoil._parse_command(b"sab12")
    assert command == "s"

def test_handle_unsupported():
    class DummyMachine:
        def __init__(self):
            pass
        
        def register_callback(self, event, callback):
            pass
    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$_#5f")
    assert resp == b"+$#00"

def test_handle_m():
    class DummyMachine:
        def __init__(self):
            self.addrs = []

        def read_memory(self, addr, width):
            self.addrs.append(addr)
            return 1
        
        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$m10,5#2f")
    assert resp == b"+$0101010101#e5"
    assert machine.addrs == [16, 17, 18, 19, 20]

def test_handle_M():
    class DummyMachine:
        def __init__(self):
            self.addrs = []
            self.values = []

        def write_memory(self, addr, value, width):
            self.addrs.append(addr)
            self.values.append(value)

        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$M10,5:0102030405#38")
    assert resp == b"+$OK#9a"
    assert machine.addrs == [16, 17, 18, 19, 20]
    assert machine.values == [1, 2, 3, 4, 5]

def test_handle_s():
    class DummyMachine:
        def __init__(self):
            self.has_been_called = False

        def step(self):
            self.has_been_called = True

        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$s#73")
    assert resp == b"+$S05#b8"
    assert machine.has_been_called

def test_handle_s_addr():
    class DummyMachine:
        def __init__(self):
            self.register = ""
            self.addr = 0
            self.has_been_called = False

        def write_register(self, r, v):
            self.register = r
            self.addr = v

        def step(self):
            self.has_been_called = True

        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$s10#d4")
    assert resp == b"+$S05#b8"
    assert machine.has_been_called
    assert machine.register == "pc"
    assert machine.addr == 16

def test_real_gdb_packet():
    class DummyMachine:
        def __init__(self):
            pass
        def register_callback(self, event, callback):
            pass
    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"+$qSupported:multiprocess+;swbreak+;hwbreak+;qRelocInsn+;fork-events+;vfork-events+;exec-events+;vContSupported+;QThreadEvents+;no-resumed+;memory-tagging+;xmlRegisters=i386#77")
    assert resp == b"+$#00"

def test_handle_g():
    class DummyMachine:
        def __init__(self):
            pass

        def read_register(self, reg):
            return 123
        
        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$g#67")
    assert len(resp) == 533
    assert resp[18:34] == b"7b00000000000000"


def test_handle_G():
    class DummyMachine:
        def __init__(self):
            self.regs = {}

        def write_register(self, reg, value):
            self.regs[reg] = value

        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"+$G00000000000000007b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000#81")
    assert resp == b"+$OK#9a"
    assert machine.regs["x1"] == 123

def test_handle_p():
    class DummyMachine:
        def __init__(self):
            pass

        def read_register(self, reg):
            return 123
        
        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$p1#a1")
    assert resp[2:-3] == b"7b00000000000000"

def test_handle_P():
    class DummyMachine:
        def __init__(self):
            pass

        def write_register(self, reg, value):
            assert reg == "x1" and value == 123

        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    server.handle(b"$P1=7b00000000000000#f7")

def test_handle_Z0():
    class DummyMachine:
        def __init__(self):
            self.pc = 0

        def read_register(self, name):
            return self.pc

        def step(self):
            self.pc += 1

        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)
    
    resp = server.handle(b"$Z0,64,0#7c")
    assert resp[2:-3] == b"OK"

    resp = server.handle(b"$c#63")
    assert resp[2:-3] == b"S05"
    assert machine.pc == 100

def test_handle_z0():
    class DummyMachine:
        def __init__(self):
            self.pc = 0

        def read_register(self, name):
            return self.pc

        def step(self):
            self.pc += 1

        def register_callback(self, event, callback):
            pass

    machine = DummyMachine()
    server = GDBServer(machine)

    resp = server.handle(b"$Z0,65,0#7d")
    assert resp[2:-3] == b"OK"
    
    resp = server.handle(b"$Z0,64,0#7c")
    assert resp[2:-3] == b"OK"

    resp = server.handle(b"$c#63")
    assert resp[2:-3] == b"S05"
    assert machine.pc == 100

    resp = server.handle(b"$z0,64,0#9c")
    assert resp[2:-3] == b"OK"

    resp = server.handle(b"$c#63")
    assert resp[2:-3] == b"S05"
    assert machine.pc == 101

def test_poll_socket():
    class DummyMachine:
        def __init__(self):
            self.pc = 0

        def read_register(self, name):
            return self.pc

        def step(self):
            self.pc += 1

        def register_callback(self, event, callback):
            pass

    class DummySocket:
        def __init__(self):
            self.msgs = []
            self.did_send = False

        def recv(self, n):
            if not self.did_send:
                self.did_send = True
                return b"+$s#73+$s#73+$s#73+-"
            return b""

        def send(self, data):
            self.msgs.append(data)

    machine = DummyMachine()
    socket = DummySocket()
    server = GDBServer(machine)
    
    server.running = True
    server.poll_socket(socket)
    server.stop()

    assert len(socket.msgs) == 3
    assert socket.msgs[0][2:-3] == b"S05"
    assert socket.msgs[1][2:-3] == b"S05"
    assert socket.msgs[2][2:-3] == b"S05"
    assert machine.pc == 3