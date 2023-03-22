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
    machine = "dummy"
    server = GDBServer(machine)
    resp = server.handle(b"$_#5f")
    assert resp == b"+$#00"

def test_handle_m():
    class DummyMachine:
        def __init__(self):
            self.addrs = []

        def read_memory(self, addr):
            self.addrs.append(addr)
            return 1

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

        def write_memory(self, addr, value):
            self.addrs.append(addr)
            self.values.append(value)

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

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$s10#d4")
    assert resp == b"+$S05#b8"
    assert machine.has_been_called
    assert machine.register == "pc"
    assert machine.addr == 16

def test_handle_X():
    class DummyMachine:
        def __init__(self):
            self.addrs = []
            self.values = []

        def write_memory(self, addr, value):
            self.addrs.append(addr)
            self.values.append(value)

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$X10,5:\1\2\3\4\5#63")
    assert resp == b"+$OK#9a"
    assert machine.addrs == [16, 17, 18, 19, 20]
    assert machine.values == [1, 2, 3, 4, 5]

def test_real_gdb_packet():
    server = GDBServer("dummy")
    resp = server.handle(b"+$qSupported:multiprocess+;swbreak+;hwbreak+;qRelocInsn+;fork-events+;vfork-events+;exec-events+;vContSupported+;QThreadEvents+;no-resumed+;memory-tagging+;xmlRegisters=i386#77")
    assert resp == b"+$#00"

def test_handle_g():
    class DummyMachine:
        def __init__(self):
            pass

        def read_register(self, reg):
            return 123

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"$g#67")
    assert len(resp) == 533
    assert resp[18:34] == b"000000000000007b"


def test_handle_G():
    class DummyMachine:
        def __init__(self):
            self.regs = {}

        def write_register(self, reg, value):
            self.regs[reg] = value

    machine = DummyMachine()
    server = GDBServer(machine)
    resp = server.handle(b"+$G00000000000000007b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000#81")
    assert resp == b"+$OK#9a"
    assert machine.regs["x1"] == 123