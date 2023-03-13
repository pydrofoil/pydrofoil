from dataclasses import dataclass

@dataclass
class GDBPacket:
    command: str
    args: bytes

def _calculate_checksum(command: bytes) -> int:
    sum = 0
    for b in command:
        sum += b
    return sum % 256

def _parse_command(packet: bytes) -> str:
    if packet.startswith((b"v", b"q")):
        cmd = packet.split(b":", 1)[0]
    else:
        cmd = packet[:1]
    return str(cmd, "ascii")

def _parse_gdb_packet(packet: bytes) -> GDBPacket:
    if packet.startswith(b"+") or packet.startswith(b"-"):
        # ignore acknowledgments
        # TODO "-" should retransmit previous command
        packet = packet[1:]

    if not packet.startswith(b"$"):
        raise ValueError()

    cmd_and_args, checksum = packet[1:].split(b"#", 1)
    checksum = int(checksum, 16)
    if _calculate_checksum(cmd_and_args) != checksum:
        raise ValueError()

    cmd = _parse_command(cmd_and_args)
    args = cmd_and_args[len(cmd):]

    return GDBPacket(cmd, args)

def _make_packet(cmd_and_args: bytes) -> bytes:
    checksum = format(_calculate_checksum(cmd_and_args), "02x")
    return b"+$" + cmd_and_args + b"#" + checksum.encode("ascii")
    
class GDBServer:
    def __init__(self, machine):
        self.machine = machine
        
    def handle(self, packet: bytes) -> bytes:
        packet = _parse_gdb_packet(packet)
        method = getattr(self, packet.command, None)
        if method is not None:
            return method(packet)
        else:
            return _make_packet(b"") # empty response signals not supported

    def m(self, packet: GDBPacket) -> bytes:
        addr, length = packet.args.split(b",", 1)
        addr = int(addr, 16)
        length = int(length, 16)

        memory = ""
        for i in range(length):
            memory += format(self.machine.read_memory(addr + i), "02x")

        return _make_packet(memory.encode("ascii"))

    def M(self, packet: GDBPacket) -> bytes:
        args, data = packet.args.split(b":", 1)
        addr, length = args.split(b",", 1)
        addr = int(addr, 16)
        length = int(length, 16)

        for i in range(length):
            value = int(data[i*2:i*2+2], 16)
            self.machine.write_memory(addr + i, value)

        return _make_packet(b"OK")

    def s(self, packet: GDBPacket):
        if len(packet.args) != 0:
            addr = int(packet.args, 16)
            self.machine.write_register("pc", addr)

        self.machine.step()

        return _make_packet(b"S05") # TODO is this the correct reply?

    def X(self, packet: GDBPacket) -> bytes:
        args, data = packet.args.split(b":", 1)
        addr, length = args.split(b",", 1)
        addr = int(addr, 16)
        length = int(length, 16)

        for i in range(length):
            self.machine.write_memory(addr + i, data[i])

        return _make_packet(b"OK")