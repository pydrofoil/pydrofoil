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

def _hex2int(data: bytes) -> int:
    b = bytes.fromhex(data.decode("ascii"))
    return int.from_bytes(b, byteorder="little")

def _int2hex(value: int, length: int = 8) -> bytes:
    data = int.to_bytes(value, length, byteorder="little")
    return data.hex().encode("ascii")
    
class GDBServer:
    def __init__(self, machine):
        self.machine = machine
        self.breakpoints = []
        
    def handle(self, packet: bytes) -> bytes:
        packet = _parse_gdb_packet(packet)
        if packet.command == "?":
            packet.command = "questionmark"
        method = getattr(self, packet.command, None)
        if method is not None:
            return method(packet)
        else:
            return _make_packet(b"") # empty response signals not supported

    def m(self, packet: GDBPacket) -> bytes:
        addr, length = packet.args.split(b",", 1)
        addr = int(addr, 16)
        length = int(length, 16)

        memory = bytearray()
        for i in range(length):
            value = self.machine.read_memory(addr + i, 1)
            memory += _int2hex(value, 1)

        return _make_packet(bytes(memory))

    def M(self, packet: GDBPacket) -> bytes:
        args, data = packet.args.split(b":", 1)
        addr, length = args.split(b",", 1)
        addr = int(addr, 16)
        length = int(length, 16)

        for i in range(length):
            value = _hex2int(data[i*2:i*2+2])
            self.machine.write_memory(addr + i, value, 1)

        return _make_packet(b"OK")

    def s(self, packet: GDBPacket):
        if len(packet.args) != 0:
            addr = int(packet.args, 16)
            self.machine.write_register("pc", addr)

        self.machine.step()

        return _make_packet(b"S05") # TODO is this the correct reply?
    
    def c(self, packet: GDBPacket):
        if len(packet.args) != 0:
            addr = int(packet.args, 16)
            self.machine.write_register("pc", addr)

        while True:
            self.machine.step()
            addr = self.machine.read_register("pc")
            if addr in self.breakpoints:
                break

        return _make_packet(b"S05") # TODO is this the correct reply?

    def questionmark(self, packet: GDBPacket) -> bytes:
        return _make_packet(b"S05") # TODO is this the correct reply?
    
    def g(self, packet: GDBPacket) -> bytes:
        register_data = bytearray()

        # zero register
        register_data += _int2hex(0)

        # general purpose registers (x1, x2, ...)
        for reg in range(1, 32):
            reg_val = self.machine.read_register("x" + str(reg))
            register_data += _int2hex(reg_val)

        # pc register
        reg_val = self.machine.read_register("pc")
        register_data += _int2hex(reg_val)

        return _make_packet(register_data)
    
    def G(self, packet: GDBPacket) -> bytes:
        data = packet.args

        # general purpose registers (x1, x2, ...)
        for reg in range(1, 32):
            value = _hex2int(data[reg*16:reg*16+16])
            self.machine.write_register("x" + str(reg), value)

        # pc register
        value = _hex2int(data[32*16:32*16+16])
        self.machine.write_register("pc", value)

        return _make_packet(b"OK")
    
    def Z(self, packet: GDBPacket):
        addr = packet.args.split(b",")[1]
        addr = int(addr, 16)

        self.breakpoints.append(addr)

        return _make_packet(b"OK")
    
    def z(self, packet: GDBPacket):
        addr = packet.args.split(b",")[1]
        addr = int(addr, 16)
        
        if addr in self.breakpoints:
            self.breakpoints.remove(addr)

        return _make_packet(b"OK")
    
    def p(self, packet: GDBPacket):
        num = int(packet.args, 16)

        if num == 33:
            value = self.machine.read_register("pc")
        else:
            value = self.machine.read_register("x" + str(num))
         
        return _make_packet(_int2hex(value))
    
    def P(self, packet: GDBPacket):
        num, value = packet.args.split(b"=", 1)
        num = int(num, 16)
        value = _hex2int(value)

        if num == 33:
            value = self.machine.write_register("pc", value)
        else:
            value = self.machine.write_register("x" + str(num), value)
         
        return _make_packet(b"OK")

    def eventloop(self, port):
        import socket
        serversocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            serversocket.bind(("localhost", port))
            serversocket.listen()
            print("starting gdb server on port", port)
            (sock, address) = serversocket.accept()
            print("got connection")
            try:

                buf = bytearray()
                while 1:
                    buf += sock.recv(4096)
                    print("FROM GDB:", buf)
                    if buf.startswith(b"+-"):
                        print("GOT -, STOPPING")
                        return
                    end = buf.find(b"#")
                    if end == -1 or end + 3 > len(buf):
                        continue
                    packet = bytes(buf[:end+3])
                    buf = buf[len(packet):]
                    print("PACKET:", packet)
                    response = self.handle(bytes(packet))
                    print("RESPONSE:", response)
                    sock.send(response)
            finally:
                sock.close()
        finally:
            serversocket.close()


def start_gdb_server(elf, port=1234):
    import pydrofoil
    machine = pydrofoil.RISCV64(elf)
    server = GDBServer(machine)
    server.eventloop(port)
