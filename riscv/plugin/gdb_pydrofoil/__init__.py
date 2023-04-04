from dataclasses import dataclass
import functools
from typing import Union

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

def _split_args(args: Union[str, bytes]) -> Union[str, bytes]:
    """
    Splits a string or bytes into a flat list at delimiters `,`,`;` or `:`.
    """
    args_comma = args.split("," if isinstance(args, str) else b",")
    args_semicolon = []
    for a in args_comma:
        args_semicolon += a.split(";" if isinstance(args, str) else b";")
    args_colon = []
    for a in args_semicolon:
        args_colon += a.split(":" if isinstance(args, str) else b":")
    return args_colon

def arguments(format: str):
    """
    Decorator to parse gdb packet arguments.

        Example:
        ```
        @arguments("hex,hex;*bytes")
        def handler(self, addr, length: int, data):
        ```

        This parses the arguments as two integers (from hexadecimal format) and one bytes object that is optional.
    """
    def decorator(func):
        @functools.wraps(func)
        def wrapper(self, packet):
            args = _split_args(packet.args)
            args = list(filter(lambda arg: len(arg) > 0, args))

            arg_types = _split_args(format)
            arg_types = list(filter(lambda ty: len(ty) > 0, arg_types))

            # parse arguments as given types
            parsed_args = []
            for ty, arg in zip(arg_types, args):
                if ty == "hex" or ty == "*hex":
                    parsed_args.append(int(arg, 16))
                if ty == "bytes" or ty == "*bytes":
                    parsed_args.append(arg)

            # fill with None arguments if optional arguments are not provided       
            if len(args) < len(arg_types):
                for i in range(len(arg_types)-len(args)):
                    if not arg_types[len(args) + i].startswith("*"):
                        raise ValueError()
                    parsed_args.append(None)

            return func(self, *parsed_args)
        return wrapper
    return decorator
    
class GDBServer:
    def __init__(self, machine):
        self.machine = machine
        self.breakpoints = []
        self.watchpoints_write = []
        self.watchpoints_read = []
        self.running = False
        self.hit_watchpoint = False

        def handle_mem_write(cpu, addr, size, value):
            for w in self.watchpoints_write:
                if w >= addr and w < addr + size:
                    self.hit_watchpoint = True

        def handle_mem_read(cpu, addr, size, value):
            for w in self.watchpoints_read:
                if w >= addr and w < addr + size:
                    self.hit_watchpoint = True

        machine.register_callback("memory_write", handle_mem_write)
        machine.register_callback("memory_read", handle_mem_read)
        
    def handle(self, packet: bytes) -> bytes:
        packet = _parse_gdb_packet(packet)
        if packet.command == "?":
            packet.command = "questionmark"
        method = getattr(self, packet.command, None)
        if method is not None:
            return method(packet)
        else:
            return _make_packet(b"") # empty response signals not supported

    @arguments("hex,hex")
    def m(self, addr: int, length: int) -> bytes:
        memory = bytearray()
        for i in range(length):
            value = self.machine.read_memory(addr + i, 1)
            memory += _int2hex(value, 1)

        return _make_packet(bytes(memory))

    @arguments("hex,hex,bytes")
    def M(self, addr: int, length: int, data: bytes) -> bytes:
        for i in range(length):
            value = _hex2int(data[i*2:i*2+2])
            self.machine.write_memory(addr + i, value, 1)

        return _make_packet(b"OK")

    @arguments("*hex")
    def s(self, addr: int):
        if addr is not None:
            self.machine.write_register("pc", addr)

        self.machine.step()

        return _make_packet(b"S05") # TODO is this the correct reply?
    
    @arguments("*hex")
    def c(self, addr: int):
        if addr is not None:
            self.machine.write_register("pc", addr)

        self.hit_watchpoint = False

        while True:
            self.machine.step()
            addr = self.machine.read_register("pc")
            if addr in self.breakpoints or self.hit_watchpoint:
                break

        return _make_packet(b"S05") # TODO is this the correct reply?

    @arguments("")
    def questionmark(self) -> bytes:
        return _make_packet(b"S05") # TODO is this the correct reply?
    
    @arguments("")
    def g(self) -> bytes:
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
    
    @arguments("bytes")
    def G(self, data: bytes) -> bytes:
        # general purpose registers (x1, x2, ...)
        for reg in range(1, 32):
            value = _hex2int(data[reg*16:reg*16+16])
            self.machine.write_register("x" + str(reg), value)

        # pc register
        value = _hex2int(data[32*16:32*16+16])
        self.machine.write_register("pc", value)

        return _make_packet(b"OK")
    
    @arguments("hex,hex")
    def Z(self, type: int, addr: int):
        if type == 0:
            self.breakpoints.append(addr)
        if type == 2:
            self.watchpoints_write.append(addr)
        if type == 3:
            self.watchpoints_read.append(addr)

        return _make_packet(b"OK")
    
    @arguments("hex,hex")
    def z(self, type: int, addr: int):
        if type == 0:
            if addr in self.breakpoints:
                self.breakpoints.remove(addr)
        if type == 2:
            if addr in self.watchpoints_write:
                self.watchpoints_write.remove(addr)
        if type == 3:
            if addr in self.watchpoints_read:
                self.watchpoints_read.remove(addr)

        return _make_packet(b"OK")
    
    @arguments("hex")
    def p(self, num: int):
        if num == 33:
            value = self.machine.read_register("pc")
        else:
            value = self.machine.read_register("x" + str(num))
         
        return _make_packet(_int2hex(value))
    
    @arguments("bytes")
    def P(self, data: bytes):
        num, value = data.split(b"=", 1)
        num = int(num, 16)
        value = _hex2int(value)

        if num == 33:
            value = self.machine.write_register("pc", value)
        else:
            value = self.machine.write_register("x" + str(num), value)
         
        return _make_packet(b"OK")
    
    def poll_socket(self, sock):
        buf = bytearray()
        while self.running:
            buf += sock.recv(4096)
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
                self.running = True
                self.poll_socket(sock)
            finally:
                sock.close()
        finally:
            serversocket.close()

    def stop(self):
        self.running = False


def start_gdb_server(elf, port=1234):
    import pydrofoil
    machine = pydrofoil.RISCV64(elf)
    global server
    server = GDBServer(machine)
    server.eventloop(port)

def stop_gdb_server():
    # TODO find better way to stop server
    global server
    server.stop()
