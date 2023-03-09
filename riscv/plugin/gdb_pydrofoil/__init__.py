from dataclasses import dataclass

@dataclass
class GDBPacket:
    command: bytes

def _calculate_checksum(command: bytes):
    sum = 0
    for b in command:
        sum += b
    return sum % 256

def _parse_gdb_packet(package: bytes):
    if not package.startswith(b"$"):
        raise ValueError()

    command, checksum = package[1:].split(b"#", 1)
    checksum = int(checksum, 16)
    if _calculate_checksum(command) != checksum:
        raise ValueError()

    return GDBPacket(command)
