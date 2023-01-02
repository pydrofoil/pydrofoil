import struct

HEADER_FMT = ">IIIIIIIIII"
HEADER_MAGIC = 0xd00dfeed
HEADER_VERSION = 17
HEADER_LAST_COMP_VERSION = 16

HEADER_SIZE = struct.calcsize(HEADER_FMT)

RSV_MAP = b"\x00" * 16
RSV_MAP_SIZE = len(RSV_MAP)

def pack32(val):
    return struct.pack(">I", val)

FDT_BEGIN_NODE = pack32(0x1)
FDT_END_NODE = pack32(0x2)
FDT_PROP = pack32(0x3)
FDT_NOP = pack32(0x4)
FDT_END = pack32(0x9)



class DeviceTree(object):
    def __init__(self):
        self._strings = b""
        self._properties = []

    def _write_header(self, buffer):
        off_mem_rsvmap = HEADER_SIZE
        off_dt_struct = off_mem_rsvmap + RSV_MAP_SIZE
        dt_struct = b"".join(self._properties)
        size_dt_struct = len(dt_struct)

        off_dt_strings = off_dt_struct + size_dt_struct

        totalsize = off_dt_strings + len(self._strings)
        
        header = (
            HEADER_MAGIC, # magic
            totalsize,
            off_dt_struct,
            off_dt_strings,
            off_mem_rsvmap,
            HEADER_VERSION,
            HEADER_LAST_COMP_VERSION,
            0, # boot_cpuid_phys, XXX correct?
            len(self._strings), # size_dt_strings
            size_dt_struct,
        )
        buffer.append(struct.pack(HEADER_FMT, *header))
        buffer.append(RSV_MAP)
        buffer.append(dt_struct)
        buffer.append(self._strings)

    def add_property(self, name, data):
        offset = self._add_string(name)
        self._properties.append(FDT_PROP)
        self._properties.append(pack32(len(data)))
        self._properties.append(pack32(offset))
        self._properties.append(data)

    def add_property_u32(self, name, data):
        return self.add_property(name, pack32(data))

    def begin_node(self, name):
        terminated = self._nullterminate(name)
        self._properties.append(FDT_BEGIN_NODE)
        self._properties.append(terminated)
        if len(terminated) & 0b11: # 4-byte-align
            self._properties.append(b"\x00" * (4 - (len(terminated) & 0b11)))
        return Node(self)

    def to_binary(self):
        self._properties.append(FDT_END)
        res = []
        self._write_header(res)
        return b"".join(res)

    def _nullterminate(self, s):
        assert b"\x00" not in s
        return s + b"\x00"

    def _add_string(self, s):
        # quadratic, but probably fine
        terminated = self._nullterminate(s)
        index = self._strings.find(terminated)
        if index >= 0:
            return index
        index = len(self._strings)
        self._strings += terminated
        return index
        
class Node(object):
    def __init__(self, dt):
        self.dt = dt

    def __enter__(self, *args):
        pass

    def __exit__(self, *args):
        self.dt._properties.append(FDT_END_NODE)
