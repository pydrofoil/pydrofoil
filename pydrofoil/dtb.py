import struct

HEADER_FMT = ">IIIIIIIIII"
HEADER_MAGIC = 0xd00dfeed
HEADER_VERSION = 17
HEADER_LAST_COMP_VERSION = 16

HEADER_SIZE = struct.calcsize(HEADER_FMT)

RSV_MAP = b"\x00" * 16
RSV_MAP_SIZE = len(RSV_MAP)

def pack32(val):
    assert 0 <= val < 2 ** 32
    b0 = chr(val >> 24)
    b1 = chr((val >> 16) & 0xff)
    b2 = chr((val >> 8) & 0xff)
    b3 = chr((val >> 0) & 0xff)
    return b0 + b1 + b2 + b3

FDT_BEGIN_NODE = pack32(0x1)
FDT_END_NODE = pack32(0x2)
FDT_PROP = pack32(0x3)
FDT_NOP = pack32(0x4)
FDT_END = pack32(0x9)


class DeviceTree(object):
    def __init__(self):
        self._strings = b""
        self._properties = []
        self._current_handle = 1

    def _write_header(self, buffer):
        off_mem_rsvmap = HEADER_SIZE
        off_dt_struct = off_mem_rsvmap + RSV_MAP_SIZE
        dt_struct = b"".join(self._properties)
        size_dt_struct = len(dt_struct)

        off_dt_strings = off_dt_struct + size_dt_struct

        totalsize = off_dt_strings + len(self._strings)
        
        header = [
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
        ]
        for num in header:
            buffer.append(pack32(num))
        buffer.append(RSV_MAP)
        buffer.append(dt_struct)
        buffer.append(self._strings)

    def add_property_raw(self, name, data):
        offset = self._add_string(name)
        self._properties.append(FDT_PROP)
        self._properties.append(pack32(len(data)))
        self._properties.append(pack32(offset))
        self._properties.append(data)
        if len(data) & 0b11: # 4-byte-align
            self._properties.append(b"\x00" * (4 - (len(data) & 0b11)))

    def add_property(self, name, data):
        return self.add_property_raw(name, self._nullterminate(data))

    def add_property_list(self, name, strlist):
        data = b"\x00".join(strlist) + b"\x00"
        return self.add_property_raw(name, data)

    def add_property_empty(self, name):
        return self.add_property_raw(name, b"")

    def add_property_u32(self, name, data):
        return self.add_property_raw(name, pack32(data))

    def add_property_u32_list(self, name, data):
        data = b"".join([pack32(u32) for u32 in data])
        return self.add_property_raw(name, data)

    def add_property_u64_list(self, name, data):
        u32data = []
        for num in data:
            u32data.append(num >> 32)
            u32data.append(num & 0xffffffff)
        return self.add_property_u32_list(name, u32data)

    def begin_node(self, name):
        terminated = self._nullterminate(name)
        self._properties.append(FDT_BEGIN_NODE)
        self._properties.append(terminated)
        if len(terminated) & 0b11: # 4-byte-align
            self._properties.append(b"\x00" * (4 - (len(terminated) & 0b11)))
        return Node(self)

    def begin_node_with_handle(self, name):
        res = self.begin_node(name)
        res.phandle = self._current_handle
        self._current_handle += 1
        return res

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
        self.phandle = -1

    def __enter__(self, *args):
        return self.phandle

    def __exit__(self, *args):
        if self.phandle != -1:
            self.dt.add_property_u32("phandle", self.phandle)
        self.dt._properties.append(FDT_END_NODE)
