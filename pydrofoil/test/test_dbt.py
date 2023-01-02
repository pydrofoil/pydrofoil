from pydrofoil.dbt import DeviceTree

def test_devicetree_strings():
    d = DeviceTree()
    res = d._add_string(b"abc")
    assert res == 0
    res = d._add_string(b"abc")
    assert res == 0
    res = d._add_string(b"abcd")
    assert res == 4
    res = d._add_string(b"bcd")
    assert res == 5
    assert d._strings == b"abc\x00abcd\x00"

def test_devicetree_property():
    d = DeviceTree()
    d.add_property(b"#address-cells", "abc")
    assert b"".join(d._properties) == (
        b"\x00\x00\x00\x03" # PROP
        b"\x00\x00\x00\x04" # length of payload
        b"\x00\x00\x00\x00" # string offset
        b"abc\x00" # payload
    )
    assert d._strings == b"#address-cells\x00"

def test_devicetree_property_u32():
    d = DeviceTree()
    d.add_property_u32(b"#address-cells", 2)
    assert b"".join(d._properties) == (
        b"\x00\x00\x00\x03" # PROP
        b"\x00\x00\x00\x04" # length of payload
        b"\x00\x00\x00\x00" # string offset
        b"\x00\x00\x00\x02" # payload
    )
    assert d._strings == b"#address-cells\x00"

def test_devicetree_node():
    d = DeviceTree()
    with d.begin_node(b"cpus") as n:
        d.add_property_u32(b"#address-cells", 1)
        d.add_property_u32(b"#size-cells", 0)
    assert b"".join(d._properties) == (
        b"\x00\x00\x00\x01" # NODE
        b"cpus\x00"         # name
        b"\x00\x00\x00"     # alignment
            b"\x00\x00\x00\x03" # PROP
            b"\x00\x00\x00\x04" # length of payload
            b"\x00\x00\x00\x00" # string offset
            b"\x00\x00\x00\x01" # payload
            b"\x00\x00\x00\x03" # PROP
            b"\x00\x00\x00\x04" # length of payload
            b"\x00\x00\x00\x0f" # string offset
            b"\x00\x00\x00\x00" # payload
        b"\x00\x00\x00\x02" # END_NODE
    )

def test_devicetree_node_with_handle():
    d = DeviceTree()
    with d.begin_node_with_handle(b"cpus") as n:
        d.add_property_u32(b"#address-cells", 1)
    assert b"".join(d._properties) == (
        b"\x00\x00\x00\x01" # NODE
        b"cpus\x00"         # name
        b"\x00\x00\x00"     # alignment
            b"\x00\x00\x00\x03" # PROP
            b"\x00\x00\x00\x04" # length of payload
            b"\x00\x00\x00\x00" # string offset
            b"\x00\x00\x00\x01" # payload
            b"\x00\x00\x00\x03" # PROP handle
            b"\x00\x00\x00\x04" # length of payload
            b"\x00\x00\x00\x0f" # string offset
            b"\x00\x00\x00\x01" # payload
        b"\x00\x00\x00\x02" # END_NODE
    )

def test_sample():
    d = DeviceTree()
    with d.begin_node(b""):
        d.add_property_u32(b"#address-cells", 2)
        d.add_property_u32(b"#size-cells", 2)
        with d.begin_node(b"cpus"):
            d.add_property_u32(b"#address-cells", 1)
            d.add_property_u32(b"#size-cells", 0)
            d.add_property_u32(b"timebase-frequency", 10000000)
    res = d.to_binary()
    assert res == (
        b"\xD0\x0D\xFE\xED" # header magic
        b"\x00\x00\x00\xD6"
        b"\x00\x00\x00\x38"
        b"\x00\x00\x00\xA8"
        b"\x00\x00\x00\x28"
        b"\x00\x00\x00\x11"
        b"\x00\x00\x00\x10"
        b"\x00\x00\x00\x00"
        b"\x00\x00\x00\x2E"
        b"\x00\x00\x00\x70"
        b"\x00\x00\x00\x00" # rsv
        b"\x00\x00\x00\x00"
        b"\x00\x00\x00\x00"
        b"\x00\x00\x00\x00"
        b"\x00\x00\x00\x01" # node
        b"\x00\x00\x00\x00" # empty string as name, plus alignment
        b"\x00\x00\x00\x03" # prop
        b"\x00\x00\x00\x04"
        b"\x00\x00\x00\x00"
        b"\x00\x00\x00\x02"
        b"\x00\x00\x00\x03" # prop
        b"\x00\x00\x00\x04"
        b"\x00\x00\x00\x0F"
        b"\x00\x00\x00\x02"
        b"\x00\x00\x00\x01" # node
        b"cpus"             # name
        b"\x00\x00\x00\x00" # \0 + padding
        b"\x00\x00\x00\x03" # prop
        b"\x00\x00\x00\x04"
        b"\x00\x00\x00\x00"
        b"\x00\x00\x00\x01"
        b"\x00\x00\x00\x03" # prop
        b"\x00\x00\x00\x04"
        b"\x00\x00\x00\x0F"
        b"\x00\x00\x00\x00"
        b"\x00\x00\x00\x03" # prop
        b"\x00\x00\x00\x04"
        b"\x00\x00\x00\x1B"
        b"\x00\x98\x96\x80"
        b"\x00\x00\x00\x02"
        b"\x00\x00\x00\x02"
        b"\x00\x00\x00\x09"
        b"#address-cells\x00"
        b"#size-cells\x00"
        b"timebase-frequency\x00"
    )



def test_rv64_dtc():
    d = DeviceTree()
    with d.begin_node(b""):
        d.add_property_u32(b"#address-cells", 2)
        d.add_property_u32(b"#size-cells", 2)
        d.add_property(b"compatible", b"ucbbar,spike-bare-dev")
        d.add_property(b"model", b"ucbbar,spike-bare")
        with d.begin_node(b"cpus"):
            d.add_property_u32(b"#address-cells", 1)
            d.add_property_u32(b"#size-cells", 0)
            d.add_property_u32(b"timebase-frequency", 10000000)
            with d.begin_node(b"cpu@0"):
                d.add_property(b"device_type", b"cpu")
                d.add_property_u32(b"reg", 0)
                d.add_property(b"status", b"okay")
                d.add_property(b"compatible", b"riscv")
                d.add_property(b"riscv,isa", b"rv64imac")
                d.add_property(b"mmu-type", b"riscv,sv39")
                d.add_property_u32(b"clock-frequency", 1000000000)
                with d.begin_node_with_handle(b"interrupt-controller") as CPU0_intc:
                    d.add_property_u32(b"#interrupt-cells", 1)
                    d.add_property_empty(b"interrupt-controller")
                    d.add_property(b"compatible", b"riscv,cpu-intc")
        with d.begin_node(b"memory@80000000"):
            d.add_property(b"device_type", b"memory")
            d.add_property_u32_list(b"reg", [0, 0x80000000, 0, 0x4000000])
        with d.begin_node(b"soc"):
            d.add_property_u32(b"#address-cells", 2)
            d.add_property_u32(b"#size-cells", 2)
            d.add_property_list(b"compatible", [b"ucbbar,spike-bare-soc", b"simple-bus"])
            d.add_property_empty(b"ranges")
            with d.begin_node("clint@2000000"):
                d.add_property(b"compatible", b"riscv,clint0")
                d.add_property_u32_list(b"interrupts-extended", [CPU0_intc, 3, CPU0_intc, 7])
                d.add_property_u32_list(b"reg", [0, 0x2000000, 0, 0xc0000])
        with d.begin_node("htif"):
                d.add_property(b"compatible", b"ucb,htif0")
    res = d.to_binary()
    with open("riscv/input/rv64-64mb.dtb", "rb") as f:
        target = f.read()
    assert res == target

