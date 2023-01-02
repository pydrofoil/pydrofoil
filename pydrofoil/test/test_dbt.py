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
    d.add_property("#address-cells", b"\x00\x00\x00\x02")
    assert b"".join(d._properties) == (
        b"\x00\x00\x00\x03" # PROP
        b"\x00\x00\x00\x04" # length of payload
        b"\x00\x00\x00\x00" # string offset
        b"\x00\x00\x00\x02" # payload
    )
    assert d._strings == b"#address-cells\x00"

def test_devicetree_property_u32():
    d = DeviceTree()
    d.add_property_u32("#address-cells", 2)
    assert b"".join(d._properties) == (
        b"\x00\x00\x00\x03" # PROP
        b"\x00\x00\x00\x04" # length of payload
        b"\x00\x00\x00\x00" # string offset
        b"\x00\x00\x00\x02" # payload
    )
    assert d._strings == b"#address-cells\x00"

def test_devicetree_node():
    d = DeviceTree()
    with d.begin_node("cpus") as n:
        d.add_property_u32("#address-cells", 1)
        d.add_property_u32("#size-cells", 0)
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

def test_header():
    d = DeviceTree()
    with d.begin_node(""):
        d.add_property_u32("#address-cells", 2)
        d.add_property_u32("#size-cells", 2)
        with d.begin_node("cpus"):
            d.add_property_u32("#address-cells", 1)
            d.add_property_u32("#size-cells", 0)
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



