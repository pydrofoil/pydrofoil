import gdb_pydrofoil
import pytest

def test_parse_gdb_packet():
    packet = b"$vMustReplyEmpty#3a"
    res = gdb_pydrofoil._parse_gdb_packet(packet)
    assert res.command == b"vMustReplyEmpty"

def test_parse_gdb_packet_checksum_wrong():
    packet = b"$vMustReplyEmpty#00"
    with pytest.raises(ValueError):
        gdb_pydrofoil._parse_gdb_packet(packet)