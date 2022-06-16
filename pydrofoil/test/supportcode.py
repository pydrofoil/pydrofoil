def my_read_rom(addr):
    l = [
    0b0000000000000010,
    0b1110110000010000,
    0b0000000000000011,
    0b1110000010010000,
    0b0000000000000000,
    0b1110001100001000,
    ]
    import pdb; pdb.set_trace()
    if addr < len(l):
        return l[addr]
    return 0
mem = [0] * 65536
def my_read_mem(addr):
    return mem[addr]
def my_write_mem(addr, val):
    mem[addr]=val
def not_(b):
    return not b
def and_bool(a, b):
    return not b
def my_print_debug(*args):
    print args

# generic helpers

def zero_extend(a, b):
    return a

def add_bits_int(a, b):
    return a.add(b)
