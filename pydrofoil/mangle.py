
def mangle(str_in):
    out = ["z"]
    for char in str_in:
        c = ord(char)
        if c <= 41:
            out.append("z")
            out.append(chr(c+16))
        elif c <= 47:
            out.append("z")
            out.append(chr(c+23))
        elif 57 < c <= 64:
            out.append("z")
            out.append(chr(c+13))
        elif 90 < c <= 94 or c == 96:
            out.append("z")
            out.append(chr(c-13))
        elif c == 0x7a:
            out.append("zz")
        elif 122 < c <= 126:
            out.append("z")
            out.append(chr(c-39))
        else:
            out.append(char)
    return "".join(out)

def demangle(str_in):
    out = []
    next_encoded = False
    for i in range(1, len(str_in)):
        c = ord(str_in[i])
        if next_encoded:
            if c <= 57:
                out.append(chr(c-16))
            elif c <= 70:
                out.append(chr(c-23))
            elif c <= 77:
                out.append(chr(c-13))
            elif c <= 83:
                out.append(chr(c+13))
            elif c == 122:
                out.append("z")
            else:
                out.append(chr(c+39))
            next_encoded = False
        elif c == 0x7a:
            next_encoded = True
        else:
            out.append(str_in[i])
    return "".join(out)