import string

def mangle(str_in):
    str_out = "z"
    for i in range(0, len(str_in)):
        c = ord(str_in[i])
        if c <= 41:
            str_out += "z"
            str_out += chr(c+16)
        elif c <= 47:
            str_out += "z"
            str_out += chr(c+23)
        elif c > 57 and c <= 64:
            str_out += "z"
            str_out += chr(c+13)
        elif (c > 90 and c <= 94) or c == 96:
            str_out += "z"
            str_out += chr(c-13)
        elif c == 0x7a:
            str_out += "zz"
        elif c > 122 and c <= 126:
            str_out += "z"
            str_out += chr(c-39)
        else:
            str_out += str_in[i]
    return str_out

def demangle(str_in):
    str_out = ""
    next_encoded = False
    for i in range(1, len(str_in)):
        c = ord(str_in[i])
        if next_encoded:
            if c <= 57:
                str_out += chr(c-16)
            elif c <= 70:
                str_out += chr(c-23)
            elif c <= 77:
                str_out += chr(c-13)
            elif c <= 83:
                str_out += chr(c+13)
            elif c == 122:
                str_out += chr(122)
            else:
                str_out += chr(c+39)
            next_encoded = False
        elif c == 0x7a:
            next_encoded = True
        else:
            str_out += str_in[i]
    return str_out