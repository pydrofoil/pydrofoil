import cffi
ffibuilder = cffi.FFI()


# steps:
# download artifact.zip from github to pydrofoil/ folder and unzip it
# then run build.sh

with open('pydrofoilcapi.h') as f:
    # read .h and pass it to embedding_api(), manually
    # removing the '#' directives
    data = ''.join([line for line in f if not line.startswith('#')])
    data = data.replace('CFFI_DLLEXPORT', '')
    ffibuilder.embedding_api(data)

ffibuilder.set_source("_pydrofoilcapi_cffi", r'''
    #include "pydrofoilcapi.h"
''')

with open("gluecode.py") as f:
    gluecode = f.read()

ffibuilder.embedding_init_code(gluecode)

ffibuilder.emit_c_code("_pydrofoilcapi_cffi.c")
