../artifact/pypy-pydrofoil-scripting-experimental/bin/pypy3 build_ext.py 
gcc -pthread -DNDEBUG -O2 -fPIC -I../artifact/pypy-pydrofoil-scripting-experimental/include/pypy3.11 -c _pydrofoilcapi_cffi.c -o ./_pydrofoilcapi_cffi.o
gcc -pthread -shared -Wl,-Bsymbolic-functions ./_pydrofoilcapi_cffi.o -L../artifact/pypy-pydrofoil-scripting-experimental/bin -L../artifact/pypy-pydrofoil-scripting-experimental/pypy/goal -lpypy3.11-c -o ./_pydrofoilcapi_cffi.so
gcc -pthread -I../artifact/pypy-pydrofoil-scripting-experimental/include/pypy3.11/ -Wl,-Bsymbolic-functions testmain.c ./_pydrofoilcapi_cffi.c -L ../artifact/pypy-pydrofoil-scripting-experimental/bin  -l pypy3.11-c -o testplugin
LD_LIBRARY_PATH=.:../artifact/pypy-pydrofoil-scripting-experimental/bin ./testplugin ../riscv/input/rv64ui-p-addi.elf 10

