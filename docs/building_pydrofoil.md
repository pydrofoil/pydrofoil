# Building pydrofoil from source

TL;DR: run `make pydrofoil-riscv`.

And for the rest of the story:

Pydrofoil uses three inputs: 
- A SAIL IR file that describes the RISCV archtecture, in the JIB format
- A checkout of the pydrosail repo, which contains source code in RPython to
  build an emulator around the IR file.
- A RPython tool chain that will compile the emulator code and produce an
  executable.

If you modify the RISCV description file, you must rebuild the emulator
executable.

There is a Makefile in the root of the repo that will rebuild the emulator:
- Get a pypy2.7 in order to run the RPython code
- Get a rpython toolchain from https://github.com/mozillazg/pypy, which is a git mirror of the upstream mercurial PyPy repo.
- Build the emulator `

This is done via `make pydrofoil-riscv`. This should run on any platform [supported by PyPy](https://www.pypy.org/features.html), we test x86_64 linux in CI.
