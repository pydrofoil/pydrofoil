# Developing Pydrofoil

This page collects instructions on how various things work when you want to work
on Pydrofoil itself.

To get started, you should clone the Pydrofoil repository:

```
git clone https://github.com/pydrofoil/pydrofoil.git
```

## Building Pydrofoil emulator binary

To build the Pydrofoil emulator binary you can run:

```
make pydrofoil-riscv
```

And for the rest of the story:

Pydrofoil uses three inputs:
- A SAIL IR file that describes the RISC-V architecture, automatically generated
  from the Sail model of RISC-V.
- A checkout of the Pydrofoil repo, which contains source code in RPython to
  build an emulator around the IR file.
- A RPython tool chain that will compile the emulator code and produce an
  executable.

If you modify the RISC-V description file, you must rebuild the emulator
executable.

There is a Makefile in the root of the repo that will rebuild the emulator:
- Get a PyPy2.7 binary in order to run the RPython code
- Get the RPython toolchain from https://github.com/mozillazg/pypy, which is a git mirror of the [upstream mercurial PyPy repo](https://foss.heptapod.net/pypy/pypy).
- Build the emulator

This is done via `make pydrofoil-riscv`. At the moment the Makefile and the
build scripts officially support x86-64 Linux. But we have gotten reports that
it also works on Mac OS, on Windows using WSL, and AArch64 Linux. It should be
possible to get this to work on any platform [supported by
PyPy](https://www.pypy.org/features.html).


## Running unit tests

Pydrofoil has a number of unit tests to check the correct behaviour of its
bitvector implementation and the rest of its support code. Those can be run
with:

```
make pydrofoil-test
```
