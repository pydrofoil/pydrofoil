# Building Pydrofoil from source

On this page we'll describe how to build or download a Pydrofoil binary.

## Requirements

So far, Pydrofoil is only properly supported on Linux and WSL, on x86-64 host
CPUs. macOS and ARM host support is planned, but not yet ready.

To build Pydrofoil, you need the following software installed:

- a working C-compiler (gcc or clang) installed
- GNU Make
- git
- Sail 0.14

If you are working on the Sail model you likely have all of these already.
[At the moment](https://github.com/pydrofoil/pydrofoil/issues/31) Pydrofoil
only works
with Sail 0.14, but we are working on 0.15 support. All the other Pydrofoil
build requirements are downloaded automatically by the build scripts/Makefile.

## Starting from a Sail-riscv checkout

If you already have a checkout of the [Sail-RISC-V
model](https://github.com/riscv/sail-riscv) there is a script that you can use
to download all the requirements for building Pydrofoil and then start the build
process. It works like this:

```bash
# get opam from apt, brew, or choco, and then get sail via "opam install sail.0.14"
git clone https://github.com/riscv/sail-riscv.git # or use your existing checkout
cd sail-riscv
wget https://raw.githubusercontent.com/pydrofoil/pydrofoil/one-stop-build-script/build-pydrofoil-from-sail.sh
chmod a+x build-pydrofoil-from-sail.sh
eval $(opam env)
./build-pydrofoil-from-sail.sh
```
This will
- clone the pydrofoil repo from github
- use sail version 0.14 to translate the ISA specifications into JIB files
  (about 5 minutes)
- download and use a pypy2.7 to translate the RPython-based pydrofoil source
  code into an executable (about 20 minutes)
- copy the executable into the sail-riscv directory

You can test that it worked like this:

```
./pydrofoil-riscv test/riscv-tests/rv64ui-p-beq.elf
```

Which should print:

```
tohost located at 0x80001000
entrypoint 0x80000000
CSR mstatus <- 0x0000000A00000000 (input: 0x0000000000000000)
SUCCESS
Instructions: 305
Total time (s): 0.000361
Perf: 844.397835 Kips
```

[See here](using_pydrofoil.md) for more instructions on how to use Pydrofoil,
including how to boot Linux.


## If you are working on Pydrofoil itself

If you are interested in working on Pydrofoil itself, please read the
instructions on the page [Developing Pydrofoil](developing_pydrofoil.md).
