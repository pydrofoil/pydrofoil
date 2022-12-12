# Building Pydrofoil from source

On this page we'll describe how to build or download a Pydrofoil binary.

## Requirements

So far, Pydrofoil is only properly supported on Linux and WSL, on x86-64 host
CPUs. macOS and ARM host support is planned, but not yet ready.

To build Pydrofoil, you need a working C-compiler (gcc or clang) installed, as
well as GNU Make. You also need Sail installed to be able to work on the
Sail model itself. [At the
moment](https://github.com/pydrofoil/pydrofoil/issues/31) Pydrofoil only works
with Sail 0.14, but we are working on 0.15 support. All the other Pydrofoil
requirements are downloaded automatically by the build scripts/Makefile.

## Starting from a Sail-riscv checkout

If you already have a checkout of the [Sail-RISC-V
model](https://github.com/riscv/sail-riscv) there is a script that you can use
to download all the requirements for building Pydrofoil and then start the build
process. It works like this:

```
git clone https://github.com/riscv/sail-riscv.git # or use your existing checkout
cd sail-riscv
wget https://raw.githubusercontent.com/pydrofoil/pydrofoil/one-stop-build-script/build-pydrofoil-from-sail.sh
bash build-pydrofoil-from-sail.sh
building pydrofoil binary, takes about 20 min
... lots of output
```

After about 20 minutes, the binary `pydrofoil-riscv` is generated, you can test
that it worked like this:

```
./pydrofoil-riscv test/riscv-tests/rv64ui-p-beq.elf
tohost located at 0x80001000
entrypoint 0x80000000
CSR mstatus <- 0x0000000A00000000 (input: 0x0000000000000000)
SUCCESS
Instructions: 305
Total time (s): 0.000361
Perf: 844.397835 Kips
```

[See here](using_pydrofoil.md) for more instructions on how to use Pydrofoil.


## If you are working on Pydrofoil itself

If you are interested in working on Pydrofoil itself, please read the
instructions on the page [Developing Pydrofoil](developing_pydrofoil.md).
