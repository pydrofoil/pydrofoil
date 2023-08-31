# Building Pydrofoil from source

On this page we'll describe how to build or download a Pydrofoil binary.

## Requirements

Pydrofoil has been extensively tested on Ubuntu Linux on x86-64 host systems.
It should also work on WSL and on macOS (with x86-64 and ARM CPUs).

To build Pydrofoil, you need the following software installed (if you are
working on the Sail model you likely have all of these already):

- a working C-compiler (gcc or clang) installed
- GNU Make
- git
- opam
- python3
- libffi and its development headers (package libffi-dev on Ubuntu)
- Sail (see next section).

On Ubuntu, you are able to install all of these with `apt` with the following
command:

```
sudo apt install build-essential git opam python3 libffi-dev
```

All the other Pydrofoil build requirements are downloaded automatically by the
build scripts/Makefile.

## Installing Sail

Pydrofoil needs a very recent unreleased version of Sail. Therefore the build
scripts will install it automatically in a local subdirectory. This will not
interfere with any existing sail installation you might have.

## Building Pydrofoil Starting from a Sail-riscv checkout

To build Pydrofoil, you first need to clone the [Sail-RISC-V
model](https://github.com/riscv/sail-riscv) repository. If you already have a
checkout, you can use that instead.

```
git clone https://github.com/riscv/sail-riscv.git # or use your existing checkout
cd sail-riscv
```

Afterwards, there is a script that you can use to download all the requirements
for building Pydrofoil and then start the build process. It works like this:

```
wget https://raw.githubusercontent.com/pydrofoil/pydrofoil/one-stop-build-script/build-pydrofoil-from-sail.sh
chmod a+x build-pydrofoil-from-sail.sh
./build-pydrofoil-from-sail.sh
```
This will
- clone the pydrofoil repo from github
- build a local switch with a recent enough sail binary, as well as isla-sail
- use isla-sail to translate the ISA specifications into JIB files (about 5
  minutes)
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

[See here](using_pydrofoil.md) for more instructions on how to **use Pydrofoil**,
including how to boot Linux.

If you are interested in working on Pydrofoil itself, please read the
instructions on the page [Developing Pydrofoil](developing_pydrofoil.md).
