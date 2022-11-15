#Fast RISC-V Sail emulation using PyPy/RPython's JIT compiler


[![CI status](https://github.com/pydrofoil/pydrofoil/actions/workflows/python-app.yml/badge.svg)](https://github.com/pydrofoil/pydrofoil/actions/workflows/python-app.yml)
[![Documentation Status](https://readthedocs.org/projects/pydrofoil/badge/?version=latest)](https://docs.pydrofoil.org/en/latest/?badge=latest)

This repository contains Pydrofoil, an experimental emulator for RISC-V based
on the [Sail RISC-V ISA model](https://github.com/riscv/sail-riscv). It
achieves fast performance by doing dynamic binary translation (aka just-in-time
compilation) from RISC-V guest instructions into host machine instructions.
It's built on top of the [RPython meta-jit
compiler](https://www3.hhu.de/stups/downloads/pdf/BoCuFiRi09_246.pdf) and
reuses all its optimizations, backends, etc.

##Getting Started

Clone the repo. Then run the top-level Makefile. Running `make pydrofoil will:
- Create a virtualenv with python2 (assuming your OS has `python2` and a
  system-level `virtualenv`
- Clone the pypy source code from a repo into a submodule, using `--depth 1` to
  save time and avoid cloning all the history
- Use the rpython toolchaing to build a pydrosail executable. This is time
  consuming, it could take up to 30 minutes.

```bash
$ make help

Help for various make targets
Possible commands are:
    pydrofoil-riscv64:  Build pydrofoil
    venv_riscv/bin/python:  create a virtualenv
    pypy/rpython/bin/rpython:  clone the submodule
    help:  Show this help.
```
