# Fast RISC-V Sail emulation using PyPy/RPython's JIT compiler


[![CI Status](https://github.com/pydrofoil/pydrofoil/actions/workflows/pydrofoil.yml/badge.svg)](https://github.com/pydrofoil/pydrofoil/actions/workflows/pydrofoil.yml)
[![Documentation Status](https://readthedocs.org/projects/pydrofoil/badge/?version=latest)](https://docs.pydrofoil.org/en/latest/?badge=latest)

This repository contains Pydrofoil, an experimental emulator for RISC-V based
on the [Sail RISC-V ISA model](https://github.com/riscv/sail-riscv). It
achieves fast performance by doing dynamic binary translation (aka just-in-time
compilation) from RISC-V guest instructions into host machine instructions.
It's built on top of the [RPython meta-jit
compiler](https://www3.hhu.de/stups/downloads/pdf/BoCuFiRi09_246.pdf) and
reuses all its optimizations, backends, etc.

See https://docs.pydrofoil.org for the complete documentation
