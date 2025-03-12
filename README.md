# Fast Sail emulation using PyPy/RPython's JIT compiler


[![CI Status](https://github.com/pydrofoil/pydrofoil/actions/workflows/pydrofoil.yml/badge.svg)](https://github.com/pydrofoil/pydrofoil/actions/workflows/pydrofoil.yml)
[![Documentation Status](https://readthedocs.org/projects/pydrofoil/badge/?version=latest)](https://docs.pydrofoil.org/en/latest/?badge=latest)

This repository contains Pydrofoil, an experimental emulator for various
instruction set architectures. The best tested one is a RISC-V emulator based
on the [Sail RISC-V ISA model](https://github.com/riscv/sail-riscv). It
achieves fast performance by doing dynamic binary translation (aka just-in-time
compilation) from RISC-V guest instructions into host machine instructions.
It's built on top of the [RPython meta-jit
compiler](https://www3.hhu.de/stups/downloads/pdf/BoCuFiRi09_246.pdf) and
reuses all its optimizations, backends, etc. The emulator is complete enough to
[boot](https://docs.pydrofoil.org/en/latest/using_pydrofoil.html#booting-linux-under-pydrofoil)
(an old version of) Linux up to the login prompt.

It also contains an even more experimental emulator for Aarch64 version 9.4,
based on the [Sail ARM ISA model](https://github.com/rems-project/sail-arm),
which is itself [automatically
generated](https://github.com/rems-project/asl_to_sail) from the
[ASL](https://developer.arm.com/downloads/-/exploration-tools) code that ARM
provides. Booting Linux on that emulator [is
possible](https://docs.pydrofoil.org/en/latest/arm.html#booting-linux), at least
up to the point where the init process starts.

The most recent ISA that is experimentally supported is
[CHERIoT](https://cheriot.org/), a variant of the 32-bit CHERI-RISC-V ISA aimed
at supporting secure IoT devices.

See https://docs.pydrofoil.org for the complete documentation
