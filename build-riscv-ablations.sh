#! /bin/bash

set -xeo pipefail

git reset --hard

PYTHONPATH=. pypy_binary/bin/python pypy2/rpython/bin/rpython -Ojit --output=pydrofoil-riscv-ablation-00-baseline riscv/targetriscv.py


patch -p1 < ablate/mem.patch
PYTHONPATH=. pypy_binary/bin/python pypy2/rpython/bin/rpython -Ojit --output=pydrofoil-riscv-ablation-01-no-jit-immutability-tracking riscv/targetriscv.py
PYTHONPATH=. pypy_binary/bin/python pypy2/rpython/bin/rpython -O2 --output=pydrofoil-riscv-ablation-02-no-jit-at-all riscv/targetriscv.py

patch -p1 < ablate/bv-int-opt.patch
PYTHONPATH=. pypy_binary/bin/python pypy2/rpython/bin/rpython -O2 --output=pydrofoil-riscv-ablation-03-no-static-int-bv-opts riscv/targetriscv.py

patch -p1 < ablate/spec-inline.patch
PYTHONPATH=. pypy_binary/bin/python pypy2/rpython/bin/rpython -O2 --output=pydrofoil-riscv-ablation-04-no-spec-no-inline riscv/targetriscv.py

patch -p1 < ablate/no-static-ir-opt.patch
PYTHONPATH=. pypy_binary/bin/python pypy2/rpython/bin/rpython -O2 --output=pydrofoil-riscv-ablation-05-no-opt riscv/targetriscv.py

patch -p1 < ablate/no-small-integers.patch
PYTHONPATH=. pypy_binary/bin/python pypy2/rpython/bin/rpython -O2 --output=pydrofoil-riscv-ablation-06-no-runtime-smallint riscv/targetriscv.py
