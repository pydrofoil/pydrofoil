#! /bin/bash

set -xeo pipefail

git reset --hard

patch -p1 < ablate/bv-int-opt.patch
patch -p1 < ablate/spec-inline.patch
patch -p1 < ablate/no-static-ir-opt.patch
PYTHONPATH=. pypy_binary/bin/python pypy2/rpython/bin/rpython -Ojit --output=pydrofoil-riscv-ablation-07-no-opt-but-jit riscv/targetriscv.py
