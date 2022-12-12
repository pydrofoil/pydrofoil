#!/usr/bin/env bash

# this script can be used to build a jitted pydrofoil-riscv emulator from a
# checkout of the risc-v sail model. it takes care of everything, clones the
# necessary repos and downloads a pypy2 binary that is needed as part of the
# build process

if [ ! -d "pydrofoil" ]; then
  # Clone the repository if the directory does not exist
  git clone https://github.com/pydrofoil/pydrofoil
fi

echo "building pydrofoil binary, takes about 20 min" && \
    export RISCVMODELCHECKOUT=$PWD && \
    cd pydrofoil/ && \
    make regen-sail-ir-files && \
    make pydrofoil-riscv && \
    mv pydrofoil-riscv $RISCVMODELCHECKOUT/ && \
    cd - && \
    echo "DONE"
