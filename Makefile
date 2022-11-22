RPYTHON_DIR ?= pypy/rpython


ALL: pydrofoil-riscv64


pydrofoil-riscv64: venv_riscv/bin/python pypy/rpython/bin/rpython ## Build pydrofoil
	PYTHONPATH=. venv_riscv/bin/python ${RPYTHON_DIR}/bin/rpython -Ojit --output=pydrofoil-riscv64 riscv/targetriscv.py

venv_riscv/bin/python:  ## create a virtualenv
	@virtualenv -p python2 ./venv_riscv
	@venv_riscv/bin/python -mpip install rply "hypothesis<4.40"

pypy/rpython/bin/rpython: ## clone the submodule
	git submodule update --init --depth 1

help:   ## Show this help.
	@echo "\nHelp for various make targets"
	@echo "Possible commands are:"
	@grep -h "##" $(MAKEFILE_LIST) | grep -v grep | sed -e 's/\(.*\):.*##\(.*\)/    \1: \2/'
 

riscv-tools/bin/riscv64-unknown-linux-gnu-gcc:  ## get the riscv-toolchain for Ubuntu 20.04
	wget https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2022.11.18/riscv64-glibc-ubuntu-20.04-nightly-2022.11.18-nightly.tar.gz -o riscv64-nightly.tar.gz
	mkdir riscv-tools
	tar -C riscv-tools --strip-components=1 -xf risc64-nightly.tar.gz
	## Delete the tarball ???


riscv-tests/isa/rv64ua-p-amominu_w: riscv-tools/bin/riscv64-unknown-linux-gnu-gcc  pydrofoil-riscv64 
	# Patch the Makefile in isa to use lp64d
	sed -i -e "s/\<lp64\>/lp64d/" riscv-tests/isa/Makefile
	# Patch the Makefile in isa to skip 32-bit tests, 
	# lines with 
	# $(eval $(call compile_template,.* -mabi=ilp32))
	# should be commented out
	export PATH=${PWD}/riscv-tools/bin:${PATH} && \
	export RISCV_PREFIX=riscv64-unknown-linux-gnu- && \
	cd riscv-tests && autoconf && ./configure && make isa

riscv-tests: riscv-tests/isa/rv64ua-p-amominu_w  ## build the riscv-tests/isa exectuables using a cross-compiler
	./run_tests.sh

riscv-tests-clean:
	cd riscv-tests && make clean
