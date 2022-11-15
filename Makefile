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
 
