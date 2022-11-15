RPYTHON_DIR ?= pypy/rpython


ALL: pydrofoil-riscv64


pydrofoil-riscv64: venv_riscv/bin/python
	PYTHONPATH=. venv_riscv/bin/python ${RPYTHON_DIR}/bin/rpython -Ojit --output=pydrofoil-riscv64 riscv/targetriscv.py

venv_riscv/bin/python:  ## create a virtualenv
	@virtualenv -p python2 ./venv_riscv
	@venv_riscv/bin/python -mpip install rply


