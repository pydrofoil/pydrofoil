RPYTHON_DIR ?= pypy/rpython


ALL: pydrofoil-riscv


pydrofoil-riscv: pypy_binary/bin/python pypy/rpython/bin/rpython ## Build pydrofoil
	PYTHONPATH=. pypy_binary/bin/python ${RPYTHON_DIR}/bin/rpython -Ojit --output=pydrofoil-riscv riscv/targetriscv.py

pypy_binary/bin/python:  ## download a PyPy binary
	wget -c https://downloads.python.org/pypy/pypy2.7-v7.3.10-linux64.tar.bz2 -O pypy-v7.3.10.tar.bz2
	mkdir -p pypy_binary
	tar -C pypy_binary --strip-components=1 -xf pypy-v7.3.10.tar.bz2
	rm pypy-v7.3.10.tar.bz2
	./pypy_binary/bin/python -m ensurepip
	./pypy_binary/bin/python -mpip install rply "hypothesis<4.40"

pypy/rpython/bin/rpython: ## clone the submodule
	git submodule update --init --depth 1

pydrofoil-test: pypy_binary/bin/python pypy/rpython/bin/rpython ## Run the pydrofoil implementation-level unit tests
	./pypy_binary/bin/python pypy/pytest.py -v pydrofoil/ riscv/

riscv-tools/bin/riscv64-unknown-linux-gnu-gcc:  ## get the riscv-toolchain for Ubuntu 20.04
	wget https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2022.11.18/riscv64-glibc-ubuntu-20.04-nightly-2022.11.18-nightly.tar.gz -o riscv64-nightly.tar.gz
	mkdir riscv-tools
	tar -C riscv-tools --strip-components=1 -xf risc64-nightly.tar.gz
	## Delete the tarball ???


riscv-tests/isa/rv64ua-p-amominu_w: riscv-tools/bin/riscv64-unknown-linux-gnu-gcc  pydrofoil-riscv
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

regen-sail-ir-files: ## regenerate the JIB IR files from a RISC-V Sail model, needs env variable RISCVMODELCHECKOUT set
ifndef RISCVMODELCHECKOUT
	$(error RISCVMODELCHECKOUT not set)
endif
	@# this is not great. ideally the sail model Makefile would have a
	@# target that generates the JIB files
	cd $(RISCVMODELCHECKOUT) && \
		sail -dno_cast -O -Oconstant_fold -memo_z3 -ir -c_include riscv_prelude.h -c_include riscv_platform.h -c_no_main model/prelude.sail model/prelude_mapping.sail model/riscv_xlen64.sail model/riscv_flen_D.sail model/prelude_mem_metadata.sail model/prelude_mem.sail model/riscv_types_common.sail model/riscv_types_ext.sail model/riscv_types.sail model/riscv_vmem_types.sail model/riscv_reg_type.sail model/riscv_freg_type.sail model/riscv_regs.sail model/riscv_pc_access.sail model/riscv_sys_regs.sail model/riscv_pmp_regs.sail model/riscv_pmp_control.sail model/riscv_ext_regs.sail model/riscv_addr_checks_common.sail model/riscv_addr_checks.sail model/riscv_misa_ext.sail model/riscv_csr_map.sail model/riscv_next_regs.sail model/riscv_sys_exceptions.sail model/riscv_sync_exception.sail model/riscv_next_control.sail model/riscv_softfloat_interface.sail model/riscv_fdext_regs.sail model/riscv_fdext_control.sail model/riscv_csr_ext.sail model/riscv_sys_control.sail model/riscv_platform.sail model/riscv_mem.sail model/riscv_pte.sail model/riscv_ptw.sail model/riscv_vmem_common.sail model/riscv_vmem_tlb.sail model/riscv_vmem_sv39.sail model/riscv_vmem_sv48.sail model/riscv_vmem_rv64.sail model/riscv_types_kext.sail model/riscv_insts_begin.sail model/riscv_insts_base.sail model/riscv_insts_aext.sail model/riscv_insts_cext.sail model/riscv_insts_mext.sail model/riscv_insts_zicsr.sail model/riscv_insts_next.sail model/riscv_insts_hints.sail model/riscv_insts_fext.sail model/riscv_insts_cfext.sail model/riscv_insts_dext.sail model/riscv_insts_cdext.sail model/riscv_insts_zba.sail model/riscv_insts_zbb.sail model/riscv_insts_zbc.sail model/riscv_insts_zbs.sail model/riscv_insts_zfh.sail model/riscv_insts_zkn.sail model/riscv_insts_zks.sail model/riscv_insts_zbkb.sail model/riscv_insts_zbkx.sail model/riscv_jalr_seq.sail model/riscv_insts_end.sail model/riscv_step_common.sail model/riscv_step_ext.sail model/riscv_decode_ext.sail model/riscv_fetch.sail model/riscv_step.sail model/riscv_analysis.sail model/main.sail -o ${PWD}/riscv/riscv_model_RV64 && \
		sail -dno_cast -O -Oconstant_fold -memo_z3 -ir -c_include riscv_prelude.h -c_include riscv_platform.h -c_no_main model/prelude.sail model/prelude_mapping.sail model/riscv_xlen32.sail model/riscv_flen_D.sail model/prelude_mem_metadata.sail model/prelude_mem.sail model/riscv_types_common.sail model/riscv_types_ext.sail model/riscv_types.sail model/riscv_vmem_types.sail model/riscv_reg_type.sail model/riscv_freg_type.sail model/riscv_regs.sail model/riscv_pc_access.sail model/riscv_sys_regs.sail model/riscv_pmp_regs.sail model/riscv_pmp_control.sail model/riscv_ext_regs.sail model/riscv_addr_checks_common.sail model/riscv_addr_checks.sail model/riscv_misa_ext.sail model/riscv_csr_map.sail model/riscv_next_regs.sail model/riscv_sys_exceptions.sail model/riscv_sync_exception.sail model/riscv_next_control.sail model/riscv_softfloat_interface.sail model/riscv_fdext_regs.sail model/riscv_fdext_control.sail model/riscv_csr_ext.sail model/riscv_sys_control.sail model/riscv_platform.sail model/riscv_mem.sail model/riscv_pte.sail model/riscv_ptw.sail model/riscv_vmem_common.sail model/riscv_vmem_tlb.sail model/riscv_vmem_sv32.sail model/riscv_vmem_rv32.sail model/riscv_types_kext.sail model/riscv_insts_begin.sail model/riscv_insts_base.sail model/riscv_insts_aext.sail model/riscv_insts_cext.sail model/riscv_insts_mext.sail model/riscv_insts_zicsr.sail model/riscv_insts_next.sail model/riscv_insts_hints.sail model/riscv_insts_fext.sail model/riscv_insts_cfext.sail model/riscv_insts_dext.sail model/riscv_insts_cdext.sail model/riscv_insts_zba.sail model/riscv_insts_zbb.sail model/riscv_insts_zbc.sail model/riscv_insts_zbs.sail model/riscv_insts_zfh.sail model/riscv_insts_zkn.sail model/riscv_insts_zks.sail model/riscv_insts_zbkb.sail model/riscv_insts_zbkx.sail model/riscv_jalr_seq.sail model/riscv_insts_end.sail model/riscv_step_common.sail model/riscv_step_ext.sail model/riscv_decode_ext.sail model/riscv_fetch.sail model/riscv_step.sail model/main.sail -o ${PWD}/riscv/riscv_model_RV32

help:   ## Show this help.
	@echo "\nHelp for various make targets"
	@echo "Possible commands are:"
	@grep -h "##" $(MAKEFILE_LIST) | grep -v grep | sed -e 's/\(.*\):.*##\(.*\)/    \1: \2/'
