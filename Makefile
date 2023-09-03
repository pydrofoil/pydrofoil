RPYTHON_DIR ?= pypy/rpython

ALL: pydrofoil-riscv

## RISC-V targets:

pydrofoil-riscv: pypy_binary/bin/python pypy/rpython/bin/rpython pydrofoil/softfloat/SoftFloat-3e/build/Linux-RISCV-GCC/softfloat.o ## Build the pydrofoil RISC-V emulator
	pkg-config libffi # if this fails, libffi development headers arent installed
	PYTHONPATH=. pypy_binary/bin/python ${RPYTHON_DIR}/bin/rpython -Ojit --output=pydrofoil-riscv riscv/targetriscv.py

pydrofoil-test: pypy_binary/bin/python pypy/rpython/bin/rpython pydrofoil/softfloat/SoftFloat-3e/build/Linux-RISCV-GCC/softfloat.o ## Run the pydrofoil implementation-level unit tests
	./pypy_binary/bin/python pypy/pytest.py -v pydrofoil/ riscv/

.PHONY: riscv-tests
riscv-tests: pypy_binary/bin/python pydrofoil-riscv  ## Run risc-v test suite, needs env variable RISCVMODELCHECKOUT set
ifndef RISCVMODELCHECKOUT
	$(error RISCVMODELCHECKOUT not set)
endif
	./pypy_binary/bin/python run_riscv_tests.py

.PHONY: regen-sail-ir-files
regen-sail-ir-files: isla/isla-sail/plugin.cmxs ## Regenerate the JIB IR files from a RISC-V Sail model, needs env variable RISCVMODELCHECKOUT set
ifndef RISCVMODELCHECKOUT
	$(error RISCVMODELCHECKOUT not set)
endif
	@# this is not great. ideally the sail model Makefile would have a
	@# target that generates the JIB files
	PATH=${realpath isla/isla-sail/}:${PATH} && export PATH && eval `opam config env --switch=sail/ --set-switch` && cd $(RISCVMODELCHECKOUT) && \
		isla-sail -dno_cast -O -Oconstant_fold -memo_z3 -c_include riscv_prelude.h -c_include riscv_platform.h -c_no_main \
		model/prelude.sail \
		model/prelude_mapping.sail \
		model/riscv_xlen64.sail \
		model/riscv_flen_D.sail \
		model/prelude_mem_metadata.sail \
		model/prelude_mem.sail \
		model/riscv_types_common.sail \
		model/riscv_types_ext.sail \
		model/riscv_types.sail \
		model/riscv_vmem_types.sail \
		model/riscv_reg_type.sail \
		model/riscv_freg_type.sail \
		model/riscv_regs.sail \
		model/riscv_pc_access.sail \
		model/riscv_sys_regs.sail \
		model/riscv_pmp_regs.sail \
		model/riscv_pmp_control.sail \
		model/riscv_ext_regs.sail \
		model/riscv_addr_checks_common.sail \
		model/riscv_addr_checks.sail \
		model/riscv_misa_ext.sail \
		model/riscv_csr_map.sail \
		model/riscv_next_regs.sail \
		model/riscv_sys_exceptions.sail \
		model/riscv_sync_exception.sail \
		model/riscv_next_control.sail \
		model/riscv_softfloat_interface.sail \
		model/riscv_fdext_regs.sail \
		model/riscv_fdext_control.sail \
		model/riscv_csr_ext.sail \
		model/riscv_sys_control.sail \
		model/riscv_platform.sail \
		model/riscv_mem.sail \
		model/riscv_pte.sail \
		model/riscv_ptw.sail \
		model/riscv_vmem_common.sail \
		model/riscv_vmem_tlb.sail \
		model/riscv_vmem_sv39.sail \
		model/riscv_vmem_sv48.sail \
		model/riscv_vmem_rv64.sail \
		model/riscv_types_kext.sail \
		model/riscv_insts_begin.sail \
		model/riscv_insts_base.sail \
		model/riscv_insts_aext.sail \
		model/riscv_insts_cext.sail \
		model/riscv_insts_mext.sail \
		model/riscv_insts_zicsr.sail \
		model/riscv_insts_next.sail \
		model/riscv_insts_hints.sail \
		model/riscv_insts_fext.sail \
		model/riscv_insts_cfext.sail \
		model/riscv_insts_dext.sail \
		model/riscv_insts_cdext.sail \
		model/riscv_insts_zba.sail \
		model/riscv_insts_zbb.sail \
		model/riscv_insts_zbc.sail \
		model/riscv_insts_zbs.sail \
		model/riscv_insts_zfh.sail \
		model/riscv_insts_zfa.sail \
		model/riscv_insts_zkn.sail \
		model/riscv_insts_zks.sail \
		model/riscv_insts_zbkb.sail \
		model/riscv_insts_zbkx.sail \
		model/riscv_insts_zicond.sail \
		model/riscv_jalr_seq.sail \
		model/riscv_insts_end.sail \
		model/riscv_step_common.sail \
		model/riscv_step_ext.sail \
		model/riscv_decode_ext.sail \
		model/riscv_fetch.sail \
		model/riscv_step.sail \
		model/riscv_analysis.sail \
		model/main.sail \
		-o ${PWD}/riscv/riscv_model_RV64 \
		&& \
		${PWD}/isla/isla-sail/isla-sail -dno_cast -O -Oconstant_fold -memo_z3 -c_include riscv_prelude.h -c_include riscv_platform.h -c_no_main \
		model/prelude.sail \
		model/prelude_mapping.sail \
		model/riscv_xlen32.sail \
		model/riscv_flen_D.sail \
		model/prelude_mem_metadata.sail \
		model/prelude_mem.sail \
		model/riscv_types_common.sail \
		model/riscv_types_ext.sail \
		model/riscv_types.sail \
		model/riscv_vmem_types.sail \
		model/riscv_reg_type.sail \
		model/riscv_freg_type.sail \
		model/riscv_regs.sail \
		model/riscv_pc_access.sail \
		model/riscv_sys_regs.sail \
		model/riscv_pmp_regs.sail \
		model/riscv_pmp_control.sail \
		model/riscv_ext_regs.sail \
		model/riscv_addr_checks_common.sail \
		model/riscv_addr_checks.sail \
		model/riscv_misa_ext.sail \
		model/riscv_csr_map.sail \
		model/riscv_next_regs.sail \
		model/riscv_sys_exceptions.sail \
		model/riscv_sync_exception.sail \
		model/riscv_next_control.sail \
		model/riscv_softfloat_interface.sail \
		model/riscv_fdext_regs.sail \
		model/riscv_fdext_control.sail \
		model/riscv_csr_ext.sail \
		model/riscv_sys_control.sail \
		model/riscv_platform.sail \
		model/riscv_mem.sail \
		model/riscv_pte.sail \
		model/riscv_ptw.sail \
		model/riscv_vmem_common.sail \
		model/riscv_vmem_tlb.sail \
		model/riscv_vmem_sv32.sail \
		model/riscv_vmem_rv32.sail \
		model/riscv_types_kext.sail \
		model/riscv_insts_begin.sail \
		model/riscv_insts_base.sail \
		model/riscv_insts_aext.sail \
		model/riscv_insts_cext.sail \
		model/riscv_insts_mext.sail \
		model/riscv_insts_zicsr.sail \
		model/riscv_insts_next.sail \
		model/riscv_insts_hints.sail \
		model/riscv_insts_fext.sail \
		model/riscv_insts_cfext.sail \
		model/riscv_insts_dext.sail \
		model/riscv_insts_cdext.sail \
		model/riscv_insts_zba.sail \
		model/riscv_insts_zbb.sail \
		model/riscv_insts_zbc.sail \
		model/riscv_insts_zbs.sail \
		model/riscv_insts_zfh.sail \
		model/riscv_insts_zfa.sail \
		model/riscv_insts_zkn.sail \
		model/riscv_insts_zks.sail \
		model/riscv_insts_zbkb.sail \
		model/riscv_insts_zbkx.sail \
		model/riscv_insts_zicond.sail \
		model/riscv_jalr_seq.sail \
		model/riscv_insts_end.sail \
		model/riscv_step_common.sail \
		model/riscv_step_ext.sail \
		model/riscv_decode_ext.sail \
		model/riscv_fetch.sail \
		model/riscv_step.sail \
		model/main.sail \
		-o ${PWD}/riscv/riscv_model_RV32 && \
		git describe --long --dirty --abbrev=10 --always --tags --first-parent > ${PWD}/riscv/riscv_model_version

pydrofoil/softfloat/SoftFloat-3e/build/Linux-RISCV-GCC/softfloat.o: ## Build the softfloat library
	make -C pydrofoil/softfloat/SoftFloat-3e/build/Linux-RISCV-GCC/ softfloat.o

## ARM model targets

pydrofoil-arm: pypy_binary/bin/python pypy/rpython/bin/rpython arm/armv9.ir ## Build the Pydrofoil ARM emulator
	PYTHONPATH=. pypy_binary/bin/python ${RPYTHON_DIR}/bin/rpython -Ojit --translation-withsmallfuncsets=0 --translation-jit_opencoder_model=big --output=pydrofoil-arm arm/targetarm.py

sail-arm/arm-v9.3-a/src/v8_base.sail: ## Clone the sail-arm submodule
	git submodule update --init --depth 1

.PHONY: regen-arm-ir-files
regen-arm-ir-files: sail-arm/arm-v9.3-a/src/v8_base.sail isla/isla-sail/plugin.cmxs ## Build arm IR
	PATH=${realpath isla/isla-sail/}:${PATH} && export PATH && eval `opam config env --switch=sail/ --set-switch` &&  make -C sail-arm/arm-v9.3-a/ gen_ir
	mv sail-arm/arm-v9.3-a/ir/armv9.ir arm/


## Housekeeping targets:

pypy_binary/bin/python:  ## Download a PyPy binary
	mkdir -p pypy_binary
	python3 get_pypy_to_download.py
	tar -C pypy_binary --strip-components=1 -xf pypy.tar.bz2
	rm pypy.tar.bz2
	./pypy_binary/bin/python -m ensurepip
	./pypy_binary/bin/python -mpip install rply "hypothesis<4.40" junit_xml

pypy/rpython/bin/rpython: ## Clone the PyPy submodule
	git submodule update --init --depth 1

isla/isla-sail/Makefile: ## Clone the isla submodule
	git submodule update --init --depth 1

sail/libsail.opam: ## Clone the sail submodule
	git submodule update --init --depth 1

sail/_opam/bin/sail: sail/libsail.opam ## Build sail switch
	opam switch create sail/ -y

isla/isla-sail/plugin.cmxs: sail/_opam/bin/sail isla/isla-sail/Makefile ## build isla-sail
	eval `opam config env --switch=sail/ --set-switch` && cd isla/isla-sail && $(MAKE)


## Other

.PHONY: clean
clean:  ## remove build artifacts.
	@# Sync with .gitignore. Could be done via git clean -xfdd ?
	rm -rf usession*
	rm -rf docs/_build
	rm -rf pypy_binary
	rm -rf pydrofoil-riscv-tests.xml
	make -C pydrofoil/softfloat/SoftFloat-3e/build/Linux-RISCV-GCC/ clean
	rm -rf pydrofoil-arm

help:   ## Show this help.
	@echo "\nHelp for various make targets"
	@echo "Possible commands are:"
	@echo
	@grep -h "##" $(MAKEFILE_LIST) | grep -v grep | sed -e 's/\(.*\):.*##\(.*\)/    \1: \2/'

