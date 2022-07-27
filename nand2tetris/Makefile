# PyPy directory
ifeq ($(PYPY_DIR),)
PYPY_DIR:=../pypy
endif

# venv directory
ifeq ($(VENV_DIR),)
VENV_DIR:=../venv
VENVBIN_DIR:=$(VENV_DIR)/bin
endif

# Find necessary library paths for include files
LIB_ADDITIONAL_FLAGS:=$(shell pkg-config --cflags-only-I gmp z3)

#Attempt to work with either sail from opam or built from repo in SAIL_DIR
ifneq ($(SAIL_DIR),)
# Use sail repo in SAIL_DIR
SAIL:=$(SAIL_DIR)/sail
export SAIL_DIR
else
# Use sail from opam package
SAIL_DIR=$(shell opam config var sail:share)
SAIL:=sail
endif
SAIL_LIB_DIR:=$(SAIL_DIR)/lib


all: nand2tetris_c

nand2tetris.c: nand2tetris.sail Makefile
	$(SAIL) -O -memo_z3 -c_no_main -c nand2tetris.sail -c_include nandsupport.h 1> $@

nand2tetris.jib: nand2tetris.sail Makefile
	$(SAIL) -O -memo_z3 -c_no_main -ir nand2tetris.sail 1> $@

build: nand2tetris_c

clean:
	rm nand2tetris_c nand2tetris.c z3_problems

venv:
	virtualenv -p python2 $(VENV_DIR)
	$(VENVBIN_DIR)/pip install rply
	$(VENVBIN_DIR)/pip install pdbpp

C_WARNINGS=-Wall -Wno-unused-but-set-variable -Wno-unused-label -Wno-unused-function -Wno-maybe-uninitialized
C_OPT=-O2
GCOV_FLAGS=
nand2tetris_c: nand2tetris.c nandsupport.c $(SAIL_LIB_DIR)/sail.h $(SAIL_LIB_DIR)/*.c Makefile
	gcc $(C_OPT) $(C_WARNINGS) $(GCOV_FLAGS) -g -I $(SAIL_LIB_DIR) nandsupport.c $< $(SAIL_LIB_DIR)/*.c $(LIB_ADDITIONAL_FLAGS) -lgmp -lz -o $@

rpython_nandtest:
	PYTHONPATH=$(PYPY_DIR)/:../ $(VENVBIN_DIR)/python ../pydrofoil/test/targetnand.py input/Add.hack.bin 100 1

rpython_nandtest_to_c:
	PYTHONPATH=$(PYPY_DIR)/:../ $(VENVBIN_DIR)/python $(PYPY_DIR)/rpython/translator/goal/translate.py ../pydrofoil/test/targetnand.py

rpython_nandtest_c_call: targetnand-c
	./targetnand-c input/Add.hack.bin 100 1
