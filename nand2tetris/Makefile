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
	$(SAIL) -O -memo_z3 -c_no_main -c nand2tetris.sail 1> $@

nand2tetris.jib: nand2tetris.sail Makefile
	$(SAIL) -O -memo_z3 -c_no_main -ir nand2tetris.sail 1> $@

C_WARNINGS=-Wall -Wno-unused-but-set-variable -Wno-unused-label -Wno-unused-function -Wno-maybe-uninitialized
C_OPT=-O2
GCOV_FLAGS=
nand2tetris_c: nand2tetris.c nandsupport.c $(SAIL_LIB_DIR)/sail.h $(SAIL_LIB_DIR)/*.c Makefile
	gcc $(C_OPT) $(C_WARNINGS) $(GCOV_FLAGS) -g -I $(SAIL_LIB_DIR) nandsupport.c $< $(SAIL_LIB_DIR)/*.c -lgmp -lz -o $@


