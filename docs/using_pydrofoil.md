# Using pydrofoil

## Testing compiled RISCV executables

Pydrofoil accepts a compiled RISCV exectuable and will run it. Typically, the
source code of the executable will test some RISCV feature and report
success/failure.

```
$ ./pydrofoil-riscv riscv/input/rv64ui-p-addi.elf 
tohost located at 0x80001000
entrypoint 0x80000000
CSR mstatus <- 0x0000000A00000000 (input: 0x0000000000000000)
SUCCESS
Instructions: 259
Total time (s): 0.000712
Perf: 363.806007 Kips
```

## Booting linux under pydrofoil

This is an example of how to boot a linux kernel using the pdrofoil emulator

`./pydrofoil-riscv -b riscv/input/rv64-64mb.dtb riscv/input/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl -l 230000000`
