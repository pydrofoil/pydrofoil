# Using Pydrofoil

## Testing compiled RISC-V executables

Pydrofoil accepts a compiled RISC-V executable and will run it. Typically, the
source code of the executable will test some RISC-V feature and report
success/failure. It should work on the same ELF files that the standard
Sail-based emulator also accepts. The following example commands should be
executed from a sail-riscv checkout.

```
./pydrofoil-riscv test/riscv-tests/rv64ui-p-addi.elf
```

which will print:

```
tohost located at 0x80001000
entrypoint 0x80000000
CSR mstatus <- 0x0000000A00000000 (input: 0x0000000000000000)
SUCCESS
Instructions: 259
Total time (s): 0.000712
Perf: 363.806007 Kips
```

A Pydrofoil binary contains an emulator for the 64-bit and for the 32-bit
variants of the RISC-V model. By default, the 64-bit emulator is used. To chose
the 32-bit emulator, you can use the `--rv32` commandline option:

```
./pydrofoil-riscv --rv32 test/riscv-tests/rv32ui-p-addi.elf
```

which prints:

```
tohost located at 0x80001000
entrypoint 0x80000000
CSR mstatus <- 0x00000000 (input: 0x00000000)
SUCCESS
Instructions: 256
Total time (s): 0.001858
Perf: 137.782859 Kips
```


## Booting Linux under Pydrofoil

This is an example of how to boot a Linux kernel using the Pydrofoil emulator:

```
dtc < os-boot/rv64-64mb.dts > os-boot/rv64-64mb.dtb

./pydrofoil-riscv -b os-boot/rv64-64mb.dtb \
   os-boot/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl -l 230000000

```

This command will run the Linux image that is part of the sail-riscv repo until
the login prompt. The `dtb` file is a device tree blob that describes the
emulated hardware to the operating system, it gets generated from a
human-readable input file with the `dtc` command.  `dtc` is provided by `apt
install device-tree-compiler` on Ubuntu. The instruction limit of 230 million
instructions is chosen such that booting proceeds until the login prompt.

You can try the
equivalent command on the standard Sail emulator:

```
./c_emulator/riscv_sim_RV64 --show-times -b os-boot/rv64-64mb.dtb \
    os-boot/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl -l 230000000 -V
```

Booting Linux is about 18 times faster with Pydrofoil  and uses about 8 times
the memory when compared to the Sail emulator on the two Ubuntu x86_64 machines
we tried:

| x86_64 machine | Pydrofoil | Sail emulator | Ratio |
|---|---|---|---|
| laptop (i7-8565U) | 4min   | 75min      | 1:18.7  |
| Ryzen 9 3900X | 115sec | 34min36sec | 1:18.1 |
| <p style='text-align: right;'> RSS memory</p>   | 318MB  | 39MB       | 8:1 |


## Commandline Options

The `pydrofoil-riscv` binary accepts the following commandline options:

- `--rv32` run emulator in 32-bit mode (default: 64-bit)
- `-b/--device-tree-blob <file>` load [device tree blob](https://www.devicetree.org/) from `file`
- `-l/--inst-limit <limit>` stop execution after `limit` instructions (by
  default execution is only halted if a test is stopped via the htif device).
- `--instructions-per-tick <num>` tick the emulated clock every `num`
  instructions (default: 100).
- `--verbose` print a detailed trace of every instruction executed
- `--jit off` turn dynamic binary translation/JIT compilation off
- `--version` print the version of pydrofoil-riscv

## Limitations

Pydrofoil [currently](https://github.com/pydrofoil/pydrofoil/issues/48) does
not support any floating point machine instructions.
