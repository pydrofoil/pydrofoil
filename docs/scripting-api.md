# Pydrofoil-RISC-V's Scripting API

**This is still a very experimental feature, we don't guarantee API stability
at this point.**

In order to make it easier to interact with a SAIL ISA model, we are working on
a scripting API using the [PyPy](https://pypy.org) Python interpreter. So far
this is only enabled for the RISC-V models (but can in principle also be added
for the other CPUs, given a small amount of effort).

## Introduction to the API

### Basics of running the simulated CPU

The binary is a normal PyPy executable, but it comes with a new special
built-in module `_pydrofoil`. The module exposes two classes, `RISCV32` and
`RISCV64` that represent simulated RISC-V CPUs. Their constructors take a path
to an ELF file as argument, which is loaded into simulated main memory:

```
>>>> m = _pydrofoil.RISCV64('riscv/input/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl', dtb=True)
tohost located at 0x80007008
ELF Entry @ 0x80000000
CSR mstatus <- 0x0000000A00000000 (input: 0x0000000000000000)
```

The `.step()` method will execute the loaded program for a single instruction:

```
>>>> m.step()
mem[X,0x0000000000001000] -> 0x0297
mem[X,0x0000000000001002] -> 0x0000
[0] [M]: 0x0000000000001000 (0x00000297) auipc t0, 0x0
x5 <- 0x0000000000001000
>>>> m.step()
mem[X,0x0000000000001004] -> 0x8593
mem[X,0x0000000000001006] -> 0x0202
[1] [M]: 0x0000000000001004 (0x02028593) addi a1, t0, 0x20
x11 <- 0x0000000000001020
>>>> m.step()
mem[X,0x0000000000001008] -> 0x2573
mem[X,0x000000000000100A] -> 0xF140
[2] [M]: 0x0000000000001008 (0xF1402573) csrrs a0, mhartid, zero
CSR mhartid -> 0x0000000000000000
x10 <- 0x0000000000000000
```

By default, every instruction prints a trace of what memory and registers it is
reading and writing, and disassembles the current instruction. For
longer-running programs this is too much output and hides the prints of the
executed program. To disable it, you can call the `.set_verbosity` method:

```
>>>> m.set_verbosity(0)
>>>> m.step()
>>>> m.step()
>>>> m.step()
```

To run the program for longer periods, use the `.run` method, which optionally
takes a number of instructions as argument:

```
>>>> m.run(500000)
bbl loader

                SIFIVE, INC.

         5555555555555555555555555
        5555                   5555
       5555                     5555
      5555                       5555
     5555       5555555555555555555555
    5555       555555555555555555555555
   5555                             5555
  5555                               5555
 5555                                 5555
5555555555555555555555555555          55555
 55555           555555555           55555
   55555           55555           55555
     55555           5           55555
       55555                   55555
         55555               55555
           55555           55555
             55555       55555
               55555   55555
                 555555555
                   55555
                     5

           SiFive RISC-V Core IP
SUCCESS
Instructions: 500000
Total time (s): 0.033948
Perf: 14728.432171 Kips
```

If you call `.run()` without arguments, the CPU will keep executing
indefinitely. You can interrupt it at any point by pressing Ctrl-C:

```
>>>> m.run()
[    0.000000] OF: fdt: Ignoring memory range 0x80000000 - 0x80200000
[    0.000000] Linux version 4.15.0-gfe92d79-dirty (mundkur@dualnic2) (gcc version 7.2.0 (GCC)) #1 SMP Wed Jun 5 14:56:25 PDT 2019
[    0.000000] bootconsole [early0] enabled
... lots of output skipped
...
[    0.050569] Freeing unused kernel memory: 4528K
[    0.050583] This architecture does not have kernel memory protection.
Starting logging: OK
Starting mdev...
modprobe: can't change directory to '/lib/modules': No such file or directory
Initializing random number generator... done.
Starting network...
ip: socket: Function not implemented
ip: socket: Function not implemented

Welcome to Buildroot
buildroot login: ^CCTRL-C was pressed
Instructions: 852835752
Total time (s): 48.992306
Perf: 17407.544607 Kips
Traceback (most recent call last):
  File "<python-input-21>", line 1, in <module>
    m.run()
KeyboardInterrupt
>>>>
```

### Inspecting the CPU state

There are a number of methods to read (and also write) the current state of the
simulated CPU. A useful high-level way to do that is to ask for the disassembly
of the last executed instruction:

```
>>>> m.disassemble_last_instruction()
'addi a3, s1, 0x128'
```

You can also read the CPU's registers (the register names are the internal
names that the Sail code uses):

```
>>>> m.read_register('pc')
bitvector(64, 0xFFFFFFE0004AFC4A)
>>>> m.read_register('x1')
bitvector(64, 0xFFFFFFE0004AFC4A)
>>>> m.read_register('cur_privilege')
'Supervisor'
```

To write them, use the `.write_register` method. E.g. if you set the `pc` to
`0`, executing the next instruction will trigger a page fault:

```
>>>> m.set_verbosity(1)
>>>> m.write_register('pc', 0)
>>>> m.step()
mem[R,0x0000000083A58000] -> 0x0000000020E96C01
mem[R,0x0000000083A5B000] -> 0x0000000020E97801
mem[R,0x0000000083A5E000] -> 0x0000000000000000
trapping from S to S to handle fetch-page-fault
handling exc#0x0C at priv S with tval 0x0000000000000000
CSR mstatus <- 0x0000000A00000180
```

Similarly, you can read from the simulated main memory:

```
>>>> m.read_memory(0x80000000, 8)
3747295551104745583
```

And also write to it with `.write_memory`.


## Examples

In this section we will show some example scripts.


### A simple PC-value profiler

To profile which values the `pc` register takes on how often during Linux boot,
we can use the following script:

```python
import time
import _pydrofoil
from collections import Counter

cpu = _pydrofoil.RISCV64('riscv/input/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl', dtb=True)
cpu.set_verbosity(0)
instructions = 23_000_000
histogram_pcs = Counter()

t1 = time.time()
try:
    for i in range(instructions):
        cpu.step()
        histogram_pcs[str(cpu.read_register("pc"))] += 1
except KeyboardInterrupt:
    pass
t2 = time.time()
print(f"instructions: {i}, kips: {round(i/(t2-t1)/100,2)}")

for pc, value in histogram_pcs.most_common(20):
    print(pc, value)
```

After every instruction, we read the value of the `pc` register and store it in
a `collections.Counter`. At the end, we print the top-20 most common `pc`
values.
