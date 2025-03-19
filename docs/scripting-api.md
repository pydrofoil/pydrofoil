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

```pycon
>>>> m = _pydrofoil.RISCV64('riscv/input/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl', dtb=True)
tohost located at 0x80007008
ELF Entry @ 0x80000000
CSR mstatus <- 0x0000000A00000000 (input: 0x0000000000000000)
```

The `.step()` method will execute the loaded program for a single instruction:

```pycon
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

```pycon
>>>> m.set_verbosity(0)
>>>> m.step()
>>>> m.step()
>>>> m.step()
```

To run the program for longer periods, use the `.run` method, which optionally
takes a number of instructions as argument:

```pycon
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

```pycon
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

```pycon
>>>> m.disassemble_last_instruction()
'addi a3, s1, 0x128'
```

You can also read the CPU's registers (the register names are the internal
names that the Sail code uses):

```pycon
>>>> m.read_register('pc')
bitvector(64, 0xFFFFFFE0004AFC4A)
>>>> m.read_register('x1')
bitvector(64, 0xFFFFFFE0004AFC4A)
>>>> m.read_register('cur_privilege')
'Supervisor'
```

To write them, use the `.write_register` method. E.g. if you set the `pc` to
`0`, executing the next instruction will trigger a page fault:

```pycon
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

```pycon
>>>> m.read_memory(0x80000000, 8)
3747295551104745583
```

And also write to it with `.write_memory`.

### Accessing the low-level functions of the Sail model directly

In addition to the "high-level" API described so far, we can also call the
function of the Sail model directly, via the `RISC64.lowlevel` namespace. All
the Sail functions that have been compiled into the simulator binary are
exposed there. For example, we can read a register, including the
zero-register, using the `rX` model function:

```pycon
>>>> m.lowlevel.rX(0)
bitvector(64, 0x0000000000000000)
```

Or we can call the `encdec_compressed` function like this, to decode the 16-bit
bitvector `1`, and then use the `assembly_forwards` function to print the
disassembled string for the operation.

```pycon
>>>> ast = m.lowlevel.encdec_compressed_backwards(_pydrofoil.bitvector(16, 1))
>>>> print(ast)
C_NOP()
>>>> m.lowlevel.assembly_forwards(ast)
'c.nop'
```

Unfortunately, not all functions of the Sail model are exposed that way at this
point. Only the functions that are needed for the simulator, and that aren't
inlined can be accessed from Python at the moment. We plan to fix this in the
future.

### Creating struct and union instances directly

There is another low-level namespace, `RISC64.types`, that can be used to
construct `union` and `struct` types directly. For example we can construct the
`AST` of a `MUL` instruction like this:

```pycon
>>>> ast = m.types.MUL(1, 2, 8, m.types.mul_op(False, True, True))
>>>> print(ast)
MUL(bitvector(5, 0b00001), bitvector(5, 0b00010), bitvector(5, 0b01000), mul_op(False, True, True))
>>>> m.lowlevel.assembly_forwards(ast)
'mul fp, sp, ra'
```


## Examples

In this section we will show some example scripts and use cases for the
scripting API.


### A simple PC-value profiler

To collect some simple statistics about which values the `pc` register takes on
how often during Linux boot, and about the instructions executed, we can use
the following script:

```python
import _pydrofoil
import time
from collections import Counter

cpu = _pydrofoil.RISCV64('riscv/input/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl', dtb=True)
cpu.set_verbosity(0)
instructions = 23_000_000
histogram_pcs = Counter()
histogram_instructions = Counter()
histogram_mnemonic = Counter()

t1 = time.time()
try:
    for i in range(instructions):
        cpu.step()
        histogram_pcs[str(cpu.read_register("pc"))] += 1
        dis = cpu.disassemble_last_instruction()
        histogram_instructions[dis] += 1
        histogram_mnemonic[dis.split()[0]] += 1
except KeyboardInterrupt:
    pass
t2 = time.time()
print(f"instructions: {i+1}, kips: {round(i/(t2-t1)/100,2)}")

print()

for pc, value in histogram_mnemonic.most_common(20):
    print(pc, value)

print()

for pc, value in histogram_instructions.most_common(20):
    print(pc, value)

print()

for pc, value in histogram_pcs.most_common(20):
    print(pc, value)
```

After every instruction, we read the value of the `pc` register and store it in
a `collections.Counter`. We also store the full disassembled instruction, and
just the mnemonic of the instruction in two other counters. At the end (or when
Ctrl-C is pressed), we print the top 20 most common entries of the three
`Counter` objects:

```
$ ./pypy-c-pydrofoil-riscv simpleprofiler.py
tohost located at 0x80007008
ELF Entry @ 0x80000000
CSR mstatus <- 0x0000000A00000000 (input: 0x0000000000000000)
bbl loader

                SIFIVE, INC.

         5555555555555555555555555
...
instructions: 23000000, kips: 4194.8

c.addi 3043168
c.sdsp 1372473
c.ldsp 1370792
c.lw 1197915
bltu 1162016
sw 1088575
c.mv 1059511
sd 1036455
addi 812684
ld 700569
c.add 557114
c.ld 529161
c.li 474221
c.bnez 427773
c.jr 405676
c.beqz 382647
beq 368920
bne 364287
lbu 351685
andi 329342

c.lw a4, a1, 0x0 959796
c.addi a1, 0x4 956499
c.addi t6, 0x4 956497
sw a4, 0x0(t6) 956495
bltu a1, a3, -0xa 956495
c.jr ra 380815
c.addi a1, 0x1 147848
c.addi sp, -0x10 144001
c.addi sp, 0x10 143980
c.addi4spn s0, 0x10 137044
c.addi a4, 0x1 136720
c.addi a0, 0x1 109330
c.sdsp fp, 0x1 94235
c.ldsp fp, 0x1 94235
c.mv s1, a0 87493
bltu a1, a3, -0xc 82017
c.addi t6, 0x1 82016
lb a4, 0x0(a1) 82015
sb a4, 0x0(t6) 82015
c.addiw a5, 0x0 79210

bitvector(64, 0xFFFFFFE00063A070) 956495
bitvector(64, 0xFFFFFFE00063A072) 956495
bitvector(64, 0xFFFFFFE00063A074) 956495
bitvector(64, 0xFFFFFFE00063A078) 956495
bitvector(64, 0xFFFFFFE00063A07A) 956495
bitvector(64, 0xFFFFFFE00063A080) 82015
bitvector(64, 0xFFFFFFE00063A084) 82015
bitvector(64, 0xFFFFFFE00063A086) 82015
bitvector(64, 0xFFFFFFE00063A08A) 82015
bitvector(64, 0xFFFFFFE00063A08C) 82015
bitvector(64, 0x000000008020229C) 65536
bitvector(64, 0x00000000802022A0) 65536
bitvector(64, 0x00000000802022A2) 65536
bitvector(64, 0x00000000802022A4) 65536
bitvector(64, 0x00000000802022A6) 65536
bitvector(64, 0x00000000802022AA) 65536
bitvector(64, 0x00000000802022AC) 65536
bitvector(64, 0x00000000802022AE) 65536
bitvector(64, 0x00000000802022B0) 65536
bitvector(64, 0xFFFFFFE0005BE198) 48389
```

### Decoding every RISC-V instruction

We can also write a simple script to decode all `2**32` full instructions and
count their types. For this we need to use the `encdec` mapping from the RISC-V
Sail model, in backwards mode (we plan to make the directionality of mapping
functions work automatically, based on the argument types, but right now the
correct direction needs to be picked manually). `encdec_backwards` takes a
32-bit bitvector and returns an instance of the `AST` union. Given the decoded
`ast`, we compute statistics based on its type.

```python
import time
from __pypy__ import _promote
from _pydrofoil import RISCV64, bitvector

from collections import Counter


t1 = time.time()
m = RISCV64()
c = Counter()
try:
    for opcode in range(2**8):
        print(hex(opcode))
        for i in range(2**24):
            bv = bitvector(32, (i << 8) | opcode)
            ast = m.lowlevel.encdec_backwards(bv)
            c[type(ast)] += 1
finally:
    for key, value in c.most_common():
        print(key, value)
    t2 = time.time()
    print("took", t2 - t1, "seconds, stopped at", opcode)
```

(This is not entirely correct because it doesn't take compressed RISC-V
instructions into account properly.)

Running this takes a while (37 minutes on a Ryzen 9 3900X) and prints:

```
...
<class 'ILLEGAL'> 4047609720
<class 'UTYPE'> 67108864
<class 'RISCV_JAL'> 33554432
<class 'LOAD'> 29360128
<class 'ITYPE'> 25165824
<class 'BTYPE'> 25165824
<class 'CSR'> 25165824
<class 'STORE'> 16777216
<class 'AMO'> 4718592
<class 'ADDIW'> 4194304
<class 'RISCV_JALR'> 4194304
<class 'FENCEI_RESERVED'> 4194303
<class 'FENCE_RESERVED'> 4193792
<class 'RTYPE'> 327680
<class 'ZBB_RTYPE'> 294912
<class 'ZBS_IOP'> 262144
<class 'STORECON'> 262144
<class 'SHIFTIOP'> 196608
<class 'RTYPEW'> 163840
<class 'MUL'> 131072
<class 'ZBS_RTYPE'> 131072
<class 'SM4ED'> 131072
<class 'SM4KS'> 131072
<class 'ZBA_RTYPEUW'> 131072
<class 'SHIFTIWOP'> 98304
<class 'ZBA_RTYPE'> 98304
<class 'RISCV_RORI'> 65536
<class 'RISCV_SLLIUW'> 65536
<class 'DIV'> 65536
<class 'REM'> 65536
<class 'ZBKB_RTYPE'> 65536
<class 'ZICOND_RTYPE'> 65536
<class 'DIVW'> 65536
<class 'REMW'> 65536
<class 'ZBB_RTYPEW'> 65536
<class 'RISCV_RORIW'> 32768
<class 'RISCV_CLMUL'> 32768
<class 'RISCV_CLMULR'> 32768
<class 'RISCV_CLMULH'> 32768
<class 'RISCV_XPERM4'> 32768
<class 'RISCV_XPERM8'> 32768
<class 'AES64ES'> 32768
<class 'AES64ESM'> 32768
<class 'AES64DS'> 32768
<class 'AES64DSM'> 32768
<class 'AES64KS2'> 32768
<class 'MULW'> 32768
<class 'RISCV_FMINM_S'> 32768
<class 'RISCV_FMAXM_S'> 32768
<class 'RISCV_FLEQ_S'> 32768
<class 'RISCV_FLTQ_S'> 32768
<class 'ZBKB_PACKW'> 31744
<class 'AES64KS1I'> 11264
<class 'LOADRES'> 8192
<class 'RISCV_FROUND_S'> 6144
<class 'RISCV_FROUNDNX_S'> 6144
<class 'ZBB_EXTOP'> 3072
<class 'SHA256SUM0'> 1024
<class 'SHA256SUM1'> 1024
<class 'SHA256SIG0'> 1024
<class 'SHA256SIG1'> 1024
<class 'SHA512SUM0'> 1024
<class 'SHA512SUM1'> 1024
<class 'SHA512SIG0'> 1024
<class 'SHA512SIG1'> 1024
<class 'SM3P0'> 1024
<class 'SM3P1'> 1024
<class 'RISCV_ORCB'> 1024
<class 'AES64IM'> 1024
<class 'RISCV_CLZ'> 1024
<class 'RISCV_CTZ'> 1024
<class 'RISCV_CPOP'> 1024
<class 'RISCV_BREV8'> 1024
<class 'RISCV_REV8'> 1024
<class 'RISCV_CLZW'> 1024
<class 'RISCV_CTZW'> 1024
<class 'RISCV_CPOPW'> 1024
<class 'RISCV_FLI_S'> 1024
<class 'SFENCE_VMA'> 1024
<class 'SINVAL_VMA'> 1024
<class 'FENCE'> 256
<class 'FENCE_TSO'> 256
<class 'RISCV_ZICBOM'> 96
<class 'RISCV_ZICBOZ'> 32
<class 'FENCEI'> 1
<class 'ECALL'> 1
<class 'EBREAK'> 1
<class 'URET'> 1
<class 'SRET'> 1
<class 'WFI'> 1
<class 'SFENCE_W_INVAL'> 1
<class 'SFENCE_INVAL_IR'> 1
<class 'MRET'> 1
```
