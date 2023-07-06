# Background: Optimizations that Pydrofoil does

On this page we want to give a brief introduction to some of the optimizations
that Pydrofoil performs, together with some links to further reading about them.

## Dynamic binary translation / just-in-time compilation

The Sail-generated emulator is an *interpreter*. Given a RISC-V binary it
fetches and decodes instructions, and every time it has to do so it will read
from emulated RAM, then re-analyze the bitpatterns of the involved instructions.
This is costly for guest instructions that are emulated again and again, for
example because they run as part of a loop in the guest program.

To optimize this overhead away, Pydrofoil uses dynamic binary translation.
The idea of binary translation is to translate the guest RISC-V instructions to
host machine instructions. This translation needs to be done at runtime (i.e.
while the emulator is running the guest program) in order to be able support
self-modifying code and code that is dynamically emitted at runtime.

Dynamic binary translation speeds up emulation because it removes the
interpretation overhead and the repeated decoding of the executed guest
instructions. Dynamic binary translation in Pydrofoil is not applied to all the
executed instructions, but only those that are executed often enough. To
identify those, Pydrofoil does runtime profiling to find the commonly executed
loops in the guest programs. Once a threshold is reached for such a loop, the
loop is translated to host machine code (typically x86 or ARM).

During the translation process various typical compiler optimizations are
applied, even across the boundaries of the individual guest instructions.
Examples are constant folding, store-to-load and load-to-load forwarding.

Further Reading:

- ["Dynamic Binary
  Translation"](http://www.complang.tuwien.ac.at/schani/papers/bintrans.pdf) is
  a survey paper.
- ["From hack to elaborate technique - A survey on binary
  rewriting"](https://publications.sba-research.org/publications/201906%20-%20GMerzdovnik%20-%20From%20hack%20to%20elaborate%20technique.pdf)
  is a survey on the more general technique of binary rewriting.
- ["A Brief History of
  Just-in-Time"](http://eecs.ucf.edu/~dcm/Teaching/COT4810-Spring2011/Literature/JustInTimeCompilation.pdf)
  is an overview paper of just-in-time compilation.
- For traditional compiler optimization please refer to your favorite compiler
  books, e.g. Cooper & Torczon, Engineering a Compiler

### Meta-Tracing

One additional complexity that Pydrofoil has compared to other dynamic binary
translators is the fact that it is always possible to add new instructions to
the Sail ISA model (for example because a new RISC-V extension comes out or
becomes added to the model). Therefore the technique of "meta-tracing" is used
in order to automatically support dynamic binary translation of all the RISC-V
instructions that are added to the Sail model. Meta-tracing was invented in the
[DynamoRIO](http://groups.csail.mit.edu/commit/papers/03/RIO-adaptive-CGO03.pdf)
project and developed further by
[PyPy](https://www3.hhu.de/stups/downloads/pdf/BoCuFiRi09_246.pdf). Pydrofoil
re-uses the PyPy/RPython meta-JIT compiler infrastructure in order to save
implementation effort.


## More efficient representation for integers and bitvectors

Another optimization of Pydrofoil compared to the standard
Sail-generated emulator are better implementations for the bitvector and integer
types that Sail supports. Integers in Sail have arbitrary precision, and
bitvector types can be parametrized with the bitwidth, which might or might not
be a constant in the Sail source code.

### How the Sail emulator does it

The Sail compiler will try to infer the maximum number of bits needed for all
the integers used in the Sail specification, and similarly will try to identify
the precise bitwidth of all bitvector types (or at least an upper bound on their
size). This analysis uses the [Z3 model
checker](https://github.com/Z3Prover/z3). If this analysis succeeds, and the
number of bits can be inferred for an integer or bitvector type, the Sail
compiler will pick an efficient representation of the involved variables when
generating C code for the emulator. For integers that have inferred sizes that
fit a machine word, they can simply be represented as machine words, and
similarly for bitvectors.

However, the analysis of the bitwidths can also fail, in which case neither a
precise nor maximum bitwidth is known. In that case the Sail compiler will
represent the corresponding variables in the C source using the arbitrary
integer implementation of the [GNU multi precision library](https://gmplib.org/)
(GMP). In particular this means that every such integer and bitvector becomes a
dynamically allocated object on the heap, which needs to be allocated with
`malloc` and `free`. This constant allocation and de-allocation of the integer
objects costs a lot of performance.



### What Pydrofoil does

Pydrofoil represents integers and bitvectors of unknown size differently.
Instead of always using a heap-allocated representation, Pydrofoil will
dynamically pick between two different representations at runtime, individually
for each created integer or bitvector:

- a small representation for integers/bitvectors that fit into a machine word
- a generic representation for those that don't, which uses a heap-allocated big
  integer implementation like in Sail

This dynamic choice of representation is useful because *in practice* most integer
values/bitvectors in a Sail model fit into a machine word, even if statically
determining this does not work. By having this dynamic representation, Pydrofoil
saves a lot of allocations and deallocations that the Sail-generated emulators
do.

This implementation approach for potentially arbitrarily sized integers is
standard in the implementation of dynamically typed programming languages and
goes back to [early Lisp
implementations](https://www.snellman.net/blog/archive/2017-09-04-lisp-numbers/).

