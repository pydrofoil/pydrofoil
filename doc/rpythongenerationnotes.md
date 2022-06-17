Notes about mapping JIB to RPython
=

JIB types:
==

- enums
- unions
- struct
- int (signed, idealized arbitrary precision)
- i64 (signed, machine int)
- bv (arbitrary size, not signed)
- bv<num> (bit vector fixed size, not signed), eg bv16
- function
- tuple (are initialized with mutation at the JIB level)
- bool
- string
- bit (why is this different from bv1?)
- ref: pointers
- unit (="void")

Mapping to RPython:

- enums: int constants, enum constants get globally unique numbers from 0
- unions: base class with different subclasses for the union members
- struct: a single class. are they immutable? does assignment copy them?
- int: rpython.rlib.rbigint.rbigint
- i64: Python int
- bv: rpython.rlib.rbigint.rbigint (only for now)
- bv<num>: `rpython.rlib.rarithmetic.r_uint`
- function: rpython function
- tuple: generate one rpython class per combination of types, fields `ztup0`, ..., `ztup<n>`
- bool: rpython bool
- string: rpython str
- bit: `r_uint(0 or 1)`
- ref: unclear! to structs: just use the struct. but to primitives I don't know yet
- unit: rpython empty tuple



Operations on values (of the types)
==

- function calls to other jib functions: maps to function calls in rpython
- "magic", built-in operations, prefixed with "@"


