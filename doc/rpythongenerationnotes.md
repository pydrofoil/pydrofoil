Notes about mapping JIB to RPython
=

JIB types:
==

- enums
- unions
- int (signed, idealized arbitrary precision)
- i64 (signed, machine int)
- bv (arbitrary size, not signed)
- bv<num> (bit vector fixed size, not signed), eg bv16
- function
- tuple (are initialized with mutation at the JIB level)
- bool
- unit (="void")

Mapping to RPython:

- enums: int constants, enum constants get globally unique numbers from 0
- unions: base class with different subclasses for the union members
- int: rpython.rlib.rbigint.rbigint
- i64: Python int
- bv: rpython.rlib.rbigint.rbigint (only for now)
- bv<num>: `rpython.rlib.rarithmetic.r_uint`
- function: rpython function
- tuple: generate one rpython class per combination of types, fields `ztup0`, ..., `ztup<n>`
- bool: rpython bool
- unit: rpython empty tuple



Operations on values (of the types)
==

- function calls to other jib functions: maps to function calls in rpython
- "magic", built-in operations, prefixed with "@"


