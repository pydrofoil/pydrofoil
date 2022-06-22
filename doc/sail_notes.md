Notes about what we have learned about SAIL
=
SAIL is a language to define hardware e.g. RISC V.
Out goal is to write/generate a fast and easy extensible simulator in RPYTHON.
Examples in this file can be found in nand2tetris.sail.

More about sail install: https://github.com/rems-project/sail/blob/0.14/INSTALL.md

Semicolon:
==
Instruction seperator

Example:
```
A = x; PC = PC + 1
```

Let keyword:
==
Immutable assignment

Example:
```
let d = D;
```


Include:
==
Copy text into file. Like C include.

Example:
```
$include <prelude.sail>
```


Bit Vector Concatenation:
==
The at symbol.

Example:
```
0b111 @ a : bits(1)
```


Normal Functions:
==
Argument types after colon and return type after ->. 
Body after =.
Brackets used when body cotains more than one statment. 
Last expression is the return value.

Example:
```
function compute_value(a : bits(1), op : arithmetic_op) -> bits(16) = {
  let result = 0x0000
  result
}
```

Functions Signature Declaration:
==
The declaration of a function can be moved into a seperate line using val.

Example:
```
val fetch_decode_execute : unit -> bool

function fetch_decode_execute () = {
    // some code
}
```

Pattern Match Functions:
==
Uses the keyword clause. Only applyes when patter matches. 
The "match all pattern" is undercore _.

Example:
```
function clause decode 0b111 @ a : bits(1) @ c : bits(6) @ dest : bits(3) @ jump : bits(3) = // some Code
function clause decode _ = None()
```

Pattern Match Assignment:
==
Assigns the value after => to variable.
The default is None().

Example:
```
  let result : bits(16) = match op {
    C_ZERO => 0x0000,
    C_ONE => 0x0001,
  };
```


Some:
==
An optional type.

Example:
```
Some(AINST(sail_zero_extend(x, 16)))
```


Union Clause:
==
Defines a struct

Example
```
union clause instr = AINST : (bits(16))
```


Scattered Union:
==
The definition of the union is scattered over the whole file.

Example
```
scattered union instr
union clause instr = AINST : (bits(16))
// later ...
union clause instr = CINST : (bits(1), arithmetic_op, (bool, bool, bool), jump)
```


Endianness:
==
big-endian (BE) or little-endian (LE)

Example
```
default Order dec.
```

Operator Overloading:
==
Use function for operators like minus. c: defines the function name on the
c level. 'n is a type variable (e.g. 16 bit)

Example:
```
val sub_vec = {c: "sub_bits", _: "sub_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val sub_vec_int = {c: "sub_bits_int", _: "sub_vec_int"} : forall 'n. (bits('n), int) -> bits('n)

overload operator - = {sub_vec, sub_vec_int}
```

Side-Effects:
==
Side effects (e.g. write memory wmv) can be expressed with the effect keyword.

Example:
```
val write_mem = { _: "my_write_mem" }
  : (bits(16), bits(16)) -> unit effect {wmv}
```