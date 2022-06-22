Notes about what we have learned about SAIL
=

Some:
==
An optional type
```
Some(AINST(sail_zero_extend(x, 16)))
```

scattered union:
==
The definition of the union is scattered over the whole file
```
scattered union instr
union clause instr = AINST : (bits(16))
// later ...
union clause instr = CINST : (bits(1), arithmetic_op, (bool, bool, bool), jump)
```