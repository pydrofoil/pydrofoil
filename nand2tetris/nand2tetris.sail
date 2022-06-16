default Order dec

$include <prelude.sail>

val sub_vec = {c: "sub_bits", _: "sub_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val sub_vec_int = {c: "sub_bits_int", _: "sub_vec_int"} : forall 'n. (bits('n), int) -> bits('n)

overload operator - = {sub_vec, sub_vec_int}

val bits1_to_bool : bits(1) -> bool

function bits1_to_bool b = match b {
  0b1  => true,
  0b0 => false
}

val write_mem = { _: "my_write_mem" }
  : (bits(16), bits(16)) -> unit effect {wmv}

val read_mem = { _: "my_read_mem" }
  : bits(16) -> bits(16)

val read_rom = { _: "my_read_rom" }
  : bits(16) -> bits(16)

val print_debug = { _: "my_print_debug" }
  : (bits(64), bits(16), bits(16), bits(16)) -> unit

register PC : bits(16)
register A : bits(16)
register D : bits(16)

enum arithmetic_op = {
  C_ZERO,
  C_ONE,
  C_MINUSONE,
  C_D,
  C_A,
  C_NOT_D,
  C_NOT_A,
  C_NEG_D,
  C_NEG_A,
  C_D_ADD_1,
  C_A_ADD_1,
  C_D_SUB_1,
  C_A_SUB_1,
  C_D_ADD_A,
  C_D_SUB_A,
  C_A_SUB_D,
  C_D_AND_A,
  C_D_OR_A
}

mapping decode_compute : arithmetic_op <-> bits(6) = {
  C_ZERO       <-> 0b101010,
  C_ONE        <-> 0b111111,
  C_MINUSONE   <-> 0b111010,
  C_D          <-> 0b001100,
  C_A          <-> 0b110000,
  C_NOT_D      <-> 0b001101,
  C_NOT_A      <-> 0b110001,
  C_NEG_D      <-> 0b001111,
  C_NEG_A      <-> 0b110011,
  C_D_ADD_1    <-> 0b011111,
  C_A_ADD_1    <-> 0b110111,
  C_D_SUB_1    <-> 0b001110,
  C_A_SUB_1    <-> 0b110010,
  C_D_ADD_A    <-> 0b000010,
  C_D_SUB_A    <-> 0b010011,
  C_A_SUB_D    <-> 0b000111,
  C_D_AND_A    <-> 0b000000,
  C_D_OR_A     <-> 0b010101
}

enum jump = { JDONT, JGT, JEQ, JGE, JLT, JNE, JLE, JMP }

mapping decode_jump : jump <-> bits(3) = {
  JDONT  <-> 0b000,
  JGT    <-> 0b001,
  JEQ    <-> 0b010,
  JGE    <-> 0b011,
  JLT    <-> 0b100,
  JNE    <-> 0b101,
  JLE    <-> 0b110,
  JMP    <-> 0b111
}


scattered union instr
val decode : bits(16) -> option(instr)
val execute : instr -> unit effect {rreg, wreg, wmv}


// A instruction

union clause instr = AINST : (bits(16))

function clause decode 0b0 @ x : bits(15)
 = Some(AINST(sail_zero_extend(x, 16)))

function clause execute(AINST(x)) = {
  A = x; PC = PC + 1
}

// C instruction

type destination = (bool, bool, bool)

function decode_destination(b : bits(3)) -> destination = {
    match b {
        a : bits(1) @ d : bits(1) @ m : bits(1) => (bits1_to_bool(a), bits1_to_bool(d), bits1_to_bool(m))
    }
}

union clause instr = CINST : (bits(1), arithmetic_op, (bool, bool, bool), jump)

function clause decode 0b111 @ a : bits(1) @ c : bits(6) @ dest : bits(3) @ jump : bits(3)
  = Some(CINST(a, decode_compute(c), decode_destination(dest), decode_jump(jump)))

function clause decode _ = None()

function compute_value(a : bits(1), op : arithmetic_op) -> bits(16) = {
  let a = if a == 0b0 then A else read_mem(A);
  let d = D;
  let result : bits(16) = match op {
    C_ZERO => 0x0000,
    C_ONE => 0x0001,
    C_MINUSONE => 0xffff,
    C_D => d,
    C_A => a,
    C_NOT_D => not_vec(d),
    C_NOT_A => not_vec(a),
    C_NEG_D => 0x0000-d,
    C_NEG_A => 0x0000-a,
    C_D_ADD_1 => d + 0x0001,
    C_A_ADD_1 => a + 0x0001,
    C_D_SUB_1 => d - 0x0001,
    C_A_SUB_1 => a - 0x0001,
    C_D_ADD_A => d + a,
    C_D_SUB_A => d - a,
    C_A_SUB_D => a - d,
    C_D_AND_A => d & a,
    C_D_OR_A => d | a
  };
  result
}

function assign_dest((a : bool, d : bool, m : bool), value : bits(16)) -> unit = {
    if m then { write_mem(A, value); };
    if a then { A = value; };
    if d then { D = value; }
}

function maybe_jump(value : bits(16), j : jump) -> unit = {
    cond : bool = match j {
      JDONT => false,
      JGT   => signed(value) > 0,
      JEQ   => signed(value) == 0,
      JGE   => signed(value) >= 0,
      JLT   => signed(value) < 0,
      JNE   => signed(value) != 0,
      JLE   => signed(value) <= 0,
      JMP   => true
    };
    if cond then {PC = A;} else {PC = PC + 1;}
}

function clause execute(CINST(a, op, dest, jump)) = {
  let value = compute_value(a, op);
  assign_dest(dest, value);
  maybe_jump(value, jump)
}


val fetch_decode_execute : unit -> bool

function fetch_decode_execute () = {
    let instr : bits(16) = read_rom(PC);
    let x = decode(instr);
    cont : bool = false;
    match x {
        Some(instr) => { execute(instr); cont = true; },
        None() => { cont = false;}
    };
    return cont;
}

val run : (bits(64), bool) -> unit effect {rreg, wreg, wmv}

function run(limit, debug) = {
    cycle_count : bits(64) = 0x0000000000000000;
    cont : bool = true;
    while (cont) do {
        cont = false;
        if debug then {
            print_debug(cycle_count, PC, A, D);
        };
        if fetch_decode_execute() then {
            if signed(cycle_count) < signed(limit) then {
                cont = true;
            }
        };
        cycle_count = cycle_count + 0x0000000000000001;
    }
}

function mymain(limit : bits(64), debug : bool) -> unit = {
    PC = 0x0000;
    A = 0x0000;
    D = 0x0000;
    run(limit, debug)
}


val main : unit -> unit

function main() = { return mymain(0x0000000000000010, false); }

