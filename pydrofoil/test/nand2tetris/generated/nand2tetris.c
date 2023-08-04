#include "sail.h"
#include "rts.h"
#include "elf.h"
#include "../nandsupport.h"

// enum jump
enum zjump { zJDONT, zJGT, zJEQ, zJGE, zJLT, zJNE, zJLE, zJMP };

static bool eq_zjump(enum zjump op1, enum zjump op2) { return op1 == op2; }

static enum zjump UNDEFINED(zjump)(unit u) { return zJDONT; }

// union exception
enum kind_zexception { Kind_z__dummy_exnz3 };

struct zexception {
  enum kind_zexception kind;
  union {struct { unit z__dummy_exnz3; };};
};

static void CREATE(zexception)(struct zexception *op)
{
  op->kind = Kind_z__dummy_exnz3;

}

static void RECREATE(zexception)(struct zexception *op) {}

static void KILL(zexception)(struct zexception *op)
{
  if (op->kind == Kind_z__dummy_exnz3){
    /* do nothing */
  };
}

static void COPY(zexception)(struct zexception *rop, struct zexception op)
{
  if (rop->kind == Kind_z__dummy_exnz3){
    /* do nothing */
  };
  rop->kind = op.kind;
  if (op.kind == Kind_z__dummy_exnz3){
    rop->z__dummy_exnz3 = op.z__dummy_exnz3;
  }
}

static bool EQUAL(zexception)(struct zexception op1, struct zexception op2) {
  if (op1.kind == Kind_z__dummy_exnz3 && op2.kind == Kind_z__dummy_exnz3) {
    return EQUAL(unit)(op1.z__dummy_exnz3, op2.z__dummy_exnz3);
  } else return false;
}

static void z__dummy_exnz3(struct zexception *rop, unit op)
{
  if (rop->kind == Kind_z__dummy_exnz3){
    /* do nothing */
  }
  rop->kind = Kind_z__dummy_exnz3;
  rop->z__dummy_exnz3 = op;
}

struct zexception *current_exception = NULL;
bool have_exception = false;
sail_string *throw_location = NULL;

// enum arithmetic_op
enum zarithmetic_op { zC_ZERO, zC_ONE, zC_MINUSONE, zC_D, zC_A, zC_NOT_D, zC_NOT_A, zC_NEG_D, zC_NEG_A, zC_D_ADD_1, zC_A_ADD_1, zC_D_SUB_1, zC_A_SUB_1, zC_D_ADD_A, zC_D_SUB_A, zC_A_SUB_D, zC_D_AND_A, zC_D_OR_A };

static bool eq_zarithmetic_op(enum zarithmetic_op op1, enum zarithmetic_op op2) { return op1 == op2; }

static enum zarithmetic_op UNDEFINED(zarithmetic_op)(unit u) { return zC_ZERO; }

// struct tuple_(%bool, %bool, %bool)
struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 {
  bool ztup0;
  bool ztup1;
  bool ztup2;
};

static void COPY(ztuple_z8z5boolzCz0z5boolzCz0z5boolz9)(struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 *rop, const struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 op) {
  rop->ztup0 = op.ztup0;
  rop->ztup1 = op.ztup1;
  rop->ztup2 = op.ztup2;
}

static bool EQUAL(ztuple_z8z5boolzCz0z5boolzCz0z5boolz9)(struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 op1, struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 op2) {
  return EQUAL(bool)(op1.ztup0, op2.ztup0) && EQUAL(bool)(op1.ztup1, op2.ztup1) && EQUAL(bool)(op1.ztup2, op2.ztup2);
}


// struct tuple_(%bv1, %enum zarithmetic_op, (%bool, %bool, %bool), %enum zjump)
struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 {
  uint64_t ztup0;
  enum zarithmetic_op ztup1;
  struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 ztup2;
  enum zjump ztup3;
};

static void COPY(ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9)(struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 *rop, const struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 op) {
  rop->ztup0 = op.ztup0;
  rop->ztup1 = op.ztup1;
  rop->ztup2 = op.ztup2;
  rop->ztup3 = op.ztup3;
}

static bool EQUAL(ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9)(struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 op1, struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 op2) {
  return EQUAL(fbits)(op1.ztup0, op2.ztup0) && EQUAL(zarithmetic_op)(op1.ztup1, op2.ztup1) && EQUAL(ztuple_z8z5boolzCz0z5boolzCz0z5boolz9)(op1.ztup2, op2.ztup2) && EQUAL(zjump)(op1.ztup3, op2.ztup3);
}

// union instr
enum kind_zinstr { Kind_zAINST, Kind_zCINST };

struct zinstr {
  enum kind_zinstr kind;
  union {
    struct { uint64_t zAINST; };
    struct { struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 zCINST; };
  };
};

static void CREATE(zinstr)(struct zinstr *op)
{
  op->kind = Kind_zAINST;

}

static void RECREATE(zinstr)(struct zinstr *op) {}

static void KILL(zinstr)(struct zinstr *op)
{
  if (op->kind == Kind_zAINST) {
    /* do nothing */
  } else if (op->kind == Kind_zCINST){
    /* do nothing */
  };
}

static void COPY(zinstr)(struct zinstr *rop, struct zinstr op)
{
  if (rop->kind == Kind_zAINST) {
    /* do nothing */
  } else if (rop->kind == Kind_zCINST){
    /* do nothing */
  };
  rop->kind = op.kind;
  if (op.kind == Kind_zAINST) {
    rop->zAINST = op.zAINST;
  } else if (op.kind == Kind_zCINST){
    rop->zCINST = op.zCINST;
  }
}

static bool EQUAL(zinstr)(struct zinstr op1, struct zinstr op2) {
  if (op1.kind == Kind_zAINST && op2.kind == Kind_zAINST) {
    return EQUAL(fbits)(op1.zAINST, op2.zAINST);
  } else if (op1.kind == Kind_zCINST && op2.kind == Kind_zCINST) {

  return EQUAL(ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9)(op1.zCINST, op2.zCINST);
  } else return false;
}

static void zAINST(struct zinstr *rop, uint64_t op)
{
  if (rop->kind == Kind_zAINST) {
    /* do nothing */
  } else if (rop->kind == Kind_zCINST){
    /* do nothing */
  }
  rop->kind = Kind_zAINST;
  rop->zAINST = op;
}

static void zCINST(struct zinstr *rop, struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 op)
{
  if (rop->kind == Kind_zAINST) {
    /* do nothing */
  } else if (rop->kind == Kind_zCINST){
    /* do nothing */
  }
  rop->kind = Kind_zCINST;
  rop->zCINST = op;
}


// union option<Uinstr<>>
enum kind_zoptionzIUinstrzIzKzK { Kind_zNonezIUinstrzIzKzK, Kind_zSomezIUinstrzIzKzK };

struct zoptionzIUinstrzIzKzK {
  enum kind_zoptionzIUinstrzIzKzK kind;
  union {
    struct { unit zNonezIUinstrzIzKzK; };
    struct { struct zinstr zSomezIUinstrzIzKzK; };
  };
};

static void CREATE(zoptionzIUinstrzIzKzK)(struct zoptionzIUinstrzIzKzK *op)
{
  op->kind = Kind_zNonezIUinstrzIzKzK;

}

static void RECREATE(zoptionzIUinstrzIzKzK)(struct zoptionzIUinstrzIzKzK *op) {}

static void KILL(zoptionzIUinstrzIzKzK)(struct zoptionzIUinstrzIzKzK *op)
{
  if (op->kind == Kind_zNonezIUinstrzIzKzK) {
    /* do nothing */
  } else if (op->kind == Kind_zSomezIUinstrzIzKzK){
    KILL(zinstr)(&op->zSomezIUinstrzIzKzK);
  };
}

static void COPY(zoptionzIUinstrzIzKzK)(struct zoptionzIUinstrzIzKzK *rop, struct zoptionzIUinstrzIzKzK op)
{
  if (rop->kind == Kind_zNonezIUinstrzIzKzK) {
    /* do nothing */
  } else if (rop->kind == Kind_zSomezIUinstrzIzKzK){
    KILL(zinstr)(&rop->zSomezIUinstrzIzKzK);
  };
  rop->kind = op.kind;
  if (op.kind == Kind_zNonezIUinstrzIzKzK) {
    rop->zNonezIUinstrzIzKzK = op.zNonezIUinstrzIzKzK;
  } else if (op.kind == Kind_zSomezIUinstrzIzKzK){
    CREATE(zinstr)(&rop->zSomezIUinstrzIzKzK); COPY(zinstr)(&rop->zSomezIUinstrzIzKzK, op.zSomezIUinstrzIzKzK);
  }
}

static bool EQUAL(zoptionzIUinstrzIzKzK)(struct zoptionzIUinstrzIzKzK op1, struct zoptionzIUinstrzIzKzK op2) {
  if (op1.kind == Kind_zNonezIUinstrzIzKzK && op2.kind == Kind_zNonezIUinstrzIzKzK) {
    return EQUAL(unit)(op1.zNonezIUinstrzIzKzK, op2.zNonezIUinstrzIzKzK);
  } else if (op1.kind == Kind_zSomezIUinstrzIzKzK && op2.kind == Kind_zSomezIUinstrzIzKzK) {
    return EQUAL(zinstr)(op1.zSomezIUinstrzIzKzK, op2.zSomezIUinstrzIzKzK);
  } else return false;
}

static void zNonezIUinstrzIzKzK(struct zoptionzIUinstrzIzKzK *rop, unit op)
{
  if (rop->kind == Kind_zNonezIUinstrzIzKzK) {
    /* do nothing */
  } else if (rop->kind == Kind_zSomezIUinstrzIzKzK){
    KILL(zinstr)(&rop->zSomezIUinstrzIzKzK);
  }
  rop->kind = Kind_zNonezIUinstrzIzKzK;
  rop->zNonezIUinstrzIzKzK = op;
}

static void zSomezIUinstrzIzKzK(struct zoptionzIUinstrzIzKzK *rop, struct zinstr op)
{
  if (rop->kind == Kind_zNonezIUinstrzIzKzK) {
    /* do nothing */
  } else if (rop->kind == Kind_zSomezIUinstrzIzKzK){
    KILL(zinstr)(&rop->zSomezIUinstrzIzKzK);
  }
  rop->kind = Kind_zSomezIUinstrzIzKzK;
  CREATE(zinstr)(&rop->zSomezIUinstrzIzKzK);
  COPY(zinstr)(&rop->zSomezIUinstrzIzKzK, op);

}













bool zneq_int(sail_int, sail_int);

bool zneq_int(sail_int zx, sail_int zy)
{
  __label__ end_function_1, end_block_exception_2;

  bool zcbz30;
  bool zgaz30;
  zgaz30 = eq_int(zx, zy);
  zcbz30 = not(zgaz30);

end_function_1: ;
  return zcbz30;
end_block_exception_2: ;

  return false;
}































bool zbits1_to_bool(uint64_t);

bool zbits1_to_bool(uint64_t zb)
{
  __label__ case_5, case_6, finish_match_4, end_function_7, end_block_exception_8;

  bool zcbz31;
  {
    uint64_t zb__0;
    zb__0 = zb;
    bool zgsz31;
    zgsz31 = (zb__0 == UINT64_C(0b1));
    if (!(zgsz31)) {

      goto case_5;
    }
    zcbz31 = true;
    goto finish_match_4;
  }
case_5: ;
  {
    zcbz31 = false;
    goto finish_match_4;
  }
case_6: ;
  sail_match_failure("bits1_to_bool");
finish_match_4: ;
end_function_7: ;
  return zcbz31;
end_block_exception_8: ;

  return false;
}









// register PC
uint64_t zPC;

// register A
uint64_t zA;

// register D
uint64_t zD;

enum zarithmetic_op zdecode_compute_backwards(uint64_t);

enum zarithmetic_op zdecode_compute_backwards(uint64_t zargz3)
{
  __label__ case_11, case_12, case_13, case_14, case_15, case_16, case_17, case_18, case_19, case_20, case_21, case_22, case_23, case_24, case_25, case_26, case_27, case_28, finish_match_10, end_function_29, end_block_exception_30;

  enum zarithmetic_op zcbz32;
  {
    uint64_t zb__0;
    zb__0 = zargz3;
    bool zgsz34;
    zgsz34 = (zb__0 == UINT64_C(0b101010));
    if (!(zgsz34)) {

      goto case_11;
    }
    zcbz32 = zC_ZERO;
    goto finish_match_10;
  }
case_11: ;
  {
    uint64_t zb__1;
    zb__1 = zargz3;
    bool zgsz35;
    zgsz35 = (zb__1 == UINT64_C(0b111111));
    if (!(zgsz35)) {

      goto case_12;
    }
    zcbz32 = zC_ONE;
    goto finish_match_10;
  }
case_12: ;
  {
    uint64_t zb__2;
    zb__2 = zargz3;
    bool zgsz36;
    zgsz36 = (zb__2 == UINT64_C(0b111010));
    if (!(zgsz36)) {

      goto case_13;
    }
    zcbz32 = zC_MINUSONE;
    goto finish_match_10;
  }
case_13: ;
  {
    uint64_t zb__3;
    zb__3 = zargz3;
    bool zgsz37;
    zgsz37 = (zb__3 == UINT64_C(0b001100));
    if (!(zgsz37)) {

      goto case_14;
    }
    zcbz32 = zC_D;
    goto finish_match_10;
  }
case_14: ;
  {
    uint64_t zb__4;
    zb__4 = zargz3;
    bool zgsz38;
    zgsz38 = (zb__4 == UINT64_C(0b110000));
    if (!(zgsz38)) {

      goto case_15;
    }
    zcbz32 = zC_A;
    goto finish_match_10;
  }
case_15: ;
  {
    uint64_t zb__5;
    zb__5 = zargz3;
    bool zgsz39;
    zgsz39 = (zb__5 == UINT64_C(0b001101));
    if (!(zgsz39)) {

      goto case_16;
    }
    zcbz32 = zC_NOT_D;
    goto finish_match_10;
  }
case_16: ;
  {
    uint64_t zb__6;
    zb__6 = zargz3;
    bool zgsz310;
    zgsz310 = (zb__6 == UINT64_C(0b110001));
    if (!(zgsz310)) {

      goto case_17;
    }
    zcbz32 = zC_NOT_A;
    goto finish_match_10;
  }
case_17: ;
  {
    uint64_t zb__7;
    zb__7 = zargz3;
    bool zgsz311;
    zgsz311 = (zb__7 == UINT64_C(0b001111));
    if (!(zgsz311)) {

      goto case_18;
    }
    zcbz32 = zC_NEG_D;
    goto finish_match_10;
  }
case_18: ;
  {
    uint64_t zb__8;
    zb__8 = zargz3;
    bool zgsz312;
    zgsz312 = (zb__8 == UINT64_C(0b110011));
    if (!(zgsz312)) {

      goto case_19;
    }
    zcbz32 = zC_NEG_A;
    goto finish_match_10;
  }
case_19: ;
  {
    uint64_t zb__9;
    zb__9 = zargz3;
    bool zgsz313;
    zgsz313 = (zb__9 == UINT64_C(0b011111));
    if (!(zgsz313)) {

      goto case_20;
    }
    zcbz32 = zC_D_ADD_1;
    goto finish_match_10;
  }
case_20: ;
  {
    uint64_t zb__10;
    zb__10 = zargz3;
    bool zgsz314;
    zgsz314 = (zb__10 == UINT64_C(0b110111));
    if (!(zgsz314)) {

      goto case_21;
    }
    zcbz32 = zC_A_ADD_1;
    goto finish_match_10;
  }
case_21: ;
  {
    uint64_t zb__11;
    zb__11 = zargz3;
    bool zgsz315;
    zgsz315 = (zb__11 == UINT64_C(0b001110));
    if (!(zgsz315)) {

      goto case_22;
    }
    zcbz32 = zC_D_SUB_1;
    goto finish_match_10;
  }
case_22: ;
  {
    uint64_t zb__12;
    zb__12 = zargz3;
    bool zgsz316;
    zgsz316 = (zb__12 == UINT64_C(0b110010));
    if (!(zgsz316)) {

      goto case_23;
    }
    zcbz32 = zC_A_SUB_1;
    goto finish_match_10;
  }
case_23: ;
  {
    uint64_t zb__13;
    zb__13 = zargz3;
    bool zgsz317;
    zgsz317 = (zb__13 == UINT64_C(0b000010));
    if (!(zgsz317)) {

      goto case_24;
    }
    zcbz32 = zC_D_ADD_A;
    goto finish_match_10;
  }
case_24: ;
  {
    uint64_t zb__14;
    zb__14 = zargz3;
    bool zgsz318;
    zgsz318 = (zb__14 == UINT64_C(0b010011));
    if (!(zgsz318)) {

      goto case_25;
    }
    zcbz32 = zC_D_SUB_A;
    goto finish_match_10;
  }
case_25: ;
  {
    uint64_t zb__15;
    zb__15 = zargz3;
    bool zgsz319;
    zgsz319 = (zb__15 == UINT64_C(0b000111));
    if (!(zgsz319)) {

      goto case_26;
    }
    zcbz32 = zC_A_SUB_D;
    goto finish_match_10;
  }
case_26: ;
  {
    uint64_t zb__16;
    zb__16 = zargz3;
    bool zgsz320;
    zgsz320 = (zb__16 == UINT64_C(0b000000));
    if (!(zgsz320)) {

      goto case_27;
    }
    zcbz32 = zC_D_AND_A;
    goto finish_match_10;
  }
case_27: ;
  {
    uint64_t zb__17;
    zb__17 = zargz3;
    bool zgsz321;
    zgsz321 = (zb__17 == UINT64_C(0b010101));
    if (!(zgsz321)) {

      goto case_28;
    }
    zcbz32 = zC_D_OR_A;
    goto finish_match_10;
  }
case_28: ;
  sail_match_failure("decode_compute_backwards");
finish_match_10: ;
end_function_29: ;
  return zcbz32;
end_block_exception_30: ;

  return zC_A;
}

enum zjump zdecode_jump_backwards(uint64_t);

enum zjump zdecode_jump_backwards(uint64_t zargz3)
{
  __label__ case_33, case_34, case_35, case_36, case_37, case_38, case_39, case_40, finish_match_32, end_function_41, end_block_exception_42;

  enum zjump zcbz33;
  {
    uint64_t zb__0;
    zb__0 = zargz3;
    bool zgsz323;
    zgsz323 = (zb__0 == UINT64_C(0b000));
    if (!(zgsz323)) {

      goto case_33;
    }
    zcbz33 = zJDONT;
    goto finish_match_32;
  }
case_33: ;
  {
    uint64_t zb__1;
    zb__1 = zargz3;
    bool zgsz324;
    zgsz324 = (zb__1 == UINT64_C(0b001));
    if (!(zgsz324)) {

      goto case_34;
    }
    zcbz33 = zJGT;
    goto finish_match_32;
  }
case_34: ;
  {
    uint64_t zb__2;
    zb__2 = zargz3;
    bool zgsz325;
    zgsz325 = (zb__2 == UINT64_C(0b010));
    if (!(zgsz325)) {

      goto case_35;
    }
    zcbz33 = zJEQ;
    goto finish_match_32;
  }
case_35: ;
  {
    uint64_t zb__3;
    zb__3 = zargz3;
    bool zgsz326;
    zgsz326 = (zb__3 == UINT64_C(0b011));
    if (!(zgsz326)) {

      goto case_36;
    }
    zcbz33 = zJGE;
    goto finish_match_32;
  }
case_36: ;
  {
    uint64_t zb__4;
    zb__4 = zargz3;
    bool zgsz327;
    zgsz327 = (zb__4 == UINT64_C(0b100));
    if (!(zgsz327)) {

      goto case_37;
    }
    zcbz33 = zJLT;
    goto finish_match_32;
  }
case_37: ;
  {
    uint64_t zb__5;
    zb__5 = zargz3;
    bool zgsz328;
    zgsz328 = (zb__5 == UINT64_C(0b101));
    if (!(zgsz328)) {

      goto case_38;
    }
    zcbz33 = zJNE;
    goto finish_match_32;
  }
case_38: ;
  {
    uint64_t zb__6;
    zb__6 = zargz3;
    bool zgsz329;
    zgsz329 = (zb__6 == UINT64_C(0b110));
    if (!(zgsz329)) {

      goto case_39;
    }
    zcbz33 = zJLE;
    goto finish_match_32;
  }
case_39: ;
  {
    uint64_t zb__7;
    zb__7 = zargz3;
    bool zgsz330;
    zgsz330 = (zb__7 == UINT64_C(0b111));
    if (!(zgsz330)) {

      goto case_40;
    }
    zcbz33 = zJMP;
    goto finish_match_32;
  }
case_40: ;
  sail_match_failure("decode_jump_backwards");
finish_match_32: ;
end_function_41: ;
  return zcbz33;
end_block_exception_42: ;

  return zJDONT;
}


void zdecode(struct zoptionzIUinstrzIzKzK *rop, uint64_t);


unit zexecute(struct zinstr);

struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zdecode_destination(uint64_t);

struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zdecode_destination(uint64_t zb)
{
  __label__ case_45, finish_match_44, end_function_46, end_block_exception_47;

  struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zcbz34;
  {
    uint64_t zv__0;
    zv__0 = zb;
    uint64_t za;
    za = (safe_rshift(UINT64_MAX, 64 - 1) & (zv__0 >> INT64_C(2)));
    uint64_t zm;
    zm = (safe_rshift(UINT64_MAX, 64 - 1) & (zv__0 >> INT64_C(0)));
    uint64_t zd;
    zd = (safe_rshift(UINT64_MAX, 64 - 1) & (zv__0 >> INT64_C(1)));
    uint64_t zashadowz30;
    zashadowz30 = (safe_rshift(UINT64_MAX, 64 - 1) & (zv__0 >> INT64_C(2)));
    bool zgaz31;
    zgaz31 = zbits1_to_bool(zashadowz30);
    bool zgaz32;
    zgaz32 = zbits1_to_bool(zd);
    bool zgaz33;
    zgaz33 = zbits1_to_bool(zm);
    zcbz34.ztup0 = zgaz31;
    zcbz34.ztup1 = zgaz32;
    zcbz34.ztup2 = zgaz33;
    goto finish_match_44;
  }
case_45: ;
  sail_match_failure("decode_destination");
finish_match_44: ;
end_function_46: ;
  return zcbz34;
end_block_exception_47: ;
  struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zcbz315 = { .ztup2 = false, .ztup1 = false, .ztup0 = false };
  return zcbz315;
}

lbits zghz30;
sail_int zghz31;
lbits zghz32;

void startup_zdecode(void)
{
  CREATE(lbits)(&zghz30);
  CREATE(sail_int)(&zghz31);
  CREATE(lbits)(&zghz32);
}







void zdecode(struct zoptionzIUinstrzIzKzK *zcbz35, uint64_t zmergez3var)
{
  __label__ case_50, case_51, case_52, finish_match_49, end_function_53, end_block_exception_54, end_function_123;

  struct zoptionzIUinstrzIzKzK zgsz334;
  CREATE(zoptionzIUinstrzIzKzK)(&zgsz334);
  {
    uint64_t zv__1;
    zv__1 = zmergez3var;
    uint64_t zgaz36;
    zgaz36 = (safe_rshift(UINT64_MAX, 64 - 1) & (zv__1 >> INT64_C(15)));
    bool zgsz335;
    zgsz335 = (zgaz36 == UINT64_C(0b0));
    if (!(zgsz335)) {

      goto case_50;
    }
    uint64_t zx;
    zx = (safe_rshift(UINT64_MAX, 64 - 15) & (zv__1 >> INT64_C(0)));
    struct zinstr zgaz35;
    CREATE(zinstr)(&zgaz35);
    {
      uint64_t zgaz34;
      {
        RECREATE(lbits)(&zghz30);
        CONVERT_OF(lbits, fbits)(&zghz30, zx, UINT64_C(15) , true);
        RECREATE(sail_int)(&zghz31);
        CONVERT_OF(sail_int, mach_int)(&zghz31, INT64_C(16));
        RECREATE(lbits)(&zghz32);
        zero_extend(&zghz32, zghz30, zghz31);
        zgaz34 = CONVERT_OF(fbits, lbits)(zghz32, true);
      }
      zAINST(&zgaz35, zgaz34);
    }
    zSomezIUinstrzIzKzK(&zgsz334, zgaz35);
    KILL(zinstr)(&zgaz35);
    goto finish_match_49;
  }
case_50: ;
  {
    uint64_t zv__3;
    zv__3 = zmergez3var;
    uint64_t zgaz312;
    zgaz312 = (safe_rshift(UINT64_MAX, 64 - 3) & (zv__3 >> INT64_C(13)));
    bool zgsz337;
    zgsz337 = (zgaz312 == UINT64_C(0b111));
    if (!(zgsz337)) {

      goto case_51;
    }
    uint64_t zjump;
    zjump = (safe_rshift(UINT64_MAX, 64 - 3) & (zv__3 >> INT64_C(0)));
    uint64_t zdest;
    zdest = (safe_rshift(UINT64_MAX, 64 - 3) & (zv__3 >> INT64_C(3)));
    uint64_t zc;
    zc = (safe_rshift(UINT64_MAX, 64 - 6) & (zv__3 >> INT64_C(6)));
    uint64_t za;
    za = (safe_rshift(UINT64_MAX, 64 - 1) & (zv__3 >> INT64_C(12)));
    struct zinstr zgaz311;
    CREATE(zinstr)(&zgaz311);
    {
      struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 zgaz310;
      {
        enum zarithmetic_op zgaz37;
        zgaz37 = zdecode_compute_backwards(zc);
        struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zgaz38;
        zgaz38 = zdecode_destination(zdest);
        enum zjump zgaz39;
        zgaz39 = zdecode_jump_backwards(zjump);
        zgaz310.ztup0 = za;
        zgaz310.ztup1 = zgaz37;
        zgaz310.ztup2 = zgaz38;
        zgaz310.ztup3 = zgaz39;
      }
      zCINST(&zgaz311, zgaz310);
    }
    zSomezIUinstrzIzKzK(&zgsz334, zgaz311);
    KILL(zinstr)(&zgaz311);
    goto finish_match_49;
  }
case_51: ;
  {
    zNonezIUinstrzIzKzK(&zgsz334, UNIT);
    goto finish_match_49;
  }
case_52: ;
  sail_match_failure("decode");
finish_match_49: ;
  COPY(zoptionzIUinstrzIzKzK)((*(&zcbz35)), zgsz334);
  KILL(zoptionzIUinstrzIzKzK)(&zgsz334);
end_function_53: ;
  goto end_function_123;
end_block_exception_54: ;
  goto end_function_123;
end_function_123: ;
}



void finish_zdecode(void)
{
  KILL(lbits)(&zghz32);
  KILL(sail_int)(&zghz31);
  KILL(lbits)(&zghz30);
}

uint64_t zcompute_value(uint64_t, enum zarithmetic_op);

uint64_t zcompute_value(uint64_t za, enum zarithmetic_op zop)
{
  __label__ end_function_75, end_block_exception_76;

  uint64_t zcbz36;
  uint64_t zashadowz31;
  {
    bool zgaz313;
    zgaz313 = (za == UINT64_C(0b0));
    if (zgaz313) {  zashadowz31 = zA;  } else {  zashadowz31 = my_read_mem(zA);  }
  }
  uint64_t zd;
  zd = zD;
  uint64_t zresult;
  {
    __label__ case_57, case_58, case_59, case_60, case_61, case_62, case_63, case_64, case_65, case_66, case_67, case_68, case_69, case_70, case_71, case_72, case_73, case_74, finish_match_56;

    {
      if ((zC_ZERO != zop)) goto case_57;
      zresult = UINT64_C(0x0000);
      goto finish_match_56;
    }
  case_57: ;
    {
      if ((zC_ONE != zop)) goto case_58;
      zresult = UINT64_C(0x0001);
      goto finish_match_56;
    }
  case_58: ;
    {
      if ((zC_MINUSONE != zop)) goto case_59;
      zresult = UINT64_C(0xFFFF);
      goto finish_match_56;
    }
  case_59: ;
    {
      if ((zC_D != zop)) goto case_60;
      zresult = zd;
      goto finish_match_56;
    }
  case_60: ;
    {
      if ((zC_A != zop)) goto case_61;
      zresult = zashadowz31;
      goto finish_match_56;
    }
  case_61: ;
    {
      if ((zC_NOT_D != zop)) goto case_62;
      zresult = (~(zd) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_62: ;
    {
      if ((zC_NOT_A != zop)) goto case_63;
      zresult = (~(zashadowz31) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_63: ;
    {
      if ((zC_NEG_D != zop)) goto case_64;
      zresult = ((UINT64_C(0x0000) - zd) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_64: ;
    {
      if ((zC_NEG_A != zop)) goto case_65;
      zresult = ((UINT64_C(0x0000) - zashadowz31) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_65: ;
    {
      if ((zC_D_ADD_1 != zop)) goto case_66;
      zresult = ((zd + UINT64_C(0x0001)) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_66: ;
    {
      if ((zC_A_ADD_1 != zop)) goto case_67;
      zresult = ((zashadowz31 + UINT64_C(0x0001)) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_67: ;
    {
      if ((zC_D_SUB_1 != zop)) goto case_68;
      zresult = ((zd - UINT64_C(0x0001)) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_68: ;
    {
      if ((zC_A_SUB_1 != zop)) goto case_69;
      zresult = ((zashadowz31 - UINT64_C(0x0001)) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_69: ;
    {
      if ((zC_D_ADD_A != zop)) goto case_70;
      zresult = ((zd + zashadowz31) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_70: ;
    {
      if ((zC_D_SUB_A != zop)) goto case_71;
      zresult = ((zd - zashadowz31) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_71: ;
    {
      if ((zC_A_SUB_D != zop)) goto case_72;
      zresult = ((zashadowz31 - zd) & UINT64_C(0xFFFF));
      goto finish_match_56;
    }
  case_72: ;
    {
      if ((zC_D_AND_A != zop)) goto case_73;
      zresult = (zd & zashadowz31);
      goto finish_match_56;
    }
  case_73: ;
    {
      if ((zC_D_OR_A != zop)) goto case_74;
      zresult = (zd | zashadowz31);
      goto finish_match_56;
    }
  case_74: ;
    sail_match_failure("compute_value");
  finish_match_56: ;
  }
  zcbz36 = zresult;



end_function_75: ;
  return zcbz36;
end_block_exception_76: ;

  return UINT64_C(0xdeadc0de);
}

unit zassign_dest(struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9, uint64_t);

unit zassign_dest(struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zgsz358, uint64_t zvalue)
{
  __label__ fundef_fail_77, fundef_body_78, end_function_79, end_block_exception_80;

  unit zcbz37;
  bool za;
  za = zgsz358.ztup0;
  bool zd;
  zd = zgsz358.ztup1;
  bool zm;
  zm = zgsz358.ztup2;
  goto fundef_body_78;
fundef_fail_77: ;
  sail_match_failure("assign_dest");
fundef_body_78: ;
  {
    unit zgsz360;
    if (zm) {  zgsz360 = my_write_mem(zA, zvalue);  } else {  zgsz360 = UNIT;  }
  }
  {
    unit zgsz359;
    if (za) {
      zA = zvalue;
      zgsz359 = UNIT;
    } else {  zgsz359 = UNIT;  }
  }
  if (zd) {
    zD = zvalue;
    zcbz37 = UNIT;
  } else {  zcbz37 = UNIT;  }



end_function_79: ;
  return zcbz37;
end_block_exception_80: ;

  return UNIT;
}

unit zmaybe_jump(uint64_t, enum zjump);

lbits zghz33;
sail_int zghz34;
lbits zghz35;
lbits zghz36;
sail_int zghz37;
sail_int zghz38;
sail_int zghz39;
lbits zghz310;
sail_int zghz311;
lbits zghz312;
sail_int zghz313;
lbits zghz314;
sail_int zghz315;
lbits zghz316;
sail_int zghz317;
lbits zghz318;
sail_int zghz319;

void startup_zmaybe_jump(void)
{
  CREATE(lbits)(&zghz33);
  CREATE(sail_int)(&zghz34);
  CREATE(lbits)(&zghz35);
  CREATE(lbits)(&zghz36);
  CREATE(sail_int)(&zghz37);
  CREATE(sail_int)(&zghz38);
  CREATE(sail_int)(&zghz39);
  CREATE(lbits)(&zghz310);
  CREATE(sail_int)(&zghz311);
  CREATE(lbits)(&zghz312);
  CREATE(sail_int)(&zghz313);
  CREATE(lbits)(&zghz314);
  CREATE(sail_int)(&zghz315);
  CREATE(lbits)(&zghz316);
  CREATE(sail_int)(&zghz317);
  CREATE(lbits)(&zghz318);
  CREATE(sail_int)(&zghz319);
}

unit zmaybe_jump(uint64_t zvalue, enum zjump zj)
{
  __label__ end_function_91, end_block_exception_92;

  unit zcbz38;
  bool zcond;
  {
    __label__ case_83, case_84, case_85, case_86, case_87, case_88, case_89, case_90, finish_match_82;

    {
      if ((zJDONT != zj)) goto case_83;
      zcond = false;
      goto finish_match_82;
    }
  case_83: ;
    {
      if ((zJGT != zj)) goto case_84;
      int64_t zgaz314;
      {
        RECREATE(lbits)(&zghz318);
        CONVERT_OF(lbits, fbits)(&zghz318, zvalue, UINT64_C(16) , true);
        RECREATE(sail_int)(&zghz319);
        sail_signed(&zghz319, zghz318);
        zgaz314 = CONVERT_OF(mach_int, sail_int)(zghz319);
      }
      zcond = (zgaz314 > INT64_C(0));
      goto finish_match_82;
    }
  case_84: ;
    {
      if ((zJEQ != zj)) goto case_85;
      int64_t zgaz315;
      {
        RECREATE(lbits)(&zghz316);
        CONVERT_OF(lbits, fbits)(&zghz316, zvalue, UINT64_C(16) , true);
        RECREATE(sail_int)(&zghz317);
        sail_signed(&zghz317, zghz316);
        zgaz315 = CONVERT_OF(mach_int, sail_int)(zghz317);
      }
      zcond = (zgaz315 == INT64_C(0));
      goto finish_match_82;
    }
  case_85: ;
    {
      if ((zJGE != zj)) goto case_86;
      int64_t zgaz316;
      {
        RECREATE(lbits)(&zghz314);
        CONVERT_OF(lbits, fbits)(&zghz314, zvalue, UINT64_C(16) , true);
        RECREATE(sail_int)(&zghz315);
        sail_signed(&zghz315, zghz314);
        zgaz316 = CONVERT_OF(mach_int, sail_int)(zghz315);
      }
      zcond = (zgaz316 >= INT64_C(0));
      goto finish_match_82;
    }
  case_86: ;
    {
      if ((zJLT != zj)) goto case_87;
      int64_t zgaz317;
      {
        RECREATE(lbits)(&zghz312);
        CONVERT_OF(lbits, fbits)(&zghz312, zvalue, UINT64_C(16) , true);
        RECREATE(sail_int)(&zghz313);
        sail_signed(&zghz313, zghz312);
        zgaz317 = CONVERT_OF(mach_int, sail_int)(zghz313);
      }
      zcond = (zgaz317 < INT64_C(0));
      goto finish_match_82;
    }
  case_87: ;
    {
      if ((zJNE != zj)) goto case_88;
      int64_t zgaz318;
      {
        RECREATE(lbits)(&zghz310);
        CONVERT_OF(lbits, fbits)(&zghz310, zvalue, UINT64_C(16) , true);
        RECREATE(sail_int)(&zghz311);
        sail_signed(&zghz311, zghz310);
        zgaz318 = CONVERT_OF(mach_int, sail_int)(zghz311);
      }
      {
        RECREATE(sail_int)(&zghz38);
        CONVERT_OF(sail_int, mach_int)(&zghz38, zgaz318);
        RECREATE(sail_int)(&zghz39);
        CONVERT_OF(sail_int, mach_int)(&zghz39, INT64_C(0));
        zcond = zneq_int(zghz38, zghz39);
      }
      goto finish_match_82;
    }
  case_88: ;
    {
      if ((zJLE != zj)) goto case_89;
      int64_t zgaz319;
      {
        RECREATE(lbits)(&zghz36);
        CONVERT_OF(lbits, fbits)(&zghz36, zvalue, UINT64_C(16) , true);
        RECREATE(sail_int)(&zghz37);
        sail_signed(&zghz37, zghz36);
        zgaz319 = CONVERT_OF(mach_int, sail_int)(zghz37);
      }
      zcond = (zgaz319 <= INT64_C(0));
      goto finish_match_82;
    }
  case_89: ;
    {
      if ((zJMP != zj)) goto case_90;
      zcond = true;
      goto finish_match_82;
    }
  case_90: ;
    sail_match_failure("maybe_jump");
  finish_match_82: ;
  }
  if (zcond) {
    zPC = zA;
    zcbz38 = UNIT;
  } else {
    {
      RECREATE(lbits)(&zghz33);
      CONVERT_OF(lbits, fbits)(&zghz33, zPC, UINT64_C(16) , true);
      RECREATE(sail_int)(&zghz34);
      CONVERT_OF(sail_int, mach_int)(&zghz34, INT64_C(1));
      RECREATE(lbits)(&zghz35);
      add_bits_int(&zghz35, zghz33, zghz34);
      zPC = CONVERT_OF(fbits, lbits)(zghz35, true);
    }
    zcbz38 = UNIT;
  }

end_function_91: ;
  return zcbz38;
end_block_exception_92: ;

  return UNIT;
}



void finish_zmaybe_jump(void)
{
  KILL(sail_int)(&zghz319);
  KILL(lbits)(&zghz318);
  KILL(sail_int)(&zghz317);
  KILL(lbits)(&zghz316);
  KILL(sail_int)(&zghz315);
  KILL(lbits)(&zghz314);
  KILL(sail_int)(&zghz313);
  KILL(lbits)(&zghz312);
  KILL(sail_int)(&zghz311);
  KILL(lbits)(&zghz310);
  KILL(sail_int)(&zghz39);
  KILL(sail_int)(&zghz38);
  KILL(sail_int)(&zghz37);
  KILL(lbits)(&zghz36);
  KILL(lbits)(&zghz35);
  KILL(sail_int)(&zghz34);
  KILL(lbits)(&zghz33);
}

lbits zghz320;
sail_int zghz321;
lbits zghz322;

void startup_zexecute(void)
{
  CREATE(lbits)(&zghz320);
  CREATE(sail_int)(&zghz321);
  CREATE(lbits)(&zghz322);
}

unit zexecute(struct zinstr zmergez3var)
{
  __label__ case_95, case_96, finish_match_94, end_function_97, end_block_exception_98;

  unit zcbz39;
  {
    if (zmergez3var.kind != Kind_zAINST) goto case_95;
    uint64_t zx;
    zx = zmergez3var.zAINST;
    {
      zA = zx;
      unit zgsz371;
      zgsz371 = UNIT;
    }
    {
      RECREATE(lbits)(&zghz320);
      CONVERT_OF(lbits, fbits)(&zghz320, zPC, UINT64_C(16) , true);
      RECREATE(sail_int)(&zghz321);
      CONVERT_OF(sail_int, mach_int)(&zghz321, INT64_C(1));
      RECREATE(lbits)(&zghz322);
      add_bits_int(&zghz322, zghz320, zghz321);
      zPC = CONVERT_OF(fbits, lbits)(zghz322, true);
    }
    zcbz39 = UNIT;
    goto finish_match_94;
  }
case_95: ;
  {
    if (zmergez3var.kind != Kind_zCINST) goto case_96;
    uint64_t za;
    za = zmergez3var.zCINST.ztup0;
    enum zarithmetic_op zop;
    zop = zmergez3var.zCINST.ztup1;
    struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zdest;
    zdest = zmergez3var.zCINST.ztup2;
    enum zjump zjump;
    zjump = zmergez3var.zCINST.ztup3;
    uint64_t zvalue;
    zvalue = zcompute_value(za, zop);
    {
      unit zgsz373;
      zgsz373 = zassign_dest(zdest, zvalue);
    }
    zcbz39 = zmaybe_jump(zvalue, zjump);
    goto finish_match_94;
  }
case_96: ;
  sail_match_failure("execute");
finish_match_94: ;
end_function_97: ;
  return zcbz39;
end_block_exception_98: ;

  return UNIT;
}



void finish_zexecute(void)
{
  KILL(lbits)(&zghz322);
  KILL(sail_int)(&zghz321);
  KILL(lbits)(&zghz320);
}

bool zfetch_decode_execute(unit);




bool zfetch_decode_execute(unit zgsz375)
{
  __label__ cleanup_104, end_cleanup_105, end_function_103, end_block_exception_106;

  bool zcbz310;
  uint64_t zinstr;
  zinstr = my_read_rom(zPC);
  struct zoptionzIUinstrzIzKzK zx;
  CREATE(zoptionzIUinstrzIzKzK)(&zx);
  zdecode(&zx, zinstr);
  zcbz310 = false;
  {
    __label__ case_101, case_102, finish_match_100;

    unit zgsz376;
    {
      if (zx.kind != Kind_zSomezIUinstrzIzKzK) goto case_101;
      struct zinstr zinstrshadowz32;
      CREATE(zinstr)(&zinstrshadowz32);
      COPY(zinstr)(&zinstrshadowz32, zx.zSomezIUinstrzIzKzK);
      {
        unit zgsz377;
        zgsz377 = zexecute(zinstrshadowz32);
      }
      zcbz310 = true;
      zgsz376 = UNIT;
      KILL(zinstr)(&zinstrshadowz32);
      goto finish_match_100;
    }
  case_101: ;
    {
      if (zx.kind != Kind_zNonezIUinstrzIzKzK) goto case_102;
      zcbz310 = false;
      zgsz376 = UNIT;
      goto finish_match_100;
    }
  case_102: ;
    sail_match_failure("fetch_decode_execute");
  finish_match_100: ;
    unit zgsz380;
    zgsz380 = zgsz376;
  }
  goto cleanup_104;
  /* unreachable after return */
  KILL(zoptionzIUinstrzIzKzK)(&zx);

  goto end_cleanup_105;
cleanup_104: ;

  KILL(zoptionzIUinstrzIzKzK)(&zx);
  goto end_function_103;
end_cleanup_105: ;
end_function_103: ;
  return zcbz310;
end_block_exception_106: ;

  return false;
}

unit zrun(uint64_t, bool);

lbits zghz323;
sail_int zghz324;
lbits zghz325;
sail_int zghz326;

void startup_zrun(void)
{
  CREATE(lbits)(&zghz323);
  CREATE(sail_int)(&zghz324);
  CREATE(lbits)(&zghz325);
  CREATE(sail_int)(&zghz326);
}

unit zrun(uint64_t zlimit, bool zdebug)
{
  __label__ while_108, wend_109, end_function_110, end_block_exception_111;

  unit zcbz311;
  uint64_t zcycle_count;
  zcycle_count = UINT64_C(0x0000000000000000);
  bool zcont;
  zcont = true;
  bool zgsz384;
  unit zgsz385;
while_108: ;
  {
    zgsz384 = zcont;
    if (!(zgsz384)) goto wend_109;
    {
      zcont = false;
      unit zgsz383;
      zgsz383 = UNIT;
    }
    {
      unit zgsz382;
      if (zdebug) {  zgsz382 = my_print_debug(zcycle_count, zPC, zA, zD);  } else {  zgsz382 = UNIT;  }
    }
    {
      bool zgaz320;
      zgaz320 = zfetch_decode_execute(UNIT);
      unit zgsz381;
      if (zgaz320) {
        bool zgaz323;
        {
          int64_t zgaz321;
          {
            RECREATE(lbits)(&zghz325);
            CONVERT_OF(lbits, fbits)(&zghz325, zcycle_count, UINT64_C(64) , true);
            RECREATE(sail_int)(&zghz326);
            sail_signed(&zghz326, zghz325);
            zgaz321 = CONVERT_OF(mach_int, sail_int)(zghz326);
          }
          int64_t zgaz322;
          {
            RECREATE(lbits)(&zghz323);
            CONVERT_OF(lbits, fbits)(&zghz323, zlimit, UINT64_C(64) , true);
            RECREATE(sail_int)(&zghz324);
            sail_signed(&zghz324, zghz323);
            zgaz322 = CONVERT_OF(mach_int, sail_int)(zghz324);
          }
          zgaz323 = (zgaz321 < zgaz322);
        }
        if (zgaz323) {
          zcont = true;
          zgsz381 = UNIT;
        } else {  zgsz381 = UNIT;  }
      } else {  zgsz381 = UNIT;  }
    }
    zcycle_count = ((zcycle_count + UINT64_C(0x0000000000000001)) & UINT64_C(0xFFFFFFFFFFFFFFFF));
    zgsz385 = UNIT;
    goto while_108;
  }
wend_109: ;
  zcbz311 = UNIT;


end_function_110: ;
  return zcbz311;
end_block_exception_111: ;

  return UNIT;
}



void finish_zrun(void)
{
  KILL(sail_int)(&zghz326);
  KILL(lbits)(&zghz325);
  KILL(sail_int)(&zghz324);
  KILL(lbits)(&zghz323);
}

unit zmymain(uint64_t, bool);

unit zmymain(uint64_t zlimit, bool zdebug)
{
  __label__ end_function_113, end_block_exception_114;

  unit zcbz312;
  {
    zPC = UINT64_C(0x0000);
    unit zgsz388;
    zgsz388 = UNIT;
  }
  {
    zA = UINT64_C(0x0000);
    unit zgsz387;
    zgsz387 = UNIT;
  }
  {
    zD = UINT64_C(0x0000);
    unit zgsz386;
    zgsz386 = UNIT;
  }
  zcbz312 = zrun(zlimit, zdebug);
end_function_113: ;
  return zcbz312;
end_block_exception_114: ;

  return UNIT;
}

unit zmain(unit);

unit zmain(unit zgsz389)
{
  __label__ cleanup_117, end_cleanup_118, end_function_116, end_block_exception_119;

  unit zcbz313;
  zcbz313 = zmymain(UINT64_C(0x0000000000000010), false);
  goto cleanup_117;
  /* unreachable after return */
  goto end_cleanup_118;
cleanup_117: ;
  goto end_function_116;
end_cleanup_118: ;
end_function_116: ;
  return zcbz313;
end_block_exception_119: ;

  return UNIT;
}

unit zinitializze_registers(unit);

sail_int zghz327;
lbits zghz328;
sail_int zghz329;
lbits zghz330;
sail_int zghz331;
lbits zghz332;

void startup_zinitializze_registers(void)
{
  CREATE(sail_int)(&zghz327);
  CREATE(lbits)(&zghz328);
  CREATE(sail_int)(&zghz329);
  CREATE(lbits)(&zghz330);
  CREATE(sail_int)(&zghz331);
  CREATE(lbits)(&zghz332);
}

unit zinitializze_registers(unit zgsz390)
{
  __label__ end_function_121, end_block_exception_122;

  unit zcbz314;
  {
    {
      RECREATE(sail_int)(&zghz331);
      CONVERT_OF(sail_int, mach_int)(&zghz331, INT64_C(16));
      RECREATE(lbits)(&zghz332);
      UNDEFINED(lbits)(&zghz332, zghz331);
      zPC = CONVERT_OF(fbits, lbits)(zghz332, true);
    }
    unit zgsz392;
    zgsz392 = UNIT;
  }
  {
    {
      RECREATE(sail_int)(&zghz329);
      CONVERT_OF(sail_int, mach_int)(&zghz329, INT64_C(16));
      RECREATE(lbits)(&zghz330);
      UNDEFINED(lbits)(&zghz330, zghz329);
      zA = CONVERT_OF(fbits, lbits)(zghz330, true);
    }
    unit zgsz391;
    zgsz391 = UNIT;
  }
  {
    RECREATE(sail_int)(&zghz327);
    CONVERT_OF(sail_int, mach_int)(&zghz327, INT64_C(16));
    RECREATE(lbits)(&zghz328);
    UNDEFINED(lbits)(&zghz328, zghz327);
    zD = CONVERT_OF(fbits, lbits)(zghz328, true);
  }
  zcbz314 = UNIT;
end_function_121: ;
  return zcbz314;
end_block_exception_122: ;

  return UNIT;
}



void finish_zinitializze_registers(void)
{
  KILL(lbits)(&zghz332);
  KILL(sail_int)(&zghz331);
  KILL(lbits)(&zghz330);
  KILL(sail_int)(&zghz329);
  KILL(lbits)(&zghz328);
  KILL(sail_int)(&zghz327);
}

void model_init(void)
{
  setup_rts();
  current_exception = sail_malloc(sizeof(struct zexception));
  CREATE(zexception)(current_exception);
  throw_location = sail_malloc(sizeof(sail_string));
  CREATE(sail_string)(throw_location);
  startup_zdecode();
  startup_zmaybe_jump();
  startup_zexecute();
  startup_zrun();
  startup_zinitializze_registers();
  zinitializze_registers(UNIT);
}

void model_fini(void)
{
  finish_zdecode();
  finish_zmaybe_jump();
  finish_zexecute();
  finish_zrun();
  finish_zinitializze_registers();
  cleanup_rts();
  if (have_exception) {fprintf(stderr, "Exiting due to uncaught exception: %s\n", *throw_location);}
  KILL(zexception)(current_exception);
  sail_free(current_exception);
  KILL(sail_string)(throw_location);
  sail_free(throw_location);
  if (have_exception) {exit(EXIT_FAILURE);}
}

void model_pre_exit()
{
}

int model_main(int argc, char *argv[])
{
  model_init();
  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);
  zmain(UNIT);
  model_fini();
  model_pre_exit();
  return EXIT_SUCCESS;
}


