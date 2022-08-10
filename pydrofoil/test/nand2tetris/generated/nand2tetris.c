#include "sail.h"
#include "rts.h"
#include "elf.h"
#include "../nandsupport.h"

// enum jump
enum zjump { zJDONT, zJGT, zJEQ, zJGE, zJLT, zJNE, zJLE, zJMP };

static bool eq_zjump(enum zjump op1, enum zjump op2) { return op1 == op2; }

static enum zjump UNDEFINED(zjump)(unit u) { return zJDONT; }

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


// union option
enum kind_zoption { Kind_zNone, Kind_zSomez3z5unionz0zzinstr };

struct zoption {
  enum kind_zoption kind;
  union {
    struct { unit zNone; };
    struct { struct zinstr zSomez3z5unionz0zzinstr; };
  };
};

static void CREATE(zoption)(struct zoption *op)
{
  op->kind = Kind_zNone;

}

static void RECREATE(zoption)(struct zoption *op) {}

static void KILL(zoption)(struct zoption *op)
{
  if (op->kind == Kind_zNone) {
    /* do nothing */
  } else if (op->kind == Kind_zSomez3z5unionz0zzinstr){
    KILL(zinstr)(&op->zSomez3z5unionz0zzinstr);
  };
}

static void COPY(zoption)(struct zoption *rop, struct zoption op)
{
  if (rop->kind == Kind_zNone) {
    /* do nothing */
  } else if (rop->kind == Kind_zSomez3z5unionz0zzinstr){
    KILL(zinstr)(&rop->zSomez3z5unionz0zzinstr);
  };
  rop->kind = op.kind;
  if (op.kind == Kind_zNone) {
    rop->zNone = op.zNone;
  } else if (op.kind == Kind_zSomez3z5unionz0zzinstr){

  CREATE(zinstr)(&rop->zSomez3z5unionz0zzinstr); COPY(zinstr)(&rop->zSomez3z5unionz0zzinstr, op.zSomez3z5unionz0zzinstr);
  }
}

static bool EQUAL(zoption)(struct zoption op1, struct zoption op2) {
  if (op1.kind == Kind_zNone && op2.kind == Kind_zNone) {
    return EQUAL(unit)(op1.zNone, op2.zNone);
  } else if (op1.kind == Kind_zSomez3z5unionz0zzinstr && op2.kind == Kind_zSomez3z5unionz0zzinstr) {
    return EQUAL(zinstr)(op1.zSomez3z5unionz0zzinstr, op2.zSomez3z5unionz0zzinstr);
  } else return false;
}

static void zNone(struct zoption *rop, unit op)
{
  if (rop->kind == Kind_zNone) {
    /* do nothing */
  } else if (rop->kind == Kind_zSomez3z5unionz0zzinstr){
    KILL(zinstr)(&rop->zSomez3z5unionz0zzinstr);
  }
  rop->kind = Kind_zNone;
  rop->zNone = op;
}

static void zSomez3z5unionz0zzinstr(struct zoption *rop, struct zinstr op)
{
  if (rop->kind == Kind_zNone) {
    /* do nothing */
  } else if (rop->kind == Kind_zSomez3z5unionz0zzinstr){
    KILL(zinstr)(&rop->zSomez3z5unionz0zzinstr);
  }
  rop->kind = Kind_zSomez3z5unionz0zzinstr;
  CREATE(zinstr)(&rop->zSomez3z5unionz0zzinstr);
  COPY(zinstr)(&rop->zSomez3z5unionz0zzinstr, op);

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

















void zsail_mask(lbits *rop, sail_int, lbits);

sail_int zghz30;

void startup_zsail_mask(void)
{    CREATE(sail_int)(&zghz30);
}

void zsail_mask(lbits *zcbz31, sail_int zlen, lbits zv)
{
  __label__ end_function_4, end_block_exception_5, end_function_135;

  bool zgaz32;
  {
    RECREATE(sail_int)(&zghz30);
    length_lbits(&zghz30, zv);
    zgaz32 = lteq(zlen, zghz30);
  }
  if (zgaz32) {  sail_truncate((*(&zcbz31)), zv, zlen);  } else {  zero_extend((*(&zcbz31)), zv, zlen);  }

end_function_4: ;
  goto end_function_135;
end_block_exception_5: ;
  goto end_function_135;
end_function_135: ;
}



void finish_zsail_mask(void)
{    KILL(sail_int)(&zghz30);
}





















void zsail_ones(lbits *rop, sail_int);

lbits zghz31;

void startup_zsail_ones(void)
{    CREATE(lbits)(&zghz31);
}

void zsail_ones(lbits *zcbz32, sail_int zn)
{
  __label__ end_function_7, end_block_exception_8, end_function_134;

  RECREATE(lbits)(&zghz31);
  zeros(&zghz31, zn);
  not_bits((*(&zcbz32)), zghz31);
end_function_7: ;
  goto end_function_134;
end_block_exception_8: ;
  goto end_function_134;
end_function_134: ;
}



void finish_zsail_ones(void)
{    KILL(lbits)(&zghz31);
}











void zfdiv_int(sail_int *rop, sail_int, sail_int);

sail_int zghz32;
sail_int zghz33;
sail_int zghz34;
sail_int zghz35;
sail_int zghz36;
sail_int zghz37;
sail_int zghz38;
sail_int zghz39;
sail_int zghz310;
sail_int zghz311;
sail_int zghz312;
sail_int zghz313;

void startup_zfdiv_int(void)
{
  CREATE(sail_int)(&zghz32);
  CREATE(sail_int)(&zghz33);
  CREATE(sail_int)(&zghz34);
  CREATE(sail_int)(&zghz35);
  CREATE(sail_int)(&zghz36);
  CREATE(sail_int)(&zghz37);
  CREATE(sail_int)(&zghz38);
  CREATE(sail_int)(&zghz39);
  CREATE(sail_int)(&zghz310);
  CREATE(sail_int)(&zghz311);
  CREATE(sail_int)(&zghz312);
  CREATE(sail_int)(&zghz313);
}

void zfdiv_int(sail_int *zcbz33, sail_int zn, sail_int zm)
{
  __label__ end_function_10, end_block_exception_11, end_function_133;

  bool zgaz35;
  {
    bool zgaz34;
    {
      RECREATE(sail_int)(&zghz313);
      CONVERT_OF(sail_int, mach_int)(&zghz313, INT64_C(0));
      zgaz34 = lt(zn, zghz313);
    }
    bool zgsz31;
    if (zgaz34) {
    {
      RECREATE(sail_int)(&zghz312);
      CONVERT_OF(sail_int, mach_int)(&zghz312, INT64_C(0));
      zgsz31 = gt(zm, zghz312);
    }
    } else {  zgsz31 = false;  }
    zgaz35 = zgsz31;

  }
  if (zgaz35) {
  RECREATE(sail_int)(&zghz38);
  {
    RECREATE(sail_int)(&zghz310);
    {
      RECREATE(sail_int)(&zghz311);
      CONVERT_OF(sail_int, mach_int)(&zghz311, INT64_C(1));
      add_int(&zghz310, zn, zghz311);
    }
    tdiv_int(&zghz38, zghz310, zm);
  }
  {
    RECREATE(sail_int)(&zghz39);
    CONVERT_OF(sail_int, mach_int)(&zghz39, INT64_C(1));
    sub_int((*(&zcbz33)), zghz38, zghz39);
  }
  } else {
  bool zgaz39;
  {
    bool zgaz38;
    {
      RECREATE(sail_int)(&zghz37);
      CONVERT_OF(sail_int, mach_int)(&zghz37, INT64_C(0));
      zgaz38 = gt(zn, zghz37);
    }
    bool zgsz34;
    if (zgaz38) {
    {
      RECREATE(sail_int)(&zghz36);
      CONVERT_OF(sail_int, mach_int)(&zghz36, INT64_C(0));
      zgsz34 = lt(zm, zghz36);
    }
    } else {  zgsz34 = false;  }
    zgaz39 = zgsz34;

  }
  if (zgaz39) {
  RECREATE(sail_int)(&zghz32);
  {
    RECREATE(sail_int)(&zghz34);
    {
      RECREATE(sail_int)(&zghz35);
      CONVERT_OF(sail_int, mach_int)(&zghz35, INT64_C(1));
      sub_int(&zghz34, zn, zghz35);
    }
    tdiv_int(&zghz32, zghz34, zm);
  }
  {
    RECREATE(sail_int)(&zghz33);
    CONVERT_OF(sail_int, mach_int)(&zghz33, INT64_C(1));
    sub_int((*(&zcbz33)), zghz32, zghz33);
  }
  } else {  tdiv_int((*(&zcbz33)), zn, zm);  }

  }

end_function_10: ;
  goto end_function_133;
end_block_exception_11: ;
  goto end_function_133;
end_function_133: ;
}



void finish_zfdiv_int(void)
{
  KILL(sail_int)(&zghz313);
  KILL(sail_int)(&zghz312);
  KILL(sail_int)(&zghz311);
  KILL(sail_int)(&zghz310);
  KILL(sail_int)(&zghz39);
  KILL(sail_int)(&zghz38);
  KILL(sail_int)(&zghz37);
  KILL(sail_int)(&zghz36);
  KILL(sail_int)(&zghz35);
  KILL(sail_int)(&zghz34);
  KILL(sail_int)(&zghz33);
  KILL(sail_int)(&zghz32);
}



bool zbits1_to_bool(uint64_t);

bool zbits1_to_bool(uint64_t zb)
{
  __label__ case_14, case_15, finish_match_13, end_function_16, end_block_exception_17;

  bool zcbz34;
  {
    uint64_t zb__0;
    zb__0 = zb;
    bool zgsz311;
    zgsz311 = (zb__0 == UINT64_C(0b1));
    if (!(zgsz311)) {

    goto case_14;
    }
    zcbz34 = true;

    goto finish_match_13;
  }
case_14: ;
  {
    uint64_t zb__1;
    zb__1 = zb;
    bool zgsz312;
    zgsz312 = (zb__1 == UINT64_C(0b0));
    if (!(zgsz312)) {

    goto case_15;
    }
    zcbz34 = false;

    goto finish_match_13;
  }
case_15: ;
  sail_match_failure("bits1_to_bool");
finish_match_13: ;
end_function_16: ;
  return zcbz34;
end_block_exception_17: ;

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
  __label__ case_20, case_21, case_22, case_23, case_24, case_25, case_26, case_27, case_28, case_29, case_30, case_31, case_32, case_33, case_34, case_35, case_36, case_37, finish_match_19, end_function_38, end_block_exception_39;

  enum zarithmetic_op zcbz35;
  {
    uint64_t zb__0;
    zb__0 = zargz3;
    bool zgsz314;
    zgsz314 = (zb__0 == UINT64_C(0b101010));
    if (!(zgsz314)) {

    goto case_20;
    }
    zcbz35 = zC_ZERO;

    goto finish_match_19;
  }
case_20: ;
  {
    uint64_t zb__1;
    zb__1 = zargz3;
    bool zgsz315;
    zgsz315 = (zb__1 == UINT64_C(0b111111));
    if (!(zgsz315)) {

    goto case_21;
    }
    zcbz35 = zC_ONE;

    goto finish_match_19;
  }
case_21: ;
  {
    uint64_t zb__2;
    zb__2 = zargz3;
    bool zgsz316;
    zgsz316 = (zb__2 == UINT64_C(0b111010));
    if (!(zgsz316)) {

    goto case_22;
    }
    zcbz35 = zC_MINUSONE;

    goto finish_match_19;
  }
case_22: ;
  {
    uint64_t zb__3;
    zb__3 = zargz3;
    bool zgsz317;
    zgsz317 = (zb__3 == UINT64_C(0b001100));
    if (!(zgsz317)) {

    goto case_23;
    }
    zcbz35 = zC_D;

    goto finish_match_19;
  }
case_23: ;
  {
    uint64_t zb__4;
    zb__4 = zargz3;
    bool zgsz318;
    zgsz318 = (zb__4 == UINT64_C(0b110000));
    if (!(zgsz318)) {

    goto case_24;
    }
    zcbz35 = zC_A;

    goto finish_match_19;
  }
case_24: ;
  {
    uint64_t zb__5;
    zb__5 = zargz3;
    bool zgsz319;
    zgsz319 = (zb__5 == UINT64_C(0b001101));
    if (!(zgsz319)) {

    goto case_25;
    }
    zcbz35 = zC_NOT_D;

    goto finish_match_19;
  }
case_25: ;
  {
    uint64_t zb__6;
    zb__6 = zargz3;
    bool zgsz320;
    zgsz320 = (zb__6 == UINT64_C(0b110001));
    if (!(zgsz320)) {

    goto case_26;
    }
    zcbz35 = zC_NOT_A;

    goto finish_match_19;
  }
case_26: ;
  {
    uint64_t zb__7;
    zb__7 = zargz3;
    bool zgsz321;
    zgsz321 = (zb__7 == UINT64_C(0b001111));
    if (!(zgsz321)) {

    goto case_27;
    }
    zcbz35 = zC_NEG_D;

    goto finish_match_19;
  }
case_27: ;
  {
    uint64_t zb__8;
    zb__8 = zargz3;
    bool zgsz322;
    zgsz322 = (zb__8 == UINT64_C(0b110011));
    if (!(zgsz322)) {

    goto case_28;
    }
    zcbz35 = zC_NEG_A;

    goto finish_match_19;
  }
case_28: ;
  {
    uint64_t zb__9;
    zb__9 = zargz3;
    bool zgsz323;
    zgsz323 = (zb__9 == UINT64_C(0b011111));
    if (!(zgsz323)) {

    goto case_29;
    }
    zcbz35 = zC_D_ADD_1;

    goto finish_match_19;
  }
case_29: ;
  {
    uint64_t zb__10;
    zb__10 = zargz3;
    bool zgsz324;
    zgsz324 = (zb__10 == UINT64_C(0b110111));
    if (!(zgsz324)) {

    goto case_30;
    }
    zcbz35 = zC_A_ADD_1;

    goto finish_match_19;
  }
case_30: ;
  {
    uint64_t zb__11;
    zb__11 = zargz3;
    bool zgsz325;
    zgsz325 = (zb__11 == UINT64_C(0b001110));
    if (!(zgsz325)) {

    goto case_31;
    }
    zcbz35 = zC_D_SUB_1;

    goto finish_match_19;
  }
case_31: ;
  {
    uint64_t zb__12;
    zb__12 = zargz3;
    bool zgsz326;
    zgsz326 = (zb__12 == UINT64_C(0b110010));
    if (!(zgsz326)) {

    goto case_32;
    }
    zcbz35 = zC_A_SUB_1;

    goto finish_match_19;
  }
case_32: ;
  {
    uint64_t zb__13;
    zb__13 = zargz3;
    bool zgsz327;
    zgsz327 = (zb__13 == UINT64_C(0b000010));
    if (!(zgsz327)) {

    goto case_33;
    }
    zcbz35 = zC_D_ADD_A;

    goto finish_match_19;
  }
case_33: ;
  {
    uint64_t zb__14;
    zb__14 = zargz3;
    bool zgsz328;
    zgsz328 = (zb__14 == UINT64_C(0b010011));
    if (!(zgsz328)) {

    goto case_34;
    }
    zcbz35 = zC_D_SUB_A;

    goto finish_match_19;
  }
case_34: ;
  {
    uint64_t zb__15;
    zb__15 = zargz3;
    bool zgsz329;
    zgsz329 = (zb__15 == UINT64_C(0b000111));
    if (!(zgsz329)) {

    goto case_35;
    }
    zcbz35 = zC_A_SUB_D;

    goto finish_match_19;
  }
case_35: ;
  {
    uint64_t zb__16;
    zb__16 = zargz3;
    bool zgsz330;
    zgsz330 = (zb__16 == UINT64_C(0b000000));
    if (!(zgsz330)) {

    goto case_36;
    }
    zcbz35 = zC_D_AND_A;

    goto finish_match_19;
  }
case_36: ;
  {
    uint64_t zb__17;
    zb__17 = zargz3;
    bool zgsz331;
    zgsz331 = (zb__17 == UINT64_C(0b010101));
    if (!(zgsz331)) {

    goto case_37;
    }
    zcbz35 = zC_D_OR_A;

    goto finish_match_19;
  }
case_37: ;
  sail_match_failure("decode_compute_backwards");
finish_match_19: ;
end_function_38: ;
  return zcbz35;
end_block_exception_39: ;

  return zC_A;
}

enum zjump zdecode_jump_backwards(uint64_t);

enum zjump zdecode_jump_backwards(uint64_t zargz3)
{
  __label__ case_42, case_43, case_44, case_45, case_46, case_47, case_48, case_49, finish_match_41, end_function_50, end_block_exception_51;

  enum zjump zcbz36;
  {
    uint64_t zb__0;
    zb__0 = zargz3;
    bool zgsz333;
    zgsz333 = (zb__0 == UINT64_C(0b000));
    if (!(zgsz333)) {

    goto case_42;
    }
    zcbz36 = zJDONT;

    goto finish_match_41;
  }
case_42: ;
  {
    uint64_t zb__1;
    zb__1 = zargz3;
    bool zgsz334;
    zgsz334 = (zb__1 == UINT64_C(0b001));
    if (!(zgsz334)) {

    goto case_43;
    }
    zcbz36 = zJGT;

    goto finish_match_41;
  }
case_43: ;
  {
    uint64_t zb__2;
    zb__2 = zargz3;
    bool zgsz335;
    zgsz335 = (zb__2 == UINT64_C(0b010));
    if (!(zgsz335)) {

    goto case_44;
    }
    zcbz36 = zJEQ;

    goto finish_match_41;
  }
case_44: ;
  {
    uint64_t zb__3;
    zb__3 = zargz3;
    bool zgsz336;
    zgsz336 = (zb__3 == UINT64_C(0b011));
    if (!(zgsz336)) {

    goto case_45;
    }
    zcbz36 = zJGE;

    goto finish_match_41;
  }
case_45: ;
  {
    uint64_t zb__4;
    zb__4 = zargz3;
    bool zgsz337;
    zgsz337 = (zb__4 == UINT64_C(0b100));
    if (!(zgsz337)) {

    goto case_46;
    }
    zcbz36 = zJLT;

    goto finish_match_41;
  }
case_46: ;
  {
    uint64_t zb__5;
    zb__5 = zargz3;
    bool zgsz338;
    zgsz338 = (zb__5 == UINT64_C(0b101));
    if (!(zgsz338)) {

    goto case_47;
    }
    zcbz36 = zJNE;

    goto finish_match_41;
  }
case_47: ;
  {
    uint64_t zb__6;
    zb__6 = zargz3;
    bool zgsz339;
    zgsz339 = (zb__6 == UINT64_C(0b110));
    if (!(zgsz339)) {

    goto case_48;
    }
    zcbz36 = zJLE;

    goto finish_match_41;
  }
case_48: ;
  {
    uint64_t zb__7;
    zb__7 = zargz3;
    bool zgsz340;
    zgsz340 = (zb__7 == UINT64_C(0b111));
    if (!(zgsz340)) {

    goto case_49;
    }
    zcbz36 = zJMP;

    goto finish_match_41;
  }
case_49: ;
  sail_match_failure("decode_jump_backwards");
finish_match_41: ;
end_function_50: ;
  return zcbz36;
end_block_exception_51: ;

  return zJDONT;
}


void zdecode(struct zoption *rop, uint64_t);


unit zexecute(struct zinstr);

struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zdecode_destination(uint64_t);

struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zdecode_destination(uint64_t zb)
{
  __label__ case_54, finish_match_53, end_function_55, end_block_exception_56;

  struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zcbz37;
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
    bool zgaz312;
    zgaz312 = zbits1_to_bool(zashadowz30);
    bool zgaz313;
    zgaz313 = zbits1_to_bool(zd);
    bool zgaz314;
    zgaz314 = zbits1_to_bool(zm);
    zcbz37.ztup0 = zgaz312;
    zcbz37.ztup1 = zgaz313;
    zcbz37.ztup2 = zgaz314;








    goto finish_match_53;
  }
case_54: ;
  sail_match_failure("decode_destination");
finish_match_53: ;
end_function_55: ;
  return zcbz37;
end_block_exception_56: ;
  struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zcbz318 = { .ztup2 = false, .ztup1 = false, .ztup0 = false };
  return zcbz318;
}

lbits zghz314;
sail_int zghz315;
lbits zghz316;

void startup_zdecode(void)
{
  CREATE(lbits)(&zghz314);
  CREATE(sail_int)(&zghz315);
  CREATE(lbits)(&zghz316);
}







void zdecode(struct zoption *zcbz38, uint64_t zmergez3var)
{
  __label__ case_59, case_60, case_61, finish_match_58, end_function_62, end_block_exception_63, end_function_132;

  struct zoption zgsz344;
  CREATE(zoption)(&zgsz344);
  {
    uint64_t zv__1;
    zv__1 = zmergez3var;
    uint64_t zgaz317;
    zgaz317 = (safe_rshift(UINT64_MAX, 64 - 1) & (zv__1 >> INT64_C(15)));
    bool zgsz348;
    zgsz348 = (zgaz317 == UINT64_C(0b0));

    if (!(zgsz348)) {

    goto case_59;
    }
    uint64_t zx;
    zx = (safe_rshift(UINT64_MAX, 64 - 15) & (zv__1 >> INT64_C(0)));
    struct zinstr zgaz316;
    CREATE(zinstr)(&zgaz316);
    {
      uint64_t zgaz315;
      {
        RECREATE(lbits)(&zghz314);
        CONVERT_OF(lbits, fbits)(&zghz314, zx, UINT64_C(15) , true);
        RECREATE(sail_int)(&zghz315);
        CONVERT_OF(sail_int, mach_int)(&zghz315, INT64_C(16));
        RECREATE(lbits)(&zghz316);
        zero_extend(&zghz316, zghz314, zghz315);
        zgaz315 = CONVERT_OF(fbits, lbits)(zghz316, true);
      }
      zAINST(&zgaz316, zgaz315);

    }
    {
      struct zinstr zgsz3120;
      CREATE(zinstr)(&zgsz3120);
      COPY(zinstr)(&zgsz3120, zgaz316);
      zSomez3z5unionz0zzinstr(&zgsz344, zgsz3120);
      KILL(zinstr)(&zgsz3120);
    }
    KILL(zinstr)(&zgaz316);


    goto finish_match_58;
  }
case_59: ;
  {
    uint64_t zv__3;
    zv__3 = zmergez3var;
    uint64_t zgaz323;
    zgaz323 = (safe_rshift(UINT64_MAX, 64 - 3) & (zv__3 >> INT64_C(13)));
    bool zgsz350;
    zgsz350 = (zgaz323 == UINT64_C(0b111));

    if (!(zgsz350)) {

    goto case_60;
    }
    uint64_t zjump;
    zjump = (safe_rshift(UINT64_MAX, 64 - 3) & (zv__3 >> INT64_C(0)));
    uint64_t zdest;
    zdest = (safe_rshift(UINT64_MAX, 64 - 3) & (zv__3 >> INT64_C(3)));
    uint64_t zc;
    zc = (safe_rshift(UINT64_MAX, 64 - 6) & (zv__3 >> INT64_C(6)));
    uint64_t za;
    za = (safe_rshift(UINT64_MAX, 64 - 1) & (zv__3 >> INT64_C(12)));
    struct zinstr zgaz322;
    CREATE(zinstr)(&zgaz322);
    {
      struct ztuple_z8z5bv1zCz0z5enumz0zzarithmetic_opzCz0z8z5boolzCz0z5boolzCz0z5boolz9zCz0z5enumz0zzjumpz9 zgaz321;
      {
        enum zarithmetic_op zgaz318;
        zgaz318 = zdecode_compute_backwards(zc);
        struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zgaz319;
        zgaz319 = zdecode_destination(zdest);
        enum zjump zgaz320;
        zgaz320 = zdecode_jump_backwards(zjump);
        zgaz321.ztup0 = za;
        zgaz321.ztup1 = zgaz318;
        zgaz321.ztup2 = zgaz319;
        zgaz321.ztup3 = zgaz320;



      }
      zCINST(&zgaz322, zgaz321);

    }
    {
      struct zinstr zgsz3121;
      CREATE(zinstr)(&zgsz3121);
      COPY(zinstr)(&zgsz3121, zgaz322);
      zSomez3z5unionz0zzinstr(&zgsz344, zgsz3121);
      KILL(zinstr)(&zgsz3121);
    }
    KILL(zinstr)(&zgaz322);





    goto finish_match_58;
  }
case_60: ;
  {
    zNone(&zgsz344, UNIT);
    goto finish_match_58;
  }
case_61: ;
  sail_match_failure("decode");
finish_match_58: ;
  COPY(zoption)((*(&zcbz38)), zgsz344);
  KILL(zoption)(&zgsz344);
end_function_62: ;
  goto end_function_132;
end_block_exception_63: ;
  goto end_function_132;
end_function_132: ;
}



void finish_zdecode(void)
{
  KILL(lbits)(&zghz316);
  KILL(sail_int)(&zghz315);
  KILL(lbits)(&zghz314);
}

uint64_t zcompute_value(uint64_t, enum zarithmetic_op);

uint64_t zcompute_value(uint64_t za, enum zarithmetic_op zop)
{
  __label__ end_function_84, end_block_exception_85;

  uint64_t zcbz39;
  uint64_t zashadowz31;
  {
    bool zgaz324;
    zgaz324 = (za == UINT64_C(0b0));
    if (zgaz324) {  zashadowz31 = zA;  } else {  zashadowz31 = my_read_mem(zA);  }

  }
  uint64_t zd;
  zd = zD;
  uint64_t zresult;
  {
    __label__ case_66, case_67, case_68, case_69, case_70, case_71, case_72, case_73, case_74, case_75, case_76, case_77, case_78, case_79, case_80, case_81, case_82, case_83, finish_match_65;

    {
      if ((zC_ZERO != zop)) goto case_66;
      zresult = UINT64_C(0x0000);
      goto finish_match_65;
    }
  case_66: ;
    {
      if ((zC_ONE != zop)) goto case_67;
      zresult = UINT64_C(0x0001);
      goto finish_match_65;
    }
  case_67: ;
    {
      if ((zC_MINUSONE != zop)) goto case_68;
      zresult = UINT64_C(0xFFFF);
      goto finish_match_65;
    }
  case_68: ;
    {
      if ((zC_D != zop)) goto case_69;
      zresult = zd;
      goto finish_match_65;
    }
  case_69: ;
    {
      if ((zC_A != zop)) goto case_70;
      zresult = zashadowz31;
      goto finish_match_65;
    }
  case_70: ;
    {
      if ((zC_NOT_D != zop)) goto case_71;
      zresult = (~(zd) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_71: ;
    {
      if ((zC_NOT_A != zop)) goto case_72;
      zresult = (~(zashadowz31) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_72: ;
    {
      if ((zC_NEG_D != zop)) goto case_73;
      zresult = ((UINT64_C(0x0000) - zd) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_73: ;
    {
      if ((zC_NEG_A != zop)) goto case_74;
      zresult = ((UINT64_C(0x0000) - zashadowz31) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_74: ;
    {
      if ((zC_D_ADD_1 != zop)) goto case_75;
      zresult = ((zd + UINT64_C(0x0001)) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_75: ;
    {
      if ((zC_A_ADD_1 != zop)) goto case_76;
      zresult = ((zashadowz31 + UINT64_C(0x0001)) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_76: ;
    {
      if ((zC_D_SUB_1 != zop)) goto case_77;
      zresult = ((zd - UINT64_C(0x0001)) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_77: ;
    {
      if ((zC_A_SUB_1 != zop)) goto case_78;
      zresult = ((zashadowz31 - UINT64_C(0x0001)) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_78: ;
    {
      if ((zC_D_ADD_A != zop)) goto case_79;
      zresult = ((zd + zashadowz31) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_79: ;
    {
      if ((zC_D_SUB_A != zop)) goto case_80;
      zresult = ((zd - zashadowz31) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_80: ;
    {
      if ((zC_A_SUB_D != zop)) goto case_81;
      zresult = ((zashadowz31 - zd) & UINT64_C(0xFFFF));
      goto finish_match_65;
    }
  case_81: ;
    {
      if ((zC_D_AND_A != zop)) goto case_82;
      zresult = (zd & zashadowz31);
      goto finish_match_65;
    }
  case_82: ;
    {
      if ((zC_D_OR_A != zop)) goto case_83;
      zresult = (zd | zashadowz31);
      goto finish_match_65;
    }
  case_83: ;
    sail_match_failure("compute_value");
  finish_match_65: ;
  }
  zcbz39 = zresult;



end_function_84: ;
  return zcbz39;
end_block_exception_85: ;

  return UINT64_C(0xdeadc0de);
}

unit zassign_dest(struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9, uint64_t);

unit zassign_dest(struct ztuple_z8z5boolzCz0z5boolzCz0z5boolz9 zgsz371, uint64_t zvalue)
{
  __label__ fundef_fail_86, fundef_body_87, end_function_88, end_block_exception_89;

  unit zcbz310;
  bool za;
  za = zgsz371.ztup0;
  bool zd;
  zd = zgsz371.ztup1;
  bool zm;
  zm = zgsz371.ztup2;
  goto fundef_body_87;
fundef_fail_86: ;
  sail_match_failure("assign_dest");
fundef_body_87: ;
  {
    unit zgsz373;
    if (zm) {  zgsz373 = my_write_mem(zA, zvalue);  } else {  zgsz373 = UNIT;  }
  }
  {
    unit zgsz372;
    if (za) {
    zA = zvalue;
    zgsz372 = UNIT;
    } else {  zgsz372 = UNIT;  }
  }
  if (zd) {
  zD = zvalue;
  zcbz310 = UNIT;
  } else {  zcbz310 = UNIT;  }



end_function_88: ;
  return zcbz310;
end_block_exception_89: ;

  return UNIT;
}

unit zmaybe_jump(uint64_t, enum zjump);

lbits zghz317;
sail_int zghz318;
lbits zghz319;
sail_int zghz320;
sail_int zghz321;

void startup_zmaybe_jump(void)
{
  CREATE(lbits)(&zghz317);
  CREATE(sail_int)(&zghz318);
  CREATE(lbits)(&zghz319);
  CREATE(sail_int)(&zghz320);
  CREATE(sail_int)(&zghz321);
}

unit zmaybe_jump(uint64_t zvalue, enum zjump zj)
{
  __label__ end_function_100, end_block_exception_101;

  unit zcbz311;
  bool zcond;
  {
    __label__ case_92, case_93, case_94, case_95, case_96, case_97, case_98, case_99, finish_match_91;

    {
      if ((zJDONT != zj)) goto case_92;
      zcond = false;
      goto finish_match_91;
    }
  case_92: ;
    {
      if ((zJGT != zj)) goto case_93;
      int64_t zgaz325;
      zgaz325 = fast_signed(zvalue, 16);
      zcond = (zgaz325 > INT64_C(0));

      goto finish_match_91;
    }
  case_93: ;
    {
      if ((zJEQ != zj)) goto case_94;
      int64_t zgaz326;
      zgaz326 = fast_signed(zvalue, 16);
      zcond = (zgaz326 == INT64_C(0));

      goto finish_match_91;
    }
  case_94: ;
    {
      if ((zJGE != zj)) goto case_95;
      int64_t zgaz327;
      zgaz327 = fast_signed(zvalue, 16);
      zcond = (zgaz327 >= INT64_C(0));

      goto finish_match_91;
    }
  case_95: ;
    {
      if ((zJLT != zj)) goto case_96;
      int64_t zgaz328;
      zgaz328 = fast_signed(zvalue, 16);
      zcond = (zgaz328 < INT64_C(0));

      goto finish_match_91;
    }
  case_96: ;
    {
      if ((zJNE != zj)) goto case_97;
      int64_t zgaz329;
      zgaz329 = fast_signed(zvalue, 16);
      {
        RECREATE(sail_int)(&zghz320);
        CONVERT_OF(sail_int, mach_int)(&zghz320, INT64_C(0));
        RECREATE(sail_int)(&zghz321);
        CONVERT_OF(sail_int, mach_int)(&zghz321, zgaz329);
        zcond = zneq_int(zghz321, zghz320);
      }

      goto finish_match_91;
    }
  case_97: ;
    {
      if ((zJLE != zj)) goto case_98;
      int64_t zgaz330;
      zgaz330 = fast_signed(zvalue, 16);
      zcond = (zgaz330 <= INT64_C(0));

      goto finish_match_91;
    }
  case_98: ;
    {
      if ((zJMP != zj)) goto case_99;
      zcond = true;
      goto finish_match_91;
    }
  case_99: ;
    sail_match_failure("maybe_jump");
  finish_match_91: ;
  }
  if (zcond) {
  zPC = zA;
  zcbz311 = UNIT;
  } else {
  {
    RECREATE(lbits)(&zghz317);
    CONVERT_OF(lbits, fbits)(&zghz317, zPC, UINT64_C(16) , true);
    RECREATE(sail_int)(&zghz318);
    CONVERT_OF(sail_int, mach_int)(&zghz318, INT64_C(1));
    RECREATE(lbits)(&zghz319);
    add_bits_int(&zghz319, zghz317, zghz318);
    zPC = CONVERT_OF(fbits, lbits)(zghz319, true);
  }
  zcbz311 = UNIT;
  }

end_function_100: ;
  return zcbz311;
end_block_exception_101: ;

  return UNIT;
}



void finish_zmaybe_jump(void)
{
  KILL(sail_int)(&zghz321);
  KILL(sail_int)(&zghz320);
  KILL(lbits)(&zghz319);
  KILL(sail_int)(&zghz318);
  KILL(lbits)(&zghz317);
}

lbits zghz322;
sail_int zghz323;
lbits zghz324;

void startup_zexecute(void)
{
  CREATE(lbits)(&zghz322);
  CREATE(sail_int)(&zghz323);
  CREATE(lbits)(&zghz324);
}

unit zexecute(struct zinstr zmergez3var)
{
  __label__ case_104, case_105, finish_match_103, end_function_106, end_block_exception_107;

  unit zcbz312;
  {
    if (zmergez3var.kind != Kind_zAINST) goto case_104;
    uint64_t zx;
    zx = zmergez3var.zAINST;
    {
      zA = zx;
      unit zgsz389;
      zgsz389 = UNIT;
    }
    {
      RECREATE(lbits)(&zghz322);
      CONVERT_OF(lbits, fbits)(&zghz322, zPC, UINT64_C(16) , true);
      RECREATE(sail_int)(&zghz323);
      CONVERT_OF(sail_int, mach_int)(&zghz323, INT64_C(1));
      RECREATE(lbits)(&zghz324);
      add_bits_int(&zghz324, zghz322, zghz323);
      zPC = CONVERT_OF(fbits, lbits)(zghz324, true);
    }
    zcbz312 = UNIT;

    goto finish_match_103;
  }
case_104: ;
  {
    if (zmergez3var.kind != Kind_zCINST) goto case_105;
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
      unit zgsz394;
      zgsz394 = zassign_dest(zdest, zvalue);
    }
    zcbz312 = zmaybe_jump(zvalue, zjump);



    goto finish_match_103;
  }
case_105: ;
  sail_match_failure("execute");
finish_match_103: ;
end_function_106: ;
  return zcbz312;
end_block_exception_107: ;

  return UNIT;
}



void finish_zexecute(void)
{
  KILL(lbits)(&zghz324);
  KILL(sail_int)(&zghz323);
  KILL(lbits)(&zghz322);
}

bool zfetch_decode_execute(unit);




bool zfetch_decode_execute(unit zgsz396)
{
  __label__ cleanup_113, end_cleanup_114, end_function_112, end_block_exception_115;

  bool zcbz313;
  uint64_t zinstr;
  zinstr = my_read_rom(zPC);
  struct zoption zx;
  CREATE(zoption)(&zx);
  zdecode(&zx, zinstr);
  zcbz313 = false;
  {
    __label__ case_110, case_111, finish_match_109;

    unit zgsz397;
    {
      if (zx.kind != Kind_zSomez3z5unionz0zzinstr) goto case_110;
      struct zinstr zinstrshadowz32;
      CREATE(zinstr)(&zinstrshadowz32);
      COPY(zinstr)(&zinstrshadowz32, zx.zSomez3z5unionz0zzinstr);
      {
        unit zgsz398;
        zgsz398 = zexecute(zinstrshadowz32);
      }
      zcbz313 = true;
      zgsz397 = UNIT;
      KILL(zinstr)(&zinstrshadowz32);
      goto finish_match_109;
    }
  case_110: ;
    {
      if (zx.kind != Kind_zNone) goto case_111;
      zcbz313 = false;
      zgsz397 = UNIT;
      goto finish_match_109;
    }
  case_111: ;
    sail_match_failure("fetch_decode_execute");
  finish_match_109: ;
    unit zgsz3101;
    zgsz3101 = zgsz397;

  }
  goto cleanup_113;
  /* unreachable after return */
  KILL(zoption)(&zx);

  goto end_cleanup_114;
cleanup_113: ;

  KILL(zoption)(&zx);
  goto end_function_112;
end_cleanup_114: ;
end_function_112: ;
  return zcbz313;
end_block_exception_115: ;

  return false;
}

unit zrun(uint64_t, bool);

unit zrun(uint64_t zlimit, bool zdebug)
{
  __label__ while_117, wend_118, end_function_119, end_block_exception_120;

  unit zcbz314;
  uint64_t zcycle_count;
  zcycle_count = UINT64_C(0x0000000000000000);
  bool zcont;
  zcont = true;
  bool zgsz3105;
  unit zgsz3106;
while_117: ;
  {
    zgsz3105 = zcont;
    if (!(zgsz3105)) goto wend_118;
    {
      zcont = false;
      unit zgsz3104;
      zgsz3104 = UNIT;
    }
    {
      unit zgsz3103;
      if (zdebug) {  zgsz3103 = my_print_debug(zcycle_count, zPC, zA, zD);  } else {  zgsz3103 = UNIT;  }
    }
    {
      bool zgaz331;
      zgaz331 = zfetch_decode_execute(UNIT);
      unit zgsz3102;
      if (zgaz331) {
      bool zgaz334;
      {
        int64_t zgaz332;
        zgaz332 = fast_signed(zcycle_count, 64);
        int64_t zgaz333;
        zgaz333 = fast_signed(zlimit, 64);
        zgaz334 = (zgaz332 < zgaz333);


      }
      if (zgaz334) {
      zcont = true;
      zgsz3102 = UNIT;
      } else {  zgsz3102 = UNIT;  }

      } else {  zgsz3102 = UNIT;  }

    }
    zcycle_count = ((zcycle_count + UINT64_C(0x0000000000000001)) & UINT64_C(0xFFFFFFFFFFFFFFFF));
    zgsz3106 = UNIT;
    goto while_117;
  }
wend_118: ;
  zcbz314 = UNIT;


end_function_119: ;
  return zcbz314;
end_block_exception_120: ;

  return UNIT;
}

unit zmymain(uint64_t, bool);

unit zmymain(uint64_t zlimit, bool zdebug)
{
  __label__ end_function_122, end_block_exception_123;

  unit zcbz315;
  {
    zPC = UINT64_C(0x0000);
    unit zgsz3109;
    zgsz3109 = UNIT;
  }
  {
    zA = UINT64_C(0x0000);
    unit zgsz3108;
    zgsz3108 = UNIT;
  }
  {
    zD = UINT64_C(0x0000);
    unit zgsz3107;
    zgsz3107 = UNIT;
  }
  zcbz315 = zrun(zlimit, zdebug);
end_function_122: ;
  return zcbz315;
end_block_exception_123: ;

  return UNIT;
}

unit zmain(unit);

unit zmain(unit zgsz3110)
{
  __label__ cleanup_126, end_cleanup_127, end_function_125, end_block_exception_128;

  unit zcbz316;
  zcbz316 = zmymain(UINT64_C(0x0000000000000010), false);
  goto cleanup_126;
  /* unreachable after return */
  goto end_cleanup_127;
cleanup_126: ;
  goto end_function_125;
end_cleanup_127: ;
end_function_125: ;
  return zcbz316;
end_block_exception_128: ;

  return UNIT;
}

unit zinitializze_registers(unit);

sail_int zghz325;
lbits zghz326;
sail_int zghz327;
lbits zghz328;
sail_int zghz329;
lbits zghz330;

void startup_zinitializze_registers(void)
{
  CREATE(sail_int)(&zghz325);
  CREATE(lbits)(&zghz326);
  CREATE(sail_int)(&zghz327);
  CREATE(lbits)(&zghz328);
  CREATE(sail_int)(&zghz329);
  CREATE(lbits)(&zghz330);
}

unit zinitializze_registers(unit zgsz3111)
{
  __label__ end_function_130, end_block_exception_131;

  unit zcbz317;
  {
    {
      RECREATE(sail_int)(&zghz329);
      CONVERT_OF(sail_int, mach_int)(&zghz329, INT64_C(16));
      RECREATE(lbits)(&zghz330);
      UNDEFINED(lbits)(&zghz330, zghz329);
      zPC = CONVERT_OF(fbits, lbits)(zghz330, true);
    }
    unit zgsz3117;
    zgsz3117 = UNIT;
  }
  {
    {
      RECREATE(sail_int)(&zghz327);
      CONVERT_OF(sail_int, mach_int)(&zghz327, INT64_C(16));
      RECREATE(lbits)(&zghz328);
      UNDEFINED(lbits)(&zghz328, zghz327);
      zA = CONVERT_OF(fbits, lbits)(zghz328, true);
    }
    unit zgsz3116;
    zgsz3116 = UNIT;
  }
  {
    RECREATE(sail_int)(&zghz325);
    CONVERT_OF(sail_int, mach_int)(&zghz325, INT64_C(16));
    RECREATE(lbits)(&zghz326);
    UNDEFINED(lbits)(&zghz326, zghz325);
    zD = CONVERT_OF(fbits, lbits)(zghz326, true);
  }
  zcbz317 = UNIT;
end_function_130: ;
  return zcbz317;
end_block_exception_131: ;

  return UNIT;
}



void finish_zinitializze_registers(void)
{
  KILL(lbits)(&zghz330);
  KILL(sail_int)(&zghz329);
  KILL(lbits)(&zghz328);
  KILL(sail_int)(&zghz327);
  KILL(lbits)(&zghz326);
  KILL(sail_int)(&zghz325);
}

void model_init(void)
{
  setup_rts();
  startup_zsail_mask();
  startup_zsail_ones();
  startup_zfdiv_int();
  startup_zdecode();
  startup_zmaybe_jump();
  startup_zexecute();
  startup_zinitializze_registers();
  zinitializze_registers(UNIT);
}

void model_fini(void)
{
  finish_zsail_mask();
  finish_zsail_ones();
  finish_zfdiv_int();
  finish_zdecode();
  finish_zmaybe_jump();
  finish_zexecute();
  finish_zinitializze_registers();
  cleanup_rts();
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


