(* Component and bitvector facts for the actual scalar logical and
   add/subtract bodies, which share the shifted-register operand. *)
needs "tools/sail/proofs/arm-shift-lemmas.ml";;

(* The s2n-bignum shift type that each Sail ShiftType constructor names. *)
let SAIL_HL_ARM_LOGICAL_KIND = new_definition
 `sail_hl_arm_logical_kind (kind:sail_hl_type_ShiftType) =
   if kind = sail_hl_ctor_ShiftType_5fLSL then LSL else
   if kind = sail_hl_ctor_ShiftType_5fLSR then LSR else
   if kind = sail_hl_ctor_ShiftType_5fASR then ASR else ROR`;;

let SAIL_HL_ARM_LOGICAL_PACKED_BITS = prove
 (`!n z.
   let w:4 word = word_join
     (word_join (word(bitval n):1 word) (word(bitval z):1 word):2 word)
     (word 0:2 word) in
   (bit 0 (word_subword w (3,1):1 word) <=> n) /\
   (bit 0 (word_subword w (2,1):1 word) <=> z) /\
   ~bit 0 (word_subword w (1,1):1 word) /\
   ~bit 0 (word_subword w (0,1):1 word)`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; BIT_WORD_SUBWORD; BIT_WORD_JOIN;
              DIMINDEX_1; DIMINDEX_2; DIMINDEX_4;
              BIT_WORD_BITVAL; BIT_WORD_0] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let SAIL_HL_ARM_LOGICAL_PACKED_REWRITES =
  REWRITE_RULE[LET_DEF; LET_END_DEF] SAIL_HL_ARM_LOGICAL_PACKED_BITS;;

let SAIL_HL_ARM_LOGICAL_FIELD31 = prove
 (`!d:5 word. d = word 31 <=> val d = 31`,
  REWRITE_TAC[GSYM VAL_EQ] THEN CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_ARM_LOGICAL_NOT_FIELD31 = prove
 (`!d:5 word. ~(d = word 31) ==> val d < 31`,
  GEN_TAC THEN REWRITE_TAC[SAIL_HL_ARM_LOGICAL_FIELD31] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `d:5 word` VAL_BOUND) THEN
  CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let SAIL_HL_ARM_LOGICAL_SP_DEST = prove
 (`!d:5 word.
   XREG_SP d = (if d = word 31 then SP else XREG(val d)) /\
   WREG_SP d = (if d = word 31 then WSP else WREG(val d))`,
  GEN_TAC THEN ASM_CASES_TAC `d:5 word = word 31` THEN
  ASM_SIMP_TAC[XREG_SP; WREG_SP; SP; WSP; WREG; XREG; WORD_VAL;
    SAIL_HL_ARM_LOGICAL_NOT_FIELD31;
    ARITH_RULE `x < 31 ==> ~(x >= 31)`] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_ARM_LOGICAL_READ_SHIFT = prove
 (`!r:(armstate,N word)component. !kind amount s.
   read (Shiftedreg r kind amount) s =
   regshift_operation kind (read r s) amount`,
  REWRITE_TAC[Shiftedreg_DEF; read]);;

let SAIL_HL_ARM_LOGICAL_ROTATE_LEGAL = prove
 (`!x:N word. !count:num. count < dimindex(:N) ==>
   (if count = 0 then x else
    word_or (word_ushr x count)
      (word_shl x (num_of_int (&(dimindex(:N)) - &count)))) =
   word_ror x count`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:N word`; `count:num`] SAIL_HL_ARM_SHIFT_ROTATE) THEN
  ASM_SIMP_TAC[MOD_LT]);;
let SAIL_HL_ARM_LOGICAL_ROTATE32 =
  REWRITE_RULE[DIMINDEX_32]
    (INST_TYPE [`:32`,`:N`] SAIL_HL_ARM_LOGICAL_ROTATE_LEGAL);;
let SAIL_HL_ARM_LOGICAL_ROTATE64 =
  REWRITE_RULE[DIMINDEX_64]
    (INST_TYPE [`:64`,`:N`] SAIL_HL_ARM_LOGICAL_ROTATE_LEGAL);;
