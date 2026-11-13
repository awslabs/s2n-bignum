(* Two exact decoder-supported vector CNT profiles. These graph claims
   quantify every five-bit vector field, including register 31 and overlap.
   Width 64 clears the upper half of Q. Successful enabled-AdvSIMD access
   remains an explicit external contract, not a full access-check proof. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-count.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

(* Pure arithmetic lemmas for the eight-bit loop in actual Sail BitCount.
   No instruction body or lane-write template is introduced here. *)
let SAIL_HL_ARM_VECTOR_COUNT_STEP = prove
 (`!a:int. !p. (if p then a + &1 else a) = a + &(bitval p)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN
  REWRITE_TAC[INT_ADD_RID]);;

let SAIL_HL_ARM_VECTOR_COUNT_FIRST = prove
 (`!p. (if p then (&1:int) else &0) = &(bitval p)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES]);;

let SAIL_HL_ARM_VECTOR_COUNT_PAIR_FIRST = prove
 (`!p (s:A). (if p then s,(&1:int) else s,&0) = (s,&(bitval p))`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES]);;

let SAIL_HL_ARM_VECTOR_COUNT_PAIR_STEP = prove
 (`!p (s:A) (a:int).
   (if p then s,a + &1 else s,a) = (s,a + &(bitval p))`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; INT_ADD_RID]);;

let SAIL_HL_ARM_VECTOR_COUNT_FST = prove
 (`!p (x:A#B) y.
   FST(if p then x else y) = if p then FST x else FST y`,
  REWRITE_TAC[FORALL_BOOL_THM]);;

let SAIL_HL_ARM_VECTOR_COUNT_SND = prove
 (`!p (x:A#B) y.
   SND(if p then x else y) = if p then SND x else SND y`,
  REWRITE_TAC[FORALL_BOOL_THM]);;

let SAIL_HL_ARM_VECTOR_COUNT_BYTE = prove
 (`!x:8 word.
   word_popcount x =
     bitval(bit 0 x) + bitval(bit 1 x) +
     bitval(bit 2 x) + bitval(bit 3 x) +
     bitval(bit 4 x) + bitval(bit 5 x) +
     bitval(bit 6 x) + bitval(bit 7 x)`,
  GEN_TAC THEN CONV_TAC(LAND_CONV WORD_POPCOUNT_EXPAND_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_AC]);;

let SAIL_HL_ARM_VECTOR_COUNT_VALUE_TAC =
  W(fun (_, goal) ->
    let is_write term =
      let head, arguments = strip_comb term in
      is_const head && fst(dest_const head) = "write" &&
      length arguments = 3 in
    let _, source = strip_comb(find_term is_write (lhand goal)) in
    let _, target = strip_comb(find_term is_write (rand goal)) in
    SUBGOAL_THEN (mk_eq(el 1 source,el 1 target))
      (fun theorem -> REWRITE_TAC[theorem; EQ_SYM_EQ]) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
      BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_OR; BIT_WORD_AND;
      BIT_WORD_SHL; BIT_WORD_0; SAIL_HL_ARM_VECTOR_COUNT_BYTE] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(REDEPTH_CONV(FIRST_CONV
      [REWR_CONV INT_OF_NUM_ADD; REWR_CONV(GSYM WORD_IWORD)])) THEN
    REWRITE_TAC[ADD_AC]);;

let SAIL_HL_ARM_VECTOR_COUNT_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_CNT; assign; LET_DEF; LET_END_DEF; FST; SND;
    QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    NUM_OF_INT_OF_NUM; usimd16; usimd8; usimd4; usimd2; o_THM;
    SAIL_HL_ARM_BIT_WORD_ONE; SAIL_HL_ARM_VECTOR_COUNT_STEP;
    SAIL_HL_ARM_VECTOR_COUNT_FIRST; SAIL_HL_ARM_VECTOR_COUNT_FST;
    SAIL_HL_ARM_VECTOR_COUNT_SND; SAIL_HL_ARM_VECTOR_COUNT_PAIR_FIRST;
    SAIL_HL_ARM_VECTOR_COUNT_PAIR_STEP] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_ADD_LID; GSYM WORD_IWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; FST; SND;
    SAIL_HL_ARM_BIT_WORD_ONE; SAIL_HL_ARM_VECTOR_COUNT_PAIR_FIRST;
    SAIL_HL_ARM_VECTOR_COUNT_PAIR_STEP] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_ADD_LID; GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_COUNT_VALUE_TAC THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_CNT64_EQ = prove
 (`!d n:5 word. !s t:armstate.
   sail_hl_arm_5fCNT64 d n s t <=>
   arm_CNT (QREG' d) (QREG' n) 64 s t`,
  SAIL_HL_ARM_VECTOR_COUNT_TAC sail_hl_arm_5fCNT64);;

let SAIL_HL_ARM_CNT128_EQ = prove
 (`!d n:5 word. !s t:armstate.
   sail_hl_arm_5fCNT128 d n s t <=>
   arm_CNT (QREG' d) (QREG' n) 128 s t`,
  SAIL_HL_ARM_VECTOR_COUNT_TAC sail_hl_arm_5fCNT128);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_CNT64_EQ", SAIL_HL_ARM_CNT64_EQ;
  "SAIL_HL_ARM_CNT128_EQ", SAIL_HL_ARM_CNT128_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_COUNT_PROOFS_OK";;
