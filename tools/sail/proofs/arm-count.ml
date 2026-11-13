(* Agreement for the two public scalar CLZ width variants. CLS has no public
   HOL instruction definition here and is not silently counted as an alias. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-count.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

(* Mathematical characterization of the leading-zero count. The exporter
   must still consume the actual bounded HighestSetBit loop and early return. *)
let SAIL_HL_ARM_COUNT_CLZ_FINITE = prove
 (`!x:N word. !n.
   n <= dimindex(:N) /\
   (n < dimindex(:N) ==> bit (dimindex(:N) - n - 1) x) /\
   (!i. i < dimindex(:N) /\ dimindex(:N) - n <= i ==> ~bit i x)
   ==> word_clz x = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_CLZ_UNIQUE_GEN] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN
  ASM_MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let SAIL_HL_ARM_COUNT_CASE_TAC =
  W(fun (_, goal) ->
    let is_clz term =
      is_comb term && is_const(rator term) &&
      fst(dest_const(rator term)) = "word_clz" in
    let is_word_literal term =
      is_comb term && is_const(rator term) &&
      fst(dest_const(rator term)) = "word" && is_numeral(rand term) in
    let clz = find_term is_clz goal in
    let count = rand(find_term is_word_literal goal) in
    SUBGOAL_THEN (mk_eq(clz,count))
      (fun theorem -> REWRITE_TAC[theorem; EQ_SYM_EQ]) THEN
    MATCH_MP_TAC SAIL_HL_ARM_COUNT_CLZ_FINITE THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMP_CONJ] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let SAIL_HL_ARM_COUNT_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_CLZ; LET_DEF; LET_END_DEF; FST; SND;
    NUM_OF_INT_OF_NUM; XREG'; WREG'; assign;
    SAIL_HL_ARM_BIT_WORD_ONE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_COUNT_CASE_TAC THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_CLZ32_EQ = prove
 (`!d n:5 word. !s t:armstate.
   sail_hl_arm_5fCLZ32 d n s t <=>
   arm_CLZ (WREG' d) (WREG' n) s t`,
  SAIL_HL_ARM_COUNT_TAC sail_hl_arm_5fCLZ32);;

let SAIL_HL_ARM_CLZ64_EQ = prove
 (`!d n:5 word. !s t:armstate.
   sail_hl_arm_5fCLZ64 d n s t <=>
   arm_CLZ (XREG' d) (XREG' n) s t`,
  SAIL_HL_ARM_COUNT_TAC sail_hl_arm_5fCLZ64);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_CLZ32_EQ", SAIL_HL_ARM_CLZ32_EQ;
  "SAIL_HL_ARM_CLZ64_EQ", SAIL_HL_ARM_CLZ64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_COUNT_PROOFS_OK";;
