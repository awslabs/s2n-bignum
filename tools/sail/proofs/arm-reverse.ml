(* Scalar REV covers one complete 32- or 64-bit GPR container. The separate
   SIMD REV32_VEC/REV64_VEC definitions have different lane profiles. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-reverse.ml";;

let SAIL_HL_ARM_REVERSE_VALUE_TAC =
  W(fun (_, goal) ->
    let is_reverse term =
      is_comb term && is_const(rator term) &&
      fst(dest_const(rator term)) = "word_bytereverse" in
    let is_source_write term =
      let head, args = strip_comb term in
      is_const head && fst(dest_const head) = "write" &&
      length args = 3 && not(can (find_term is_reverse) (el 1 args)) in
    let _, source_args = strip_comb(find_term is_source_write goal) in
    let value = el 1 source_args in
    let reversed = find_term is_reverse goal in
    SUBGOAL_THEN (mk_eq(value,reversed))
      (fun theorem -> REWRITE_TAC[theorem; EQ_SYM_EQ]) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
      BIT_WORD_INSERT; BIT_WORD_BYTEREVERSE; BIT_WORD_OR;
      BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_0] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_REVERSE_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_REV; LET_DEF; LET_END_DEF; FST; SND;
    NUM_OF_INT_OF_NUM; XREG'; WREG'; assign] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_REVERSE_VALUE_TAC THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_REV32_EQ = prove
 (`!d n:5 word. !s t:armstate.
   sail_hl_arm_5fREV32 d n s t <=>
   arm_REV (WREG' d) (WREG' n) s t`,
  SAIL_HL_ARM_REVERSE_TAC sail_hl_arm_5fREV32);;

let SAIL_HL_ARM_REV64_EQ = prove
 (`!d n:5 word. !s t:armstate.
   sail_hl_arm_5fREV64 d n s t <=>
   arm_REV (XREG' d) (XREG' n) s t`,
  SAIL_HL_ARM_REVERSE_TAC sail_hl_arm_5fREV64);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_REV32_EQ", SAIL_HL_ARM_REV32_EQ;
  "SAIL_HL_ARM_REV64_EQ", SAIL_HL_ARM_REV64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_REVERSE_PROOFS_OK";;
