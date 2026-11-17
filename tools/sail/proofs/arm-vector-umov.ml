(* The public HOL decoder supports S32 -> W32 and D64 -> X64 only.
   All four or two lane indices and both actual source read widths remain
   included. XZR/WZR destination and vector source31 are not excluded.
   Full access checks and decoding are not claimed here; the two distinct
   original successful FP/AdvSIMD access calls require explicit contracts. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-umov.ml";;

let SAIL_HL_ARM_VECTOR_UMOV_TAC selector dimension definition =
  REPEAT GEN_TAC THEN SPEC_TAC (selector,selector) THEN
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN REWRITE_TAC[dimension] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[definition; arm_UMOV; assign; LET_DEF; LET_END_DEF;
    FST; SND; NUM_OF_INT_OF_NUM; XREG'; WREG'; QREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_SUBWORD_ZX; WORD_ZX_SUBWORD; EQ_SYM_EQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  PRINT_GOAL_TAC;;

let SAIL_HL_ARM_UMOV32E32_EQ = prove
 (`!d n:5 word. !lane:2 word. !s t:armstate.
   sail_hl_arm_5fUMOV32E32 d n lane s t <=>
   arm_UMOV (WREG' d) (QREG' n) (val lane) 4 s t`,
  SAIL_HL_ARM_VECTOR_UMOV_TAC `lane:2 word` DIMINDEX_2
    sail_hl_arm_5fUMOV32E32);;

let SAIL_HL_ARM_UMOV64E64_EQ = prove
 (`!d n:5 word. !lane:1 word. !s t:armstate.
   sail_hl_arm_5fUMOV64E64 d n lane s t <=>
   arm_UMOV (XREG' d) (QREG' n) (val lane) 8 s t`,
  SAIL_HL_ARM_VECTOR_UMOV_TAC `lane:1 word` DIMINDEX_1
    sail_hl_arm_5fUMOV64E64);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_UMOV32E32_EQ", SAIL_HL_ARM_UMOV32E32_EQ;
  "SAIL_HL_ARM_UMOV64E64_EQ", SAIL_HL_ARM_UMOV64E64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_UMOV_PROOFS_OK";;
