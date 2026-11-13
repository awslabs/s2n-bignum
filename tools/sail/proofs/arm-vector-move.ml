(* Exact public MOVI immediate domain: arbitrary imm64, repeated for Q128.
   This claims effects under successful-enabled-AdvSIMD, not the decoder's
   AdvSIMDExpandImm calculation or full enable-check/platform refinement. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-move.ml";;

let SAIL_HL_ARM_VECTOR_MOVE_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_MOVI; assign; LET_DEF; LET_END_DEF; FST; SND;
    NUM_OF_INT_OF_NUM; QREG'; DREG'; DIMINDEX_64; DIMINDEX_128;
    WORD_ZX_TRIVIAL; WORD_VAL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_VAL; EQ_SYM_EQ] THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_MOVI64_EQ = prove
 (`!d:5 word. !imm:64 word. !s t:armstate.
   sail_hl_arm_5fMOVI64 d imm s t <=> arm_MOVI (DREG' d) imm s t`,
  SAIL_HL_ARM_VECTOR_MOVE_TAC sail_hl_arm_5fMOVI64);;

let SAIL_HL_ARM_MOVI128_EQ = prove
 (`!d:5 word. !imm:64 word. !s t:armstate.
   sail_hl_arm_5fMOVI128 d imm s t <=> arm_MOVI (QREG' d) imm s t`,
  SAIL_HL_ARM_VECTOR_MOVE_TAC sail_hl_arm_5fMOVI128);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_MOVI64_EQ", SAIL_HL_ARM_MOVI64_EQ;
  "SAIL_HL_ARM_MOVI128_EQ", SAIL_HL_ARM_MOVI128_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_MOVE_PROOFS_OK";;
