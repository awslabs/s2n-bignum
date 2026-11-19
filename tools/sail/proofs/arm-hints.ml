(* Exact NOP and BTI c encodings under the explicit BType-write exclusion.
   The BTI compatibility calculation retains an arbitrary PSTATE component;
   neither theorem verifies physical branch metadata or BTI enforcement. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-hints.ml";;

let SAIL_HL_ARM_NOP_EQ = prove
 (`!s t:armstate. sail_hl_arm_5fNOP s t <=> arm_NOP s t`,
  REWRITE_TAC[sail_hl_arm_5fNOP; arm_NOP; LET_DEF; LET_END_DEF;
              FST; SND]);;
sail_hl_report ("SAIL_HL_ARM_NOP_EQ", SAIL_HL_ARM_NOP_EQ);;

let SAIL_HL_ARM_BTI_C_EQ = prove
 (`!reg_PSTATE. !s t:armstate.
   sail_hl_arm_5fBTI_5fC reg_PSTATE s t <=> arm_BTI s t`,
  REWRITE_TAC[sail_hl_arm_5fBTI_5fC; arm_BTI; LET_DEF; LET_END_DEF;
              FST; SND; COND_ID] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; FST; SND; COND_ID]);;
sail_hl_report ("SAIL_HL_ARM_BTI_C_EQ", SAIL_HL_ARM_BTI_C_EQ);;

check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_HINTS_PROOFS_OK";;
