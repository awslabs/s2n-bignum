(* The actual Sail high-multiply body computes an integer product and extracts
   bits 127..64. Floor division gives the infinite two's-complement slice,
   including negative signed products. These graph claims quantify every
   encoded register field, zero register and source/destination overlap. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-multiply-high.ml";;

let SAIL_HL_ARM_MULTIPLY_HIGH_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC (definitions @
    [assign; LET_DEF; LET_END_DEF; FST; SND; XREG';
     NUM_OF_INT_OF_NUM; ARM_ZERO_REGISTER; READ_RVALUE;
     DIMINDEX_64; INT_OF_NUM_MUL; INT_OF_NUM_POW; INT_OF_NUM_DIV;
     GSYM WORD_IWORD]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARM_ZERO_REGISTER; READ_RVALUE];;

let SAIL_HL_ARM_SMULH64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_arm_5fSMULH64 d n m s t <=>
   arm_SMULH (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_MULTIPLY_HIGH_TAC [sail_hl_arm_5fSMULH64; arm_SMULH]);;

let SAIL_HL_ARM_UMULH64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_arm_5fUMULH64 d n m s t <=>
   arm_UMULH (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_MULTIPLY_HIGH_TAC [sail_hl_arm_5fUMULH64; arm_UMULH]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_SMULH64_EQ", SAIL_HL_ARM_SMULH64_EQ;
  "SAIL_HL_ARM_UMULH64_EQ", SAIL_HL_ARM_UMULH64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MULTIPLY_HIGH_PROOFS_OK";;
