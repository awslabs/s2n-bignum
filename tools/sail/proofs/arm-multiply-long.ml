(* Actual unsigned 32-by-32 widening multiply/add/subtract body, including
   UMULL/UMNEGL aliases. The destination and accumulator are 64-bit;
   multiplicands are 32-bit. Register fields include zero and all overlaps. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-multiply-long.ml";;

let SAIL_HL_ARM_MULTIPLY_LONG_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC (definitions @
    [assign; LET_DEF; LET_END_DEF; FST; SND; XREG'; WREG';
     NUM_OF_INT_OF_NUM; IWORD_INT_ADD; IWORD_INT_SUB; IWORD_INT_MUL;
     IWORD_IVAL; GSYM WORD_IWORD; WORD_ADD; WORD_MUL; WORD_VAL;
     ARM_ZERO_REGISTER; READ_RVALUE]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[ARM_ZERO_REGISTER; READ_RVALUE; WORD_VAL];;

let SAIL_HL_ARM_UMADDL64_EQ = prove
 (`!d n m a:5 word. !s t:armstate.
   sail_hl_arm_5fUMADDL64 d n m a s t <=>
   arm_UMADDL (XREG' d) (WREG' n) (WREG' m) (XREG' a) s t`,
  SAIL_HL_ARM_MULTIPLY_LONG_TAC [sail_hl_arm_5fUMADDL64; arm_UMADDL]);;

let SAIL_HL_ARM_UMSUBL64_EQ = prove
 (`!d n m a:5 word. !s t:armstate.
   sail_hl_arm_5fUMSUBL64 d n m a s t <=>
   arm_UMSUBL (XREG' d) (WREG' n) (WREG' m) (XREG' a) s t`,
  SAIL_HL_ARM_MULTIPLY_LONG_TAC [sail_hl_arm_5fUMSUBL64; arm_UMSUBL]);;

let SAIL_HL_ARM_UMULL64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_arm_5fUMULL64 d n m s t <=>
   arm_UMULL (XREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_MULTIPLY_LONG_TAC [
    sail_hl_arm_5fUMULL64; arm_UMULL; arm_UMADDL]);;

let SAIL_HL_ARM_UMNEGL64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_arm_5fUMNEGL64 d n m s t <=>
   arm_UMNEGL (XREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_MULTIPLY_LONG_TAC [
    sail_hl_arm_5fUMNEGL64; arm_UMNEGL; arm_UMSUBL]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_UMADDL64_EQ", SAIL_HL_ARM_UMADDL64_EQ;
  "SAIL_HL_ARM_UMSUBL64_EQ", SAIL_HL_ARM_UMSUBL64_EQ;
  "SAIL_HL_ARM_UMULL64_EQ", SAIL_HL_ARM_UMULL64_EQ;
  "SAIL_HL_ARM_UMNEGL64_EQ", SAIL_HL_ARM_UMNEGL64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MULTIPLY_LONG_PROOFS_OK";;
