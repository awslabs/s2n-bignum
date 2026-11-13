(* Actual upstream multiply/add/subtract instruction body at both decoder
   widths, including MUL/MNEG aliases. Integer signedness disappears only
   after the kernel proves equal low-word modular arithmetic. Register fields
   are universally quantified, including zero and overlapping destinations. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-multiply.ml";;

let SAIL_HL_ARM_MULTIPLY_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC (definitions @
    [assign; LET_DEF; LET_END_DEF; XREG'; WREG'; NUM_OF_INT_OF_NUM;
     IWORD_INT_ADD; IWORD_INT_SUB; IWORD_INT_MUL; IWORD_IVAL;
     GSYM WORD_IWORD; WORD_ADD; WORD_MUL; WORD_VAL;
     ARM_ZERO_REGISTER; READ_RVALUE]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[ARM_ZERO_REGISTER; READ_RVALUE; WORD_VAL];;

let SAIL_HL_ARM_MADD64_EQ = prove
 (`!d n m a:5 word. !s t:armstate.
   sail_hl_arm_5fMADD64 d n m a s t <=>
   arm_MADD (XREG' d) (XREG' n) (XREG' m) (XREG' a) s t`,
  SAIL_HL_ARM_MULTIPLY_TAC [sail_hl_arm_5fMADD64; arm_MADD]);;

let SAIL_HL_ARM_MADD32_EQ = prove
 (`!d n m a:5 word. !s t:armstate.
   sail_hl_arm_5fMADD32 d n m a s t <=>
   arm_MADD (WREG' d) (WREG' n) (WREG' m) (WREG' a) s t`,
  SAIL_HL_ARM_MULTIPLY_TAC [sail_hl_arm_5fMADD32; arm_MADD]);;

let SAIL_HL_ARM_MSUB64_EQ = prove
 (`!d n m a:5 word. !s t:armstate.
   sail_hl_arm_5fMSUB64 d n m a s t <=>
   arm_MSUB (XREG' d) (XREG' n) (XREG' m) (XREG' a) s t`,
  SAIL_HL_ARM_MULTIPLY_TAC [sail_hl_arm_5fMSUB64; arm_MSUB]);;

let SAIL_HL_ARM_MSUB32_EQ = prove
 (`!d n m a:5 word. !s t:armstate.
   sail_hl_arm_5fMSUB32 d n m a s t <=>
   arm_MSUB (WREG' d) (WREG' n) (WREG' m) (WREG' a) s t`,
  SAIL_HL_ARM_MULTIPLY_TAC [sail_hl_arm_5fMSUB32; arm_MSUB]);;

let SAIL_HL_ARM_MUL64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_arm_5fMUL64 d n m s t <=>
   arm_MUL (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_MULTIPLY_TAC [sail_hl_arm_5fMUL64; arm_MUL; arm_MADD]);;

let SAIL_HL_ARM_MUL32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_arm_5fMUL32 d n m s t <=>
   arm_MUL (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_MULTIPLY_TAC [sail_hl_arm_5fMUL32; arm_MUL; arm_MADD]);;

let SAIL_HL_ARM_MNEG64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_arm_5fMNEG64 d n m s t <=>
   arm_MNEG (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_MULTIPLY_TAC [sail_hl_arm_5fMNEG64; arm_MNEG; arm_MSUB]);;

let SAIL_HL_ARM_MNEG32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_arm_5fMNEG32 d n m s t <=>
   arm_MNEG (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_MULTIPLY_TAC [sail_hl_arm_5fMNEG32; arm_MNEG; arm_MSUB]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_MADD32_EQ", SAIL_HL_ARM_MADD32_EQ;
  "SAIL_HL_ARM_MADD64_EQ", SAIL_HL_ARM_MADD64_EQ;
  "SAIL_HL_ARM_MSUB32_EQ", SAIL_HL_ARM_MSUB32_EQ;
  "SAIL_HL_ARM_MSUB64_EQ", SAIL_HL_ARM_MSUB64_EQ;
  "SAIL_HL_ARM_MUL32_EQ", SAIL_HL_ARM_MUL32_EQ;
  "SAIL_HL_ARM_MUL64_EQ", SAIL_HL_ARM_MUL64_EQ;
  "SAIL_HL_ARM_MNEG32_EQ", SAIL_HL_ARM_MNEG32_EQ;
  "SAIL_HL_ARM_MNEG64_EQ", SAIL_HL_ARM_MNEG64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MULTIPLY_PROOFS_OK";;
