(* Agreement of EXTR execution effects, not reserved-encoding decoding.
   Five- and six-bit position arguments quantify all legal lsb values.
   Register fields remain symbolic and include the zero-register field. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-extract.ml";;

let SAIL_HL_ARM_EXTRACT_POSITION32 = prove
 (`!lsb:5 word. val lsb MOD 32 = val lsb`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `lsb:5 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let SAIL_HL_ARM_EXTRACT_POSITION64 = prove
 (`!lsb:6 word. val lsb MOD 64 = val lsb`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `lsb:6 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let SAIL_HL_ARM_EXTRACT_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @
    [arm_EXTR; LET_DEF; LET_END_DEF; FST; SND;
     NUM_OF_INT_OF_NUM; XREG'; WREG'; assign; DIMINDEX_32; DIMINDEX_64;
     SAIL_HL_ARM_EXTRACT_POSITION32; SAIL_HL_ARM_EXTRACT_POSITION64;
     EQ_SYM_EQ]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EQ_SYM_EQ] THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_EXTR32_EQ = prove
 (`!d n m:5 word. !lsb:5 word. !s t:armstate.
   sail_hl_arm_5fEXTR32 d n m lsb s t <=>
   arm_EXTR (WREG' d) (WREG' n) (WREG' m) (val lsb) s t`,
  SAIL_HL_ARM_EXTRACT_TAC [sail_hl_arm_5fEXTR32]);;

let SAIL_HL_ARM_EXTR64_EQ = prove
 (`!d n m:5 word. !lsb:6 word. !s t:armstate.
   sail_hl_arm_5fEXTR64 d n m lsb s t <=>
   arm_EXTR (XREG' d) (XREG' n) (XREG' m) (val lsb) s t`,
  SAIL_HL_ARM_EXTRACT_TAC [sail_hl_arm_5fEXTR64]);;

let SAIL_HL_ARM_ROR32_EQ = prove
 (`!d n:5 word. !lsb:5 word. !s t:armstate.
   sail_hl_arm_5fROR32 d n lsb s t <=>
   arm_ROR (WREG' d) (WREG' n) (val lsb) s t`,
  SAIL_HL_ARM_EXTRACT_TAC [sail_hl_arm_5fROR32; arm_ROR]);;

let SAIL_HL_ARM_ROR64_EQ = prove
 (`!d n:5 word. !lsb:6 word. !s t:armstate.
   sail_hl_arm_5fROR64 d n lsb s t <=>
   arm_ROR (XREG' d) (XREG' n) (val lsb) s t`,
  SAIL_HL_ARM_EXTRACT_TAC [sail_hl_arm_5fROR64; arm_ROR]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_EXTR32_EQ", SAIL_HL_ARM_EXTR32_EQ;
  "SAIL_HL_ARM_EXTR64_EQ", SAIL_HL_ARM_EXTR64_EQ;
  "SAIL_HL_ARM_ROR32_EQ", SAIL_HL_ARM_ROR32_EQ;
  "SAIL_HL_ARM_ROR64_EQ", SAIL_HL_ARM_ROR64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_EXTRACT_PROOFS_OK";;
