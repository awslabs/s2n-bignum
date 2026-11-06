(* Actual add/sub-with-carry instruction body at both decoder widths.
   X/W register contracts include field 31 and overlapping operands. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-carry.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

let SAIL_HL_ARM_CARRY_RESULT = prove
 (`!x y:N word. !cin.
   iword((&(val x) + &(val y)) + &(bitval cin)):N word =
   word_add (word_add x y) (word(bitval cin))`,
  REWRITE_TAC[IWORD_INT_ADD; GSYM WORD_IWORD; WORD_VAL; WORD_ADD_ASSOC]);;

let SAIL_HL_ARM_CARRY_SBB_FLAG_REWRITES =
  REWRITE_RULE[LET_DEF; LET_END_DEF; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
               WORD_ADD_AC; ADD_AC; INT_ADD_AC; EQ_SYM_EQ]
    SAIL_HL_ARM_SBB_FLAGS;;
let SAIL_HL_ARM_CARRY_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @
    [LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM;
     VAL_WORD_BITVAL; SAIL_HL_ARM_CARRY_RESULT;
     SAIL_HL_ARM_NOT_FLAG; GSYM WORD_BITVAL;
     GSYM VAL_EQ; VAL_WORD_0;
     SAIL_HL_ARM_MSB32; SAIL_HL_ARM_MSB64;
     DIMINDEX_32; DIMINDEX_64]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ; WORD_ADD_AC;
              ADD_AC; INT_ADD_AC; EQ_SYM_EQ;
              SAIL_HL_ARM_PACKED_REWRITES;
              SAIL_HL_ARM_SBB_RESULT] THEN
  REWRITE_TAC[SAIL_HL_ARM_CARRY_SBB_FLAG_REWRITES;
              SEQ; assign; XREG'; WREG'] THEN
  ASM_SIMP_TAC[SAIL_HL_ARM_XFLAG_COMMUTE;
               SAIL_HL_ARM_WFLAG_COMMUTE] THEN
  REWRITE_TAC[WORD_ADD_AC; ADD_AC; INT_ADD_AC; EQ_SYM_EQ] THEN
  PRINT_GOAL_TAC;;

let SAIL_HL_ARM_ADC32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_ARM_5fADC32 d n m s t <=>
   arm_ADC (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_CARRY_TAC [sail_hl_ARM_5fADC32; arm_ADC]);;
let SAIL_HL_ARM_ADC64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_ARM_5fADC64 d n m s t <=>
   arm_ADC (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_CARRY_TAC [sail_hl_ARM_5fADC64; arm_ADC]);;
let SAIL_HL_ARM_ADCS32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_ARM_5fADCS32 d n m s t <=>
   arm_ADCS (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_CARRY_TAC [sail_hl_ARM_5fADCS32; arm_ADCS]);;
let SAIL_HL_ARM_ADCS64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_ARM_5fADCS64 d n m s t <=>
   arm_ADCS (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_CARRY_TAC [sail_hl_ARM_5fADCS64; arm_ADCS]);;
let SAIL_HL_ARM_SBC32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_ARM_5fSBC32 d n m s t <=>
   arm_SBC (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_CARRY_TAC [sail_hl_ARM_5fSBC32; arm_SBC]);;
let SAIL_HL_ARM_SBC64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_ARM_5fSBC64 d n m s t <=>
   arm_SBC (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_CARRY_TAC [sail_hl_ARM_5fSBC64; arm_SBC]);;
let SAIL_HL_ARM_SBCS32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_ARM_5fSBCS32 d n m s t <=>
   arm_SBCS (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_CARRY_TAC [sail_hl_ARM_5fSBCS32; arm_SBCS]);;
let SAIL_HL_ARM_SBCS64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
   sail_hl_ARM_5fSBCS64 d n m s t <=>
   arm_SBCS (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_CARRY_TAC [sail_hl_ARM_5fSBCS64; arm_SBCS]);;

let SAIL_HL_ARM_CARRY_ALIAS_MODEL_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @
    [LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM]) THEN
  CONV_TAC WORD_REDUCE_CONV;;

let SAIL_HL_ARM_NGC32_MODEL = prove
 (`!d m:5 word. !s:armstate.
   sail_hl_ARM_5fNGC32 d m s =
   sail_hl_ARM_5fSBC32 d (word 31) m s`,
  SAIL_HL_ARM_CARRY_ALIAS_MODEL_TAC [sail_hl_ARM_5fNGC32; sail_hl_ARM_5fSBC32]);;
let SAIL_HL_ARM_NGC64_MODEL = prove
 (`!d m:5 word. !s:armstate.
   sail_hl_ARM_5fNGC64 d m s =
   sail_hl_ARM_5fSBC64 d (word 31) m s`,
  SAIL_HL_ARM_CARRY_ALIAS_MODEL_TAC [sail_hl_ARM_5fNGC64; sail_hl_ARM_5fSBC64]);;
let SAIL_HL_ARM_NGCS32_MODEL = prove
 (`!d m:5 word. !s:armstate.
   sail_hl_ARM_5fNGCS32 d m s =
   sail_hl_ARM_5fSBCS32 d (word 31) m s`,
  SAIL_HL_ARM_CARRY_ALIAS_MODEL_TAC [sail_hl_ARM_5fNGCS32; sail_hl_ARM_5fSBCS32]);;
let SAIL_HL_ARM_NGCS64_MODEL = prove
 (`!d m:5 word. !s:armstate.
   sail_hl_ARM_5fNGCS64 d m s =
   sail_hl_ARM_5fSBCS64 d (word 31) m s`,
  SAIL_HL_ARM_CARRY_ALIAS_MODEL_TAC [sail_hl_ARM_5fNGCS64; sail_hl_ARM_5fSBCS64]);;

let SAIL_HL_ARM_CARRY_ALIAS_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC definitions THEN
  REWRITE_TAC[XREG'; WREG'; ARM_ZERO_REGISTER] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[ARM_ZERO_REGISTER];;

let SAIL_HL_ARM_NGC32_EQ = prove
 (`!d m:5 word. !s t:armstate.
   sail_hl_ARM_5fNGC32 d m s t <=>
   arm_NGC (WREG' d) (WREG' m) s t`,
  SAIL_HL_ARM_CARRY_ALIAS_TAC
    [SAIL_HL_ARM_NGC32_MODEL; SAIL_HL_ARM_SBC32_EQ; arm_NGC]);;
let SAIL_HL_ARM_NGC64_EQ = prove
 (`!d m:5 word. !s t:armstate.
   sail_hl_ARM_5fNGC64 d m s t <=>
   arm_NGC (XREG' d) (XREG' m) s t`,
  SAIL_HL_ARM_CARRY_ALIAS_TAC
    [SAIL_HL_ARM_NGC64_MODEL; SAIL_HL_ARM_SBC64_EQ; arm_NGC]);;
let SAIL_HL_ARM_NGCS32_EQ = prove
 (`!d m:5 word. !s t:armstate.
   sail_hl_ARM_5fNGCS32 d m s t <=>
   arm_NGCS (WREG' d) (WREG' m) s t`,
  SAIL_HL_ARM_CARRY_ALIAS_TAC
    [SAIL_HL_ARM_NGCS32_MODEL; SAIL_HL_ARM_SBCS32_EQ; arm_NGCS]);;
let SAIL_HL_ARM_NGCS64_EQ = prove
 (`!d m:5 word. !s t:armstate.
   sail_hl_ARM_5fNGCS64 d m s t <=>
   arm_NGCS (XREG' d) (XREG' m) s t`,
  SAIL_HL_ARM_CARRY_ALIAS_TAC
    [SAIL_HL_ARM_NGCS64_MODEL; SAIL_HL_ARM_SBCS64_EQ; arm_NGCS]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_ADC32_EQ", SAIL_HL_ARM_ADC32_EQ;
  "SAIL_HL_ARM_ADC64_EQ", SAIL_HL_ARM_ADC64_EQ;
  "SAIL_HL_ARM_ADCS32_EQ", SAIL_HL_ARM_ADCS32_EQ;
  "SAIL_HL_ARM_ADCS64_EQ", SAIL_HL_ARM_ADCS64_EQ;
  "SAIL_HL_ARM_SBC32_EQ", SAIL_HL_ARM_SBC32_EQ;
  "SAIL_HL_ARM_SBC64_EQ", SAIL_HL_ARM_SBC64_EQ;
  "SAIL_HL_ARM_SBCS32_EQ", SAIL_HL_ARM_SBCS32_EQ;
  "SAIL_HL_ARM_SBCS64_EQ", SAIL_HL_ARM_SBCS64_EQ;
  "SAIL_HL_ARM_NGC32_EQ", SAIL_HL_ARM_NGC32_EQ;
  "SAIL_HL_ARM_NGC64_EQ", SAIL_HL_ARM_NGC64_EQ;
  "SAIL_HL_ARM_NGCS32_EQ", SAIL_HL_ARM_NGCS32_EQ;
  "SAIL_HL_ARM_NGCS64_EQ", SAIL_HL_ARM_NGCS64_EQ
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_CARRY_PROOFS_OK";;
