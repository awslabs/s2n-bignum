(* ADR and ADRP consume the actual upstream decoders, execute body and
   PC_read helper. HOL's fetch step has already advanced PC by four bytes,
   so the exported Sail current-PC component reads that value minus four.
   The theorem covers every encoded destination/immediate, including XZR,
   negative offsets and page-boundary wraparound. It does not validate
   instruction decoding or a full-platform Sail state projection. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-address.ml";;

let SAIL_HL_ARM_ADDRESS_IMMEDIATE = prove
 (`!off:21 word.
    word_join (word_subword off (2,19):19 word)
              (word_subword off (0,2):2 word):21 word = off`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_ADDRESS_PAGE = prove
 (`!pc:64 word.
    word_insert pc (0,12) (word 0:12 word):64 word =
    word_and pc (word 0xFFFFFFFFFFFFF000)`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_ADDRESS_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC (definitions @
    [assign; LET_DEF; LET_END_DEF; XREG'; NUM_OF_INT_OF_NUM;
     READ_COMPONENT_COMPOSE; READ_WRITE_EVALUATE;
     SAIL_HL_ARM_ADDRESS_IMMEDIATE; SAIL_HL_ARM_ADDRESS_PAGE;
     ARM_ZERO_REGISTER; READ_RVALUE]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[ARM_ZERO_REGISTER; READ_RVALUE];;

let SAIL_HL_ARM_ADR64_EQ = prove
 (`!d:5 word. !off:21 word. !s t:armstate.
    sail_hl_arm_5fADR64
      (PC :> evaluate (\pc:64 word. word_sub pc (word 4))) d off s t <=>
    arm_ADR (XREG' d) off s t`,
  SAIL_HL_ARM_ADDRESS_TAC [sail_hl_arm_5fADR64; arm_ADR]);;

let SAIL_HL_ARM_ADRP64_EQ = prove
 (`!d:5 word. !off:21 word. !s t:armstate.
    sail_hl_arm_5fADRP64
      (PC :> evaluate (\pc:64 word. word_sub pc (word 4))) d off s t <=>
    arm_ADRP (XREG' d) off s t`,
  SAIL_HL_ARM_ADDRESS_TAC [sail_hl_arm_5fADRP64; arm_ADRP]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_ADR64_EQ", SAIL_HL_ARM_ADR64_EQ;
  "SAIL_HL_ARM_ADRP64_EQ", SAIL_HL_ARM_ADRP64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_ADDRESS_PROOFS_OK";;
