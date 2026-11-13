(* Four actual SHA3 bitwise execute bodies, not decoders.
   Successful enabled-AdvSIMD access is an explicit named hook contract.
   All 32 Q-register fields, overlapping operands and every legal six-bit
   XAR count are universally quantified. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-crypto-bitwise.ml";;
needs "tools/sail/proofs/arm-shift-lemmas.ml";;

(* Mathematical facts for the actual ROL/ROR helper calculations. *)
let SAIL_HL_ARM_CRYPTO_ROL1 = prove
 (`!x:64 word.
    word_or (word_ushr x 63) (word_shl x 1) = word_rol x 1`,
  GEN_TAC THEN
  SIMP_TAC[WORD_ROL_ROR; WORD_ROR_SHIFTS; DIMINDEX_64; ARITH]);;

let SAIL_HL_ARM_CRYPTO_ROTATE6 = prove
 (`!x:64 word. !amount:6 word.
    (if val amount = 0 then x else
      word_or (word_ushr x (val amount MOD 64))
        (word_shl x (num_of_int (&64 - &(val amount MOD 64))))) =
    word_ror x (val amount)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `val(amount:6 word) < 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `amount:6 word` VAL_BOUND) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`x:64 word`; `val(amount:6 word)`]
    SAIL_HL_ARM_SHIFT_ROTATE64) THEN
  ASM_SIMP_TAC[MOD_LT]);;

let SAIL_HL_ARM_CRYPTO_BITWISE_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC (definitions @
    [assign; LET_DEF; LET_END_DEF; FST; SND; QREG';
     NUM_OF_INT_OF_NUM; INT_OF_NUM_REM; INT_OF_NUM_EQ;
     WORD_ZX_TRIVIAL; DIMINDEX_64; DIMINDEX_128]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_ARM_CRYPTO_ROL1; SAIL_HL_ARM_CRYPTO_ROTATE6];;

let SAIL_HL_ARM_EOR3128_EQ = prove
 (`!d n m a:5 word. !s t:armstate.
    sail_hl_ARM_5fEOR3128 d n m a s t <=>
    arm_EOR3 (QREG' d) (QREG' n) (QREG' m) (QREG' a) s t`,
  SAIL_HL_ARM_CRYPTO_BITWISE_TAC [sail_hl_ARM_5fEOR3128; arm_EOR3]);;

let SAIL_HL_ARM_BCAX128_EQ = prove
 (`!d n m a:5 word. !s t:armstate.
    sail_hl_ARM_5fBCAX128 d n m a s t <=>
    arm_BCAX (QREG' d) (QREG' n) (QREG' m) (QREG' a) s t`,
  SAIL_HL_ARM_CRYPTO_BITWISE_TAC [sail_hl_ARM_5fBCAX128; arm_BCAX]);;

let SAIL_HL_ARM_RAX1128_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_ARM_5fRAX1128 d n m s t <=>
    arm_RAX1 (QREG' d) (QREG' n) (QREG' m) s t`,
  SAIL_HL_ARM_CRYPTO_BITWISE_TAC [sail_hl_ARM_5fRAX1128; arm_RAX1]);;

let SAIL_HL_ARM_XAR128_EQ = prove
 (`!d n m:5 word. !amount:6 word. !s t:armstate.
    sail_hl_ARM_5fXAR128 d n m amount s t <=>
    arm_XAR (QREG' d) (QREG' n) (QREG' m) amount s t`,
  SAIL_HL_ARM_CRYPTO_BITWISE_TAC [sail_hl_ARM_5fXAR128; arm_XAR]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_EOR3128_EQ", SAIL_HL_ARM_EOR3128_EQ;
  "SAIL_HL_ARM_BCAX128_EQ", SAIL_HL_ARM_BCAX128_EQ;
  "SAIL_HL_ARM_RAX1128_EQ", SAIL_HL_ARM_RAX1128_EQ;
  "SAIL_HL_ARM_XAR128_EQ", SAIL_HL_ARM_XAR128_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_CRYPTO_BITWISE_PROOFS_OK";;
