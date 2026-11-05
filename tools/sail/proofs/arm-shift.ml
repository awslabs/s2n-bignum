(* The upstream variable-shift instruction masks its register shift count;
   ShiftReg reads the value register, and the actual ROR helper implements
   rotation with logical shifts. All encoded registers, high shift-count
   bits, zero counts and overlapping operands remain universally quantified.
   These are flat-register graph claims, not full-platform refinement. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-shift.ml";;
needs "tools/sail/proofs/arm-shift-lemmas.ml";;

let SAIL_HL_ARM_SHIFT_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC (definitions @
    [assign; LET_DEF; LET_END_DEF; FST; SND; XREG'; WREG';
     INT_OF_NUM_REM; INT_OF_NUM_EQ; NUM_OF_INT_OF_NUM;
     word_jshl; word_jushr; word_jshr; word_jror;
     MOD_MOD_REFL; DIMINDEX_32; DIMINDEX_64;
     SAIL_HL_ARM_SHIFT_ROTATE32; SAIL_HL_ARM_SHIFT_ROTATE64;
     ARM_ZERO_REGISTER; READ_RVALUE]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[ARM_ZERO_REGISTER; READ_RVALUE; MOD_MOD_REFL;
    INT_OF_NUM_EQ; SAIL_HL_ARM_SHIFT_ROTATE32;
    SAIL_HL_ARM_SHIFT_ROTATE64];;

let SAIL_HL_ARM_LSLV32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_arm_5fLSLV32 d n m s t <=>
    arm_LSLV (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_SHIFT_TAC [sail_hl_arm_5fLSLV32; arm_LSLV]);;

let SAIL_HL_ARM_LSLV64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_arm_5fLSLV64 d n m s t <=>
    arm_LSLV (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_SHIFT_TAC [sail_hl_arm_5fLSLV64; arm_LSLV]);;

let SAIL_HL_ARM_LSRV32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_arm_5fLSRV32 d n m s t <=>
    arm_LSRV (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_SHIFT_TAC [sail_hl_arm_5fLSRV32; arm_LSRV]);;

let SAIL_HL_ARM_LSRV64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_arm_5fLSRV64 d n m s t <=>
    arm_LSRV (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_SHIFT_TAC [sail_hl_arm_5fLSRV64; arm_LSRV]);;

let SAIL_HL_ARM_ASRV32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_arm_5fASRV32 d n m s t <=>
    arm_ASRV (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_SHIFT_TAC [sail_hl_arm_5fASRV32; arm_ASRV]);;

let SAIL_HL_ARM_ASRV64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_arm_5fASRV64 d n m s t <=>
    arm_ASRV (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_SHIFT_TAC [sail_hl_arm_5fASRV64; arm_ASRV]);;

let SAIL_HL_ARM_RORV32_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_arm_5fRORV32 d n m s t <=>
    arm_RORV (WREG' d) (WREG' n) (WREG' m) s t`,
  SAIL_HL_ARM_SHIFT_TAC [sail_hl_arm_5fRORV32; arm_RORV]);;

let SAIL_HL_ARM_RORV64_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_arm_5fRORV64 d n m s t <=>
    arm_RORV (XREG' d) (XREG' n) (XREG' m) s t`,
  SAIL_HL_ARM_SHIFT_TAC [sail_hl_arm_5fRORV64; arm_RORV]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_LSLV32_EQ", SAIL_HL_ARM_LSLV32_EQ;
  "SAIL_HL_ARM_LSLV64_EQ", SAIL_HL_ARM_LSLV64_EQ;
  "SAIL_HL_ARM_LSRV32_EQ", SAIL_HL_ARM_LSRV32_EQ;
  "SAIL_HL_ARM_LSRV64_EQ", SAIL_HL_ARM_LSRV64_EQ;
  "SAIL_HL_ARM_ASRV32_EQ", SAIL_HL_ARM_ASRV32_EQ;
  "SAIL_HL_ARM_ASRV64_EQ", SAIL_HL_ARM_ASRV64_EQ;
  "SAIL_HL_ARM_RORV32_EQ", SAIL_HL_ARM_RORV32_EQ;
  "SAIL_HL_ARM_RORV64_EQ", SAIL_HL_ARM_RORV64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_SHIFT_PROOFS_OK";;
