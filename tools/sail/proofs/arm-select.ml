(* Actual upstream conditional-select bodies, including ConditionHolds.
   Fields are universally quantified: register 31 and operand/destination
   overlap are included. Both decoder widths and all five aliases are checked.
   Alias agreement includes the HOL definitions at AL/NV, where encoded
   inversion is not Boolean negation. It does not make those encodings valid
   assembly aliases. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-select.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

let SAIL_HL_ARM_SELECT_TAC definitions =
  REPEAT GEN_TAC THEN
  SPEC_TAC (`condition:4 word`, `condition:4 word`) THEN
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN
  REWRITE_TAC[DIMINDEX_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC (definitions @
    [assign; LET_DEF; LET_END_DEF; FST; SND; INVERT_CONDITION;
     XREG'; WREG'; NUM_OF_INT_OF_NUM]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[REWRITE_RULE CONDITION_CLAUSES condition_semantics;
    SAIL_HL_ARM_BIT_WORD; SAIL_HL_ARM_BIT_WORD_EQ;
    GSYM WORD_NEG_AS_ADD; ARM_ZERO_REGISTER; READ_RVALUE;
    CONJ_ACI] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[CONJ_ACI] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[] THEN TRY (ASM_MESON_TAC[]) THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_CSEL64_EQ = prove
 (`!condition:4 word. !d n m:5 word. !s t:armstate.
   sail_hl_arm_5fCSEL64 condition d n m s t <=>
   arm_CSEL (XREG' d) (XREG' n) (XREG' m) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSEL64; arm_CSEL]);;

let SAIL_HL_ARM_CSEL32_EQ = prove
 (`!condition:4 word. !d n m:5 word. !s t:armstate.
   sail_hl_arm_5fCSEL32 condition d n m s t <=>
   arm_CSEL (WREG' d) (WREG' n) (WREG' m) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSEL32; arm_CSEL]);;

let SAIL_HL_ARM_CSINC64_EQ = prove
 (`!condition:4 word. !d n m:5 word. !s t:armstate.
   sail_hl_arm_5fCSINC64 condition d n m s t <=>
   arm_CSINC (XREG' d) (XREG' n) (XREG' m) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSINC64; arm_CSINC]);;

let SAIL_HL_ARM_CSINC32_EQ = prove
 (`!condition:4 word. !d n m:5 word. !s t:armstate.
   sail_hl_arm_5fCSINC32 condition d n m s t <=>
   arm_CSINC (WREG' d) (WREG' n) (WREG' m) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSINC32; arm_CSINC]);;

let SAIL_HL_ARM_CSINV64_EQ = prove
 (`!condition:4 word. !d n m:5 word. !s t:armstate.
   sail_hl_arm_5fCSINV64 condition d n m s t <=>
   arm_CSINV (XREG' d) (XREG' n) (XREG' m) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSINV64; arm_CSINV]);;

let SAIL_HL_ARM_CSINV32_EQ = prove
 (`!condition:4 word. !d n m:5 word. !s t:armstate.
   sail_hl_arm_5fCSINV32 condition d n m s t <=>
   arm_CSINV (WREG' d) (WREG' n) (WREG' m) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSINV32; arm_CSINV]);;

let SAIL_HL_ARM_CSNEG64_EQ = prove
 (`!condition:4 word. !d n m:5 word. !s t:armstate.
   sail_hl_arm_5fCSNEG64 condition d n m s t <=>
   arm_CSNEG (XREG' d) (XREG' n) (XREG' m) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSNEG64; arm_CSNEG]);;

let SAIL_HL_ARM_CSNEG32_EQ = prove
 (`!condition:4 word. !d n m:5 word. !s t:armstate.
   sail_hl_arm_5fCSNEG32 condition d n m s t <=>
   arm_CSNEG (WREG' d) (WREG' n) (WREG' m) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSNEG32; arm_CSNEG]);;

let SAIL_HL_ARM_CINC64_EQ = prove
 (`!condition:4 word. !d n:5 word. !s t:armstate.
   sail_hl_arm_5fCINC64 condition d n s t <=>
   arm_CINC (XREG' d) (XREG' n) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCINC64; arm_CINC; arm_CSINC]);;

let SAIL_HL_ARM_CINC32_EQ = prove
 (`!condition:4 word. !d n:5 word. !s t:armstate.
   sail_hl_arm_5fCINC32 condition d n s t <=>
   arm_CINC (WREG' d) (WREG' n) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCINC32; arm_CINC; arm_CSINC]);;

let SAIL_HL_ARM_CINV64_EQ = prove
 (`!condition:4 word. !d n:5 word. !s t:armstate.
   sail_hl_arm_5fCINV64 condition d n s t <=>
   arm_CINV (XREG' d) (XREG' n) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCINV64; arm_CINV; arm_CSINV]);;

let SAIL_HL_ARM_CINV32_EQ = prove
 (`!condition:4 word. !d n:5 word. !s t:armstate.
   sail_hl_arm_5fCINV32 condition d n s t <=>
   arm_CINV (WREG' d) (WREG' n) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCINV32; arm_CINV; arm_CSINV]);;

let SAIL_HL_ARM_CNEG64_EQ = prove
 (`!condition:4 word. !d n:5 word. !s t:armstate.
   sail_hl_arm_5fCNEG64 condition d n s t <=>
   arm_CNEG (XREG' d) (XREG' n) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCNEG64; arm_CNEG; arm_CSNEG]);;

let SAIL_HL_ARM_CNEG32_EQ = prove
 (`!condition:4 word. !d n:5 word. !s t:armstate.
   sail_hl_arm_5fCNEG32 condition d n s t <=>
   arm_CNEG (WREG' d) (WREG' n) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCNEG32; arm_CNEG; arm_CSNEG]);;

let SAIL_HL_ARM_CSET64_EQ = prove
 (`!condition:4 word. !d:5 word. !s t:armstate.
   sail_hl_arm_5fCSET64 condition d s t <=>
   arm_CSET (XREG' d) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSET64; arm_CSET; arm_CSINC]);;

let SAIL_HL_ARM_CSET32_EQ = prove
 (`!condition:4 word. !d:5 word. !s t:armstate.
   sail_hl_arm_5fCSET32 condition d s t <=>
   arm_CSET (WREG' d) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSET32; arm_CSET; arm_CSINC]);;

let SAIL_HL_ARM_CSETM64_EQ = prove
 (`!condition:4 word. !d:5 word. !s t:armstate.
   sail_hl_arm_5fCSETM64 condition d s t <=>
   arm_CSETM (XREG' d) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSETM64; arm_CSETM; arm_CSINV]);;

let SAIL_HL_ARM_CSETM32_EQ = prove
 (`!condition:4 word. !d:5 word. !s t:armstate.
   sail_hl_arm_5fCSETM32 condition d s t <=>
   arm_CSETM (WREG' d) (Condition condition) s t`,
  SAIL_HL_ARM_SELECT_TAC [sail_hl_arm_5fCSETM32; arm_CSETM; arm_CSINV]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_CSEL32_EQ", SAIL_HL_ARM_CSEL32_EQ;
  "SAIL_HL_ARM_CSEL64_EQ", SAIL_HL_ARM_CSEL64_EQ;
  "SAIL_HL_ARM_CSINC32_EQ", SAIL_HL_ARM_CSINC32_EQ;
  "SAIL_HL_ARM_CSINC64_EQ", SAIL_HL_ARM_CSINC64_EQ;
  "SAIL_HL_ARM_CSINV32_EQ", SAIL_HL_ARM_CSINV32_EQ;
  "SAIL_HL_ARM_CSINV64_EQ", SAIL_HL_ARM_CSINV64_EQ;
  "SAIL_HL_ARM_CSNEG32_EQ", SAIL_HL_ARM_CSNEG32_EQ;
  "SAIL_HL_ARM_CSNEG64_EQ", SAIL_HL_ARM_CSNEG64_EQ;
  "SAIL_HL_ARM_CINC32_EQ", SAIL_HL_ARM_CINC32_EQ;
  "SAIL_HL_ARM_CINC64_EQ", SAIL_HL_ARM_CINC64_EQ;
  "SAIL_HL_ARM_CINV32_EQ", SAIL_HL_ARM_CINV32_EQ;
  "SAIL_HL_ARM_CINV64_EQ", SAIL_HL_ARM_CINV64_EQ;
  "SAIL_HL_ARM_CNEG32_EQ", SAIL_HL_ARM_CNEG32_EQ;
  "SAIL_HL_ARM_CNEG64_EQ", SAIL_HL_ARM_CNEG64_EQ;
  "SAIL_HL_ARM_CSET32_EQ", SAIL_HL_ARM_CSET32_EQ;
  "SAIL_HL_ARM_CSET64_EQ", SAIL_HL_ARM_CSET64_EQ;
  "SAIL_HL_ARM_CSETM32_EQ", SAIL_HL_ARM_CSETM32_EQ;
  "SAIL_HL_ARM_CSETM64_EQ", SAIL_HL_ARM_CSETM64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_SELECT_PROOFS_OK";;
