(* Both actual register and immediate compare bodies are exported at each
   decoder width. The universally quantified one-bit selector covers both
   forms; operand fields, NZCV fallback and all 16 conditions remain symbolic. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-compare.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

(* The relation proof can expose a bit of the packed NZCV word directly,
   after reducing its one-bit subword. Derive that spelling from the same
   checked packed-bit equations; the flag values and state writes remain. *)
let SAIL_HL_ARM_COMPARE_PACKED_DIRECT_REWRITES =
  CONV_RULE NUM_REDUCE_CONV
    (REWRITE_RULE[BIT_WORD_SUBWORD; DIMINDEX_1; DIMINDEX_4]
      SAIL_HL_ARM_PACKED_REWRITES);;

let SAIL_HL_ARM_COMPARE_TAC definitions =
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `use_immediate:1 word = word 1` THEN
  SPEC_TAC (`condition:4 word`, `condition:4 word`) THEN
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN
  REWRITE_TAC[DIMINDEX_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN
  ASM_REWRITE_TAC(definitions @
    [LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM;
     XREG'; WREG'; READ_RVALUE]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[REWRITE_RULE CONDITION_CLAUSES condition_semantics;
    SAIL_HL_ARM_BIT_WORD; SAIL_HL_ARM_BIT_WORD_EQ;
    CONJ_ACI; IWORD_INT_ADD; GSYM WORD_IWORD; WORD_VAL;
    WORD_ADD_0; SAIL_HL_ARM_NOT_FLAG; GSYM WORD_BITVAL;
    SAIL_HL_ARM_SUB_RESULT;
    SAIL_HL_ARM_MSB32; SAIL_HL_ARM_MSB64] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
    WORD_ADD_AC; ADD_AC; INT_ADD_AC; EQ_SYM_EQ;
    ADD_CLAUSES; INT_ADD_LID; INT_ADD_RID;
    SAIL_HL_ARM_PACKED_REWRITES;
    SAIL_HL_ARM_COMPARE_PACKED_DIRECT_REWRITES;
    SAIL_HL_ARM_SUB_FLAGS;
    BIT_WORD_SUBWORD; DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SEQ; assign; CONJ_ACI] THEN
  (* Selecting a condition can expose the packed flags only at this stage.
     Reduce those bits here as well, then compare the state equations
     directly instead of searching with the unreduced flag expressions. *)
  REPEAT (COND_CASES_TAC THEN
    ASM_REWRITE_TAC[SAIL_HL_ARM_COMPARE_PACKED_DIRECT_REWRITES]) THEN
  ASM_REWRITE_TAC[SAIL_HL_ARM_COMPARE_PACKED_DIRECT_REWRITES;
    EQ_SYM_EQ; CONJ_ACI] THEN
  (* Splitting a composite condition can leave contradictory flag cases.
     Check those small hypotheses alone, without searching state writes. *)
  TRY (SUBGOAL_THEN `F` MP_TAC THENL
    [ASM_MESON_TAC[]; REWRITE_TAC[]]) THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_CCMN32_EQ = prove
 (`!use_immediate:1 word. !operand n:5 word. !nzcv condition:4 word.
   !s t:armstate.
   sail_hl_arm_5fCCMN32 use_immediate operand n nzcv condition s t <=>
   arm_CCMN (WREG' n)
     (if use_immediate = word 1
      then rvalue(word_zx operand:32 word) else WREG' operand)
     nzcv (Condition condition) s t`,
  SAIL_HL_ARM_COMPARE_TAC [sail_hl_arm_5fCCMN32; arm_CCMN]);;

let SAIL_HL_ARM_CCMN64_EQ = prove
 (`!use_immediate:1 word. !operand n:5 word. !nzcv condition:4 word.
   !s t:armstate.
   sail_hl_arm_5fCCMN64 use_immediate operand n nzcv condition s t <=>
   arm_CCMN (XREG' n)
     (if use_immediate = word 1
      then rvalue(word_zx operand:64 word) else XREG' operand)
     nzcv (Condition condition) s t`,
  SAIL_HL_ARM_COMPARE_TAC [sail_hl_arm_5fCCMN64; arm_CCMN]);;

let SAIL_HL_ARM_CCMP32_EQ = prove
 (`!use_immediate:1 word. !operand n:5 word. !nzcv condition:4 word.
   !s t:armstate.
   sail_hl_arm_5fCCMP32 use_immediate operand n nzcv condition s t <=>
   arm_CCMP (WREG' n)
     (if use_immediate = word 1
      then rvalue(word_zx operand:32 word) else WREG' operand)
     nzcv (Condition condition) s t`,
  SAIL_HL_ARM_COMPARE_TAC [sail_hl_arm_5fCCMP32; arm_CCMP]);;

let SAIL_HL_ARM_CCMP64_EQ = prove
 (`!use_immediate:1 word. !operand n:5 word. !nzcv condition:4 word.
   !s t:armstate.
   sail_hl_arm_5fCCMP64 use_immediate operand n nzcv condition s t <=>
   arm_CCMP (XREG' n)
     (if use_immediate = word 1
      then rvalue(word_zx operand:64 word) else XREG' operand)
     nzcv (Condition condition) s t`,
  SAIL_HL_ARM_COMPARE_TAC [sail_hl_arm_5fCCMP64; arm_CCMP]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_CCMN32_EQ", SAIL_HL_ARM_CCMN32_EQ;
  "SAIL_HL_ARM_CCMN64_EQ", SAIL_HL_ARM_CCMN64_EQ;
  "SAIL_HL_ARM_CCMP32_EQ", SAIL_HL_ARM_CCMP32_EQ;
  "SAIL_HL_ARM_CCMP64_EQ", SAIL_HL_ARM_CCMP64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_COMPARE_PROOFS_OK";;
