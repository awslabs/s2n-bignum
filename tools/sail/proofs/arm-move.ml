(* These claims compare execution effects for legal halfword positions.
   They do not compare decoders or admit the reserved 32-bit hw=10/11 forms.
   Registers include field 31; MOVK preserves the unwritten low-word bits
   and W-register writes clear the high half through the existing component. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-move.ml";;

(* Generic word facts relate Sail's local range assignment to the existing
   HOL subword component. They introduce no instruction semantics. *)
let SAIL_HL_ARM_MOVE_WRITE_SUBWORD = prove
 (`!pos len (value:M word) (original:N word).
     write (subword(pos,len)) value original =
     (word_insert original (pos,len) value:N word)`,
  REWRITE_TAC[subword; write; word_insert]);;

let SAIL_HL_ARM_MOVE_INSERT_ZERO = prove
 (`!pos (imm:16 word).
     (word_insert (word 0:N word) (pos,16) imm:N word) =
     word(val imm * 2 EXP pos)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_insert; VAL_WORD_0; MULT_CLAUSES; DIV_0;
    MOD_0; ADD_CLAUSES] THEN
  SIMP_TAC[MOD_LT; REWRITE_RULE[DIMINDEX_16] (ISPEC `imm:16 word` VAL_BOUND)] THEN
  REWRITE_TAC[MULT_SYM]);;

let SAIL_HL_ARM_MOVE_TAC selector dimension definitions =
  REPEAT GEN_TAC THEN
  SPEC_TAC (selector, selector) THEN
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN
  REWRITE_TAC[dimension] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC(definitions @
    [LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM; XREG'; WREG';
     assign; WRITE_COMPONENT_COMPOSE; SAIL_HL_ARM_MOVE_WRITE_SUBWORD;
     SAIL_HL_ARM_MOVE_INSERT_ZERO]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EQ_SYM_EQ; SAIL_HL_ARM_MOVE_INSERT_ZERO] THEN
  PRINT_GOAL_TAC;;

let SAIL_HL_ARM_MOVK32_EQ = prove
 (`!d:5 word. !imm:16 word. !hw:1 word. !s t:armstate.
   sail_hl_arm_5fMOVK32 d imm hw s t <=>
   arm_MOVK (WREG' d) imm (16 * val hw) s t`,
  SAIL_HL_ARM_MOVE_TAC `hw:1 word` DIMINDEX_1
    [sail_hl_arm_5fMOVK32; arm_MOVK]);;

let SAIL_HL_ARM_MOVK64_EQ = prove
 (`!d:5 word. !imm:16 word. !hw:2 word. !s t:armstate.
   sail_hl_arm_5fMOVK64 d imm hw s t <=>
   arm_MOVK (XREG' d) imm (16 * val hw) s t`,
  SAIL_HL_ARM_MOVE_TAC `hw:2 word` DIMINDEX_2
    [sail_hl_arm_5fMOVK64; arm_MOVK]);;

let SAIL_HL_ARM_MOVN32_EQ = prove
 (`!d:5 word. !imm:16 word. !hw:1 word. !s t:armstate.
   sail_hl_arm_5fMOVN32 d imm hw s t <=>
   arm_MOVN (WREG' d) imm (16 * val hw) s t`,
  SAIL_HL_ARM_MOVE_TAC `hw:1 word` DIMINDEX_1
    [sail_hl_arm_5fMOVN32; arm_MOVN]);;

let SAIL_HL_ARM_MOVN64_EQ = prove
 (`!d:5 word. !imm:16 word. !hw:2 word. !s t:armstate.
   sail_hl_arm_5fMOVN64 d imm hw s t <=>
   arm_MOVN (XREG' d) imm (16 * val hw) s t`,
  SAIL_HL_ARM_MOVE_TAC `hw:2 word` DIMINDEX_2
    [sail_hl_arm_5fMOVN64; arm_MOVN]);;

let SAIL_HL_ARM_MOVZ32_EQ = prove
 (`!d:5 word. !imm:16 word. !hw:1 word. !s t:armstate.
   sail_hl_arm_5fMOVZ32 d imm hw s t <=>
   arm_MOVZ (WREG' d) imm (16 * val hw) s t`,
  SAIL_HL_ARM_MOVE_TAC `hw:1 word` DIMINDEX_1
    [sail_hl_arm_5fMOVZ32; arm_MOVZ]);;

let SAIL_HL_ARM_MOVZ64_EQ = prove
 (`!d:5 word. !imm:16 word. !hw:2 word. !s t:armstate.
   sail_hl_arm_5fMOVZ64 d imm hw s t <=>
   arm_MOVZ (XREG' d) imm (16 * val hw) s t`,
  SAIL_HL_ARM_MOVE_TAC `hw:2 word` DIMINDEX_2
    [sail_hl_arm_5fMOVZ64; arm_MOVZ]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_MOVK32_EQ", SAIL_HL_ARM_MOVK32_EQ;
  "SAIL_HL_ARM_MOVK64_EQ", SAIL_HL_ARM_MOVK64_EQ;
  "SAIL_HL_ARM_MOVN32_EQ", SAIL_HL_ARM_MOVN32_EQ;
  "SAIL_HL_ARM_MOVN64_EQ", SAIL_HL_ARM_MOVN64_EQ;
  "SAIL_HL_ARM_MOVZ32_EQ", SAIL_HL_ARM_MOVZ32_EQ;
  "SAIL_HL_ARM_MOVZ64_EQ", SAIL_HL_ARM_MOVZ64_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MOVE_PROOFS_OK";;
