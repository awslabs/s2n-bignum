(* Actual conditional-branch decoder/execute graphs, under successful flat
   branch contracts. HOL has already advanced PC by four bytes. Canonical
   register fields, all encoded offsets/conditions and both outcomes are
   quantified. TBZ/TBNZ preserve the decoder's width/bit-position coupling.
   This is not a decoder theorem, platform/fault refinement or compiler proof. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-branch-conditional.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-branch-state-lemmas.ml";;

(* Pure representation facts for the actual branch decoder parameters.
   These do not define instruction effects. *)
let SAIL_HL_ARM_BRANCH_OFFSET19 = prove
 (`!immediate:19 word.
   word_join immediate (word 0:2 word):21 word =
   word(val immediate * 4)`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_BRANCH_OFFSET14 = prove
 (`!immediate:14 word.
   word_join immediate (word 0:2 word):16 word =
   word(val immediate * 4)`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_BRANCH_LOW_BIT_POSITION = prove
 (`!position:5 word.
   val(word_join (word 0:1 word) position:6 word) = val position`,
  GEN_TAC THEN MP_TAC(ISPEC `position:5 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 32 ==> n < 64`] THEN
  PRINT_GOAL_TAC);;

let SAIL_HL_ARM_BRANCH_HIGH_BIT_POSITION = prove
 (`!position:5 word.
   val(word_join (word 1:1 word) position:6 word) = 32 + val position`,
  GEN_TAC THEN MP_TAC(ISPEC `position:5 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 32 ==> 32 + n < 64`]);;

(* Normalize actual branch exports without changing either state model. *)
let SAIL_HL_ARM_BRANCH_CONDITIONAL_REDUCE definitions =
  REWRITE_TAC(definitions @
    [assign; SEQ; LET_DEF; LET_END_DEF; FST; SND;
     XREG'; WREG'; NUM_OF_INT_OF_NUM; READ_COMPONENT_COMPOSE;
     READ_WRITE_EVALUATE; ARM_ZERO_REGISTER; READ_RVALUE;
     SAIL_HL_ARM_BRANCH_OFFSET19; SAIL_HL_ARM_BRANCH_OFFSET14;
     SAIL_HL_ARM_BRANCH_LOW_BIT_POSITION;
     SAIL_HL_ARM_BRANCH_HIGH_BIT_POSITION;
     SAIL_HL_ARM_BRANCH_PC_READS; SAIL_HL_ARM_BRANCH_PC_SELF]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[condition_semantics;
    REWRITE_RULE CONDITION_CLAUSES condition_semantics;
    SAIL_HL_ARM_BIT_WORD; SAIL_HL_ARM_BIT_WORD_EQ;
    BIT_WORD_SUBWORD; DIMINDEX_1; CONJ_ACI] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; ARM_ZERO_REGISTER; READ_RVALUE; EQ_SYM_EQ] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[SAIL_HL_ARM_BRANCH_PC_READS;
    SAIL_HL_ARM_BRANCH_PC_SELF] THEN ASM_MESON_TAC[];;

let SAIL_HL_ARM_BRANCH_CONDITIONAL_TAC definitions =
  REPEAT GEN_TAC THEN SAIL_HL_ARM_BRANCH_CONDITIONAL_REDUCE definitions;;

let SAIL_HL_ARM_BRANCH_CONDITION_TAC definitions =
  REPEAT GEN_TAC THEN
  SPEC_TAC (`condition:4 word`, `condition:4 word`) THEN
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN
  REWRITE_TAC[DIMINDEX_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN
  SAIL_HL_ARM_BRANCH_CONDITIONAL_REDUCE definitions;;

let SAIL_HL_ARM_BCOND_EQ = prove
 (`!condition:4 word. !immediate:19 word. !s t:armstate.
   sail_hl_arm_5fBCOND
     (PC :> evaluate (\pc:64 word. word_sub pc (word 4)))
     condition immediate s t <=>
   arm_Bcond (Condition condition) (word(val immediate * 4):21 word) s t`,
  SAIL_HL_ARM_BRANCH_CONDITION_TAC [sail_hl_arm_5fBCOND; arm_Bcond]);;
sail_hl_report ("SAIL_HL_ARM_BCOND_EQ", SAIL_HL_ARM_BCOND_EQ);;

(* Construct theorem statements only, never instruction effects. *)
let SAIL_HL_ARM_BRANCH_CONDITIONAL_CLAIM name definition parameters arguments target definitions =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term(
    parameters ^ " !s t:armstate. " ^ source ^
    " (PC :> evaluate (\\pc:64 word. word_sub pc (word 4))) " ^
    arguments ^ " s t <=> " ^ target ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_BRANCH_CONDITIONAL_TAC (definition :: definitions)) in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_BRANCH_COMPARE_CLAIMS = map
  (fun (name, definition, instruction, component, semantics) ->
    SAIL_HL_ARM_BRANCH_CONDITIONAL_CLAIM name definition
      "!register:5 word. !immediate:19 word." "register immediate"
      ("arm_" ^ instruction ^ " (" ^ component ^ "' register) " ^
       "(word(val immediate * 4):21 word)") [semantics]) [
  "SAIL_HL_ARM_CBZ32_EQ", sail_hl_arm_5fCBZ32, "CBZ", "WREG", arm_CBZ;
  "SAIL_HL_ARM_CBZ64_EQ", sail_hl_arm_5fCBZ64, "CBZ", "XREG", arm_CBZ;
  "SAIL_HL_ARM_CBNZ32_EQ", sail_hl_arm_5fCBNZ32, "CBNZ", "WREG", arm_CBNZ;
  "SAIL_HL_ARM_CBNZ64_EQ", sail_hl_arm_5fCBNZ64, "CBNZ", "XREG", arm_CBNZ;
];;

let SAIL_HL_ARM_BRANCH_ALIAS_CLAIMS = map
  (fun (instruction, definition, semantics) ->
    SAIL_HL_ARM_BRANCH_CONDITIONAL_CLAIM
      ("SAIL_HL_ARM_" ^ instruction ^ "_EQ") definition
      "!immediate:19 word." "immediate"
      ("arm_" ^ instruction ^ " (word(val immediate * 4):21 word)")
      [semantics; arm_Bcond]) [
  "BEQ", sail_hl_arm_5fBEQ, arm_BEQ;
  "BNE", sail_hl_arm_5fBNE, arm_BNE;
  "BCS", sail_hl_arm_5fBCS, arm_BCS;
  "BHS", sail_hl_arm_5fBHS, arm_BHS;
  "BCC", sail_hl_arm_5fBCC, arm_BCC;
  "BLO", sail_hl_arm_5fBLO, arm_BLO;
  "BMI", sail_hl_arm_5fBMI, arm_BMI;
  "BPL", sail_hl_arm_5fBPL, arm_BPL;
  "BVS", sail_hl_arm_5fBVS, arm_BVS;
  "BVC", sail_hl_arm_5fBVC, arm_BVC;
  "BHI", sail_hl_arm_5fBHI, arm_BHI;
  "BLS", sail_hl_arm_5fBLS, arm_BLS;
  "BGE", sail_hl_arm_5fBGE, arm_BGE;
  "BLT", sail_hl_arm_5fBLT, arm_BLT;
  "BGT", sail_hl_arm_5fBGT, arm_BGT;
  "BLE", sail_hl_arm_5fBLE, arm_BLE;
  "BAL", sail_hl_arm_5fBAL, arm_BAL;
  "BNV", sail_hl_arm_5fBNV, arm_BNV;
];;
assert(length SAIL_HL_ARM_BRANCH_COMPARE_CLAIMS = 4);;
assert(length SAIL_HL_ARM_BRANCH_ALIAS_CLAIMS = 18);;

let SAIL_HL_ARM_BRANCH_TEST_CLAIMS = map
  (fun (name, definition, instruction, component, bit_position, semantics) ->
    SAIL_HL_ARM_BRANCH_CONDITIONAL_CLAIM name definition
      "!register position:5 word. !immediate:14 word."
      "register position immediate"
      ("arm_" ^ instruction ^ " (" ^ component ^ "' register) " ^
       "(" ^ bit_position ^ ") (word(val immediate * 4):16 word)")
      [semantics]) [
  "SAIL_HL_ARM_TBZ32_EQ", sail_hl_arm_5fTBZ32, "TBZ", "WREG",
    "val position", arm_TBZ;
  "SAIL_HL_ARM_TBZ64_HI_EQ", sail_hl_arm_5fTBZ64_5fHI, "TBZ", "XREG",
    "32 + val position", arm_TBZ;
  "SAIL_HL_ARM_TBNZ32_EQ", sail_hl_arm_5fTBNZ32, "TBNZ", "WREG",
    "val position", arm_TBNZ;
  "SAIL_HL_ARM_TBNZ64_HI_EQ", sail_hl_arm_5fTBNZ64_5fHI, "TBNZ", "XREG",
    "32 + val position", arm_TBNZ;
];;

assert(length SAIL_HL_ARM_BRANCH_COMPARE_CLAIMS = 4);;
assert(length SAIL_HL_ARM_BRANCH_TEST_CLAIMS = 4);;
assert(length SAIL_HL_ARM_BRANCH_ALIAS_CLAIMS = 18);;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_BRANCH_CONDITIONAL_PROOFS_OK";;
