(* Floating-point conditional selection transfers a register bit pattern.
   Both widths, all sixteen condition fields, every register/state/data
   value and operand overlap are included. This is whole-armstate agreement
   under the existing instruction-enable/register boundaries; no FPCR or
   FPSR component is replaced or discarded. Move and conversion requests
   remain separate and are not claimed by this proof. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-fp-select.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-duplicate-lemmas.ml";;

let SAIL_HL_ARM_FP_SELECT_NORM definition =
  REWRITE_TAC[definition; arm_FCSEL; assign; LET_DEF; LET_END_DEF;
    FST; SND; NUM_OF_INT_OF_NUM; QREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    REWRITE_RULE CONDITION_CLAUSES condition_semantics;
    SAIL_HL_ARM_BIT_WORD; SAIL_HL_ARM_BIT_WORD_EQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (* GT is written as NZCV-equality /\ ~ZF in Sail and with the two
     conjuncts reversed in HOL. Normalize conjunctions before splitting
     the flag cases, so the same test is not treated as two independent
     conditions. All sixteen condition fields and all flag values remain. *)
  REWRITE_TAC[CONJ_ACI] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[CONJ_ACI]) THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ZX_TRIVIAL; EQ_SYM_EQ] THEN
  TRY SAIL_HL_ARM_VECTOR_DUPLICATE_VALUE_TAC THEN
  TRY(ASM_MESON_TAC[]) THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_FP_SELECT_CLAIM width definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 4 definition in
  let statement = parse_term(
    configuration ^ "!condition:4 word. !d n m:5 word. !s t:armstate. " ^
    source ^
    " condition d n m s t <=> arm_FCSEL (QREG' d) (QREG' n) " ^
    "(QREG' m) (Condition condition) " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN
    SPEC_TAC(`condition:4 word`,`condition:4 word`) THEN
    ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN REWRITE_TAC[DIMINDEX_4] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
    REPEAT CONJ_TAC THEN SAIL_HL_ARM_FP_SELECT_NORM definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_FCSEL%d_EQ" width in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_FP_SELECT_CLAIMS = map
  (fun (width,definition) -> SAIL_HL_ARM_FP_SELECT_CLAIM width definition) [
  32,sail_hl_arm_5fFCSEL32;
  64,sail_hl_arm_5fFCSEL64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_FP_SELECT_PROOFS_OK";;
