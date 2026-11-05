(* Agreement for the five FMOV register-transfer forms under the common
   enabled-FP access interpretation and checked capability/mode facts.
   FPCR remains an arbitrary component. Its original masking and
   IsMerging calculations are retained in the generated model.
   The MOV arms do not perform numerical FP conversion or select the
   shared execute body's conversion-only merging behavior.
   FCSEL is proved in arm-fp-select.ml.

   The domains are low32/low64/high64 vector-to-GPR and low64/high64
   GPR-to-vector, with all register fields, states and overlaps. This does
   not prove numerical conversion, access-fault or platform refinement. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-fpbits.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-duplicate-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_FPBITS_NORM definition =
  REWRITE_TAC[definition; arm_FCSEL; arm_FMOV_FtoI; arm_FMOV_ItoF;
    assign; LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM;
    QREG'; XREG'; WREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    READ_ZEROTOP_32;
    REWRITE_RULE CONDITION_CLAUSES condition_semantics;
    SAIL_HL_ARM_BIT_WORD;
    SAIL_HL_ARM_BIT_WORD_EQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ZX_TRIVIAL; EQ_SYM_EQ] THEN
  TRY SAIL_HL_ARM_VECTOR_DUPLICATE_VALUE_TAC THEN
  (* Vpart_set joins the new high64 with the old low64. The target uses
     word_insert; after observing bits, both have the same two halves. *)
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_ZX; BIT_WORD_0] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let SAIL_HL_ARM_VECTOR_FPBITS_MOVE_CLAIM operation width part definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 2 definition in
  let target = if operation = "FMOV_FtoI" then
    "arm_FMOV_FtoI (" ^ (if width = 32 then "WREG' d" else "XREG' d") ^
    ") (QREG' n) " ^ string_of_int part ^ " " ^ string_of_int width
    else "arm_FMOV_ItoF (QREG' d) (XREG' n) " ^ string_of_int part in
  let statement = parse_term(
    configuration ^ "!d n:5 word. !s t:armstate. " ^
    source ^ " d n s t <=> " ^
    target ^ " s t") in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN SAIL_HL_ARM_VECTOR_FPBITS_NORM definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%d_%s_EQ" operation width
    (if part = 0 then "LO" else "HI") in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_FPBITS_MOVE_CLAIMS = map
  (fun (operation,width,part,definition) ->
    SAIL_HL_ARM_VECTOR_FPBITS_MOVE_CLAIM operation width part definition) [
  "FMOV_FtoI",32,0,sail_hl_arm_5fFMOV_5fFtoI32_5fLO;
  "FMOV_FtoI",64,0,sail_hl_arm_5fFMOV_5fFtoI64_5fLO;
  "FMOV_FtoI",64,1,sail_hl_arm_5fFMOV_5fFtoI64_5fHI;
  "FMOV_ItoF",64,0,sail_hl_arm_5fFMOV_5fItoF64_5fLO;
  "FMOV_ItoF",64,1,sail_hl_arm_5fFMOV_5fItoF64_5fHI;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_FPBITS_PROOFS_OK";;
