(* Exact decoder-supported min/max geometries, not reserved E64 forms.
   Signed and unsigned operand values, vector31 and every overlap remain
   universally included. Original helper evaluation and effects come from
   the unchanged generated model; no decode/access-fault refinement. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-minmax.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_MINMAX_VALUE_TAC =
  W(fun (_, goal) ->
    let is_write term =
      let head, arguments = strip_comb term in
      is_const head && fst(dest_const head) = "write" &&
      length arguments = 3 in
    let _, source = strip_comb(find_term is_write (lhand goal)) in
    let _, target = strip_comb(find_term is_write (rand goal)) in
    SUBGOAL_THEN (mk_eq(el 1 source,el 1 target))
      (fun theorem -> REWRITE_TAC[theorem; EQ_SYM_EQ]) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
      BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_OR; BIT_WORD_AND;
      BIT_WORD_SHL; BIT_WORD_0] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_MINMAX_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_SMAX_VEC; arm_UMAX_VEC; arm_UMIN_VEC;
    assign; LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM;
    QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    SAIL_HL_ARM_CONDITIONAL_PAIR;
    SAIL_HL_ARM_INSERT_IF; SAIL_HL_ARM_IWORD_IF;
    simd16; simd8; simd4; simd2;
    word_umax; word_umin; word_imax; modular; imodular;
    GSYM INT_MAX; GSYM INT_MIN; INT_OF_NUM_LE;
    INT_OF_NUM_MAX; INT_OF_NUM_MIN; GSYM WORD_IWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM INT_MAX; GSYM INT_MIN;
    SAIL_HL_ARM_INSERT_IF; SAIL_HL_ARM_IWORD_IF;
    INT_OF_NUM_MAX; INT_OF_NUM_MIN; GSYM WORD_IWORD; EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_MINMAX_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* Construct claim statements, not model definitions. *)
let SAIL_HL_ARM_VECTOR_MINMAX_CLAIM instruction width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term
    ("!d n m:5 word. !s t:armstate. " ^ source ^ " d n m s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n) (QREG' m) " ^
     string_of_int element_width ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_MINMAX_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ"
    instruction width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_MINMAX_CLAIMS = map
  (fun (instruction, width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_MINMAX_CLAIM instruction width element_width definition) [
  "SMAX_VEC",64,8,sail_hl_arm_5fSMAX_5fVEC64E8;
  "SMAX_VEC",64,16,sail_hl_arm_5fSMAX_5fVEC64E16;
  "SMAX_VEC",64,32,sail_hl_arm_5fSMAX_5fVEC64E32;
  "SMAX_VEC",128,8,sail_hl_arm_5fSMAX_5fVEC128E8;
  "SMAX_VEC",128,16,sail_hl_arm_5fSMAX_5fVEC128E16;
  "SMAX_VEC",128,32,sail_hl_arm_5fSMAX_5fVEC128E32;
  "UMAX_VEC",64,8,sail_hl_arm_5fUMAX_5fVEC64E8;
  "UMAX_VEC",64,16,sail_hl_arm_5fUMAX_5fVEC64E16;
  "UMAX_VEC",64,32,sail_hl_arm_5fUMAX_5fVEC64E32;
  "UMAX_VEC",128,8,sail_hl_arm_5fUMAX_5fVEC128E8;
  "UMAX_VEC",128,16,sail_hl_arm_5fUMAX_5fVEC128E16;
  "UMAX_VEC",128,32,sail_hl_arm_5fUMAX_5fVEC128E32;
  "UMIN_VEC",64,8,sail_hl_arm_5fUMIN_5fVEC64E8;
  "UMIN_VEC",64,16,sail_hl_arm_5fUMIN_5fVEC64E16;
  "UMIN_VEC",64,32,sail_hl_arm_5fUMIN_5fVEC64E32;
  "UMIN_VEC",128,8,sail_hl_arm_5fUMIN_5fVEC128E8;
  "UMIN_VEC",128,16,sail_hl_arm_5fUMIN_5fVEC128E16;
  "UMIN_VEC",128,32,sail_hl_arm_5fUMIN_5fVEC128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_MINMAX_PROOFS_OK";;
