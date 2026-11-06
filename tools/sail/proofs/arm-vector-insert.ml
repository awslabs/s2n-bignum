(* Twelve complete decoded insert profiles. Destination selectors cover
   every Q128 lane; LO/HI vector source selectors cover both actual source
   read widths. General sources use W32 for lanes8/16/32 and X64 for lane64.
   Only finite lane indices are enumerated: register fields, register values,
   complete states and every operand overlap remain universally quantified. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-insert.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-duplicate-lemmas.ml";;

(* Enumerate the complete finite word domain without sampling register data. *)
let SAIL_HL_ARM_VECTOR_INSERT_SELECTOR_TAC name width =
  let selector = mk_var(name,type_of(parse_term
    (Printf.sprintf "(word 0:%d word)" width))) in
  SPEC_TAC(selector,selector) THEN
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC;;

let SAIL_HL_ARM_VECTOR_INSERT_TAC definition =
  REWRITE_TAC[definition; arm_INS; arm_INS_GEN; assign;
    LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM;
    QREG'; XREG'; WREG'; WREG; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    READ_ZEROTOP_32; WORD_VAL; WORD_ZX_TRIVIAL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_DUPLICATE_VALUE_TAC THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_VECTOR_INSERT_CLAIM element high definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION
      (if element = 64 then 3 else 4) definition in
  let destination_width =
    if element = 8 then 4 else if element = 16 then 3
    else if element = 32 then 2 else 1 in
  let source_width = destination_width - 1 in
  let implicit = element = 64 in
  let source_quantifier = if implicit then "" else
    Printf.sprintf "!idx:%d word. " source_width in
  let arguments = if implicit then "d n dest" else "d n dest idx" in
  let source_index = if implicit then string_of_int (if high then 1 else 0)
    else Printf.sprintf "(val idx + %d)" (if high then 64 / element else 0) in
  let statement = parse_term(
    configuration ^ "!d n:5 word. !dest:" ^
    string_of_int destination_width ^ " word. " ^
    source_quantifier ^ "!s t:armstate. " ^ source ^ " " ^ arguments ^
    " s t <=> arm_INS (QREG' d) (QREG' n) (" ^
    string_of_int element ^ " * val dest) (" ^ string_of_int element ^
    " * " ^ source_index ^ ") " ^ string_of_int element ^ " " ^
    string_of_int (if high then 128 else 64) ^ " s t") in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN
    SAIL_HL_ARM_VECTOR_INSERT_SELECTOR_TAC "dest" destination_width THEN
    (if implicit then ALL_TAC else
     SAIL_HL_ARM_VECTOR_INSERT_SELECTOR_TAC "idx" source_width) THEN
    SAIL_HL_ARM_VECTOR_INSERT_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_INS128E%d_%s_EQ" element
    (if high then "HI" else "LO") in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_INSERT_GENERAL_CLAIM element definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let destination_width =
    if element = 8 then 4 else if element = 16 then 3
    else if element = 32 then 2 else 1 in
  let statement = parse_term(
    configuration ^ "!d n:5 word. !dest:" ^ string_of_int destination_width ^
    " word. !s t:armstate. " ^ source ^ " d n dest s t <=> " ^
    "arm_INS_GEN (QREG' d) (" ^ (if element = 64 then "XREG' n" else "WREG' n") ^
    ") (" ^ string_of_int element ^ " * val dest) " ^
    string_of_int element ^ " s t") in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN
    SAIL_HL_ARM_VECTOR_INSERT_SELECTOR_TAC "dest" destination_width THEN
    SAIL_HL_ARM_VECTOR_INSERT_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_INS_GEN128E%d_EQ" element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_INSERT_CLAIMS = map
  (fun (element,high,definition) ->
    SAIL_HL_ARM_VECTOR_INSERT_CLAIM element high definition) [
  8,false,sail_hl_arm_5fINS128E8_5fLO;
  8,true,sail_hl_arm_5fINS128E8_5fHI;
  16,false,sail_hl_arm_5fINS128E16_5fLO;
  16,true,sail_hl_arm_5fINS128E16_5fHI;
  32,false,sail_hl_arm_5fINS128E32_5fLO;
  32,true,sail_hl_arm_5fINS128E32_5fHI;
  64,false,sail_hl_arm_5fINS128E64_5fLO;
  64,true,sail_hl_arm_5fINS128E64_5fHI;
];;
let SAIL_HL_ARM_VECTOR_INSERT_GENERAL_CLAIMS = map
  (fun (element,definition) ->
    SAIL_HL_ARM_VECTOR_INSERT_GENERAL_CLAIM element definition) [
  8,sail_hl_arm_5fINS_5fGEN128E8;
  16,sail_hl_arm_5fINS_5fGEN128E16;
  32,sail_hl_arm_5fINS_5fGEN128E32;
  64,sail_hl_arm_5fINS_5fGEN128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_INSERT_PROOFS_OK";;
