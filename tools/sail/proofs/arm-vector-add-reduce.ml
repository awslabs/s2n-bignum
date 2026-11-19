(* Agreement for the five decoded ADDV geometries under the common Arm
   access interpretation and checked capability/mode facts. FPCR remains
   an arbitrary component: the selected integer ADD operation does not use
   its floating-point controls.

   The comparison follows Sail's recursive lane combination modulo
   lane width and HOL's unsigned sum modulo that width. Every encoded
   register, input value, state and operand overlap remains in the statements;
   this is not a proof of decoder or complete-platform behavior. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-add-reduce.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;

let SAIL_HL_ARM_VECTOR_ADD_REDUCE_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_ADDV_ALT; assign; LET_DEF; LET_END_DEF;
    FST; SND; NUM_OF_INT_OF_NUM; QREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64; INT_OF_NUM_ADD;
    GSYM WORD_IWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ZX_WORD; VAL_WORD_SUBWORD; WORD_ADD;
    GSYM WORD_IWORD; ADD_ASSOC; EQ_SYM_EQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC MOD_DOWN_CONV THEN
  (* Put the recursive word-add tree and the library's lane sum in the
     same arithmetic form. The final lane-width modulus remains; only
     redundant inner moduli are removed. *)
  REWRITE_TAC[word_subword; GSYM WORD_ADD; WORD_ZX_WORD;
    ADD_ASSOC; DIV_1; EQ_SYM_EQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[ADD_ASSOC; DIV_1; EQ_SYM_EQ];;

(* Construct theorem statements only: calculations remain in the export. *)
let SAIL_HL_ARM_VECTOR_ADD_REDUCE_CLAIM width element_width definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 2 definition in
  let statement = parse_term
    (configuration ^ "!d n:5 word. !s t:armstate. " ^ source ^
     " d n s t <=> arm_ADDV (QREG' d) (QREG' n) " ^
     string_of_int (width / element_width) ^ " " ^
     string_of_int element_width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_ADD_REDUCE_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_ADDV%dE%d_EQ" width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_ADD_REDUCE_CLAIMS = map
  (fun (width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_ADD_REDUCE_CLAIM width element_width definition) [
  64,8,sail_hl_arm_5fADDV64E8;
  64,16,sail_hl_arm_5fADDV64E16;
  128,8,sail_hl_arm_5fADDV128E8;
  128,16,sail_hl_arm_5fADDV128E16;
  128,32,sail_hl_arm_5fADDV128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_ADD_REDUCE_PROOFS_OK";;
