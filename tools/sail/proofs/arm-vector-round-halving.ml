(* Six decoded unsigned rounded halving-add geometries. Arithmetic is
   compared as a lane word before bitwise comparison of lane placement.
   The sum includes the rounding increment before division by two.
   All register fields, input values and operand overlaps are retained. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-round-halving.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-multiply-long-support.ml";;

let SAIL_HL_ARM_VECTOR_ROUND_HALVING_LANE = prove
 (`!x y:N word.
   word_urhadd x y =
   iword ((&(val x) + &(val y) + &1) div &2)`,
  REWRITE_TAC[word_urhadd; WORD_IWORD] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_DIV; INT_OF_NUM_ADD]);;

let SAIL_HL_ARM_VECTOR_ROUND_HALVING_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_URHADD_VEC; assign; LET_DEF; LET_END_DEF;
    FST; SND; QREG'; DREG; NUM_OF_INT_OF_NUM;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    SAIL_HL_ARM_VECTOR_ROUND_HALVING_LANE;
    simd16; simd8; simd4; simd2] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_DIV; GSYM WORD_IWORD;
    ADD_ASSOC] THEN
  SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_VALUE_TAC THEN
  REWRITE_TAC[ADD_ASSOC];;

let SAIL_HL_ARM_VECTOR_ROUND_HALVING_CLAIM width element definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let statement = parse_term(
    configuration ^ "!d n m:5 word. !s t:armstate. " ^
    source ^ " d n m s t <=> " ^
    "arm_URHADD_VEC (QREG' d) (QREG' n) (QREG' m) " ^
    string_of_int element ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_ROUND_HALVING_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_URHADD_VEC%dE%d_EQ" width element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_ROUND_HALVING_CLAIMS = map
  (fun (width,element,definition) ->
    SAIL_HL_ARM_VECTOR_ROUND_HALVING_CLAIM width element definition) [
  64,8,sail_hl_arm_5fURHADD_5fVEC64E8;
  64,16,sail_hl_arm_5fURHADD_5fVEC64E16;
  64,32,sail_hl_arm_5fURHADD_5fVEC64E32;
  128,8,sail_hl_arm_5fURHADD_5fVEC128E8;
  128,16,sail_hl_arm_5fURHADD_5fVEC128E16;
  128,32,sail_hl_arm_5fURHADD_5fVEC128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_ROUND_HALVING_PROOFS_OK";;
