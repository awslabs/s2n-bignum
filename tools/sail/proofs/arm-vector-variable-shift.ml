(* USHL uses the signed low byte of each amount lane, including -128.
   The pure lane lemma enumerates all256 byte amounts, never lane data.
   Full vector claims quantify every register value/state and operand overlap. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-variable-shift.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-multiply-long-support.ml";;

let SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_BYTE = prove
 (`!(x:N word) (amount:8 word).
   (if &0 <= ival amount
    then iword (&(val x) * &(2 EXP (num_of_int(ival amount))))
    else iword (&(val x) div &(2 EXP (num_of_int(--ival amount))))) =
   (if ~(bit 7 amount) then word_shl x (val amount)
    else word_ushr x (val(word_neg amount)))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`amount:8 word`,`amount:8 word`) THEN
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[word_shl; word_ushr; NUM_OF_INT_OF_NUM;
    GSYM INT_OF_NUM_MUL; INT_OF_NUM_DIV; WORD_IWORD]);;

let SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_LANE = prove
 (`!x y:N word.
   word_ushl x y =
   if &0 <= ival(word_subword y (0,8):8 word)
   then iword (&(val x) *
         &(2 EXP (num_of_int(ival(word_subword y (0,8):8 word)))))
   else iword (&(val x) div
         &(2 EXP (num_of_int(--ival(word_subword y (0,8):8 word)))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_BYTE;
    word_ushl; LET_DEF; LET_END_DEF]);;

let SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_TAC definition =
  REPEAT GEN_TAC THEN
  (* Both placements of iword around the amount-sign conditional are
     equal for every lane value and signed low-byte shift amount. *)
  REWRITE_TAC[definition; arm_USHL_VEC; assign; LET_DEF; LET_END_DEF;
    FST; SND; QREG'; DREG; NUM_OF_INT_OF_NUM;
    SAIL_HL_ARM_CONDITIONAL_PAIR;
    SAIL_HL_ARM_CONDITIONAL_INSERT;
    SAIL_HL_ARM_IWORD_IF;
    COND_ID;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64; INT_GE;
    SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_LANE;
    simd16; simd8; simd4; simd2] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[EQ_SYM_EQ; SAIL_HL_ARM_IWORD_IF] THEN
  SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_VALUE_TAC;;

let SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_CLAIM width element definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let statement = parse_term(
    configuration ^ "!d n m:5 word. !s t:armstate. " ^
    source ^ " d n m s t <=> " ^
    "arm_USHL_VEC (QREG' d) (QREG' n) (QREG' m) " ^
    string_of_int element ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_USHL_VEC%dE%d_EQ" width element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_CLAIMS = map
  (fun (width,element,definition) ->
    SAIL_HL_ARM_VECTOR_VARIABLE_SHIFT_CLAIM width element definition) [
  64,8,sail_hl_arm_5fUSHL_5fVEC64E8;
  64,16,sail_hl_arm_5fUSHL_5fVEC64E16;
  64,32,sail_hl_arm_5fUSHL_5fVEC64E32;
  128,8,sail_hl_arm_5fUSHL_5fVEC128E8;
  128,16,sail_hl_arm_5fUSHL_5fVEC128E16;
  128,32,sail_hl_arm_5fUSHL_5fVEC128E32;
  128,64,sail_hl_arm_5fUSHL_5fVEC128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_VARIABLE_SHIFT_PROOFS_OK";;
