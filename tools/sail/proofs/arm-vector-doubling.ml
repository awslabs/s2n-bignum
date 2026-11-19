(* Twenty-four decoded doubled-product high-half forms: vector and indexed,
   rounded/unrounded, D64/Q128, lane16/32, every legal source element.
   The exporter explicitly excludes FPSR writes, while retaining saturation
   calculations, reads and all other effects. Any retained reg_FPSR read
   component is universally quantified, not replaced by rvalue in this proof.
   Agreement concerns represented armstate, not physical FPSR preservation
   or subsequent FPSR-reading instructions. All legal operand, lane and
   register-overlap domains remain universally quantified. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-doubling.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-multiply-long-support.ml";;

let SAIL_HL_ARM_VECTOR_DOUBLING_SATURATION = prove
 (`!value:int.
   iword_saturate value:N word =
   if &2 pow (dimindex(:N) - 1) - &1 < value
   then iword (&2 pow (dimindex(:N) - 1) - &1)
   else if value < --(&2 pow (dimindex(:N) - 1))
   then iword (--(&2 pow (dimindex(:N) - 1)))
   else iword value`,
  GEN_TAC THEN
  REWRITE_TAC[iword_saturate; IVAL_WORD_INT_MIN; IVAL_WORD_INT_MAX;
    word_INT_MIN; word_INT_MAX] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `dimindex(:N) - 1` INT_LT_POW2) THEN ASM_INT_ARITH_TAC);;

let SAIL_HL_ARM_VECTOR_DOUBLING_TAC definition =
  REPEAT GEN_TAC THEN
  (* Joined source branches keep their integer conditional inside iword.
     Match that form before literal reduction spells the signed minimum
     as its unsigned word value and obscures the conditional identity. *)
  REWRITE_TAC[definition; arm_SQDMULH_VEC; arm_SQRDMULH_VEC;
    word_2smulh; word_2smulh_round; SAIL_HL_ARM_VECTOR_DOUBLING_SATURATION;
    assign; LET_DEF; LET_END_DEF; FST; SND; QREG'; DREG;
    COND_ID;
    SAIL_HL_ARM_CONDITIONAL_PAIR;
    SAIL_HL_ARM_CONDITIONAL_INSERT;
    SAIL_HL_ARM_IWORD_IF;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64; NUM_OF_INT_OF_NUM; INT_GT;
    QLANE; LANE_H; LANE_S; READ_COMPONENT_COMPOSE; through; read;
    simd16; simd8; simd4; simd2; INT_OF_NUM_POW] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
    ADD_CLAUSES; ARITH_RULE `(n:num) * 16 = 16 * n`;
    ARITH_RULE `(n:num) * 32 = 32 * n`;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_MFIELD;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW16;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW32] THEN
  SIMP_TAC[WORD_SUBWORD_SUBWORD; WORD_SUBWORD_ZX;
    DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_HIGH_POSITION;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_POSITION; WORD_ZX_TRIVIAL;
    ADD_CLAUSES; ARITH_RULE `(n:num) * 16 = 16 * n`;
    ARITH_RULE `(n:num) * 32 = 32 * n`;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_MFIELD;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW16;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW32; INT_MUL_ASSOC;
    SAIL_HL_ARM_IWORD_IF] THEN
  SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_VALUE_TAC;;

let SAIL_HL_ARM_VECTOR_DOUBLING_CLAIM operation width element definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let statement = parse_term(
    configuration ^ "!d n m:5 word. !s t:armstate. " ^
    source ^ " d n m s t <=> arm_" ^
    operation ^ " (QREG' d) (QREG' n) (QREG' m) " ^
    string_of_int element ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_DOUBLING_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ" operation width element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_DOUBLING_INDEXED_CLAIM
    operation width element high definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 4 definition in
  let register_width = if element = 16 then 4 else 5 in
  let index_width = if element = 16 then 2 else 1 in
  let operand = if element = 16 then "(word_zx m:5 word)" else "m" in
  let statement = parse_term(
    configuration ^ "!d n:5 word. !m:" ^
    string_of_int register_width ^ " word. !idx:" ^
    string_of_int index_width ^ " word. !s t:armstate. " ^ source ^
    " d n m idx s t <=> arm_" ^ operation ^ " (QREG' d) (QREG' n) " ^
    "(QLANE " ^ operand ^ " " ^ string_of_int element ^ " (val idx + " ^
    string_of_int (if high then 64 / element else 0) ^ ")) " ^
    string_of_int element ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_DOUBLING_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_%s_EQ"
    operation width element (if high then "HI" else "LO") in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_DOUBLING_CLAIMS = map
  (fun (operation,width,element,definition) ->
    SAIL_HL_ARM_VECTOR_DOUBLING_CLAIM operation width element definition) [
  "SQDMULH_VEC",64,16,sail_hl_arm_5fSQDMULH_5fVEC64E16;
  "SQDMULH_VEC",64,32,sail_hl_arm_5fSQDMULH_5fVEC64E32;
  "SQDMULH_VEC",128,16,sail_hl_arm_5fSQDMULH_5fVEC128E16;
  "SQDMULH_VEC",128,32,sail_hl_arm_5fSQDMULH_5fVEC128E32;
  "SQRDMULH_VEC",64,16,sail_hl_arm_5fSQRDMULH_5fVEC64E16;
  "SQRDMULH_VEC",64,32,sail_hl_arm_5fSQRDMULH_5fVEC64E32;
  "SQRDMULH_VEC",128,16,sail_hl_arm_5fSQRDMULH_5fVEC128E16;
  "SQRDMULH_VEC",128,32,sail_hl_arm_5fSQRDMULH_5fVEC128E32;
];;
let SAIL_HL_ARM_VECTOR_DOUBLING_INDEXED_CLAIMS = map
  (fun (operation,width,element,high,definition) ->
    SAIL_HL_ARM_VECTOR_DOUBLING_INDEXED_CLAIM
      operation width element high definition) [
  "SQDMULH_VEC",64,16,false,sail_hl_arm_5fSQDMULH_5fVEC64E16_5fLO;
  "SQDMULH_VEC",64,16,true,sail_hl_arm_5fSQDMULH_5fVEC64E16_5fHI;
  "SQDMULH_VEC",64,32,false,sail_hl_arm_5fSQDMULH_5fVEC64E32_5fLO;
  "SQDMULH_VEC",64,32,true,sail_hl_arm_5fSQDMULH_5fVEC64E32_5fHI;
  "SQDMULH_VEC",128,16,false,sail_hl_arm_5fSQDMULH_5fVEC128E16_5fLO;
  "SQDMULH_VEC",128,16,true,sail_hl_arm_5fSQDMULH_5fVEC128E16_5fHI;
  "SQDMULH_VEC",128,32,false,sail_hl_arm_5fSQDMULH_5fVEC128E32_5fLO;
  "SQDMULH_VEC",128,32,true,sail_hl_arm_5fSQDMULH_5fVEC128E32_5fHI;
  "SQRDMULH_VEC",64,16,false,sail_hl_arm_5fSQRDMULH_5fVEC64E16_5fLO;
  "SQRDMULH_VEC",64,16,true,sail_hl_arm_5fSQRDMULH_5fVEC64E16_5fHI;
  "SQRDMULH_VEC",64,32,false,sail_hl_arm_5fSQRDMULH_5fVEC64E32_5fLO;
  "SQRDMULH_VEC",64,32,true,sail_hl_arm_5fSQRDMULH_5fVEC64E32_5fHI;
  "SQRDMULH_VEC",128,16,false,sail_hl_arm_5fSQRDMULH_5fVEC128E16_5fLO;
  "SQRDMULH_VEC",128,16,true,sail_hl_arm_5fSQRDMULH_5fVEC128E16_5fHI;
  "SQRDMULH_VEC",128,32,false,sail_hl_arm_5fSQRDMULH_5fVEC128E32_5fLO;
  "SQRDMULH_VEC",128,32,true,sail_hl_arm_5fSQRDMULH_5fVEC128E32_5fHI;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_DOUBLING_PROOFS_OK";;
