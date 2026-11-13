(* Prove MUL_VEC, MLA_VEC and MLS_VEC agreement for 42 vector/indexed forms.
   Each claim keeps all encoded register and lane fields and initial states.
   The shared support compares products, sums and register packing under the
   generated model's register interpretation; no decoder proof is asserted. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-multiply.ml";;
needs "tools/sail/proofs/arm-vector-multiply-long-support.ml";;

(* Normalize only cast/lane packing. Products and sums are opaque words.
   D64 writes use the actual zero-top component contract; target instructions
   use QREG at both data widths, just as the existing decoder does. *)
let SAIL_HL_ARM_VECTOR_MULTIPLY_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_MUL_VEC_ALT; arm_MLA_VEC_ALT; arm_MLS_VEC_ALT;
    assign; LET_DEF; LET_END_DEF; FST; SND; QREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64; NUM_OF_INT_OF_NUM;
    IWORD_INT_MUL; GSYM WORD_IWORD; GSYM word_zx;
    QLANE; LANE_H; LANE_S; READ_COMPONENT_COMPOSE; through; read] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
    ADD_CLAUSES; ARITH_RULE `(n:num) * 16 = 16 * n`;
    ARITH_RULE `(n:num) * 32 = 32 * n`;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_MFIELD;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW16;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW32; WORD_ZX_TRIVIAL] THEN
  SIMP_TAC[WORD_SUBWORD_SUBWORD; WORD_SUBWORD_ZX;
    DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_HIGH_POSITION;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_POSITION;
    ADD_CLAUSES; ARITH_RULE `(n:num) * 16 = 16 * n`;
    ARITH_RULE `(n:num) * 32 = 32 * n`;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_MFIELD;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW16;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW32; WORD_ZX_TRIVIAL; WORD_ADD_SYM] THEN
  SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_VALUE_TAC;;

let SAIL_HL_ARM_VECTOR_MULTIPLY_CLAIM instruction width element definition =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term(
    "!d n m:5 word. !s t:armstate. " ^ source ^ " d n m s t <=> arm_" ^
    instruction ^ " (QREG' d) (QREG' n) (QREG' m) " ^
    string_of_int element ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_MULTIPLY_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ" instruction width element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_MULTIPLY_INDEXED_CLAIM
    instruction width element high definition =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let register_width = if element = 16 then 4 else 5 in
  let index_width = if element = 16 then 2 else 1 in
  let offset = if high then 64 / element else 0 in
  let operand = if element = 16 then "(word_zx m:5 word)" else "m" in
  let statement = parse_term(
    "!d n:5 word. !m:" ^ string_of_int register_width ^ " word. !idx:" ^
    string_of_int index_width ^ " word. !s t:armstate. " ^ source ^
    " d n m idx s t <=> arm_" ^ instruction ^ " (QREG' d) (QREG' n) " ^
    "(QLANE " ^ operand ^ " " ^ string_of_int element ^ " (val idx + " ^
    string_of_int offset ^ ")) " ^ string_of_int element ^ " " ^
    string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_MULTIPLY_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_%s_EQ"
    instruction width element (if high then "HI" else "LO") in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_MULTIPLY_CLAIMS = map
  (fun (instruction,width,element,definition) ->
    SAIL_HL_ARM_VECTOR_MULTIPLY_CLAIM instruction width element definition)
  [
    "MUL_VEC",64,8,sail_hl_arm_5fMUL_5fVEC64E8;
    "MUL_VEC",64,16,sail_hl_arm_5fMUL_5fVEC64E16;
    "MUL_VEC",64,32,sail_hl_arm_5fMUL_5fVEC64E32;
    "MUL_VEC",128,8,sail_hl_arm_5fMUL_5fVEC128E8;
    "MUL_VEC",128,16,sail_hl_arm_5fMUL_5fVEC128E16;
    "MUL_VEC",128,32,sail_hl_arm_5fMUL_5fVEC128E32;
    "MLA_VEC",64,8,sail_hl_arm_5fMLA_5fVEC64E8;
    "MLA_VEC",64,16,sail_hl_arm_5fMLA_5fVEC64E16;
    "MLA_VEC",64,32,sail_hl_arm_5fMLA_5fVEC64E32;
    "MLA_VEC",128,8,sail_hl_arm_5fMLA_5fVEC128E8;
    "MLA_VEC",128,16,sail_hl_arm_5fMLA_5fVEC128E16;
    "MLA_VEC",128,32,sail_hl_arm_5fMLA_5fVEC128E32;
    "MLS_VEC",64,8,sail_hl_arm_5fMLS_5fVEC64E8;
    "MLS_VEC",64,16,sail_hl_arm_5fMLS_5fVEC64E16;
    "MLS_VEC",64,32,sail_hl_arm_5fMLS_5fVEC64E32;
    "MLS_VEC",128,8,sail_hl_arm_5fMLS_5fVEC128E8;
    "MLS_VEC",128,16,sail_hl_arm_5fMLS_5fVEC128E16;
    "MLS_VEC",128,32,sail_hl_arm_5fMLS_5fVEC128E32;
  ];;

let SAIL_HL_ARM_VECTOR_MULTIPLY_INDEXED_CLAIMS = map
  (fun (instruction,width,element,high,definition) ->
    SAIL_HL_ARM_VECTOR_MULTIPLY_INDEXED_CLAIM
      instruction width element high definition)
  [
    "MUL_VEC",64,16,false,sail_hl_arm_5fMUL_5fVEC64E16_5fLO;
    "MUL_VEC",64,16,true,sail_hl_arm_5fMUL_5fVEC64E16_5fHI;
    "MUL_VEC",64,32,false,sail_hl_arm_5fMUL_5fVEC64E32_5fLO;
    "MUL_VEC",64,32,true,sail_hl_arm_5fMUL_5fVEC64E32_5fHI;
    "MUL_VEC",128,16,false,sail_hl_arm_5fMUL_5fVEC128E16_5fLO;
    "MUL_VEC",128,16,true,sail_hl_arm_5fMUL_5fVEC128E16_5fHI;
    "MUL_VEC",128,32,false,sail_hl_arm_5fMUL_5fVEC128E32_5fLO;
    "MUL_VEC",128,32,true,sail_hl_arm_5fMUL_5fVEC128E32_5fHI;
    "MLA_VEC",64,16,false,sail_hl_arm_5fMLA_5fVEC64E16_5fLO;
    "MLA_VEC",64,16,true,sail_hl_arm_5fMLA_5fVEC64E16_5fHI;
    "MLA_VEC",64,32,false,sail_hl_arm_5fMLA_5fVEC64E32_5fLO;
    "MLA_VEC",64,32,true,sail_hl_arm_5fMLA_5fVEC64E32_5fHI;
    "MLA_VEC",128,16,false,sail_hl_arm_5fMLA_5fVEC128E16_5fLO;
    "MLA_VEC",128,16,true,sail_hl_arm_5fMLA_5fVEC128E16_5fHI;
    "MLA_VEC",128,32,false,sail_hl_arm_5fMLA_5fVEC128E32_5fLO;
    "MLA_VEC",128,32,true,sail_hl_arm_5fMLA_5fVEC128E32_5fHI;
    "MLS_VEC",64,16,false,sail_hl_arm_5fMLS_5fVEC64E16_5fLO;
    "MLS_VEC",64,16,true,sail_hl_arm_5fMLS_5fVEC64E16_5fHI;
    "MLS_VEC",64,32,false,sail_hl_arm_5fMLS_5fVEC64E32_5fLO;
    "MLS_VEC",64,32,true,sail_hl_arm_5fMLS_5fVEC64E32_5fHI;
    "MLS_VEC",128,16,false,sail_hl_arm_5fMLS_5fVEC128E16_5fLO;
    "MLS_VEC",128,16,true,sail_hl_arm_5fMLS_5fVEC128E16_5fHI;
    "MLS_VEC",128,32,false,sail_hl_arm_5fMLS_5fVEC128E32_5fLO;
    "MLS_VEC",128,32,true,sail_hl_arm_5fMLS_5fVEC128E32_5fHI;
  ];;

check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_MULTIPLY_PROOFS_OK";;
