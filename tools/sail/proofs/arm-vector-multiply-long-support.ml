(* Product values are retained as words; only the lane packing is compared
   bitwise. No multiplication truth table or replacement Sail model is used. *)
let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_POSITION = prove
 (`!n k:num. num_of_int (&n * &k) = n * k`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [INT_OF_NUM_MUL] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM]);;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_HIGH_POSITION = prove
 (`!n k w:num. num_of_int ((&n + &k) * &w) = (n + k) * w`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [INT_OF_NUM_ADD] THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_POSITION]);;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_MFIELD = prove
 (`!m:4 word. val(word_zx m:5 word) = val m`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC);;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW16 = prove
 (`!x:128 word. !idx:2 word.
   word_subword (word_zx x:64 word) (16 * val idx,16):16 word =
   word_subword x (16 * val idx,16)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_ZX THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  MP_TAC(ISPEC `idx:2 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW32 = prove
 (`!x:128 word. !idx:1 word.
   word_subword (word_zx x:64 word) (32 * val idx,32):32 word =
   word_subword x (32 * val idx,32)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_ZX THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  MP_TAC(ISPEC `idx:1 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_VALUE_TAC =
  W(fun (_,goal) ->
    let is_write term =
      let head, arguments = strip_comb term in
      is_const head && fst(dest_const head) = "write" &&
      length arguments = 3 in
    let _, source = strip_comb(find_term is_write(lhand goal)) in
    let _, target = strip_comb(find_term is_write(rand goal)) in
    SUBGOAL_THEN (mk_eq(el 1 source,el 1 target))
      (fun theorem -> REWRITE_TAC[theorem; EQ_SYM_EQ]) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
      BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_0] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[] THEN PRINT_GOAL_TAC);;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_SMULL_VEC_ALT; arm_SMULL2_VEC_ALT;
    arm_UMULL_VEC_ALT; arm_UMULL2_VEC_ALT; assign; LET_DEF; LET_END_DEF;
    FST; SND; QREG'; DREG; READ_ZEROTOP_64; NUM_OF_INT_OF_NUM;
    IWORD_INT_MUL; GSYM WORD_IWORD; GSYM word_sx; GSYM word_zx;
    QLANE; LANE_H; LANE_S; READ_COMPONENT_COMPOSE; through; read] THEN
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
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_HIGH_POSITION;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_POSITION;
    ADD_CLAUSES; ARITH_RULE `(n:num) * 16 = 16 * n`;
    ARITH_RULE `(n:num) * 32 = 32 * n`;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_MFIELD;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW16;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW32] THEN
  SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_VALUE_TAC;;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_CLAIM instruction element definition =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term(
    "!d n m:5 word. !s t:armstate. " ^ source ^ " d n m s t <=> arm_" ^
    instruction ^ " (QREG' d) (QREG' n) (QREG' m) " ^
    string_of_int element ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s128E%d_EQ" instruction element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_INDEXED_CLAIM instruction element high definition =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let register_width = if element = 16 then 4 else 5 in
  let index_width = if element = 16 then 2 else 1 in
  let offset = if high then 64 / element else 0 in
  let operand =
    if element = 16 then "(word_zx m:5 word)" else "m" in
  let statement = parse_term(
    "!d n:5 word. !m:" ^ string_of_int register_width ^ " word. !idx:" ^
    string_of_int index_width ^ " word. !s t:armstate. " ^ source ^
    " d n m idx s t <=> arm_" ^ instruction ^ " (QREG' d) (QREG' n) " ^
    "(QLANE " ^ operand ^ " " ^ string_of_int element ^ " (val idx + " ^
    string_of_int offset ^ ")) " ^ string_of_int element ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s128E%d_%s_EQ"
    instruction element (if high then "HI" else "LO") in
  sail_hl_report (name, theorem);
  name,theorem;;
