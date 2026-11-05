(* Generic word/bit proof normalization for the two pairwise instruction
   families. Source effects and expressions remain generated definitions;
   these tactics construct/prove claims but supply no model semantics. *)
let SAIL_HL_ARM_VECTOR_PAIR_ADD_ZX_SUBWORD = prove
 (`!x:N word p n.
   word_zx(word_subword x (p,n):M word):P word =
   word ((val x DIV 2 EXP p) MOD 2 EXP MIN n (dimindex(:M)))`,
  REWRITE_TAC[word_zx; VAL_WORD_SUBWORD]);;

let SAIL_HL_ARM_VECTOR_PAIR_ADD_ZERO_SUBWORD = prove
 (`!(x:N word) n.
   n = dimindex(:M) ==> word_subword x (0,n):M word = word_zx x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ZX_SUBWORD]);;

let SAIL_HL_ARM_VECTOR_PAIR_ADD_VALUE_TAC =
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
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
      DIMINDEX_64; DIMINDEX_128; ARITH_LE] THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_PAIR_ADD_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_UADDLP; arm_UADALP; assign;
    LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM;
    QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    simd8; simd4; simd2; usimd8; usimd4; usimd2;
    INT_OF_NUM_ADD; GSYM WORD_IWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD;
    VAL_WORD; SAIL_HL_ARM_VECTOR_PAIR_ADD_ZX_SUBWORD;
    INT_OF_NUM_ADD; GSYM WORD_IWORD; EQ_SYM_EQ] THEN
  SIMP_TAC[SAIL_HL_ARM_VECTOR_PAIR_ADD_ZERO_SUBWORD;
    DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_MOD_LE; MOD_MOD_REFL; ARITH_EQ; ARITH_LE] THEN
  SAIL_HL_ARM_VECTOR_PAIR_ADD_VALUE_TAC THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_VECTOR_PAIR_ADD_CLAIM instruction width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term
    ("!d n:5 word. !s t:armstate. " ^ source ^
     " d n s t <=> arm_" ^ instruction ^ " (QREG' d) (QREG' n) " ^
     string_of_int element_width ^
     (if instruction = "UADALP" then " " ^ string_of_int width else "") ^
     " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_PAIR_ADD_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ"
    instruction width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;
