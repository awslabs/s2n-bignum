(* Shared proof steps for DUP_ELEM and DUP_GEN instruction agreement.
   Compare lane extraction, repeated bits and register writes, including
   zero-register reads and upper-bit clearing. Instruction claims are in
   the corresponding body files; these helpers alone do not grant coverage. *)
let SAIL_HL_ARM_VECTOR_DUPLICATE_VALUE_TAC =
  W(fun (_, goal) ->
    let is_write term =
      let head, arguments = strip_comb term in
      is_const head && fst(dest_const head) = "write" &&
      length arguments = 3 in
    let _, source = strip_comb(find_term is_write (lhand goal)) in
    let _, target = strip_comb(find_term is_write (rand goal)) in
    SUBGOAL_THEN (mk_eq(el 1 source,el 1 target))
      (fun theorem -> REWRITE_TAC[theorem; EQ_SYM_EQ]) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_DUPLICATE;
      BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_OR; BIT_WORD_AND;
      BIT_WORD_SHL; BIT_WORD_0] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_DUPLICATE_NORM definition =
  REWRITE_TAC[definition; arm_DUP_ELEM; arm_DUP_GEN; assign;
    LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM;
    QREG'; XREG'; WREG; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    READ_ZEROTOP_32;
    WORD_VAL; WORD_ZX_TRIVIAL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_DUPLICATE_VALUE_TAC THEN PRINT_GOAL_TAC;;
