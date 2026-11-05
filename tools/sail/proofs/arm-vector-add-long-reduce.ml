(* Exact five decoded unsigned widening sum reductions. Every vector
   register, input value and overlap remains included. The actual scalar
   result width is twice esize, with zero-top Q128 effect, and the native
   proof establishes that the sum fits that width. No decoder/access-fault
   refinement, signed reduction or reserved geometry is claimed. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-add-long-reduce.ml";;

(* Pure arithmetic: remove only moduli whose dividend is proved smaller.
   Numeric bounds on remainder atoms follow from the standard MOD theorem.
   The expression is taken from the proof goal, not an instruction template. *)
let SAIL_HL_ARM_VECTOR_ADD_LONG_REDUCE_BOUNDS_TAC =
  W(fun (_, goal) ->
    let modulo = `MOD` and addition = `(+):num->num->num` in
    let rec bound term =
      if is_binop addition term then
        let left, right = dest_binop addition term in
        CONV_RULE NUM_REDUCE_CONV
          (MATCH_MP LT_ADD2 (CONJ (bound left) (bound right)))
      else
        let _, divisor = dest_binop modulo term in
        prove(mk_comb(mk_comb(`(<):num->num->bool`,term),divisor),
          REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV) in
    let wide = filter (fun term ->
      is_binop addition (fst(dest_binop modulo term)))
      (find_terms (is_binop modulo) goal) in
    let equations = map (fun term ->
      let dividend = fst(dest_binop modulo term) in
      let theorem = bound dividend in
      prove(mk_eq(term,dividend),
        MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN
        EXISTS_TAC(rand(concl theorem)) THEN CONJ_TAC THENL
          [ACCEPT_TAC theorem; CONV_TAC NUM_REDUCE_CONV])) wide in
    REWRITE_TAC equations);;

let SAIL_HL_ARM_VECTOR_ADD_LONG_REDUCE_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_UADDLV_ALT; assign; LET_DEF; LET_END_DEF;
    FST; SND; NUM_OF_INT_OF_NUM; QREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    INT_OF_NUM_ADD; GSYM WORD_IWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD;
    WORD_ZX_WORD; VAL_WORD_SUBWORD; ADD_ASSOC; EQ_SYM_EQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SAIL_HL_ARM_VECTOR_ADD_LONG_REDUCE_BOUNDS_TAC THEN
  REWRITE_TAC[word_subword; GSYM WORD_ADD; ADD_ASSOC; EQ_SYM_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_VECTOR_ADD_LONG_REDUCE_CLAIM width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term
    ("!d n:5 word. !s t:armstate. " ^ source ^
     " d n s t <=> arm_UADDLV (QREG' d) (QREG' n) " ^
     string_of_int (width / element_width) ^ " " ^
     string_of_int element_width ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_VECTOR_ADD_LONG_REDUCE_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_UADDLV%dE%d_EQ" width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_ADD_LONG_REDUCE_CLAIMS = map
  (fun (width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_ADD_LONG_REDUCE_CLAIM width element_width definition) [
  64,8,sail_hl_arm_5fUADDLV64E8;
  64,16,sail_hl_arm_5fUADDLV64E16;
  128,8,sail_hl_arm_5fUADDLV128E8;
  128,16,sail_hl_arm_5fUADDLV128E16;
  128,32,sail_hl_arm_5fUADDLV128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_ADD_LONG_REDUCE_PROOFS_OK";;
