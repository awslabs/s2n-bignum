(* PMUL's byte products have no widening-PMULL feature query or FPSR update.
   Translate PolynomialMult's genuine XOR loop, then compare its bits with
   HOL's polynomial product. Every lane value, state and register overlap is
   arbitrary. PMULL/PMULL2 are proved in arm-vector-poly.ml. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-polynomial-multiply.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;

let SAIL_HL_ARM_PMUL_VALUE_TAC =
  W(fun (_,goal) ->
    let is_write term =
      let head,arguments = strip_comb term in
      is_const head && fst(dest_const head) = "write" &&
      length arguments = 3 in
    let _,source = strip_comb(find_term is_write(lhand goal)) in
    let _,target = strip_comb(find_term is_write(rand goal)) in
    SUBGOAL_THEN(mk_eq(el 1 source,el 1 target))
      (fun theorem -> SUBST1_TAC theorem THEN REWRITE_TAC[EQ_SYM_EQ]) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    (* Reduce each concrete output-bit position before entering the lane
       calculations. This avoids copying all other lanes through the
       insert/join conditions for every bit of the complete vector. *)
    CONV_TAC(TOP_DEPTH_CONV
      (BIT_WORD_CONV ORELSEC
       GEN_REWRITE_CONV I [SAIL_HL_ARM_CONDITIONAL_BIT])) THEN
    REWRITE_TAC[SAIL_HL_ARM_XOR_STEP; BIT_WORD_PMUL] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; SAIL_HL_ARM_ODD_BITVAL;
      BIT_WORD_SUBWORD; BIT_WORD_ZX;
      SAIL_HL_ARM_CONDITIONAL_BIT;
      SAIL_HL_ARM_XOR_STEP] THEN
    SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8; DIMINDEX_16; DIMINDEX_64;
      DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SAIL_HL_ARM_XOR_STEP] THEN CONV_TAC TAUT);;

let SAIL_HL_ARM_PMUL_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; SAIL_HL_ARM_CONDITIONAL_PAIR; COND_ID;
    SAIL_HL_ARM_WORD_XOR_STEP;
    arm_PMUL_VEC_ALT; assign; LET_DEF; LET_END_DEF; FST; SND;
    NUM_OF_INT_OF_NUM; QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    SAIL_HL_ARM_BIT_WORD_ONE; WORD_PMUL_ZX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_ARM_BIT_WORD_ONE; WORD_PMUL_ZX; EQ_SYM_EQ] THEN
  SAIL_HL_ARM_PMUL_VALUE_TAC;;

let SAIL_HL_ARM_PMUL_CLAIM width definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let statement = parse_term(
    configuration ^ "!d n m:5 word. !s t:armstate. " ^
    source ^ " d n m s t <=> arm_PMUL_VEC " ^
    "(QREG' d) (QREG' n) (QREG' m) " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_PMUL_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_PMUL_VEC%dE8_EQ" width in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_PMUL_CLAIMS = map
  (fun (width,definition) -> SAIL_HL_ARM_PMUL_CLAIM width definition) [
  64,sail_hl_arm_5fPMUL_5fVEC64E8;
  128,sail_hl_arm_5fPMUL_5fVEC128E8;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_POLYNOMIAL_MULTIPLY_PROOFS_OK";;
