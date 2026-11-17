(* Five decoded UMAXV input profiles and the source's scalar vector write.
   No E64 or D64E32 forms, aliases, decoder/access-fault refinement, or
   replacement reduction/zero-top effect template are claimed. Every
   vector register and overlap remain included in the state graphs. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-max-reduce.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_MAX_REDUCE_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_UMAXV_ALT; assign; LET_DEF; LET_END_DEF;
    FST; SND; NUM_OF_INT_OF_NUM; QREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    SAIL_HL_ARM_CONDITIONAL_PAIR; SAIL_HL_ARM_IWORD_IF;
    GSYM INT_MAX; INT_OF_NUM_MAX; GSYM WORD_IWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM INT_MAX; INT_OF_NUM_MAX; GSYM WORD_IWORD;
    WORD_ZX_WORD; VAL_WORD_SUBWORD;
    ARITH_RULE `MAX (MAX x y) z = MAX x (MAX y z)`; EQ_SYM_EQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ;
    ARITH_RULE `MAX x y < n <=> x < n /\ y < n`] THEN
  PRINT_GOAL_TAC;;

(* These statements quantify state/register fields, not lane data samples. *)
let SAIL_HL_ARM_VECTOR_MAX_REDUCE_CLAIM width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term
    ("!d n:5 word. !s t:armstate. " ^ source ^
     " d n s t <=> arm_UMAXV (QREG' d) (QREG' n) " ^
     string_of_int (width / element_width) ^ " " ^
     string_of_int element_width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_MAX_REDUCE_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_UMAXV%dE%d_EQ" width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_MAX_REDUCE_CLAIMS = map
  (fun (width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_MAX_REDUCE_CLAIM width element_width definition) [
  64,8,sail_hl_arm_5fUMAXV64E8;
  64,16,sail_hl_arm_5fUMAXV64E16;
  128,8,sail_hl_arm_5fUMAXV128E8;
  128,16,sail_hl_arm_5fUMAXV128E16;
  128,32,sail_hl_arm_5fUMAXV128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_MAX_REDUCE_PROOFS_OK";;
