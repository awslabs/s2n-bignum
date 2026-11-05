(* Proof support shared by the exact UZP/ZIP/TRN execution profiles.
   It expands the existing HOL definitions and compares written word bits.
   No exported instruction body is replaced, and no decoder is proved. *)
let SAIL_HL_ARM_VECTOR_PERMUTE_VALUE_TAC =
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
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_PERMUTE_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_UZP1; arm_UZP2; arm_ZIP1; arm_ZIP2;
    arm_TRN1; arm_TRN2; assign; LET_DEF; LET_END_DEF; FST; SND;
    NUM_OF_INT_OF_NUM; QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    usimd16; usimd8; usimd4; usimd2;
    simd8; simd4; simd2; word_interleave2; word_interleave4;
    word_interleave8; word_interleave16; word_interleave_lo;
    word_interleave_hi; word_split_lohi; word_split_lo; word_split_hi] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_PERMUTE_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* This table helper constructs proof statements only. Each source constant
   is the backend's unchanged export of an actual upstream instruction body.
   Every field is symbolic, including register 31 and all overlap cases.
   V64 writes clear the upper 64 bits of Q; V128 writes all 128 bits. *)
let SAIL_HL_ARM_VECTOR_PERMUTE_CLAIM instruction width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let width_argument =
    if instruction = "UZP1" || instruction = "UZP2" then ""
    else " " ^ string_of_int width in
  let statement = parse_term
    ("!d n m:5 word. !s t:armstate. " ^ source ^ " d n m s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n) (QREG' m) " ^
     string_of_int element_width ^ width_argument ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_PERMUTE_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ"
    instruction width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;
