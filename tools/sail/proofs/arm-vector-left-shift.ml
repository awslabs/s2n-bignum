(* Complete SHL domain: the seven vector geometries and the scalar D64E64
   form, including shift0, vector31
   and all overlaps. Execute agreement under enabled access is separate
   from decoder or fault refinement. The model is the actual Sail body. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-left-shift.ml";;

let SAIL_HL_ARM_VECTOR_LEFT_SHIFT_VALUE_TAC =
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
      BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_0] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    (* The scalar form also compares bits 64 to 127 of a 64-bit word. *)
    SIMP_TAC[BIT_TRIVIAL; DIMINDEX_64; ARITH]);;

(* The scalar form truncates the source with word_zx where s2n-bignum
   takes its low 64 bits with word_subword. *)
let SAIL_HL_ARM_VECTOR_LEFT_SHIFT_LOW64 = prove
 (`!x:128 word. (word_zx x:64 word) = word_subword x (0,64)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_SUBWORD;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[ADD_CLAUSES; ARITH_RULE `i < 64 ==> i < 128`]);;

let SAIL_HL_ARM_VECTOR_LEFT_SHIFT_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_SHL_VEC; assign; LET_DEF; LET_END_DEF;
    SAIL_HL_ARM_VECTOR_LEFT_SHIFT_LOW64;
    FST; SND; QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    NUM_OF_INT_OF_NUM; usimd16; usimd8; usimd4; usimd2] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_LEFT_SHIFT_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* Only theorem statements are constructed, never source model effects. *)
let SAIL_HL_ARM_VECTOR_LEFT_SHIFT_CLAIM width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let amount_width = if element_width = 8 then 3
                     else if element_width = 16 then 4
                     else if element_width = 32 then 5 else 6 in
  let statement = parse_term
    ("!amount:" ^ string_of_int amount_width ^ " word. !d n:5 word. " ^
     "!s t:armstate. " ^ source ^ " amount d n s t <=> arm_SHL_VEC " ^
     "(QREG' d) (QREG' n) (val amount) " ^
     string_of_int element_width ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_LEFT_SHIFT_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_SHL_VEC%dE%d_EQ" width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_LEFT_SHIFT_CLAIMS = map
  (fun (width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_LEFT_SHIFT_CLAIM width element_width definition) [
  64,8,sail_hl_arm_5fSHL_5fVEC64E8;
  64,16,sail_hl_arm_5fSHL_5fVEC64E16;
  64,32,sail_hl_arm_5fSHL_5fVEC64E32;
  64,64,sail_hl_arm_5fSHL_5fVEC64E64;
  128,8,sail_hl_arm_5fSHL_5fVEC128E8;
  128,16,sail_hl_arm_5fSHL_5fVEC128E16;
  128,32,sail_hl_arm_5fSHL_5fVEC128E32;
  128,64,sail_hl_arm_5fSHL_5fVEC128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_LEFT_SHIFT_PROOFS_OK";;
