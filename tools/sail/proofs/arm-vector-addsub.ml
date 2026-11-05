(* Exact vector ADD/SUB execution for all fourteen supported geometries.
   D64E64 is reserved and absent. Vector register31 and every overlap are
   included. Undefined source locals become observable only after every
   result bit is initialized through actual Elem_set calls.
   Decoding and full enabled-AdvSIMD access checks are not refined. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-addsub.ml";;

let SAIL_HL_ARM_VECTOR_ADDSUB_VALUE_TAC =
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
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_ADDSUB_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_ADD_VEC; arm_SUB_VEC; assign;
    LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM; QREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64; simd16; simd8; simd4; simd2] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_ADDSUB_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* Only proof statements are constructed here, never instruction semantics. *)
let SAIL_HL_ARM_VECTOR_ADDSUB_CLAIM instruction width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term
    ("!d n m:5 word. !s t:armstate. " ^ source ^ " d n m s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n) (QREG' m) " ^
     string_of_int element_width ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_ADDSUB_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ"
    instruction width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_ADDSUB_CLAIMS = map
  (fun (instruction, width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_ADDSUB_CLAIM instruction width element_width definition) [
  "ADD_VEC",64,8,sail_hl_arm_5fADD_5fVEC64E8;
  "ADD_VEC",64,16,sail_hl_arm_5fADD_5fVEC64E16;
  "ADD_VEC",64,32,sail_hl_arm_5fADD_5fVEC64E32;
  "ADD_VEC",128,8,sail_hl_arm_5fADD_5fVEC128E8;
  "ADD_VEC",128,16,sail_hl_arm_5fADD_5fVEC128E16;
  "ADD_VEC",128,32,sail_hl_arm_5fADD_5fVEC128E32;
  "ADD_VEC",128,64,sail_hl_arm_5fADD_5fVEC128E64;
  "SUB_VEC",64,8,sail_hl_arm_5fSUB_5fVEC64E8;
  "SUB_VEC",64,16,sail_hl_arm_5fSUB_5fVEC64E16;
  "SUB_VEC",64,32,sail_hl_arm_5fSUB_5fVEC64E32;
  "SUB_VEC",128,8,sail_hl_arm_5fSUB_5fVEC128E8;
  "SUB_VEC",128,16,sail_hl_arm_5fSUB_5fVEC128E16;
  "SUB_VEC",128,32,sail_hl_arm_5fSUB_5fVEC128E32;
  "SUB_VEC",128,64,sail_hl_arm_5fSUB_5fVEC128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_ADDSUB_PROOFS_OK";;
