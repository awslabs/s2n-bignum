(* All six decoder-supported lane profiles of XTN/XTN2.
   "64" is the narrow result width. Both instructions read Q128; XTN clears
   its upper half, while XTN2 preserves the old low half through the actual
   Sail Vpart_set helper. No preserve-low primitive/template is introduced.
   Graphs include vector31 and arbitrary overlap; enabled AdvSIMD access
   remains the explicit external projection contract, not full refinement. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-narrow.ml";;

let SAIL_HL_ARM_VECTOR_NARROW_VALUE_TAC =
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

let SAIL_HL_ARM_VECTOR_NARROW_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_XTN; arm_XTN2; assign;
    LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM; QREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64; usimd8; usimd4; usimd2] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_NARROW_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* A table of proof statements only; the actual exports remain unchanged. *)
let SAIL_HL_ARM_VECTOR_NARROW_CLAIM instruction element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term
    ("!d n:5 word. !s t:armstate. " ^ source ^ " d n s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n) " ^
     string_of_int element_width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_NARROW_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s64E%d_EQ"
    instruction element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_NARROW_CLAIMS = map
  (fun (instruction, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_NARROW_CLAIM instruction element_width definition) [
  "XTN",8,sail_hl_arm_5fXTN64E8;
  "XTN",16,sail_hl_arm_5fXTN64E16;
  "XTN",32,sail_hl_arm_5fXTN64E32;
  "XTN2",8,sail_hl_arm_5fXTN264E8;
  "XTN2",16,sail_hl_arm_5fXTN264E16;
  "XTN2",32,sail_hl_arm_5fXTN264E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_NARROW_PROOFS_OK";;
