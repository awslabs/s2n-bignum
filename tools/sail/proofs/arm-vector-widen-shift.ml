(* All twelve decoded profiles quantify the complete immediate domain,
   including zero, and every vector register/value/overlap. The source
   helper retains low D64 versus high Q128 reads and original guards.
   SHLL has no decoder mapping here; decoding and access-fault refinement
   are not claimed. No replacement effects or shift truth table is used. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-widen-shift.ml";;

let SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_ZX = prove
 (`!(x:M word) n.
   word_shl (word_zx x:N word) n = iword (&(val x) * &(2 EXP n))`,
  REWRITE_TAC[word_zx; WORD_SHL_WORD] THEN
  REWRITE_TAC[WORD_IWORD; INT_OF_NUM_MUL; MULT_SYM]);;

let SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_SX = prove
 (`!(x:M word) n.
   word_shl (word_sx x:N word) n = iword (ival x * &(2 EXP n))`,
  REWRITE_TAC[word_sx; WORD_SHL_IWORD; INT_OF_NUM_POW; INT_MUL_SYM]);;

let SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_VALUE_TAC =
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
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_USHLL_VEC; arm_USHLL2_VEC;
    arm_SSHLL_VEC; arm_SSHLL2_VEC; assign; LET_DEF; LET_END_DEF;
    FST; SND; QREG'; DREG; READ_ZEROTOP_64; NUM_OF_INT_OF_NUM;
    INT_GE; INT_OF_NUM_LE; LE_0; usimd8; usimd4; usimd2;
    SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_ZX;
    SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_SX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* Construct proof statements only; generated definitions supply models. *)
let SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_CLAIM instruction element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let amount_width = if element_width = 8 then 3
                     else if element_width = 16 then 4 else 5 in
  let statement = parse_term
    ("!amount:" ^ string_of_int amount_width ^ " word. !d n:5 word. " ^
     "!s t:armstate. " ^ source ^ " amount d n s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n) (val amount) " ^
     string_of_int element_width ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s128E%d_EQ"
    instruction element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_CLAIMS = map
  (fun (instruction, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_WIDEN_SHIFT_CLAIM instruction element_width definition) [
  "USHLL_VEC",8,sail_hl_arm_5fUSHLL_5fVEC128E8;
  "USHLL_VEC",16,sail_hl_arm_5fUSHLL_5fVEC128E16;
  "USHLL_VEC",32,sail_hl_arm_5fUSHLL_5fVEC128E32;
  "USHLL2_VEC",8,sail_hl_arm_5fUSHLL2_5fVEC128E8;
  "USHLL2_VEC",16,sail_hl_arm_5fUSHLL2_5fVEC128E16;
  "USHLL2_VEC",32,sail_hl_arm_5fUSHLL2_5fVEC128E32;
  "SSHLL_VEC",8,sail_hl_arm_5fSSHLL_5fVEC128E8;
  "SSHLL_VEC",16,sail_hl_arm_5fSSHLL_5fVEC128E16;
  "SSHLL_VEC",32,sail_hl_arm_5fSSHLL_5fVEC128E32;
  "SSHLL2_VEC",8,sail_hl_arm_5fSSHLL2_5fVEC128E8;
  "SSHLL2_VEC",16,sail_hl_arm_5fSSHLL2_5fVEC128E16;
  "SSHLL2_VEC",32,sail_hl_arm_5fSSHLL2_5fVEC128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_WIDEN_SHIFT_PROOFS_OK";;
