(* Complete decoded immediate ranges, including the full lane width.
   Source RShr supplies the signed floor division and rounding offset;
   USRA additionally preserves the original old-destination read. Every
   vector register/value/overlap is universally quantified. No unsupported
   D64E64/scalar alias, decoder or access-fault refinement is claimed. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-right-shift.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_UNSIGNED = prove
 (`!(x:N word) n.
   word_ushr x n = iword (&(val x) div &(2 EXP n))`,
  REWRITE_TAC[word_ushr; WORD_IWORD; INT_OF_NUM_DIV]);;

let SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_SIGNED = prove
 (`!(x:N word) n.
   word_ishr x n = iword (ival x div &(2 EXP n))`,
  REWRITE_TAC[word_ishr; INT_OF_NUM_POW]);;

let SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_HALF_POWER = prove
 (`!n:num. (&2 pow (n + 1)) div &2 = &(2 EXP n)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_DIV; EXP_ADD; EXP_1] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_ROUNDED = prove
 (`!(x:N word) n.
   word_ishr_round x (n + 1) =
   iword ((ival x + &(2 EXP n)) div &(2 EXP (n + 1)))`,
  REWRITE_TAC[word_ishr_round;
    SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_HALF_POWER; INT_OF_NUM_POW]);;

let SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_VALUE_TAC =
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

let SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_USHR_VEC; arm_SSHR_VEC;
    arm_SRSHR_VEC; arm_USRA_VEC; assign; LET_DEF; LET_END_DEF;
    FST; SND; QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    INT_OF_NUM_ADD; INT_ADD_SUB;
    SAIL_HL_ARM_PREDECESSOR; NUM_OF_INT_OF_NUM;
    INT_GE; INT_OF_NUM_LE; LE_0; INT_MUL_LID;
    simd16; simd8; simd4; simd2; usimd16; usimd8; usimd4; usimd2;
    SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_UNSIGNED;
    SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_SIGNED;
    SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_ROUNDED] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* Only theorem statements are constructed, never source model effects. *)
let SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_CLAIM
    instruction width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let amount_width = if element_width = 8 then 3
                     else if element_width = 16 then 4
                     else if element_width = 32 then 5 else 6 in
  let statement = parse_term
    ("!amount:" ^ string_of_int amount_width ^ " word. !d n:5 word. " ^
     "!s t:armstate. " ^ source ^ " amount d n s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n) (val amount + 1) " ^
     string_of_int element_width ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ"
    instruction width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_CLAIMS = map
  (fun (instruction, width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_RIGHT_SHIFT_CLAIM
      instruction width element_width definition) [
  "USHR_VEC",64,8,sail_hl_arm_5fUSHR_5fVEC64E8;
  "USHR_VEC",64,16,sail_hl_arm_5fUSHR_5fVEC64E16;
  "USHR_VEC",64,32,sail_hl_arm_5fUSHR_5fVEC64E32;
  "USHR_VEC",128,8,sail_hl_arm_5fUSHR_5fVEC128E8;
  "USHR_VEC",128,16,sail_hl_arm_5fUSHR_5fVEC128E16;
  "USHR_VEC",128,32,sail_hl_arm_5fUSHR_5fVEC128E32;
  "USHR_VEC",128,64,sail_hl_arm_5fUSHR_5fVEC128E64;
  "SSHR_VEC",64,8,sail_hl_arm_5fSSHR_5fVEC64E8;
  "SSHR_VEC",64,16,sail_hl_arm_5fSSHR_5fVEC64E16;
  "SSHR_VEC",64,32,sail_hl_arm_5fSSHR_5fVEC64E32;
  "SSHR_VEC",128,8,sail_hl_arm_5fSSHR_5fVEC128E8;
  "SSHR_VEC",128,16,sail_hl_arm_5fSSHR_5fVEC128E16;
  "SSHR_VEC",128,32,sail_hl_arm_5fSSHR_5fVEC128E32;
  "SSHR_VEC",128,64,sail_hl_arm_5fSSHR_5fVEC128E64;
  "SRSHR_VEC",64,8,sail_hl_arm_5fSRSHR_5fVEC64E8;
  "SRSHR_VEC",64,16,sail_hl_arm_5fSRSHR_5fVEC64E16;
  "SRSHR_VEC",64,32,sail_hl_arm_5fSRSHR_5fVEC64E32;
  "SRSHR_VEC",128,8,sail_hl_arm_5fSRSHR_5fVEC128E8;
  "SRSHR_VEC",128,16,sail_hl_arm_5fSRSHR_5fVEC128E16;
  "SRSHR_VEC",128,32,sail_hl_arm_5fSRSHR_5fVEC128E32;
  "SRSHR_VEC",128,64,sail_hl_arm_5fSRSHR_5fVEC128E64;
  "USRA_VEC",64,8,sail_hl_arm_5fUSRA_5fVEC64E8;
  "USRA_VEC",64,16,sail_hl_arm_5fUSRA_5fVEC64E16;
  "USRA_VEC",64,32,sail_hl_arm_5fUSRA_5fVEC64E32;
  "USRA_VEC",128,8,sail_hl_arm_5fUSRA_5fVEC128E8;
  "USRA_VEC",128,16,sail_hl_arm_5fUSRA_5fVEC128E16;
  "USRA_VEC",128,32,sail_hl_arm_5fUSRA_5fVEC128E32;
  "USRA_VEC",128,64,sail_hl_arm_5fUSRA_5fVEC128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_RIGHT_SHIFT_PROOFS_OK";;
