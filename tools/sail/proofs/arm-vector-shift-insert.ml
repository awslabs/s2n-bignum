(* All decoded immediate amounts and vector register fields/overlaps.
   Mask lemmas below are word algebra, not source instruction templates.
   Actual Ones/LSL/LSR and both preserved-destination execute bodies are
   exported through Sail. This proves execute agreement under the enabled
   access contract, not decoding or access-fault refinement. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-shift-insert.ml";;

let SAIL_HL_ARM_VECTOR_SHIFT_INSERT_LEFT_MASK = prove
 (`!n:num. word_not(word_shl (word_not(word 0):N word) n) =
           word(2 EXP n - 1)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_NOT; BIT_WORD_SHL;
    BIT_WORD_0; BIT_MASK_WORD] THEN ARITH_TAC);;

let SAIL_HL_ARM_VECTOR_SHIFT_INSERT_RIGHT_MASK = prove
 (`!n:num. word_ushr (word_not(word 0):N word) n =
           word(2 EXP (dimindex(:N) - n) - 1)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_NOT;
    BIT_WORD_0; BIT_MASK_WORD] THEN ARITH_TAC);;

let SAIL_HL_ARM_VECTOR_SHIFT_INSERT_ONES = map
 (fun statement -> prove(statement, CONV_TAC WORD_REDUCE_CONV))
 [`word 255:8 word = word_not(word 0)`;
  `word 65535:16 word = word_not(word 0)`;
  `word 4294967295:32 word = word_not(word 0)`;
  `word 18446744073709551615:64 word = word_not(word 0)`];;

let SAIL_HL_ARM_VECTOR_SHIFT_INSERT_VALUE_TAC =
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
      BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_0;
      BIT_WORD_OR; BIT_WORD_AND] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONV_TAC TAUT);;

let SAIL_HL_ARM_VECTOR_SHIFT_INSERT_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_SLI_VEC; arm_SRI_VEC;
    assign; LET_DEF; LET_END_DEF; FST; SND;
    QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    INT_OF_NUM_ADD; NUM_OF_INT_OF_NUM;
    simd16; simd8; simd4; simd2] THEN
  REWRITE_TAC SAIL_HL_ARM_VECTOR_SHIFT_INSERT_ONES THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_SHIFT_INSERT_LEFT_MASK;
    SAIL_HL_ARM_VECTOR_SHIFT_INSERT_RIGHT_MASK] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_SHIFT_INSERT_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* Only theorem statements are constructed, never source model effects. *)
let SAIL_HL_ARM_VECTOR_SHIFT_INSERT_CLAIM
    instruction width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let amount_width = if element_width = 8 then 3
                     else if element_width = 16 then 4
                     else if element_width = 32 then 5 else 6 in
  let amount = if instruction = "SLI_VEC" then "(val amount)"
               else "(val amount + 1)" in
  let sizes = if instruction = "SLI_VEC"
              then string_of_int width ^ " " ^ string_of_int element_width
              else string_of_int element_width ^ " " ^ string_of_int width in
  let statement = parse_term
    ("!amount:" ^ string_of_int amount_width ^ " word. !d n:5 word. " ^
     "!s t:armstate. " ^ source ^ " amount d n s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n) " ^ amount ^ " " ^ sizes ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_VECTOR_SHIFT_INSERT_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ"
    instruction width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_SHIFT_INSERT_CLAIMS = map
  (fun (instruction, width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_SHIFT_INSERT_CLAIM
      instruction width element_width definition) [
  "SLI_VEC",64,8,sail_hl_arm_5fSLI_5fVEC64E8;
  "SLI_VEC",64,16,sail_hl_arm_5fSLI_5fVEC64E16;
  "SLI_VEC",64,32,sail_hl_arm_5fSLI_5fVEC64E32;
  "SLI_VEC",128,8,sail_hl_arm_5fSLI_5fVEC128E8;
  "SLI_VEC",128,16,sail_hl_arm_5fSLI_5fVEC128E16;
  "SLI_VEC",128,32,sail_hl_arm_5fSLI_5fVEC128E32;
  "SLI_VEC",128,64,sail_hl_arm_5fSLI_5fVEC128E64;
  "SRI_VEC",64,8,sail_hl_arm_5fSRI_5fVEC64E8;
  "SRI_VEC",64,16,sail_hl_arm_5fSRI_5fVEC64E16;
  "SRI_VEC",64,32,sail_hl_arm_5fSRI_5fVEC64E32;
  "SRI_VEC",128,8,sail_hl_arm_5fSRI_5fVEC128E8;
  "SRI_VEC",128,16,sail_hl_arm_5fSRI_5fVEC128E16;
  "SRI_VEC",128,32,sail_hl_arm_5fSRI_5fVEC128E32;
  "SRI_VEC",128,64,sail_hl_arm_5fSRI_5fVEC128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_SHIFT_INSERT_PROOFS_OK";;
