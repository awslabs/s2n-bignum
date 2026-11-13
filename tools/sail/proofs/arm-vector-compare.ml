(* Execution agreement for the four public vector comparison names.
   All seven geometries, signed/unsigned lane values, vector31 and overlap
   cases are included. Source signed interpretation and all-ones/zero masks
   come from actual source/helper bodies, not replacement model templates.
   Reserved D64E64 forms, unsupported public names and access-fault/decoder
   refinement are not claimed. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-compare.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

(* Pure word-mask and conditional/tuple identities for source-generated joins.
   Only the differing result is moved out of the tuple; common state and
   local values are retained. No instruction effects are supplied here. *)
(* Upstream Ones helpers print each complete lane mask as a numeral.
   Normalize those literals before recognizing a conditional word mask. *)
let SAIL_HL_ARM_VECTOR_COMPARE_ONES8 =
  SYM(WORD_REDUCE_CONV `word_not(word 0):8 word`);;
let SAIL_HL_ARM_VECTOR_COMPARE_ONES16 =
  SYM(WORD_REDUCE_CONV `word_not(word 0):16 word`);;
let SAIL_HL_ARM_VECTOR_COMPARE_ONES32 =
  SYM(WORD_REDUCE_CONV `word_not(word 0):32 word`);;
let SAIL_HL_ARM_VECTOR_COMPARE_ONES64 =
  SYM(WORD_REDUCE_CONV `word_not(word 0):64 word`);;

let SAIL_HL_ARM_VECTOR_COMPARE_JOIN5 = prove
 (`!p (s:S) (a:A) (b:B) (x:W) y (c:C).
   (if p then (s,a,b,x,c) else (s,a,b,y,c)) =
   (s,a,b,(if p then x else y),c)`,
  REWRITE_TAC[FORALL_BOOL_THM]);;

let SAIL_HL_ARM_VECTOR_COMPARE_JOIN4 = prove
 (`!p (s:S) (a:A) (x:W) y (c:C).
   (if p then (s,a,x,c) else (s,a,y,c)) =
   (s,a,(if p then x else y),c)`,
  REWRITE_TAC[FORALL_BOOL_THM]);;

let SAIL_HL_ARM_VECTOR_COMPARE_VALUE_TAC =
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
      BIT_WORD_SHL; BIT_WORD_0; BIT_WORD_MASK] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    TRY(CONV_TAC EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_COMPARE_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_CMGT_VEC; arm_CMHI_VEC; arm_CMGE_VEC;
    arm_CMLE_VEC_ZERO; assign; LET_DEF; LET_END_DEF; FST; SND;
    NUM_OF_INT_OF_NUM; QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    SAIL_HL_ARM_VECTOR_COMPARE_JOIN5; SAIL_HL_ARM_VECTOR_COMPARE_JOIN4;
    SAIL_HL_ARM_INSERT_IF;
    simd16; simd8; simd4; simd2; masking; word_ugt; word_igt; word_ile;
    relational2; irelational2; INT_GT; INT_GE; GT; GE; INT_OF_NUM_LT;
    IVAL_WORD_0;
    SAIL_HL_ARM_VECTOR_COMPARE_ONES8; SAIL_HL_ARM_VECTOR_COMPARE_ONES16;
    SAIL_HL_ARM_VECTOR_COMPARE_ONES32; SAIL_HL_ARM_VECTOR_COMPARE_ONES64;
    GSYM WORD_MASK] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_MASK; EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_COMPARE_VALUE_TAC;;

(* Construct statements only; all model constants are unchanged exports. *)
let SAIL_HL_ARM_VECTOR_COMPARE_CLAIM instruction width element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let unary = instruction = "CMLE_VEC_ZERO" in
  let statement = parse_term
    ("!d n" ^ (if unary then "" else " m") ^
     ":5 word. !s t:armstate. " ^ source ^ " d n" ^
     (if unary then "" else " m") ^ " s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n)" ^
     (if unary then "" else " (QREG' m)") ^ " " ^
     string_of_int element_width ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_COMPARE_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ"
    instruction width element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_COMPARE_CLAIMS = map
  (fun (instruction, width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_COMPARE_CLAIM instruction width element_width definition) [
  "CMGT_VEC",64,8,sail_hl_arm_5fCMGT_5fVEC64E8;
  "CMGT_VEC",64,16,sail_hl_arm_5fCMGT_5fVEC64E16;
  "CMGT_VEC",64,32,sail_hl_arm_5fCMGT_5fVEC64E32;
  "CMGT_VEC",128,8,sail_hl_arm_5fCMGT_5fVEC128E8;
  "CMGT_VEC",128,16,sail_hl_arm_5fCMGT_5fVEC128E16;
  "CMGT_VEC",128,32,sail_hl_arm_5fCMGT_5fVEC128E32;
  "CMGT_VEC",128,64,sail_hl_arm_5fCMGT_5fVEC128E64;
  "CMHI_VEC",64,8,sail_hl_arm_5fCMHI_5fVEC64E8;
  "CMHI_VEC",64,16,sail_hl_arm_5fCMHI_5fVEC64E16;
  "CMHI_VEC",64,32,sail_hl_arm_5fCMHI_5fVEC64E32;
  "CMHI_VEC",128,8,sail_hl_arm_5fCMHI_5fVEC128E8;
  "CMHI_VEC",128,16,sail_hl_arm_5fCMHI_5fVEC128E16;
  "CMHI_VEC",128,32,sail_hl_arm_5fCMHI_5fVEC128E32;
  "CMHI_VEC",128,64,sail_hl_arm_5fCMHI_5fVEC128E64;
  "CMGE_VEC",64,8,sail_hl_arm_5fCMGE_5fVEC64E8;
  "CMGE_VEC",64,16,sail_hl_arm_5fCMGE_5fVEC64E16;
  "CMGE_VEC",64,32,sail_hl_arm_5fCMGE_5fVEC64E32;
  "CMGE_VEC",128,8,sail_hl_arm_5fCMGE_5fVEC128E8;
  "CMGE_VEC",128,16,sail_hl_arm_5fCMGE_5fVEC128E16;
  "CMGE_VEC",128,32,sail_hl_arm_5fCMGE_5fVEC128E32;
  "CMGE_VEC",128,64,sail_hl_arm_5fCMGE_5fVEC128E64;
  "CMLE_VEC_ZERO",64,8,sail_hl_arm_5fCMLE_5fVEC_5fZERO64E8;
  "CMLE_VEC_ZERO",64,16,sail_hl_arm_5fCMLE_5fVEC_5fZERO64E16;
  "CMLE_VEC_ZERO",64,32,sail_hl_arm_5fCMLE_5fVEC_5fZERO64E32;
  "CMLE_VEC_ZERO",128,8,sail_hl_arm_5fCMLE_5fVEC_5fZERO128E8;
  "CMLE_VEC_ZERO",128,16,sail_hl_arm_5fCMLE_5fVEC_5fZERO128E16;
  "CMLE_VEC_ZERO",128,32,sail_hl_arm_5fCMLE_5fVEC_5fZERO128E32;
  "CMLE_VEC_ZERO",128,64,sail_hl_arm_5fCMLE_5fVEC_5fZERO128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_COMPARE_PROOFS_OK";;
