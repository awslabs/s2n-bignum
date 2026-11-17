(* Twelve exact decoded profiles: Q128 reads, narrow E8/E16/E32 results,
   all shifts1..E and vector31/overlap. Low writes zero top; high writes
   preserve old low64 through the real Vpart_set. No hand preservation
   effects or decoder/access-fault refinement are introduced. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-shift-narrow.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_SHIFT_NARROW_UNSIGNED = prove
 (`!(x:N word) n.
   word_zx(word_ushr x n):M word =
   iword (&(val x) div &(2 EXP n))`,
  REWRITE_TAC[word_zx; VAL_WORD_USHR; WORD_IWORD; INT_OF_NUM_DIV]);;

let SAIL_HL_ARM_VECTOR_SHIFT_NARROW_ROUNDED = prove
 (`!(x:N word) n.
   word_rshrn x (n + 1):M word =
   iword ((&(val x) + &(2 EXP n)) div &(2 EXP (n + 1)))`,
  REWRITE_TAC[word_rshrn; ARITH_RULE `(n + 1) - 1 = n`;
    WORD_IWORD; INT_OF_NUM_ADD; INT_OF_NUM_DIV]);;

let SAIL_HL_ARM_VECTOR_SHIFT_NARROW_VALUE_TAC =
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
      BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_0; BIT_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_SHIFT_NARROW_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_SHRN; arm_SHRN2; arm_RSHRN; arm_RSHRN2;
    assign; LET_DEF; LET_END_DEF; FST; SND;
    QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    INT_OF_NUM_ADD; SAIL_HL_ARM_PREDECESSOR;
    NUM_OF_INT_OF_NUM; INT_MUL_LID; usimd8; usimd4; usimd2;
    SAIL_HL_ARM_VECTOR_SHIFT_NARROW_ROUNDED] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_SHIFT_NARROW_UNSIGNED;
    INT_OF_NUM_ADD; INT_OF_NUM_DIV; word_ushr; GSYM WORD_IWORD; EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_SHIFT_NARROW_VALUE_TAC THEN PRINT_GOAL_TAC;;

(* Only theorem statements are constructed, never source model effects. *)
let SAIL_HL_ARM_VECTOR_SHIFT_NARROW_CLAIM
    instruction element_width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let amount_width = if element_width = 8 then 3
                     else if element_width = 16 then 4 else 5 in
  let statement = parse_term
    ("!amount:" ^ string_of_int amount_width ^ " word. !d n:5 word. " ^
     "!s t:armstate. " ^ source ^ " amount d n s t <=> arm_" ^
     instruction ^ " (QREG' d) (QREG' n) (val amount + 1) " ^
     string_of_int element_width ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_VECTOR_SHIFT_NARROW_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s64E%d_EQ" instruction element_width in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_SHIFT_NARROW_CLAIMS = map
  (fun (instruction, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_SHIFT_NARROW_CLAIM instruction element_width definition) [
  "SHRN",8,sail_hl_arm_5fSHRN64E8;
  "SHRN",16,sail_hl_arm_5fSHRN64E16;
  "SHRN",32,sail_hl_arm_5fSHRN64E32;
  "SHRN2",8,sail_hl_arm_5fSHRN264E8;
  "SHRN2",16,sail_hl_arm_5fSHRN264E16;
  "SHRN2",32,sail_hl_arm_5fSHRN264E32;
  "RSHRN",8,sail_hl_arm_5fRSHRN64E8;
  "RSHRN",16,sail_hl_arm_5fRSHRN64E16;
  "RSHRN",32,sail_hl_arm_5fRSHRN64E32;
  "RSHRN2",8,sail_hl_arm_5fRSHRN264E8;
  "RSHRN2",16,sail_hl_arm_5fRSHRN264E16;
  "RSHRN2",32,sail_hl_arm_5fRSHRN264E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_SHIFT_NARROW_PROOFS_OK";;
