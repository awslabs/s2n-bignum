(* Signed-to-unsigned narrowing with optional rounding, twelve full decoded
   lane/half profiles. Every legal shift and vector register/overlap is
   included. The exporter explicitly excludes FPSR writes, while retaining
   saturation calculations, reads and all other effects. Any retained
   reg_FPSR read component is universally quantified. No proof-side rvalue
   substitution discards writes. The claim concerns represented armstate,
   not physical FPSR preservation or subsequent FPSR-reading instructions. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-saturating-narrow.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-duplicate-lemmas.ml";;

(* The two helpers test the same clamp bounds in opposite orders. Since
   the upper bound is nonnegative, the high and low cases cannot both hold. *)
let SAIL_HL_ARM_VECTOR_SATURATING_NARROW_CLAMP_ORDER = prove
 (`!(value:int) upper:num.
   (if &upper < value then word upper:N word
    else if value < &0 then word 0 else iword value) =
   (if value < &0 then word 0
    else if &upper < value then word upper else iword value)`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `upper:num` INT_POS) THEN ASM_INT_ARITH_TAC);;

(* Keep the same clamp-order identity after the word conditional has been
   moved inside iword. This avoids comparing separately reduced literal
   words against the original integer bounds under an opaque condition. *)
let SAIL_HL_ARM_VECTOR_SATURATING_NARROW_CLAMP_INT_ORDER = prove
 (`!(value:int) upper:num.
   (if &upper < value then &upper
    else if value < &0 then &0 else value) =
   (if value < &0 then &0
    else if &upper < value then &upper else value)`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `upper:num` INT_POS) THEN ASM_INT_ARITH_TAC);;

let SAIL_HL_ARM_VECTOR_SATURATING_NARROW_TAC definition =
  REPEAT GEN_TAC THEN
  (* Move word literals and branch results into one integer conditional
     before comparing clamp order or expanding the packed result bits. *)
  REWRITE_TAC[definition; arm_SQSHRUN; arm_SQSHRUN2;
    arm_SQRSHRUN; arm_SQRSHRUN2; word_uqshrun; word_uqrshrun;
    assign; LET_DEF; LET_END_DEF; FST; SND;
    COND_ID;
    SAIL_HL_ARM_CONDITIONAL_PAIR;
    SAIL_HL_ARM_CONDITIONAL_INSERT;
    WORD_IWORD; SAIL_HL_ARM_IWORD_IF;
    QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    INT_OF_NUM_ADD; NUM_OF_INT_OF_NUM; INT_GT;
    SAIL_HL_ARM_PREDECESSOR;
    ARITH_RULE `(n + 1) - 1 = n`; usimd8; usimd4; usimd2;
    INT_OF_NUM_POW] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_IWORD;
    SAIL_HL_ARM_IWORD_IF;
    SAIL_HL_ARM_VECTOR_SATURATING_NARROW_CLAMP_INT_ORDER;
    GSYM SAIL_HL_ARM_VECTOR_SATURATING_NARROW_CLAMP_ORDER;
    INT_MUL_LID; EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_DUPLICATE_VALUE_TAC THEN
  REPEAT(CHANGED_TAC(
    REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_INSERT; BIT_WORD_SUBWORD;
      BIT_WORD_ZX; BIT_WORD_0] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[] THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_VECTOR_SATURATING_NARROW_CLAIM
    instruction element definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let amount_width = if element = 8 then 3 else if element = 16 then 4 else 5 in
  let statement = parse_term(
    configuration ^ "!amount:" ^ string_of_int amount_width ^
    " word. !d n:5 word. " ^
    "!s t:armstate. " ^ source ^ " amount d n s t <=> arm_" ^
    instruction ^ " (QREG' d) (QREG' n) (val amount + 1) " ^
    string_of_int element ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_VECTOR_SATURATING_NARROW_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s64E%d_EQ" instruction element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_SATURATING_NARROW_CLAIMS = map
  (fun (instruction,element,definition) ->
    SAIL_HL_ARM_VECTOR_SATURATING_NARROW_CLAIM instruction element definition) [
  "SQSHRUN",8,sail_hl_arm_5fSQSHRUN64E8;
  "SQSHRUN",16,sail_hl_arm_5fSQSHRUN64E16;
  "SQSHRUN",32,sail_hl_arm_5fSQSHRUN64E32;
  "SQSHRUN2",8,sail_hl_arm_5fSQSHRUN264E8;
  "SQSHRUN2",16,sail_hl_arm_5fSQSHRUN264E16;
  "SQSHRUN2",32,sail_hl_arm_5fSQSHRUN264E32;
  "SQRSHRUN",8,sail_hl_arm_5fSQRSHRUN64E8;
  "SQRSHRUN",16,sail_hl_arm_5fSQRSHRUN64E16;
  "SQRSHRUN",32,sail_hl_arm_5fSQRSHRUN64E32;
  "SQRSHRUN2",8,sail_hl_arm_5fSQRSHRUN264E8;
  "SQRSHRUN2",16,sail_hl_arm_5fSQRSHRUN264E16;
  "SQRSHRUN2",32,sail_hl_arm_5fSQRSHRUN264E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_SATURATING_NARROW_PROOFS_OK";;
