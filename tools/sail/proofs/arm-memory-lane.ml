(* Every decoded 32-bit single-lane load/store, retaining full Q128 state. *)
loadt "arm/proofs/base.ml";;
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_hl_memory_model = struct
loadt "tools/sail/proofs/arm-memory-model-loader.ml";;
loadt "tools/sail/_build/arm-memory-lane.ml";;
end;;
loadt "tools/sail/proofs/arm-memory-support.ml";;

let SAIL_HL_ARM_MEMORY_LANE_FORMS =
  flat(map (fun operation -> map (fun mode ->
    let fields = SAIL_HL_ARM_MEMORY_FIELDS
      (["rt";"n"] @ if mode = "POSTR" then ["m"] else []) @
      ["ix",`:2 word`] in
    "arm_" ^ operation ^ "128_SIMD_E32_" ^ mode, fields,
    parse_term ("arm_" ^ operation ^ " (QREG' rt) (XREG_SP n) (" ^
      SAIL_HL_ARM_MEMORY_POST mode 4 ^ ") 32 (val(ix:2 word))")
  ) ["NO";"POSTI";"POSTR"]) ["LD1_LANE";"ST1_LANE"]);;

(* This exhaustive proof split retains all four encoded Q:S values.
   It does not constrain a program's lane selector. *)
let SAIL_HL_ARM_MEMORY_LANE_CASES = prove
 (`!ix:2 word.
     ix = word 0 \/ ix = word 1 \/
     ix = word 2 \/ ix = word 3`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `ix:2 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let SAIL_HL_ARM_MEMORY_LANE_TAC source_definition target_definition =
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `ix:2 word` SAIL_HL_ARM_MEMORY_LANE_CASES) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  SAIL_HL_ARM_MEMORY_STRUCTURE_TAC source_definition target_definition;;

SAIL_HL_ARM_MEMORY_CLAIMS "SAIL_HOL_LIGHT_ARM_MEMORY_LANE_PROOFS_OK"
  SAIL_HL_ARM_MEMORY_LANE_TAC SAIL_HL_ARM_MEMORY_LANE_FORMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MEMORY_LANE_PROOFS_OK";;
