(* Prove signed/unsigned widening multiplication for twenty vector/indexed
   forms. Low/high source halves and every encoded lane are retained, with
   unrestricted register overlap. The common support proves the packing
   equations; the generated model supplies the declared register boundary. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-multiply-long.ml";;
needs "tools/sail/proofs/arm-vector-multiply-long-support.ml";;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_CLAIMS = map
  (fun (instruction,element,definition) ->
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_CLAIM instruction element definition) [
    "SMULL_VEC",8,sail_hl_arm_5fSMULL_5fVEC128E8;
    "SMULL_VEC",16,sail_hl_arm_5fSMULL_5fVEC128E16;
    "SMULL_VEC",32,sail_hl_arm_5fSMULL_5fVEC128E32;
    "SMULL2_VEC",8,sail_hl_arm_5fSMULL2_5fVEC128E8;
    "SMULL2_VEC",16,sail_hl_arm_5fSMULL2_5fVEC128E16;
    "SMULL2_VEC",32,sail_hl_arm_5fSMULL2_5fVEC128E32;
    "UMULL_VEC",8,sail_hl_arm_5fUMULL_5fVEC128E8;
    "UMULL_VEC",16,sail_hl_arm_5fUMULL_5fVEC128E16;
    "UMULL_VEC",32,sail_hl_arm_5fUMULL_5fVEC128E32;
    "UMULL2_VEC",8,sail_hl_arm_5fUMULL2_5fVEC128E8;
    "UMULL2_VEC",16,sail_hl_arm_5fUMULL2_5fVEC128E16;
    "UMULL2_VEC",32,sail_hl_arm_5fUMULL2_5fVEC128E32;
  ];;

let SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_INDEXED_CLAIMS = map
  (fun (instruction,element,high,definition) ->
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_INDEXED_CLAIM
      instruction element high definition) [
    "UMULL_VEC",16,false,sail_hl_arm_5fUMULL_5fVEC128E16_5fLO;
    "UMULL_VEC",16,true,sail_hl_arm_5fUMULL_5fVEC128E16_5fHI;
    "UMULL_VEC",32,false,sail_hl_arm_5fUMULL_5fVEC128E32_5fLO;
    "UMULL_VEC",32,true,sail_hl_arm_5fUMULL_5fVEC128E32_5fHI;
    "UMULL2_VEC",16,false,sail_hl_arm_5fUMULL2_5fVEC128E16_5fLO;
    "UMULL2_VEC",16,true,sail_hl_arm_5fUMULL2_5fVEC128E16_5fHI;
    "UMULL2_VEC",32,false,sail_hl_arm_5fUMULL2_5fVEC128E32_5fLO;
    "UMULL2_VEC",32,true,sail_hl_arm_5fUMULL2_5fVEC128E32_5fHI;
  ];;

check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_MULTIPLY_LONG_PROOFS_OK";;
