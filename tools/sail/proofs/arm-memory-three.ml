(* Three contiguous registers through LD1/ST1, not interleaved LD3/ST3. *)
loadt "arm/proofs/base.ml";;
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_hl_memory_model = struct
loadt "tools/sail/proofs/arm-memory-model-loader.ml";;
loadt "tools/sail/_build/arm-memory-three.ml";;
end;;
loadt "tools/sail/proofs/arm-memory-support.ml";;

let SAIL_HL_ARM_MEMORY_THREE_FORMS =
  SAIL_HL_ARM_MEMORY_STRUCTURE_FORMS ["LDP3";"STP3"] [64;128]
    (fun _ -> [8;16;32;64]) ["NO";"POSTI";"POSTR"]
    (fun operation width -> SAIL_HL_ARM_MEMORY_MULTIPLE_FORM operation width "1" 3);;

let SAIL_HL_ARM_MEMORY_THREE_TAC source_definition target_definition =
  SAIL_HL_ARM_MEMORY_STRUCTURE_TAC
    ~defer_read_state:(target_definition == arm_STP3)
    source_definition target_definition;;

SAIL_HL_ARM_MEMORY_CLAIMS "SAIL_HOL_LIGHT_ARM_MEMORY_THREE_PROOFS_OK"
  SAIL_HL_ARM_MEMORY_THREE_TAC SAIL_HL_ARM_MEMORY_THREE_FORMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MEMORY_THREE_PROOFS_OK";;
