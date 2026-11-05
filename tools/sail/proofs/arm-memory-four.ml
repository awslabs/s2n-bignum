(* Every encoded four-register LD1/ST1 form represented by LDP4/STP4. *)
loadt "arm/proofs/base.ml";;
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_hl_memory_model = struct
loadt "tools/sail/proofs/arm-memory-model-loader.ml";;
loadt "tools/sail/_build/arm-memory-four.ml";;
end;;
loadt "tools/sail/proofs/arm-memory-support.ml";;

let SAIL_HL_ARM_MEMORY_FOUR_FORMS =
  SAIL_HL_ARM_MEMORY_STRUCTURE_FORMS ["LDP4";"STP4"] [64;128]
    (fun _ -> [8;16;32;64]) ["NO";"POSTI";"POSTR"]
    (fun operation width -> SAIL_HL_ARM_MEMORY_MULTIPLE_FORM operation width "1" 4);;

(* Deferring read states reduced normalization time for four-register
   stores. Loads keep strict evaluation so joined lane histories stay
   shared. This selects proof evaluation only, not operands, guards or
   claims. *)
let SAIL_HL_ARM_MEMORY_FOUR_TAC source_definition target_definition =
  SAIL_HL_ARM_MEMORY_STRUCTURE_TAC
    ~defer_read_state:(target_definition == arm_STP4)
    source_definition target_definition;;

SAIL_HL_ARM_MEMORY_CLAIMS "SAIL_HOL_LIGHT_ARM_MEMORY_FOUR_PROOFS_OK"
  SAIL_HL_ARM_MEMORY_FOUR_TAC SAIL_HL_ARM_MEMORY_FOUR_FORMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MEMORY_FOUR_PROOFS_OK";;
