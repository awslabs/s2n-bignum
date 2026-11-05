(* Every decoded LD2/ST2 lane layout and immediate post-increment form. *)
loadt "arm/proofs/base.ml";;
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_hl_memory_model = struct
loadt "tools/sail/proofs/arm-memory-model-loader.ml";;
loadt "tools/sail/_build/arm-memory-structure2.ml";;
end;;
loadt "tools/sail/proofs/arm-memory-support.ml";;

let SAIL_HL_ARM_MEMORY_STRUCTURE2_FORMS =
  SAIL_HL_ARM_MEMORY_STRUCTURE_FORMS ["LD2";"ST2"] [64;128]
    SAIL_HL_ARM_MEMORY_INTERLEAVED_ELEMENTS ["POSTI"]
    (SAIL_HL_ARM_MEMORY_INTERLEAVED_FORM 2);;

SAIL_HL_ARM_MEMORY_CLAIMS "SAIL_HOL_LIGHT_ARM_MEMORY_STRUCTURE2_PROOFS_OK"
  SAIL_HL_ARM_MEMORY_STRUCTURE_TAC
  SAIL_HL_ARM_MEMORY_STRUCTURE2_FORMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MEMORY_STRUCTURE2_PROOFS_OK";;
