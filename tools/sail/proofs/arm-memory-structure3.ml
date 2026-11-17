(* Every decoded LD3/ST3 layout and immediate/register post-increment form. *)
loadt "arm/proofs/base.ml";;
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_hl_memory_model = struct
loadt "tools/sail/proofs/arm-memory-model-loader.ml";;
loadt "tools/sail/_build/arm-memory-structure3.ml";;
end;;
loadt "tools/sail/proofs/arm-memory-support.ml";;

let SAIL_HL_ARM_MEMORY_STRUCTURE3_FORMS =
  SAIL_HL_ARM_MEMORY_STRUCTURE_FORMS ["LD3";"ST3"] [64;128]
    SAIL_HL_ARM_MEMORY_INTERLEAVED_ELEMENTS ["POSTI";"POSTR"]
    (SAIL_HL_ARM_MEMORY_INTERLEAVED_FORM 3);;

SAIL_HL_ARM_MEMORY_CLAIMS "SAIL_HOL_LIGHT_ARM_MEMORY_STRUCTURE3_PROOFS_OK"
  (fun source_definition target_definition ->
    (* Expand the target's three-register interleave and its local bindings
       before normalizing individual byte values. The Sail equation and
       every encoded operand stay unchanged. *)
    SAIL_HL_ARM_MEMORY_STRUCTURE_TAC source_definition
      (REWRITE_RULE[word_interleave; LET_DEF] target_definition))
  SAIL_HL_ARM_MEMORY_STRUCTURE3_FORMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MEMORY_STRUCTURE3_PROOFS_OK";;
