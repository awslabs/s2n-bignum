(* All eight LD1R lane/register widths and encoded immediate increments. *)
loadt "arm/proofs/base.ml";;
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_hl_memory_model = struct
loadt "tools/sail/proofs/arm-memory-model-loader.ml";;
loadt "tools/sail/_build/arm-memory-replicate.ml";;
end;;
loadt "tools/sail/proofs/arm-memory-support.ml";;

let SAIL_HL_ARM_MEMORY_REPLICATE_FORMS =
  SAIL_HL_ARM_MEMORY_STRUCTURE_FORMS ["LD1R"] [64;128]
    (fun _ -> [8;16;32;64]) ["POSTI"] (fun operation width element mode fields ->
      let target = "arm_LD1R (QREG' rt) (XREG_SP n) (" ^
        SAIL_HL_ARM_MEMORY_POST mode (element / 8) ^ ") " ^
        string_of_int element ^ " " ^ string_of_int width in
      "arm_" ^ operation ^ string_of_int width ^ "_SIMD_LD1R_E" ^
        string_of_int element ^ "_" ^ mode,fields,parse_term target);;

SAIL_HL_ARM_MEMORY_CLAIMS "SAIL_HOL_LIGHT_ARM_MEMORY_REPLICATE_PROOFS_OK"
  SAIL_HL_ARM_MEMORY_STRUCTURE_TAC
  SAIL_HL_ARM_MEMORY_REPLICATE_FORMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MEMORY_REPLICATE_PROOFS_OK";;
