(* Three decoded Q128 UADDLP profiles. The original unsigned pair reads,
   integer widening and result writes are source exports. All vector
   registers/overlaps are quantified; no unsupported D64/signed/decoder
   or full access-fault refinement is claimed. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-pair-add-long.ml";;
needs "tools/sail/proofs/arm-vector-pair-add-support.ml";;

let SAIL_HL_ARM_VECTOR_PAIR_ADD_LONG_CLAIMS = map
  (fun (width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_PAIR_ADD_CLAIM "UADDLP" width element_width definition) [
  128,8,sail_hl_arm_5fUADDLP128E8;
  128,16,sail_hl_arm_5fUADDLP128E16;
  128,32,sail_hl_arm_5fUADDLP128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_PAIR_ADD_LONG_PROOFS_OK";;
