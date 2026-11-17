(* Six decoded UADALP profiles. Every old destination value, vector register
   and overlap is quantified. The source supplies the read/paired widening
   sum/accumulation and D64 zero-top behavior. No unsupported E64/signed
   geometry, decoding or full access-fault refinement is claimed. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-pair-add-accumulate-long.ml";;
needs "tools/sail/proofs/arm-vector-pair-add-support.ml";;

let SAIL_HL_ARM_VECTOR_PAIR_ADD_ACCUMULATE_LONG_CLAIMS = map
  (fun (width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_PAIR_ADD_CLAIM "UADALP" width element_width definition) [
  64,8,sail_hl_arm_5fUADALP64E8;
  64,16,sail_hl_arm_5fUADALP64E16;
  64,32,sail_hl_arm_5fUADALP64E32;
  128,8,sail_hl_arm_5fUADALP128E8;
  128,16,sail_hl_arm_5fUADALP128E16;
  128,32,sail_hl_arm_5fUADALP128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_PAIR_ADD_ACCUMULATE_LONG_PROOFS_OK";;
