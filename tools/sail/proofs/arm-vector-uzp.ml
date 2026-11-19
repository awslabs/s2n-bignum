(* The HOL decoder accepts UZP1/UZP2 only with Q=1. All four lane widths
   are claimed; no unsupported 64-bit profile is counted. The enabled
   AdvSIMD check remains an explicit external projection contract. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-uzp.ml";;
needs "tools/sail/proofs/arm-vector-permute-support.ml";;

let SAIL_HL_ARM_VECTOR_UZP_CLAIMS = map
  (fun (instruction, width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_PERMUTE_CLAIM instruction width element_width definition) [
  "UZP1",128,8,sail_hl_arm_5fUZP1128E8;
  "UZP1",128,16,sail_hl_arm_5fUZP1128E16;
  "UZP1",128,32,sail_hl_arm_5fUZP1128E32;
  "UZP1",128,64,sail_hl_arm_5fUZP1128E64;
  "UZP2",128,8,sail_hl_arm_5fUZP2128E8;
  "UZP2",128,16,sail_hl_arm_5fUZP2128E16;
  "UZP2",128,32,sail_hl_arm_5fUZP2128E32;
  "UZP2",128,64,sail_hl_arm_5fUZP2128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_UZP_PROOFS_OK";;
