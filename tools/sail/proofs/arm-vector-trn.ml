(* Both TRN instructions cover every legal Q/size profile. The 64-bit
   E64 encoding is undefined and is not exported here.
   Agreement is execution under successful enabled-AdvSIMD projection,
   not a proof of decode or of the full architectural access check. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-trn.ml";;
needs "tools/sail/proofs/arm-vector-permute-support.ml";;

let SAIL_HL_ARM_VECTOR_TRN_CLAIMS = map
  (fun (instruction, width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_PERMUTE_CLAIM instruction width element_width definition) [
  "TRN1",64,8,sail_hl_arm_5fTRN164E8;
  "TRN1",64,16,sail_hl_arm_5fTRN164E16;
  "TRN1",64,32,sail_hl_arm_5fTRN164E32;
  "TRN1",128,8,sail_hl_arm_5fTRN1128E8;
  "TRN1",128,16,sail_hl_arm_5fTRN1128E16;
  "TRN1",128,32,sail_hl_arm_5fTRN1128E32;
  "TRN1",128,64,sail_hl_arm_5fTRN1128E64;
  "TRN2",64,8,sail_hl_arm_5fTRN264E8;
  "TRN2",64,16,sail_hl_arm_5fTRN264E16;
  "TRN2",64,32,sail_hl_arm_5fTRN264E32;
  "TRN2",128,8,sail_hl_arm_5fTRN2128E8;
  "TRN2",128,16,sail_hl_arm_5fTRN2128E16;
  "TRN2",128,32,sail_hl_arm_5fTRN2128E32;
  "TRN2",128,64,sail_hl_arm_5fTRN2128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_TRN_PROOFS_OK";;
