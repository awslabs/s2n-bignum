(* Both ZIP instructions cover every legal Q/size profile. The 64-bit
   E64 encoding is undefined and is not exported here.
   Agreement is execution under successful enabled-AdvSIMD projection,
   not a proof of decode or of the full architectural access check. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-zip.ml";;
needs "tools/sail/proofs/arm-vector-permute-support.ml";;

let SAIL_HL_ARM_VECTOR_ZIP_CLAIMS = map
  (fun (instruction, width, element_width, definition) ->
    SAIL_HL_ARM_VECTOR_PERMUTE_CLAIM instruction width element_width definition) [
  "ZIP1",64,8,sail_hl_arm_5fZIP164E8;
  "ZIP1",64,16,sail_hl_arm_5fZIP164E16;
  "ZIP1",64,32,sail_hl_arm_5fZIP164E32;
  "ZIP1",128,8,sail_hl_arm_5fZIP1128E8;
  "ZIP1",128,16,sail_hl_arm_5fZIP1128E16;
  "ZIP1",128,32,sail_hl_arm_5fZIP1128E32;
  "ZIP1",128,64,sail_hl_arm_5fZIP1128E64;
  "ZIP2",64,8,sail_hl_arm_5fZIP264E8;
  "ZIP2",64,16,sail_hl_arm_5fZIP264E16;
  "ZIP2",64,32,sail_hl_arm_5fZIP264E32;
  "ZIP2",128,8,sail_hl_arm_5fZIP2128E8;
  "ZIP2",128,16,sail_hl_arm_5fZIP2128E16;
  "ZIP2",128,32,sail_hl_arm_5fZIP2128E32;
  "ZIP2",128,64,sail_hl_arm_5fZIP2128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_ZIP_PROOFS_OK";;
