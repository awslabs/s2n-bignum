(* Prove DUP_GEN agreement for all seven decoded vector layouts.
   HOL uses an XREG' source even for byte/halfword lanes; Sail's X_read
   takes esize. The proofs compare the appropriate low bits and include X31
   zero behavior. Scalar DUP, decoder and full-platform correspondence are
   outside these claims; AdvSIMD access uses the declared interpretation. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-duplicate-general.ml";;
needs "tools/sail/proofs/arm-vector-duplicate-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_DUPLICATE_GENERAL_CLAIM width element definition =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term
    ("!d n:5 word. !s t:armstate. " ^ source ^
     " d n s t <=> arm_DUP_GEN (QREG' d) (XREG' n) " ^
     string_of_int element ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN SAIL_HL_ARM_VECTOR_DUPLICATE_NORM definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_DUP_GEN%dE%d_EQ" width element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_DUPLICATE_GENERAL_CLAIMS = map
  (fun (width,element,definition) ->
    SAIL_HL_ARM_VECTOR_DUPLICATE_GENERAL_CLAIM width element definition) [
  64,8,sail_hl_arm_5fDUP_5fGEN64E8;
  64,16,sail_hl_arm_5fDUP_5fGEN64E16;
  64,32,sail_hl_arm_5fDUP_5fGEN64E32;
  128,8,sail_hl_arm_5fDUP_5fGEN128E8;
  128,16,sail_hl_arm_5fDUP_5fGEN128E16;
  128,32,sail_hl_arm_5fDUP_5fGEN128E32;
  128,64,sail_hl_arm_5fDUP_5fGEN128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_DUPLICATE_GENERAL_PROOFS_OK";;
