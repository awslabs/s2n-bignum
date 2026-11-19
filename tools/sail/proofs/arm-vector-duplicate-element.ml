(* Prove DUP_ELEM agreement for all fourteen vector forms.
   Both lower and upper source reads are included, with implicit E64 lanes
   0/1. Claims quantify all 32 register fields and every legal element index.
   Decoder and full-platform correspondence remain separate obligations;
   enabled AdvSIMD access uses the declared register interpretation. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-duplicate-element.ml";;
needs "tools/sail/proofs/arm-vector-duplicate-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_DUPLICATE_ELEMENT_CLAIM width element high definition =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let selector_width = if element = 8 then 3
                       else if element = 16 then 2 else 1 in
  let implicit = element = 64 in
  let offset = if high then 64 / element else 0 in
  let quantifier = if implicit then "" else
    Printf.sprintf "!idx:%d word. " selector_width in
  let arguments = if implicit then "d n" else "d n idx" in
  let lane = if implicit then string_of_int offset else
    Printf.sprintf "(val idx + %d)" offset in
  let statement = parse_term
    ("!d n:5 word. " ^ quantifier ^ "!s t:armstate. " ^
     source ^ " " ^ arguments ^ " s t <=> arm_DUP_ELEM " ^
     "(QREG' d) (QREG' n) " ^ lane ^ " " ^ string_of_int element ^
     " " ^ string_of_int width ^ " s t") in
  let tactic =
    REPEAT GEN_TAC THEN
    (if implicit then ALL_TAC else
     let selector = mk_var("idx",type_of(parse_term
       (Printf.sprintf "(word 0:%d word)" selector_width))) in
     SPEC_TAC(selector,selector) THEN
     ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN
     CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
     REPEAT CONJ_TAC) THEN
    SAIL_HL_ARM_VECTOR_DUPLICATE_NORM definition in
  let theorem = prove(statement,tactic) in
  let name = Printf.sprintf "SAIL_HL_ARM_DUP_ELEM%dE%d_%s_EQ"
    width element (if high then "HI" else "LO") in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_DUPLICATE_ELEMENT_CLAIMS = map
  (fun (width,element,high,definition) ->
    SAIL_HL_ARM_VECTOR_DUPLICATE_ELEMENT_CLAIM
      width element high definition) [
  64,8,false,sail_hl_arm_5fDUP_5fELEM64E8_5fLO;
  64,8,true,sail_hl_arm_5fDUP_5fELEM64E8_5fHI;
  64,16,false,sail_hl_arm_5fDUP_5fELEM64E16_5fLO;
  64,16,true,sail_hl_arm_5fDUP_5fELEM64E16_5fHI;
  64,32,false,sail_hl_arm_5fDUP_5fELEM64E32_5fLO;
  64,32,true,sail_hl_arm_5fDUP_5fELEM64E32_5fHI;
  128,8,false,sail_hl_arm_5fDUP_5fELEM128E8_5fLO;
  128,8,true,sail_hl_arm_5fDUP_5fELEM128E8_5fHI;
  128,16,false,sail_hl_arm_5fDUP_5fELEM128E16_5fLO;
  128,16,true,sail_hl_arm_5fDUP_5fELEM128E16_5fHI;
  128,32,false,sail_hl_arm_5fDUP_5fELEM128E32_5fLO;
  128,32,true,sail_hl_arm_5fDUP_5fELEM128E32_5fHI;
  128,64,false,sail_hl_arm_5fDUP_5fELEM128E64_5fLO;
  128,64,true,sail_hl_arm_5fDUP_5fELEM128E64_5fHI;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_DUPLICATE_ELEMENT_PROOFS_OK";;
