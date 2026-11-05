(* Prove scalar DUP_ELEM agreement for all eight forms: element sizes 8,
   16, 32 and 64, each reading a lane of the low or high source half, with
   implicit E64 lanes 0/1. Claims quantify all 32 register fields and every
   legal element index. Decoder and full-platform correspondence remain
   separate obligations; enabled AdvSIMD access uses the declared register
   interpretation. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-duplicate-element-scalar.ml";;
needs "tools/sail/proofs/arm-vector-duplicate-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_DUPLICATE_ELEMENT_SCALAR_CLAIM element high definition =
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
     source ^ " " ^ arguments ^ " s t <=> arm_DUP_ELEM_SCALAR " ^
     "(QREG' d) (QREG' n) " ^ lane ^ " " ^ string_of_int element ^ " s t") in
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
    REWRITE_TAC[arm_DUP_ELEM_SCALAR] THEN
    SAIL_HL_ARM_VECTOR_DUPLICATE_NORM definition in
  let theorem = prove(statement,tactic) in
  let name = Printf.sprintf "SAIL_HL_ARM_DUP_ELEM_SCALAR_E%d_%s_EQ"
    element (if high then "HI" else "LO") in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_DUPLICATE_ELEMENT_SCALAR_CLAIMS = map
  (fun (element,high,definition) ->
    SAIL_HL_ARM_VECTOR_DUPLICATE_ELEMENT_SCALAR_CLAIM element high definition) [
  8,false,sail_hl_arm_5fDUP_5fELEM_5fSCALAR_5fE8_5fLO;
  8,true,sail_hl_arm_5fDUP_5fELEM_5fSCALAR_5fE8_5fHI;
  16,false,sail_hl_arm_5fDUP_5fELEM_5fSCALAR_5fE16_5fLO;
  16,true,sail_hl_arm_5fDUP_5fELEM_5fSCALAR_5fE16_5fHI;
  32,false,sail_hl_arm_5fDUP_5fELEM_5fSCALAR_5fE32_5fLO;
  32,true,sail_hl_arm_5fDUP_5fELEM_5fSCALAR_5fE32_5fHI;
  64,false,sail_hl_arm_5fDUP_5fELEM_5fSCALAR_5fE64_5fLO;
  64,true,sail_hl_arm_5fDUP_5fELEM_5fSCALAR_5fE64_5fHI;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_DUPLICATE_ELEMENT_SCALAR_PROOFS_OK";;
