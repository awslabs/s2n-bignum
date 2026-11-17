(* Tactic shared by the move, select and bit suites.

   These roots keep the decoder steps of dispatch_2byte_gpr and
   decode_execute: prefix record, ModR/M field extraction, operand-size
   selection and partial-register access. The tactic unfolds the generated
   definitions, evaluates the decoder on the supplied fields, and leaves
   the instruction's own data flow to be compared with s2n-bignum's
   definition. It assumes nothing about the operand registers, which may
   be equal, or about flags and the remaining state.

   A legacy byte field has three bits; 4..7 select AH/CH/DH/BH. For each
   such field the tactic splits on 4 <= val field before unfolding. *)
needs "tools/sail/proofs/x86-gpr-lemmas.ml";;
loadt "tools/sail/proofs/x86-gpr-claims.ml";;

(* s2n-bignum's POPCNT and PEXT record an event before their other writes;
   the statements append the event after Sail's. Move an events write to
   the innermost position, which the two states share. *)
let SAIL_HL_X86_EVENTS_INWARD_CONV =
  let rule = PART_MATCH (lhand o rand) SAIL_HL_X86_WRITE_COMMUTE in
  fun tm ->
    match strip_comb tm with
    | Const("write",_), [c; _; body] when c = `events` ->
        (match strip_comb body with
         | Const("write",_), [d; _; _] when d <> c ->
             let th = rule tm in
             MP th (ORTHOGONAL_COMPONENTS_CONV (lhand(concl th)))
         | _ -> failwith "events already innermost")
    | _ -> failwith "not an events write";;

(* NORMALIZE unfolds the generated bodies and normalizes register fields
   and partial-register accesses. A suite passes `fields_step`, applied after
   the fields are normalized, and `final_step`, applied last, for facts of its
   own (the condition-code select, the byte swap). *)
let SAIL_HL_X86_SCALAR_NORMALIZE fields_step final_step definitions widths
    legacy_fields extra =
  let sources = map (fun width -> SAIL_HL_X86_LOW_SUBWORD(mk_finty(num width)))
    (setify widths) in
  REPEAT GEN_TAC THEN
  (if legacy_fields = [] then ALL_TAC else
   MAP_EVERY (fun name ->
     MP_TAC(ISPEC (parse_term(name ^ ":3 word")) VAL_BOUND))
     legacy_fields THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   REPEAT DISCH_TAC THEN
   MAP_EVERY (fun name ->
     ASM_CASES_TAC(parse_term("4 <= val(" ^ name ^ ":3 word)")))
     legacy_fields) THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @ extra @
    [assign; SEQ; ASSIGNS_THM; LET_DEF; LET_END_DEF; FST; SND;
     UNDEFINED_VALUES; SEQ_ID; ASSIGNS_SEQ;
     GSYM WORD_IWORD; WORD_VAL; SAIL_HL_X86_JOIN_ZERO;
     GPR8; GPR16; GPR32_Z; GPR64; READ_SHORT; WRITE_SHORT;
     READ_ZEROTOP_32; WRITE_ZEROTOP_32; SAIL_HL_X86_LOW_SUBWORD `:8`] @
    sources) THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[COND_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SAIL_HL_X86_GPR_REGISTER_FIELDS_TAC THEN
  fields_step THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC SAIL_HL_X86_GPR_INSERT_REWRITES THEN
  REWRITE_TAC[GSYM word_zx; WORD_ZX_TRIVIAL] THEN
  SAIL_HL_X86_GPR_REGISTER_FIELDS_TAC THEN
  final_step THEN
  TRY(REWRITE_TAC extra);;

let SAIL_HL_X86_SCALAR_TAC_WITH fields_step final_step definitions widths
    legacy_fields extra =
  SAIL_HL_X86_SCALAR_NORMALIZE fields_step final_step definitions widths
    legacy_fields extra THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

let SAIL_HL_X86_SCALAR_TAC =
  SAIL_HL_X86_SCALAR_TAC_WITH ALL_TAC ALL_TAC;;
