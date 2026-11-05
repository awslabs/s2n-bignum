(* Closed counterexamples to agreement for the six 8- and 16-bit carry
   rotates, derived from their _EXACT theorems in x86-shift.ml.

   At a whole-cycle count, 9 for a byte and 17 for a word, rotating the
   operand with CF through all w + 1 bits leaves both unchanged, and
   s2n-bignum leaves OF undefined. By _EXACT, shina keeps OF at that
   count. So for every register field d and state s, s2n-bignum permits
   the final state that differs from s only in OF, and shina rejects it.
   The architectural classification of this difference is unresolved. *)
let SAIL_HL_X86_CARRY_DIFF (root, exact) =
  let vars, body = strip_forall (concl exact) in
  let d, count, s, t = match vars with
    | [d; count; s; t] -> d, count, s, t
    | _ -> failwith "carry rotate: unexpected _EXACT statement" in
  let shina, rhs = dest_eq body in
  let s2n, kept = dest_conj rhs in
  let k = rand (hd (disjuncts (lhand kept))) in
  let flipped = mk_comb(mk_comb(`write OF:bool->x86state->x86state`,
    mk_neg(mk_comb(`read OF:x86state->bool`, s))), s) in
  let relation, arguments = strip_comb s2n in
  let statement = list_mk_forall([d; s], mk_conj(
    list_mk_comb(relation, [hd arguments; k; s; flipped]),
    mk_neg(vsubst [mk_comb(`word:num->8 word`, k), count; flipped, t]
      shina))) in
  let cycle = SAIL_HL_X86_SHIFT_AT (dest_small_numeral k - 1)
    SAIL_HL_X86_CARRY_JOIN in
  root, prove(statement,
    REPEAT GEN_TAC THEN REWRITE_TAC[exact] THEN
    CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
             WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN
    REWRITE_TAC[TAUT `(~p <=> p) <=> F`] THEN
    TRY COND_CASES_TAC THEN
    REWRITE_TAC[x86_RCL; x86_RCR; GPR8; GPR16] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
    REWRITE_TAC[cycle; BIT_WORD_BITVAL; assign; SEQ; UNDEFINED_VALUES;
                SEQ_ID; ASSIGNS_SEQ; ASSIGNS_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
    EXISTS_TAC `~read OF (s:x86state)` THEN REFL_TAC);;

let SAIL_HL_X86_DISCREPANCY_CLAIMS =
  map SAIL_HL_X86_CARRY_DIFF SAIL_HL_X86_EXACT_CLAIMS;;
