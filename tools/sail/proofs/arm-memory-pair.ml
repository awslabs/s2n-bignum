(* Every encoded LDP/STP form, including two-Q-register LD1/ST1 forms. *)
loadt "arm/proofs/base.ml";;
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_hl_memory_model = struct
loadt "tools/sail/proofs/arm-memory-model-loader.ml";;
loadt "tools/sail/_build/arm-memory-pair.ml";;
end;;
loadt "tools/sail/proofs/arm-memory-support.ml";;

let SAIL_HL_ARM_MEMORY_PAIR_FORMS =
  let ordinary = flat(map (fun operation ->
    flat(map (fun (width,view) -> map (fun form ->
      let component = if view = "GPR" then (if width = 32 then "WREG'" else "XREG'")
        else if width = 64 then "DREG'" else "QREG'" in
      let offset = (if form = "POST" then "Postimmediate_Offset"
        else if form = "PRE" then "Preimmediate_Offset" else "Immediate_Offset") ^
        " (iword (ival (imm:7 word) * &" ^ string_of_int(width / 8) ^ "))" in
      let target = "arm_" ^ operation ^ " (" ^ component ^ " rt) (" ^
        component ^ " rt2) (XREG_SP n) (" ^ offset ^ ")" in
      "arm_" ^ operation ^ string_of_int width ^ "_" ^ view ^ "_" ^ form,
      SAIL_HL_ARM_MEMORY_FIELDS ["rt";"rt2";"n"] @ ["imm",`:7 word`],
      parse_term target
    ) ["POST";"PRE";"OFFSET"]) [32,"GPR";64,"GPR";64,"SIMD";128,"SIMD"])
  ) ["LDP";"STP"]) in
  ordinary @ SAIL_HL_ARM_MEMORY_STRUCTURE_FORMS ["LDP";"STP"] [128]
    (fun _ -> [8;16;32;64]) ["NO";"POSTI";"POSTR"]
    (fun operation width -> SAIL_HL_ARM_MEMORY_MULTIPLE_FORM operation width "1" 2);;

(* A combined little-endian access has the same bytes as two adjacent
   accesses, including when the address wraps modulo 64 bits. *)
let SAIL_HL_MEMORY_PAIR_LOAD_LOW = prove
 (`!a:int64. !s:armstate. !m n.
     dimindex(:L) = 8 * m /\
     dimindex(:W) = 8 * (m + n)
     ==> word_subword (read (memory :> wbytes a) s:W word) (0,8*m) =
         (read (memory :> wbytes a) s:L word)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `s:armstate`; `0`; `m:num`; `m+n:num`]
    SAIL_HL_MEMORY_LANE_READ) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; MULT_CLAUSES; LE_ADD] THEN
  MESON_TAC[]);;

let SAIL_HL_MEMORY_PAIR_LOAD_HIGH = prove
 (`!a:int64. !s:armstate. !m n.
     dimindex(:L) = 8 * n /\
     dimindex(:W) = 8 * (m + n)
     ==> word_subword (read (memory :> wbytes a) s:W word) (8*m,8*n) =
         (read (memory :> wbytes (word_add a (word m))) s:L word)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `s:armstate`; `m:num`; `n:num`; `m+n:num`]
    SAIL_HL_MEMORY_LANE_READ) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN MESON_TAC[]);;

let SAIL_HL_ARM_MEMORY_PAIR_LOAD_CONV term =
  let head,args = strip_comb term in
  if fst(dest_const head) <> "word_subword" then
    failwith "not a paired load slice";
  let whole = hd args in
  let lane_bytes = SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH term in
  let whole_bytes = SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH whole in
  if lane_bytes >= whole_bytes then
    failwith "paired load slice does not have a second word";
  let types = [
    hd(snd(dest_type(type_of term))),`:L`;
    hd(snd(dest_type(type_of whole))),`:W`] in
  let low = SAIL_HL_ARM_MEMORY_PAIR_WIDTH_RULE types lane_bytes
    (whole_bytes-lane_bytes) SAIL_HL_MEMORY_PAIR_LOAD_LOW in
  let high = SAIL_HL_ARM_MEMORY_PAIR_WIDTH_RULE types
    (whole_bytes-lane_bytes) lane_bytes SAIL_HL_MEMORY_PAIR_LOAD_HIGH in
  (PART_MATCH lhand low ORELSEC PART_MATCH lhand high) term;;

let SAIL_HL_ARM_MEMORY_PAIR_CONV =
  SAIL_HL_ARM_MEMORY_PAIR_LOAD_CONV ORELSEC
  SAIL_HL_ARM_MEMORY_PAIR_STORE_CONV;;

let SAIL_HL_ARM_ALIGNED_SP_ROUND_DOWN = prove
 (`!sp:64 word.
     aligned 16 sp
     ==> word(num_of_int ((&(val sp) div &16) * &16)):64 word = sp`,
  REWRITE_TAC[INT_OF_NUM_DIV; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
              aligned; DIVIDES_DIV_MULT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_VAL]);;

(* A component inequality gives a field inequality by congruence. The
   converse is deliberately not assumed: two encodings could select the
   same component. This one-way fact prunes the source's duplicate-load
   destination branch under the HOL instruction's actual safety guard. *)
let SAIL_HL_ARM_PAIR_REGISTER_FIELDS_DISTINCT = prove
 (`!(c:5 word->A) t t2.
     ~(c t = c t2) ==> ~(val t = val t2)`,
  REWRITE_TAC[VAL_EQ] THEN MESON_TAC[]);;

(* The load guard excludes equal destination components. Congruence then
   excludes equal encoded fields; the reverse implication is not assumed.
   Retain the original guard and derive only its actual conjuncts. *)
let SAIL_HL_ARM_MEMORY_PAIR_GUARD_FACTS guard =
  let facts = CONJUNCTS guard in
  let indices = List.filter_map (fun fact ->
    try
      let left,right = dest_eq(dest_neg(concl fact)) in
      let c,left = dest_comb left and d,right = dest_comb right in
      if c <> d || type_of left <> `:5 word` ||
         type_of right <> `:5 word` then None else
      Some(MATCH_MP
        (ISPECL [c;left;right] SAIL_HL_ARM_PAIR_REGISTER_FIELDS_DISTINCT)
        fact)
    with Failure _ -> None) facts in
  facts @ indices @ map (REWRITE_RULE[VAL_EQ]) indices;;

(* A writeback pair checks both destination/base overlaps. Derive the
   encoded-field checks from the existing HOL guard, then combine them:
   neither destination can overlap the non-SP base. No field is restricted
   independently of that guard, and register 31 remains included. *)
let SAIL_HL_ARM_MEMORY_PAIR_OVERLAP = TAUT
 `~(p /\ r) /\ ~(q /\ r) ==> ~((p \/ q) /\ r)`;;

let SAIL_HL_ARM_MEMORY_PAIR_WRITEBACK_FACTS guard =
  let facts = SAIL_HL_ARM_MEMORY_SINGLE_GUARD_FACTS guard in
  let overlap = List.filter_map (fun fact ->
    try
      let p,r = dest_conj(dest_neg(concl fact)) in Some(p,r,fact)
    with Failure _ -> None) facts in
  facts @ flat(map (fun (p,r,first) ->
    List.filter_map (fun (q,s,second) ->
      if r <> s then None else
      Some(MATCH_MP (INST [p,`p:bool`;q,`q:bool`;r,`r:bool`]
        SAIL_HL_ARM_MEMORY_PAIR_OVERLAP) (CONJ first second))) overlap) overlap);;

let SAIL_HL_ARM_MEMORY_PAIR_PREPARE_TAC source_definition target_definition =
  REPEAT GEN_TAC THEN DISCH_THEN(fun guard ->
    MAP_EVERY ASSUME_TAC
      (guard::SAIL_HL_ARM_MEMORY_PAIR_WRITEBACK_FACTS guard) THEN MP_TAC guard) THEN
  SAIL_HL_ARM_MEMORY_PREPARE_TAC [] source_definition target_definition THEN
  (* Apply both guard-derived implications only in the non-SP case.
     The source tests the individual equalities before their conjunction,
     so the negative conjunction alone cannot prune those tests. *)
  SAIL_HL_ARM_MEMORY_SINGLE_BRANCH_FACTS_TAC THEN
  PURE_ASM_REWRITE_TAC[EQ_SYM_EQ; INT_OF_NUM_EQ; COND_CLAUSES; COND_ID];;

(* The catalogue includes ordinary LDP/STP and contiguous two-register
   LD1/ST1. Choose only the proof simplifier from the checked root's name;
   both paths prove the same _SAFE_EQ claim about its actual equation.
   LD1/ST1 uses the vector lane/register bridges of the other structure
   suites. An ordinary pair rewrites combined accesses to adjacent accesses
   and proves both values of the source's LSE2 component when that test
   remains in the goal. Erasure removes only access events from both
   states. *)
let SAIL_HL_ARM_MEMORY_PAIR_TAC source_definition target_definition =
  let _,equation =
    strip_forall(concl(hd(CONJUNCTS source_definition))) in
  let root,_ = strip_comb(lhand equation) in
  let name = fst(dest_const root) in
  if mem "5fLD1" (String.split_on_char '_' name) then
    SAIL_HL_ARM_MEMORY_STRUCTURE_TAC source_definition target_definition
  else
    (* The actual guard supplies SP alignment. Discharge that premise
       before evaluating newly exposed normal sum constructors. *)
    let normalize =
      PURE_ASM_SIMP_TAC[SAIL_HL_ARM_ALIGNED_SP_IWORD;
        COND_CLAUSES; COND_ID] THEN
      SAIL_HL_ARM_MEMORY_STATE_CBV_TAC [source_definition] in
    REPEAT GEN_TAC THEN DISCH_THEN(fun guard ->
      MAP_EVERY ASSUME_TAC
        (guard::SAIL_HL_ARM_MEMORY_PAIR_GUARD_FACTS guard) THEN
      MP_TAC guard) THEN
    SAIL_HL_ARM_MEMORY_PAIR_PREPARE_TAC source_definition target_definition THEN
    PURE_REWRITE_TAC[BYTES32_WBYTES; BYTES64_WBYTES;
      BYTES128_WBYTES; BYTES256_WBYTES;
      WREG'; DREG'; QREG'; WREG; DREG;
      READ_ZEROTOP_32; READ_ZEROTOP_64;
      WRITE_ZEROTOP_32; WRITE_ZEROTOP_64; word_sx; WORD_SHL_IWORD] THEN
    normalize THEN
    PURE_REWRITE_TAC[INT_MUL_SYM; WORD_ADD_AC; WORD_ADD_0] THEN
    CONV_TAC(DEPTH_CONV SAIL_HL_ARM_MEMORY_PAIR_CONV) THEN
    W(fun (_,goal) ->
      let choice =
        `read (reg_FlatHaveLSE2:(armstate,bool)component) (s:armstate)` in
      if can (find_term ((=) choice)) goal then ASM_CASES_TAC choice
      else ALL_TAC) THEN
    (* Selecting LSE2 or discharging alignment can expose a normal control
       constructor only after the earlier value pass. Re-enter the same
       normalizer and pair/erasure rules; stop as soon as this decreasing
       cleanup no longer changes the goal. *)
    REPEAT(CHANGED_TAC
     (PURE_ASM_REWRITE_TAC[COND_CLAUSES; COND_ID;
        UNWIND_THM1; UNWIND_THM2; VAL_EQ; INT_OF_NUM_EQ;
        SAIL_HL_ARM_ALIGNED_SP_ROUND_DOWN; SAIL_HL_ARM_ALIGNED_SP_IWORD] THEN
      normalize THEN
      PURE_REWRITE_TAC[INT_MUL_SYM; WORD_ADD_AC; WORD_ADD_0] THEN
      CONV_TAC(DEPTH_CONV SAIL_HL_ARM_MEMORY_PAIR_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV) THEN
      PURE_REWRITE_TAC[SAIL_HL_ARM_MEMORY_ERASE_EVENT_WRITE] THEN
      PURE_ASM_REWRITE_TAC[WORD_ADD_AC; EQ_SYM_EQ; EXISTS_SIMP] THEN
      REWRITE_TAC[])) THEN
    (* Value evaluation and equality orientation can expose the final
       observed-state witness after the common erasure pass. *)
    PURE_REWRITE_TAC[EXISTS_SIMP; UNWIND_THM1; UNWIND_THM2] THEN
    CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV) THEN
    REWRITE_TAC[] THEN PRINT_GOAL_TAC;;

(* A regression check of s2n-bignum's symbolic execution after the arm_LDP
   fix, not a Sail claim: equal destinations, even LDP XZR, XZR, take the
   unsafe branch (ASSIGNS entirety), while a pair of distinct registers
   still executes. *)
let () =
  let unsafe instruction =
    let executed = (ARM_EXEC_CONV THENC REWRITE_CONV[XREG_NE_SP]) instruction in
    can (find_term (fun term ->
      is_const term && fst(dest_const term) = "ASSIGNS")) (rhs(concl executed)) in
  if not(unsafe `arm_LDP XZR XZR X0 No_Offset`) ||
     unsafe `arm_LDP X1 X2 X0 No_Offset` then
    failwith "ARM_EXEC_CONV regression for arm_LDP";;

SAIL_HL_ARM_MEMORY_CLAIMS "SAIL_HOL_LIGHT_ARM_MEMORY_PAIR_PROOFS_OK"
  SAIL_HL_ARM_MEMORY_PAIR_TAC SAIL_HL_ARM_MEMORY_PAIR_FORMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MEMORY_PAIR_PROOFS_OK";;
