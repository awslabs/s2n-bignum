(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Loops and regions that clang 23 -O3 inlines into mldsa-native's verify    *)
(* and signing functions in the monolithic reduced-RAM build, as lemmas from *)
(* the head of the code to its exit that the proofs of the callers use as    *)
(* they use the theorem for a subroutine (as the arm/proofs/mlkem_native/    *)
(* inline_loops.ml of the AArch64 proofs of mlkem-native).                   *)
(*                                                                           *)
(* Each lemma has the form                                                   *)
(*                                                                           *)
(*   exists f_events. forall e args pc. ... ==> ensures x86                  *)
(*     (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + head) /\   *)
(*          <registers> /\ <input> /\ read events s = e)                     *)
(*     (\s. read RIP s = word(pc + exit) /\ <registers> /\ <result> /\       *)
(*          exists e2. read events s = APPEND e2 e /\ e2 = f_events .. /\    *)
(*                     memaccess_inbounds e2 reads writes)                   *)
(*     (MAYCHANGE registers ,, MAYCHANGE [events] ,, MAYCHANGE memory)       *)
(*                                                                           *)
(* so that it serves for correctness and for constant time and memory        *)
(* safety. The lemmas are generated for the labels of the code (the head and *)
(* exit of a loop, in layout.ml), so that the instances in the 44, 65 and 87 *)
(* functions share their statements and proofs. The stack pointer of the     *)
(* caller is the variable rsp0 (as RSP is an inline address base), the       *)
(* addresses in the frame being at fixed offsets from it.                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;
needs "x86/proofs/utils/mldsa_native_pack.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/utils/mldsa_native_rounding.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

(* utilities for the clang23 inline lemmas *)

(* A numeral expression linear in one variable (built from +, * and
   numerals), as base + (s * i + d), with d >= 0 (or base + s * i if d = 0
   and base if s = 0). *)
let LINEAR_ADDR_CONV_B bases tm =
  let (+/) = (+) and ( */ ) = ( * ) in
  let rec ev t =                       (* (constant, coefficient of i) *)
    match t with
      Comb(Comb(Const("+",_),a),b) -> let (c1,s1) = ev a and (c2,s2) = ev b in (c1 +/ c2, s1 +/ s2)
    | Comb(Comb(Const("*",_),a),b) ->
        let (c1,s1) = ev a and (c2,s2) = ev b in
        if s1 = 0 then (c1 */ c2, c1 */ s2)
        else if s2 = 0 then (c1 */ c2, s1 */ c2)
        else failwith "LINEAR_ADDR_CONV: not linear"
    | Var(_,_) -> (0,1)
    | _ -> (dest_small_numeral t, 0) in
  let (c,s) = ev tm in
  let ok = filter (fun b -> b <= c) bases in
  if ok = [] then failwith "LINEAR_ADDR_CONV: below the base" else
  let base = end_itlist max ok in
  let d = c - base in
  let iv = hd (frees tm) in
  let si = mk_comb(mk_comb(`(*):num->num->num`, mk_small_numeral s), iv) in
  let plus a b = mk_comb(mk_comb(`(+):num->num->num`, a), b) in
  let r = if s = 0 then mk_small_numeral base
          else if d = 0 then plus (mk_small_numeral base) si
          else plus (mk_small_numeral base) (plus si (mk_small_numeral d)) in
  if r = tm then failwith "LINEAR_ADDR_CONV: unchanged" else
  ARITH_RULE (mk_eq(tm, r));;

(* the same for the address expressions word_add p (word n) in the assumptions
   about memory *)
let ADDR_LINEAR_BASES_TAC bases =
  let pat = `read (memory :> c) (s:x86state) = v` in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] pat) (concl th)
    then (try CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV (fun tm ->
                 if type_of tm = `:num` && not(is_numeral tm) && (is_comb tm)
                 then LINEAR_ADDR_CONV_B bases tm else failwith ""))) th
          with Failure _ -> th)
    else th);;

let LINEAR_ADDR_CONV base = LINEAR_ADDR_CONV_B [base];;
let ADDR_LINEAR_TAC base = ADDR_LINEAR_BASES_TAC [base];;
let ADDR_MUL1_TAC = ADDR_LINEAR_TAC;;

(* as CHUNK_FULL_FINAL_TAC, for a loop whose stores are indexed by a register
   (addresses 1 * (c + s * i) + k, normalised to base + (s * i + d)), and with
   the arithmetic rules ars used in the increments *)
let CHUNK_FULL_FINAL3_TAC base ars (extra:tactic) fdef (x:term) =
  ADDR_MUL1_TAC base THEN ADDR_NORMALIZE_TAC THEN ADDR_MUL1_TAC base THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC ars THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(extra THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[fdef] THEN
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_DIV_256_MOD_256] THEN
      REPEAT CONJ_TAC THEN APP_BLAST_TAC x THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* the exit of an inlined loop: no instruction to simulate *)
let FULL_EXIT0_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* Instantiating a template: replace each @NAME@ by its value. *)

let subst_tokens (kvs:(string*string) list) (s:string) =
  let rec go s (k,v) =
    let kl = String.length k in
    let b = Buffer.create (String.length s) in
    let i = ref 0 in
    while !i < String.length s do
      if !i + kl <= String.length s && String.sub s !i kl = k
      then (Buffer.add_string b v; i := !i + kl)
      else (Buffer.add_char b s.[!i]; incr i)
    done;
    Buffer.contents b in
  List.fold_left go s kvs;;

let image_mc = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

(* A wide read of a region of bytes at base a + (m + c), merged from the facts
   about its bytes, with the byte addresses in the form a + (m + c') of the
   facts of CHUNK_INPUT_TAC; the fact is added together with its form of
   INPUT_ALT_ADDR_TAC. *)
let MERGE_FACT_CONV n tm =
  CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                      DEPTH_CONV(CHANGED_CONV(REWRITE_CONV[GSYM ADD_ASSOC]) THENC
                                 NUM_REDUCE_CONV)))
   (READ_MEMORY_MERGE_CONV n tm);;

let MERGE_FACT_TAC n tm a =
  MP_TAC(MERGE_FACT_CONV n tm) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  INPUT_ALT_ADDR_TAC a;;

(* The 128-bit part of a vector register after SSE steps, as a fact
   read YMMk s = word_join hi lo with a large lo, is made opaque: lo is
   replaced by a variable v with the assumption v = lo, so that the next
   step (a store of the register, say) does not simplify the large term. *)
let SSE_OPAQUE_TAC reg vname =
  W(fun (asl,w) ->
    let isreg t =
      match t with
        Comb(Comb(Const("read",_),Const(r,_)),_) -> r = reg
      | _ -> false in
    let (_,th) = find (fun (_,th) ->
      let c = concl th in
      is_eq c && isreg (lhs c) &&
      (match rhs c with
         Comb(Comb(Const("word_join",_),_),_) -> true | _ -> false)) asl in
    let c = concl th in
    let lo = rand(rhs c) in
    let v = mk_var(vname,type_of lo) in
    let ex = mk_exists(v,mk_eq(v,lo)) in
    MP_TAC(EXISTS (ex,lo) (REFL lo)) THEN
    DISCH_THEN(X_CHOOSE_THEN v (fun dth ->
      FIRST_X_ASSUM(fun th' -> if concl th' = c
                      then ASSUME_TAC(REWRITE_RULE[GSYM dth] th')
                      else NO_TAC) THEN
      ASSUME_TAC dth)));;

let CHUNK_FULL_FINAL2_TAC base ars = CHUNK_FULL_FINAL3_TAC base ars ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* The chunk lemmas of common/fips204/properties/mldsa_native.ml (for 4      *)
(* coefficients per iteration) for any number n of coefficients, over a      *)
(* polynomial of 256 coefficients of w bytes each: the facts about the n     *)
(* coefficients of iteration i, and the addresses of its coefficients.       *)
(* ------------------------------------------------------------------------- *)

let CHUNK_INPUT_SPLIT_GEN = prove
 (`!n P x. (!j. x <= j /\ j < 256 ==> P j) <=>
           (!j. x + n <= j /\ j < 256 ==> P j) /\
           (!k. k < n /\ x + k < 256 ==> P(x + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `x + n <= j` THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - x`) THEN
    SUBGOAL_THEN `x + (j - x) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK_OUTPUT_SPLIT_GEN = prove
 (`!n P x. (!j. j < x + n ==> P j) <=>
           (!j. j < x ==> P j) /\ (!k. k < n ==> P(x + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < x` THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - x`) THEN
    SUBGOAL_THEN `x + (j - x) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* the chunk lemmas for n coefficients per iteration of a loop of 256 / n
   iterations (n a power of two), as those of mldsa_native.ml for n = 4 *)
let CHUNK_INPUT_SPLIT_N n =
  let nt = mk_small_numeral n and mt = mk_small_numeral(256 / n) in
  prove(subst [nt,`n:num`; mt,`m:num`]
   `!P i. i < m
          ==> ((!j. n * i <= j /\ j < 256 ==> P j) <=>
               (!j. n * (i + 1) <= j /\ j < 256 ==> P j) /\
               (!k. k < n ==> P(n * i + k)))`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN (subst [nt,`n:num`] `!k. k < n ==> n * i + k < 256`)
     ASSUME_TAC THENL
      [X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   GEN_REWRITE_TAC (LAND_CONV) [SPEC nt CHUNK_INPUT_SPLIT_GEN] THEN
   REWRITE_TAC[ARITH_RULE (subst [nt,`n:num`] `n * (i + 1) = n * i + n`)] THEN
   MATCH_MP_TAC(TAUT `(b <=> c) ==> (a /\ b <=> a /\ c)`) THEN
   EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `k:num` THENL
    [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[];
     STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]]);;

let CHUNK_OUTPUT_SPLIT_N n =
  let nt = mk_small_numeral n in
  prove(subst [nt,`n:num`]
   `!P i. (!j. j < n * (i + 1) ==> P j) <=>
          (!j. j < n * i ==> P j) /\ (!k. k < n ==> P(n * i + k))`,
   REWRITE_TAC[ARITH_RULE (subst [nt,`n:num`] `n * (i + 1) = n * i + n`);
               SPEC nt CHUNK_OUTPUT_SPLIT_GEN]);;

(* word_add a (word(4 * (n * i + k))) as an offset from the pointer of the
   iteration, for 32-bit coefficients *)
let CHUNK_ADDR_N n w =
  let nt = mk_small_numeral n and wt = mk_small_numeral w
  and nw = mk_small_numeral(n * w) in
  prove(subst [nt,`n:num`; wt,`w:num`; nw,`nw:num`]
   `!a i k. word_add a (word(w * (n * i + k))):int64 =
            word_add (word_add a (word(nw * i))) (word(w * k))`,
   REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
   REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* aligned 16 (word_add p (word t)) for t = c + s * i in the form of the
   simulator (t is any linear expression in i), from an assumption
   aligned 16 (word_add p (word B)), B = c mod 16 and 16 | s, as for the
   indexed SSE loads and stores of a loop over a polynomial. *)
let ALIGN16_IDX_TAC (p:term) (t:term) =
  let rec ev t =
    match t with
      Comb(Comb(Const("+",_),a),b) -> let (c1,s1) = ev a and (c2,s2) = ev b in (c1 + c2, s1 + s2)
    | Comb(Comb(Const("*",_),a),b) ->
        let (c1,s1) = ev a and (c2,s2) = ev b in
        if s1 = 0 then (c1 * c2, c1 * s2) else if s2 = 0 then (c1 * c2, s1 * c2)
        else failwith "ALIGN16_IDX_TAC: not linear"
    | Var(_,_) -> (0,1)
    | _ -> (dest_small_numeral t, 0) in
  let (c,s) = ev t in
  if s mod 16 <> 0 then failwith "ALIGN16_IDX_TAC: stride not a multiple of 16" else
  let iv = hd(frees t) in
  W(fun (asl,w) ->
    (* a base fact aligned 16 (word_add p (word B)) with B <= c, 16 | c - B *)
    let bs = mapfilter (fun (_,th) ->
      let c' = concl th in
      match c' with
        Comb(Comb(Const("aligned",_),_),Comb(Comb(Const("word_add",_),q),Comb(Const("word",_),b)))
          when q = p -> let b = dest_small_numeral b in
                        if b <= c && (c - b) mod 16 = 0 then b else failwith ""
      | _ -> failwith "") asl in
    let b = hd bs in
    let d = c - b in
    let at = mk_comb(mk_comb(`aligned:num->int64->bool`,`16`),
                     mk_comb(mk_comb(`word_add:int64->int64->int64`,p),
                             mk_comb(`word:num->int64`,t))) in
    let nb = mk_small_numeral b and nd = mk_small_numeral d
    and ns = mk_small_numeral s in
    let rest = mk_comb(mk_comb(`(+):num->num->num`,nd),
                       mk_comb(mk_comb(`(*):num->num->num`,ns),iv)) in
    SUBGOAL_THEN at ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`word_add:int64->int64->int64`,p),
                                  mk_comb(`word:num->int64`,t)),
                          mk_comb(mk_comb(`word_add:int64->int64->int64`,
                                    mk_comb(mk_comb(`word_add:int64->int64->int64`,p),
                                            mk_comb(`word:num->int64`,nb))),
                                  mk_comb(`word:num->int64`,rest))))
        SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE (mk_eq(t, mk_comb(mk_comb(`(+):num->num->num`,nb),rest)))] THEN
        CONV_TAC WORD_RULE; ALL_TAC] THEN
      MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
      ALL_TAC]);;

(* A wide read at the address as the simulator writes it (an indexed address
   with the index register word(c + s * i)), as the join of the narrower
   facts of the invariant (whose addresses are base + (s' * i + d)). *)
let MERGE_LIN_CONV_B n bases tm =
  CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                      DEPTH_CONV(fun t ->
                        if type_of t = `:num` && not(is_numeral t) && is_comb t
                        then LINEAR_ADDR_CONV_B bases t else failwith "")))
   (READ_MEMORY_MERGE_CONV n tm);;

let MERGE_LIN_CONV n base = MERGE_LIN_CONV_B n [base];;

let MERGE_LIN_TAC_B n bases tm =
  MP_TAC(MERGE_LIN_CONV_B n bases tm) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let MERGE_LIN_TAC n base tm =
  MP_TAC(MERGE_LIN_CONV n base tm) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* the same normalisation of the addresses in the goal *)
let GOAL_LINEAR_BASES_TAC bases =
  CONV_TAC(DEPTH_CONV(fun tm ->
    if type_of tm = `:num` && not(is_numeral tm) && is_comb tm
    then LINEAR_ADDR_CONV_B bases tm else failwith ""));;

(* The end of the body of iteration i of a loop over a polynomial of
   256 coefficients of w bytes, n per iteration (n a power of two), whose
   stores are wide stores that have been split into narrow facts, outputs
   j at the addresses base + w * j for the bases of bases: the invariant for
   i + 1, with the new outputs equal to the specification, which the
   tactic spec_tac proves for the expanded cases (after the rewriting of the
   goal and with the assumptions). *)
let CHUNKN_FULL_FINAL_TAC bases n ars (extra:tactic) (spec_tac:tactic) =
  ADDR_LINEAR_BASES_TAC bases THEN ADDR_NORMALIZE_TAC THEN ADDR_LINEAR_BASES_TAC bases THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC ars THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(extra THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N n] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      GOAL_LINEAR_BASES_TAC bases THEN
      ASM_REWRITE_TAC[] THEN spec_tac THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* copies of the facts about memory in the address form of the simulator:
   each pair (c, t) of numeral expressions with c = t (in i) gives, for each
   assumption mentioning c, a copy with t in place of c *)
let ALT_SIM_TAC (prs:(term*term) list) =
  W(fun (asl,w) ->
    MAP_EVERY (fun (c,t) ->
      let eq = ARITH_RULE (mk_eq(c,t)) in
      MAP_EVERY (fun (_,th) ->
        let tm = concl th in
        if is_eq tm && can (term_match [] `read (memory :> bytes32 a) s`) (lhs tm) &&
           free_in c tm
        then ASSUME_TAC(REWRITE_RULE[eq] th) else ALL_TAC) asl) prs);;

(* a byte inside a region that does not overlap another stays apart from it *)
let NONOV_OFFSET_IN = prove
 (`!op:int64 n pc sz len.
        n + 1 <= len /\ len < 2 EXP 64 /\ nonoverlapping (op,len) (pc,sz)
        ==> nonoverlapping (word_add op (word n),1) (pc,sz)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonoverlapping; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(SPECL [`2 EXP 64`; `val(op:int64)`; `len:num`; `val(pc:int64)`; `sz:num`;
                `(val(op:int64) + n MOD 2 EXP 64) MOD 2 EXP 64`; `1`;
                `val(pc:int64)`; `sz:num`] NONOVERLAPPING_MODULO_SUBREGIONS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[nonoverlapping; DIMINDEX_64] o
        check (fun th -> can (term_match [] `nonoverlapping (a,l) (b,m)`) (concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
      SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL]];
    SIMP_TAC[]]);;

(* the same in the form after NONOVERLAPPING_CLAUSES *)
let NONOV_OFFSET_IN2 = prove
 (`!op:int64 n pc sz len.
        n + 1 <= len /\ len < 2 EXP 64 /\
        nonoverlapping_modulo (2 EXP 64) (val op,len) (pc,sz)
        ==> nonoverlapping_modulo (2 EXP 64) (val(word_add op (word n):int64),1) (pc,sz)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(SPECL [`2 EXP 64`; `val(op:int64)`; `len:num`; `pc:num`; `sz:num`;
                `(val(op:int64) + n MOD 2 EXP 64) MOD 2 EXP 64`; `1`;
                `pc:num`; `sz:num`] NONOVERLAPPING_MODULO_SUBREGIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
      SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN ASM_ARITH_TAC;
      REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL]];
    SIMP_TAC[]]);;

(* CHUNK_FULL_FINAL_TAC with the rules ars (arithmetic of the increments of
   the registers) tried before WORD_RULE *)
let CHUNK_FULL_FINAL_ARS_TAC ars fdef (x:term) =
  ADDR_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC ars THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[fdef] THEN
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_DIV_256_MOD_256] THEN
      REPEAT CONJ_TAC THEN APP_BLAST_TAC x THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
(* ------------------------------------------------------------------------- *)
(* mld_polyz_unpack_c with gamma1 = 2^17 (ML-DSA-44): 9 bytes of the input a  *)
(* become 4 coefficients of 32 bits, 64 iterations of 16 bytes of output at   *)
(* rsp0 + ob. The output is addressed as [rsp + rcx + 0x10d4], the register  *)
(* RCX being rcx0 + 16 i (so ob = rcx0 + 4308), and RAX is the input pointer *)
(* a + 8 + 9 i, used at negative displacements.                              *)
(* ------------------------------------------------------------------------- *)

let UNPACKZ17_STMT fn loop exit rcx0 =
  let ob = rcx0 + 4308 in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e a rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(a,576); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\
              read RAX s = word_add a (word 8) /\\ read RCX s = word %d /\\
              (!j. j < 576 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\
              read RAX s = word_add a (word 584) /\\ read RCX s = word %d /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_polyz_unpack_17 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a rsp0 pc /\\
                 memaccess_inbounds e2 [a,576; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob image_mc fn loop rcx0 fn exit (rcx0+1024) ob ob ob ob);;

let UNPACKZ17_TAC exec fn loop exit rcx0 =
  let ob = rcx0 + 4308 in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil a rsp0 pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop a rsp0 pc i)) (f_ev_prol a rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word_add (word_add a (word(9 * i))) (word 8) /\\
          read RCX s = word(%d + 16 * i) /\\
          (!j. j < 576
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_polyz_unpack_17 b j)" rcx0 ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `b:num->byte` 9 THEN
    INPUT_ALT_ADDR_TAC `a:int64` THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes8 (word_add a (word (9 * i + 8)))) s0 = x`) (concl th) then ASSUME_TAC(REWRITE_RULE[ARITH_RULE `9 * i + 8 = 8 + 9 * i`] th) else NO_TAC) THEN
    VAL_INT64_TAC (parse_term(Printf.sprintf "%d + 16 * i" rcx0)) THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 1 `read(memory :> bytes16(word_add a (word(9 * i)))) s0`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC exec (1--46) THEN
    CHUNK_FULL_FINAL2_TAC ob [ARITH_RULE `9 * (i + 1) = 9 * i + 9`; ARITH_RULE `16 * (i + 1) = 16 * i + 16`] mld_polyz_unpack_17 `b:num->byte`;
    FULL_EXIT0_TAC];;

(* fn: the function, loop and exit: the labels of its loop; rcx0: the value of
   RCX at the head, 12 + 1024 k for the k-th polynomial of the vector. *)
let PROVE_UNPACKZ17 fn loop exit rcx0 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(UNPACKZ17_STMT fn loop exit rcx0, UNPACKZ17_TAC exec fn loop exit rcx0);;

(* ------------------------------------------------------------------------- *)
(* mld_polyt1_unpack as clang -O3 has vectorised it (SSE2): 5 bytes of the   *)
(* input a become 4 coefficients of 10 bits in 32 bits, 64 iterations; RAX   *)
(* is a + 1 + 5 i, RCX the offset 16 i of the output at rsp0 + ob. The       *)
(* constants of the multiplications and masks are in XMM3 and XMM4.          *)
(* ------------------------------------------------------------------------- *)

let UNPACKT1_STMT fn loop exit ob =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e a rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024)) [(a,320); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\
              read RAX s = word_add a (word 1) /\\ read RCX s = word 0 /\\
              read XMM2 s = word 0 /\\
              read XMM3 s = word 0x0004001000400100 /\\
              read XMM4 s = word 0xffff03f003c00300 /\\
              (!j. j < 320 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\
              read RAX s = word_add a (word 321) /\\ read RCX s = word 1024 /\\
              read XMM2 s = word 0 /\\
              read XMM3 s = word 0x0004001000400100 /\\
              read XMM4 s = word 0xffff03f003c00300 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_polyt1_unpack b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a rsp0 pc /\\
                 memaccess_inbounds e2 [a,320; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8] ,, MAYCHANGE [ZMM0; ZMM1] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob ob image_mc fn loop fn exit ob ob ob ob);;

let UNPACKT1_TAC exec fn loop exit ob =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil a rsp0 pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop a rsp0 pc i)) (f_ev_prol a rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word_add (word_add a (word(5 * i))) (word 1) /\\
          read RCX s = word(16 * i) /\\
          read XMM2 s = word 0 /\\
          read XMM3 s = word 0x0004001000400100 /\\
          read XMM4 s = word 0xffff03f003c00300 /\\
          (!j. j < 320
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_polyt1_unpack b j)" ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "top2" `YMM2` THEN XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    CHUNK_INPUT_TAC `b:num->byte` 5 THEN
    INPUT_ALT_ADDR_TAC `a:int64` THEN
    VAL_INT64_TAC `16 * i` THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "aligned 16 (word_add rsp0 (word (1 * (16 * i) + %d)):int64)" ob)) ASSUME_TAC THENL
     [SUBGOAL_THEN (parse_term(Printf.sprintf "word_add rsp0 (word (1 * (16 * i) + %d)):int64 = word_add (word_add rsp0 (word %d)) (word (16 * i))" ob ob)) SUBST1_TAC THENL
       [CONV_TAC WORD_RULE; ALL_TAC] THEN
      MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MERGE_FACT_TAC 2 `read(memory :> bytes32(word_add a (word(5 * i + 1)))) s0` `a:int64` THEN
    VERIF_SSE_STEPS_TAC exec (1--20) THEN
    X86_STEPS_TAC exec (21--24) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) && free_in `rsp0:int64` (concl th))) THEN
    CHUNK_FULL_FINAL3_TAC ob [ARITH_RULE `5 * (i + 1) = 5 * i + 5`; ARITH_RULE `16 * (i + 1) = 16 * i + 16`]
      (REWRITE_TAC[XMM2; XMM3; XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
      mld_polyt1_unpack `b:num->byte`;
    FULL_EXIT0_TAC];;

let PROVE_UNPACKT1 fn loop exit ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(UNPACKT1_STMT fn loop exit ob, UNPACKT1_TAC exec fn loop exit ob);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_sub as clang -O3 has vectorised it (SSE2): a -= b, 16 iterations *)
(* of 64 bytes with four loads, four PSUBD with a memory operand and four    *)
(* stores. RAX is the index 12 + 16 i, addressed as [rsp + rax * 4 + k]: the *)
(* operand a at rsp0 + 4 * 12 + kx, the operand b at rsp0 + 4 * 12 + ky.     *)
(* ------------------------------------------------------------------------- *)

let SUBLOOP_STMT fn loop exit kx ky =
  let ob = 48 + kx and bb = 48 + ky in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word %d)) /\\ aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 12 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 268 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_sub x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob bb ob bb image_mc fn loop ob bb fn exit ob bb ob bb ob ob);;

let SUBLOOP_TAC exec fn loop exit kx ky =
  let ob = 48 + kx and bb = 48 + ky in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_sub] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (12 + 16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. 16 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < 16 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   word_sub (x j) (y j))" bb ob ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `12 + 16 * i` THEN
    MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
        (parse_term(Printf.sprintf "4 * (12 + 16 * i) + %d" k)))
      [kx; kx + 16; kx + 32; kx + 48; ky; ky + 16; ky + 32; ky + 48] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 16) (ASSUME `i < 16`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `word_sub` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [bb; ob] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (y:num->int32)(16 * i + k)" bb)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [bb; ob] THEN
    MAP_EVERY (fun g ->
      MERGE_LIN_TAC_B 2 [bb; ob]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (12 + 16 * i) + %d)))) s0" (kx + 16 * g))) THEN
      MERGE_LIN_TAC_B 2 [bb; ob]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (12 + 16 * i) + %d)))) s0" (ky + 16 * g))))
      [0;1;2;3] THEN
    VERIF_SSE_STEPS_TAC exec (1--12) THEN X86_STEPS_TAC exec (13--15) THEN
    MAP_EVERY (fun g ->
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
                         free_in (parse_term(Printf.sprintf "4 * (12 + 16 * i) + %d" (kx + 16 * g))) (concl th) &&
                         free_in `word_sub:int32->int32->int32` (concl th)))) [0;1;2;3] THEN
    CHUNKN_FULL_FINAL_TAC [bb; ob] 16
      [ARITH_RULE `16 * (i + 1) = 16 * i + 16`; ARITH_RULE `12 + 16 * (i + 1) = 12 + 16 * i + 16`] ALL_TAC ALL_TAC;
    FULL_EXIT0_TAC];;

let PROVE_SUBLOOP fn loop exit kx ky =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(SUBLOOP_STMT fn loop exit kx ky, SUBLOOP_TAC exec fn loop exit kx ky);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_add as clang -O3 has vectorised it (SSE2): y += x, 16 iterations *)
(* of 64 bytes with four loads of x, four PADDD with a memory operand of y   *)
(* and four stores to y. RAX is the index r0 + 16 i, addressed as [rsp + rax *)
(* * 4 + k]: x at rsp0 + 4 * r0 + kx, y at rsp0 + 4 * r0 + ky.               *)
(* ------------------------------------------------------------------------- *)

let ADDLOOPG_STMT fn loop exit kx ky r0 =
  let ob = 4 * r0 + kx and bb = 4 * r0 + ky in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word %d)) /\\ aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_add y x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob bb bb ob image_mc fn loop r0 ob bb fn exit (r0 + 256) ob bb ob bb bb bb);;

let ADDLOOPG_TAC exec fn loop exit kx ky r0 =
  let ob = 4 * r0 + kx and bb = 4 * r0 + ky in
  let idx = if r0 = 0 then "16 * i" else Printf.sprintf "%d + 16 * i" r0 in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_add] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (%s) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. 16 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. j < 16 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   word_add (y j) (x j))" idx ob bb bb)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC (parse_term idx) THEN
    MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
        (parse_term(Printf.sprintf "4 * (%s) + %d" idx k)))
      [kx; kx + 16; kx + 32; kx + 48; ky; ky + 16; ky + 32; ky + 48] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 16) (ASSUME `i < 16`)] o
      check (fun th -> free_in `y:num->int32` (concl th) && not(free_in `word_add:int32->int32->int32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [bb; ob] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (x:num->int32)(16 * i + k)" ob)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [bb; ob] THEN
    MAP_EVERY (fun g ->
      MERGE_LIN_TAC_B 2 [bb; ob]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (%s) + %d)))) s0" idx (kx + 16 * g))) THEN
      MERGE_LIN_TAC_B 2 [bb; ob]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (%s) + %d)))) s0" idx (ky + 16 * g))))
      [0;1;2;3] THEN
    VERIF_SSE_STEPS_TAC exec (1--12) THEN X86_STEPS_TAC exec (13--15) THEN
    MAP_EVERY (fun g ->
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
                         free_in (parse_term(Printf.sprintf "4 * (%s) + %d" idx (ky + 16 * g))) (concl th) &&
                         free_in `word_add:int32->int32->int32` (concl th)))) [0;1;2;3] THEN
    CHUNKN_FULL_FINAL_TAC [bb; ob] 16
      [ARITH_RULE `16 * (i + 1) = 16 * i + 16`; ARITH_RULE (parse_term(Printf.sprintf "%d + 16 * (i + 1) = %d + 16 * i + 16" r0 r0))]
      ALL_TAC (REWRITE_TAC[WORD_ADD_SYM]);
    FULL_EXIT0_TAC];;

let PROVE_ADDLOOPG fn loop exit kx ky r0 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ADDLOOPG_STMT fn loop exit kx ky r0, ADDLOOPG_TAC exec fn loop exit kx ky r0);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_caddq (a + q if a is negative) on the polynomial at rsp0 + ob, in *)
(* 256 iterations of one coefficient, addressed as [rsp + rax * 4 + d], RAX  *)
(* being r0 + i and d = ob - 4 * r0 (r0 = 0 in verify_internal, 256 k for    *)
(* the k-th polynomial of a vector in signature_internal).                   *)
(* ------------------------------------------------------------------------- *)

let CADDQ_LANE_TAC =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if can (term_match [] `read (memory :> bytes32 a) s`) l &&
       free_in `x:num->int32` r then
      let v = `(x:num->int32) i` and y = genvar `:int32` in
      let lemma = prove
       (mk_forall(y,mk_eq(subst[y,v] r,mk_comb(`mld_caddq`,y))),
        GEN_TAC THEN REWRITE_TAC[mld_caddq; GSYM MSB_IVAL; DIMINDEX_32] THEN
        CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC) in
      ASSUME_TAC(REWRITE_RULE[lemma] th)
    else NO_TAC);;

let CADDQG_STMT fn loop exit ob r0 =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024)) [(word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_caddq x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024] [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob image_mc fn loop r0 ob fn exit (r0 + 256) ob ob ob ob);;

(* RAX is r0 + i, the displacement of the addressing mode ob - 4 * r0 *)
let CADDQG_TAC exec fn loop exit ob r0 nsteps =
  let idx = if r0 = 0 then "i:num" else Printf.sprintf "%d + i" r0 in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_caddq] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (%s) /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = mld_caddq (x j))" idx ob ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_caddq` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    VAL_INT64_TAC (parse_term idx) THEN
    ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%d + 4 * i = 4 * (%s) + %d" ob idx (ob - 4 * r0)))]
      (ASSUME (parse_term(Printf.sprintf "read(memory :> bytes32(word_add rsp0 (word(%d + 4 * i)))) s0 = (x:num->int32) i" ob)))) THEN
    X86_STEPS_TAC exec (1--(nsteps - 3)) THEN
    CADDQ_LANE_TAC THEN
    X86_STEPS_TAC exec ((nsteps - 2)--nsteps) THEN
    ADDR_LINEAR_BASES_TAC [ob] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FULL_EXIT0_TAC];;

let PROVE_CADDQG fn loop exit ob r0 nsteps =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(CADDQG_STMT fn loop exit ob r0, CADDQG_TAC exec fn loop exit ob r0 nsteps);;

(* The loops of verify_internal start with RAX = 0. *)
let CADDQ_STMT fn loop exit ob = CADDQG_STMT fn loop exit ob 0;;
let CADDQ_TAC exec fn loop exit ob nsteps = CADDQG_TAC exec fn loop exit ob 0 nsteps;;
let PROVE_CADDQ fn loop exit ob nsteps = PROVE_CADDQG fn loop exit ob 0 nsteps;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_pointwise_montgomery of x (at rsp0 + dx + 4 r0) by y (at rsp0 +  *)
(* dy + 4 r0), in place in x: 128 iterations of two coefficients, with the   *)
(* index RAX = r0 + 2 i (r0 = 1 or 0), addressed as [rsp + rax * 4 + dx] and *)
(* [rsp + rax * 4 + dy] (and + 4 for the second coefficient), the constant   *)
(* q^-1 * 2^32 in R12 and the Montgomery reduction by IMUL, SAR, IMUL by -q, *)
(* ADD, SHR.                                                                 *)
(* ------------------------------------------------------------------------- *)

let PWM_MONTRED_CLANG = prove
 (`!p:int64.
     word_zx(word_ushr
       (word_add (word_mul (word_ishr (word_mul p (word 252236767799803904)) 32)
                           (word 18446744073701171199)) p) 32):int32 =
     mld_montgomery_reduce p`,
  GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_ishr (word_mul p (word 252236767799803904)) 32:int64 =
    word_sx (word_mul (word_zx p:int32) (word 58728449))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `word_mul p (word 252236767799803904):int64 =
                  word_shl (word_mul p (word 58728449)) 32` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `word_mul (word_zx p:int32) (word 58728449) =
                  word_zx (word_mul p (word 58728449):int64)` SUBST1_TAC THENL
     [SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
      REWRITE_TAC[WORD_BLAST `word_zx (word 58728449:int64):int32 = word 58728449`];
      ALL_TAC] THEN
    SPEC_TAC(`word_mul p (word 58728449):int64`,`u:int64`) THEN
    GEN_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_ushr (v:int64) 32):int32 = word_subword v (32,32)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_BLAST `word 18446744073701171199:int64 = word_neg(word 8380417)`] THEN
  CONV_TAC WORD_RULE);;

let PWM_MONTRED_CLANG2 = prove
 (`!a b:int64.
     word_zx(word_ushr
       (word_add (word_mul (word_ishr (word_mul (word_mul a b) (word 252236767799803904)) 32)
                           (word 18446744073701171199)) (word_mul a b)) 32):int32 =
     mld_montgomery_reduce (word_mul b a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PWM_MONTRED_CLANG; WORD_MUL_SYM]);;

let PWMLOOPG_STMT fn loop exit dx dy r0 =
  let ob = dx + 4 * r0 and bb = dy + 4 * r0 in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\ read R12 s = word 0x0380200100000000 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\ read R12 s = word 0x0380200100000000 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_pointwise_montgomery x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob bb image_mc fn loop r0 ob bb fn exit (r0 + 256) ob bb ob bb ob ob);;

let PWMLOOPG_TAC exec fn loop exit dx dy r0 =
  let ob = dx + 4 * r0 and bb = dy + 4 * r0 in
  let idx = if r0 = 0 then "2 * i" else Printf.sprintf "%d + 2 * i" r0 in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 128 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_pointwise_montgomery] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
          read RAX s = word (%s) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. 2 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < 2 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_montgomery_reduce (word_mul (word_sx (x j)) (word_sx (y j))))" idx bb ob ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC (parse_term idx) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 2) (ASSUME `i < 128`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `mld_montgomery_reduce` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [ob; bb] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 2 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (2 * i + k))))) s0 = (y:num->int32)(2 * i + k)" bb)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [ob; bb] THEN
    ALT_SIM_TAC
     (map (fun (c,t) -> (parse_term c, parse_term t))
        [Printf.sprintf "%d + 8 * i" ob, Printf.sprintf "4 * (%s) + %d" idx dx;
         Printf.sprintf "%d + (8 * i + 4)" ob, Printf.sprintf "4 * (%s) + %d" idx (dx + 4);
         Printf.sprintf "%d + 8 * i" bb, Printf.sprintf "4 * (%s) + %d" idx dy;
         Printf.sprintf "%d + (8 * i + 4)" bb, Printf.sprintf "4 * (%s) + %d" idx (dy + 4)]) THEN
    X86_STEPS_TAC exec (1--10) THEN RULE_ASSUM_TAC(REWRITE_RULE[PWM_MONTRED_CLANG2]) THEN
    X86_STEPS_TAC exec (11--20) THEN RULE_ASSUM_TAC(REWRITE_RULE[PWM_MONTRED_CLANG2]) THEN
    X86_STEPS_TAC exec (21--23) THEN
    CHUNKN_FULL_FINAL_TAC [ob; bb] 2
      [ARITH_RULE `2 * (i + 1) = 2 * i + 2`; ARITH_RULE (parse_term(Printf.sprintf "%d + 2 * (i + 1) = %d + 2 * i + 2" r0 r0))] ALL_TAC ALL_TAC;
    FULL_EXIT0_TAC];;

let PROVE_PWMLOOPG fn loop exit dx dy r0 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(PWMLOOPG_STMT fn loop exit dx dy r0, PWMLOOPG_TAC exec fn loop exit dx dy r0);;

(* The loops of verify_internal start with RAX = 1. *)
let PWMLOOP_STMT fn loop exit dx dy = PWMLOOPG_STMT fn loop exit dx dy 1;;
let PWMLOOP_TAC exec fn loop exit dx dy = PWMLOOPG_TAC exec fn loop exit dx dy 1;;
let PROVE_PWMLOOP fn loop exit dx dy = PROVE_PWMLOOPG fn loop exit dx dy 1;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_reduce on the polynomial at rsp0 + ob as clang -O3 has vectorised *)
(* it (SSE2): 32 iterations of 8 coefficients, two 128-bit words, with        *)
(* PADDD, PSRAD, and the products by -q of the even and odd lanes by PMULUDQ  *)
(* and PSHUFD, RAX being the index 4 + 8 i addressed as [rsp + rax * 4 + k]   *)
(* (k = ob - 16), with 2^22 in XMM5 and -q in XMM6.                           *)
(* ------------------------------------------------------------------------- *)

(* A lane of the vectorised reduction, as the simulation gives it: the     *)
(* quotient t (ival(x + 2^22) >> 23) times -q in the low 32 bits of a 64-bit *)
(* product (PMULUDQ), added to x. It is mld_reduce32 x, by the arithmetic of *)
(* the low half of the product, without bit-blasting the product.            *)

let REDUCE32_SUBWORD_MUL = prove
 (`!t:int32 c. word_subword (word_mul (word_zx t:int64) (word c)) (0,32) =
               word_mul t (word c):int32`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1; ARITH_RULE `18446744073709551616 = 4294967296 * 4294967296`;
              MOD_MOD] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  CONV_TAC(BINOP_CONV(ONCE_REWRITE_CONV[GSYM MOD_MULT_MOD2])) THEN
  REWRITE_TAC[MOD_MOD; MOD_MOD_REFL]);;

let REDUCE32_LANE_SSE = prove
 (`!y:int32.
     word_add
      (word_subword
        (word_mul (word_zx (word_ishr (word_add y (word 4194304)) 23):int64)
                  (word 4286586879))
        (0,32))
      y = mld_reduce32 y`,
  GEN_TAC THEN REWRITE_TAC[mld_reduce32; REDUCE32_SUBWORD_MUL] THEN
  SUBGOAL_THEN `word 4286586879:int32 = word_neg(word 8380417)` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; CONV_TAC WORD_RULE]);;

let xmm_def n = match n with 5 -> XMM5 | 6 -> XMM6 | 7 -> XMM7 | _ -> failwith "xmm_def";;

let REDLOOPX_STMT fn loop exit k r0 xa xb =
  let ob = k + 16 + 4 * (r0 - 4) in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024)) [(word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              read XMM%d s = word 0x00400000004000000040000000400000 /\\
              read XMM%d s = word 0xff801fffff801fffff801fffff801fff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              read XMM%d s = word 0x00400000004000000040000000400000 /\\
              read XMM%d s = word 0xff801fffff801fffff801fffff801fff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_reduce x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024] [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob ob image_mc fn loop r0 xa xb ob fn exit (r0 + 256) xa xb ob ob ob ob);;

let REDLOOPX_TAC exec fn loop exit k r0 xa xb =
  let ob = k + 16 + 4 * (r0 - 4) in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_reduce] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (%d + 8 * i) /\\
          read XMM%d s = word 0x00400000004000000040000000400000 /\\
          read XMM%d s = word 0xff801fffff801fffff801fffff801fff /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = mld_reduce32 (x j))" r0 xa xb ob ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "topa" (mk_const(Printf.sprintf "YMM%d" xa,[])) THEN
    XMM_EXISTSTOP_TAC "topb" (mk_const(Printf.sprintf "YMM%d" xb,[])) THEN
    VAL_INT64_TAC (parse_term(Printf.sprintf "%d + 8 * i" r0)) THEN
    MAP_EVERY (fun g -> ALIGN16_IDX_TAC `rsp0:int64`
        (parse_term(Printf.sprintf "4 * (%d + 8 * i) + %d" r0 (k + 16 * g)))) [0;1] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 8) (ASSUME `i < 32`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `mld_reduce32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [ob] THEN
    MAP_EVERY (fun g ->
      MERGE_LIN_TAC_B 2 [ob]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (%d + 8 * i) + %d)))) s0" r0 (k + 16 * g)))) [0;1] THEN
    VERIF_SSE_STEPS_TAC exec (1--24) THEN X86_STEPS_TAC exec (25--27) THEN
    MAP_EVERY (fun g ->
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
                         free_in (parse_term(Printf.sprintf "4 * (%d + 8 * i) + %d" r0 (k + 16 * g))) (concl th)))) [0;1] THEN
    CHUNKN_FULL_FINAL_TAC [ob] 8
      [ARITH_RULE `8 * (i + 1) = 8 * i + 8`; ARITH_RULE (parse_term(Printf.sprintf "%d + 8 * (i + 1) = %d + 8 * i + 8" r0 r0))]
      (REWRITE_TAC[xmm_def xa; xmm_def xb; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
      (REWRITE_TAC[REDUCE32_LANE_SSE]);
    FULL_EXIT0_TAC];;

let PROVE_REDLOOPX fn loop exit k r0 xa xb =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(REDLOOPX_STMT fn loop exit k r0 xa xb, REDLOOPX_TAC exec fn loop exit k r0 xa xb);;

let REDLOOPG_STMT fn loop exit k r0 = REDLOOPX_STMT fn loop exit k r0 5 6;;
let REDLOOPG_TAC exec fn loop exit k r0 = REDLOOPX_TAC exec fn loop exit k r0 5 6;;
let PROVE_REDLOOPG fn loop exit k r0 = PROVE_REDLOOPX fn loop exit k r0 5 6;;

(* The loops of verify_internal start with RAX = 4. *)
let REDLOOP_STMT fn loop exit k = REDLOOPG_STMT fn loop exit k 4;;
let REDLOOP_TAC exec fn loop exit k = REDLOOPG_TAC exec fn loop exit k 4;;
let PROVE_REDLOOP fn loop exit k = PROVE_REDLOOPG fn loop exit k 4;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_shiftl (multiplication by 2^13) of the polynomial at rsp0 + ob,   *)
(* which clang -O3 has vectorised (PSLLD) and unrolled completely: 192      *)
(* instructions from the label start (at the offset len from the start of    *)
(* the loop it follows).                                                     *)
(* ------------------------------------------------------------------------- *)

let SHL13 = WORD_BLAST `word_shl (x:int32) 13 = word_mul x (word 8192)`;;

let SHIFTL_STMT fn start ob =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024)) [(word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + (%s_%s + 1472)) /\\
              read RSP s = rsp0 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_shiftl x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024] [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob ob image_mc fn start ob fn start ob ob ob ob);;

let SHIFTL_TAC exec ob =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num). f_ev_all rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_shiftl] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  FULL_INIT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) && free_in `x:num->int32` (concl th) &&
                                          not(free_in `word_mul` (concl th)))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC THEN
  MAP_EVERY (fun g ->
    MERGE_FACT_TAC 2 (parse_term(Printf.sprintf "read(memory :> bytes128(word_add (rsp0:int64) (word %d))) s0" (ob + 16 * g))) `rsp0:int64`)
    (0--63) THEN
  VERIF_SSE_STEPS_TAC exec (1--192) THEN
  MAP_EVERY (fun g ->
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
                       free_in (parse_term(Printf.sprintf "word_add (rsp0:int64) (word %d)" (ob + 16 * g))) (concl th) &&
                       free_in `word_shl:int32->num->int32` (concl th)))) (0--63) THEN
  ADDR_NORMALIZE_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[SHL13];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_SHIFTL fn start ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^start), layout (fn^"_"^start) + 1472)] in
  prove(SHIFTL_STMT fn start ob, SHIFTL_TAC exec ob);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_use_hint (gamma2 = (q - 1) / 88) as clang -O3 has inlined it: one *)
(* coefficient per iteration, in place, a[i] := use_hint(a[i], h[i]), with    *)
(* a at rsp0 + ob (4 * RAX + ob) and h at rsp0 + hb, and three paths (hint    *)
(* zero, low part positive, otherwise) that join at the store. The loop is    *)
(* entered at its first load, join11 in the code of verify_internal, with     *)
(* RAX = 0, R8 = 0 and R9 = 43, and left after the test of RAX at join12; the *)
(* code from join9 to join12 is that of the loop.                            *)
(* ------------------------------------------------------------------------- *)

let USEHINT88_STMT fn first head0 exit ob hb =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 0 /\\ read R8 s = word 0 /\\ read R9 s = word 43 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 256 /\\ read R8 s = word 0 /\\ read R9 s = word 43 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_use_hint_88 x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc x y /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RDX; RSI; RDI; R10] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob hb image_mc fn first ob hb fn exit ob hb ob hb ob ob);;

let USEHINT88_TAC exec fn first exit ob hb =
  let path_end addr =
    SCALAR_LANE2_TAC addr `(x:num->int32) i` `(y:num->int32) i` `mld_use_hint_88` [mld_use_hint_88] THEN
    ADDR_LINEAR_BASES_TAC [hb; ob] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    PATH_DISCHARGE_TAC in
  let addr = parse_term(Printf.sprintf "word_add (rsp0:int64) (word (4 * i + %d))" ob) in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num) (x:num->int32) (y:num->int32).
      APPEND (f_ev_epil rsp0 pc x y)
       (APPEND (ENUMERATEL 256
          (\i. if y i = word 0 then f_ev_zero rsp0 pc x y i
               else if &0 < ival(mld_decompose_lo_88 (x i)) then f_ev_pos rsp0 pc x y i
               else f_ev_neg rsp0 pc x y i))
          (f_ev_prol rsp0 pc x y))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_use_hint_88] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term(Printf.sprintf "pc + %s_%s" fn first))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ read RAX s = word i /\\ read R8 s = word 0 /\\ read R9 s = word 43 /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = mld_use_hint_88 (x j) (y j))" hb ob ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) && free_in `x:num->int32` (concl th) &&
        not(free_in `mld_use_hint_88` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < 256`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) && free_in `y:num->int32` (concl th) &&
        not(free_in `x:num->int32` (concl th)))) THEN DISCH_TAC THEN
    ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%d + 4 * i = 4 * i + %d" ob ob))]
      (ASSUME (parse_term(Printf.sprintf "read(memory :> bytes32(word_add rsp0 (word(%d + 4 * i)))) s0 = (x:num->int32) i" ob)))) THEN
    ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%d + 4 * i = 4 * i + %d" hb hb))]
      (ASSUME (parse_term(Printf.sprintf "read(memory :> bytes32(word_add rsp0 (word(%d + 4 * i)))) s0 = (y:num->int32) i" hb)))) THEN
    X86_STEPS_TAC exec (1--13) THEN
    REG_LANE_TAC `R10` `(x:num->int32) i` `mld_decompose_hi_88` [mld_decompose_hi_88; mld_ct_sel] THEN
    X86_STEPS_TAC exec (14--21) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN BRANCH_CASES_TAC THENL
     [X86_STEPS_TAC exec (22--25) THEN path_end addr;
      X86_STEPS_TAC exec (22--25) THEN
      REG32_LANE_TAC `RDI` `(x:num->int32) i` `mld_decompose_lo_88` [DECOMPOSE_LO_88_ALT; mld_ct_sel] THEN
      X86_STEPS_TAC exec (26--26) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[USE_HINT_GT_COND]) THEN BRANCH_CASES_TAC THENL
       [X86_STEPS_TAC exec (27--34) THEN path_end addr;
        X86_STEPS_TAC exec (27--33) THEN path_end addr]];
    FULL_EXIT0_TAC];;

let PROVE_USEHINT88 fn first exit ob hb join9 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^join9), layout (fn^"_"^exit))] in
  prove(USEHINT88_STMT fn first first exit ob hb, USEHINT88_TAC exec fn first exit ob hb);;
