(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa44_verify_internal,             *)
(* mldsa65_verify_internal and mldsa87_verify_internal (sign.c), with those  *)
(* of mldsa_native_top.ml: the inline copies of c~ and of mu as              *)
(* 128-bit chunks, and the reduction of the vectorized constant-time         *)
(* comparison of c~ with its recomputation.                                  *)
(* ========================================================================= *)

needs "common/fips202/properties/keccak_fips202.ml";;
needs "common/fips204/properties/mldsa_native_top.ml";;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows stops after the first row whose hints do not       *)
(* unpack: with P i for the success of row i, the code runs the rows below   *)
(* k = n if all n rows succeed, and k = m + 1 for the first failing row m    *)
(* otherwise. For a row i < k, the rows before it succeed, i < n, and the    *)
(* loop goes on after it exactly if it succeeds and i + 1 < n (and if it     *)
(* succeeds and i + 1 = n, all rows succeed).                                *)
(* ------------------------------------------------------------------------- *)

let VERIF_ROWS = prove
 (`!(P:num->bool) n i.
     i < (if (!i. i < n ==> P i) then n else (minimal i. ~P i) + 1)
     ==> (!j. j < i ==> P j) /\ i < n /\
         (P i ==> (i + 1 < (if (!i. i < n ==> P i) then n
                            else (minimal i. ~P i) + 1) <=> i + 1 < n) /\
                  (~(i + 1 < n) ==> !i. i < n ==> P i)) /\
         (~P i ==> ~(i + 1 < (if (!i. i < n ==> P i) then n
                              else (minimal i. ~P i) + 1)) /\
                   ~(!i. i < n ==> P i))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `!i. i < n ==> (P:num->bool) i` THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_TAC `i0:num`) THEN
  MP_TAC(fst(EQ_IMP_RULE(BETA_RULE(ISPEC `\i. ~(P:num->bool) i` MINIMAL)))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m = minimal i. ~(P:num->bool) i` THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `m < n:num` ASSUME_TAC THENL
   [ASM_CASES_TAC `i0 < m:num` THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    DISCH_TAC THEN SUBGOAL_THEN `~(i = m:num)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_ARITH_TAC];
    DISCH_TAC THEN SUBGOAL_THEN `i = m:num` SUBST1_TAC THENL
     [ASM_CASES_TAC `i < m:num` THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
      ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Byte k of the packing of row i of w1', for the packing of ML-DSA-65 and   *)
(* ML-DSA-87 (4 bits per coefficient), is the packing of the row.            *)
(* ------------------------------------------------------------------------- *)

let VERIF_POLYW1_PACK_32_LOCAL = prove
 (`!(a:num->int32) b j.
        (!i. i < 256 ==> a i = b i) /\ j < 128
        ==> mld_polyw1_pack_32 a j = mld_polyw1_pack_32 b j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyw1_pack_32] THEN
  SUBGOAL_THEN `(a:num->int32)(2 * j) = b(2 * j) /\
                a(2 * j + 1) = b(2 * j + 1)`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let VERIF_W1B_ROW_32 = prove
 (`!l usehint rho zhat cphat (pk:num->byte) omega (hb:num->byte) i k.
     k < 128
     ==> mld_polyvec_pack 128 mld_polyw1_pack_32
           (mld_polyvec (mld_verify_w1 l usehint rho zhat cphat pk omega hb))
           (128 * i + k) =
         mld_polyw1_pack_32
          (mld_verify_w1 l usehint rho zhat cphat pk omega hb i) k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_POLYVEC_PACK_COEFF] THEN
  MATCH_MP_TAC VERIF_POLYW1_PACK_32_LOCAL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC]);;

(*** The same for the packing of ML-DSA-44 (6 bits per coefficient) ***)

let VERIF_POLYW1_PACK_88_LOCAL = prove
 (`!(a:num->int32) b j.
        (!i. i < 256 ==> a i = b i) /\ j < 192
        ==> mld_polyw1_pack_88 a j = mld_polyw1_pack_88 b j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyw1_pack_88] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!m. m < 4 ==> (a:num->int32)(4 * j DIV 3 + m) =
                              b(4 * j DIV 3 + m)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `j DIV 3 < 64` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let VERIF_W1B_ROW_88 = prove
 (`!l usehint rho zhat cphat (pk:num->byte) omega (hb:num->byte) i k.
     k < 192
     ==> mld_polyvec_pack 192 mld_polyw1_pack_88
           (mld_polyvec (mld_verify_w1 l usehint rho zhat cphat pk omega hb))
           (192 * i + k) =
         mld_polyw1_pack_88
          (mld_verify_w1 l usehint rho zhat cphat pk omega hb i) k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_POLYVEC_PACK_COEFF] THEN
  MATCH_MP_TAC VERIF_POLYW1_PACK_88_LOCAL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the FULL proofs of verify_internal.                           *)
(*                                                                           *)
(* VERIF_FILTER_ASM_TAC keep drops the assumptions whose conclusions do not  *)
(* satisfy keep (a weakening), VERIF_EVENTS_ONLY_TAC those about a state and *)
(* the theorems of the callees (before the events are discharged), and       *)
(* VERIF_DROP_MEM_TAC keep those about memory not satisfying keep.           *)
(* ------------------------------------------------------------------------- *)

let VERIF_FILTER_ASM_TAC keep : tactic =
  fun (asl,w) -> ALL_TAC (filter (fun (_,th) -> keep(concl th)) asl,w);;

let VERIF_PTR_SUB = prove
 (`!x:int64 a b. word_sub (word_add x a) (word_add x b) = word_sub a b`,
  CONV_TAC WORD_RULE);;

let VERIF_MP_CASE_TAC c =
  RULE_ASSUM_TAC(fun th ->
    if is_imp(concl th) && lhand(concl th) = c then MP th (ASSUME c) else th);;

(*** The goal from the assumption c and a conjunct c ==> goal of another ***)

let VERIF_IMP_CASE_TAC c =
  FIRST_ASSUM(fun cth -> if concl cth <> c then NO_TAC else
    FIRST_ASSUM(fun th ->
      FIRST(map (fun ith ->
        if is_imp(concl ith) && lhand(concl ith) = c
        then ACCEPT_TAC(MP ith cth) else NO_TAC) (CONJUNCTS th))));;

(* ------------------------------------------------------------------------- *)
(* The events of a segment whose precondition fixes the events so far as     *)
(* e2 = OLD. VERIF_GEN_TAIL_TAC whole generalizes OLD (whole) or its part    *)
(* after the ENUMERATEL of a loop to a variable, with the name given, so     *)
(* that the simulation keeps it opaque. VERIF_FINAL_TAC ths is               *)
(* ENSURES_FINAL_STATE_TAC and the rewriting of the final state with the     *)
(* assumptions and ths, except the equation of e2. VERIF_EVENTS_TAC olds     *)
(* then picks the paths of conditionals of the template by the case          *)
(* assumptions, unifies the events with the template (with e2 expanded       *)
(* there only), and proves memaccess_inbounds, split along the lists that    *)
(* contain one of the variables olds (or an ENUMERATEL), so that those       *)
(* pieces are proved by the memaccess_inbounds fact of e2.                   *)
(* ------------------------------------------------------------------------- *)

let VERIF_GEN_TAIL_TAC whole name =
  W(fun (asl,w) ->
    let pre = rand(rator(rator w)) in
    let t = find_term (fun t ->
      is_comb t &&
      (try fst(dest_const(fst(strip_comb t))) = "APPEND" with _ -> false) &&
      (try fst(dest_const(fst(strip_comb(hd(snd(strip_comb t)))))) =
           "ENUMERATEL" with _ -> false)) pre in
    let x = if whole then t else rand t in
    SPEC_TAC(x,mk_var(name,type_of x)) THEN GEN_TAC);;

let VERIF_IS_E2_EQ th =
  let c = concl th in is_eq c && is_var(lhs c) && name_of(lhs c) = "e2";;

let VERIF_FINAL_TAC ths =
  ENSURES_FINAL_STATE_TAC THEN
  FIRST_X_ASSUM(fun eqth ->
    if VERIF_IS_E2_EQ eqth then ASM_REWRITE_TAC ths THEN ASSUME_TAC eqth
    else NO_TAC);;

let VERIF_HAS_OLD olds tm =
  exists (fun v -> free_in v tm) olds ||
  can (find_term (fun t -> is_const t && fst(dest_const t) = "ENUMERATEL"))
      tm;;

(* ------------------------------------------------------------------------- *)
(* The events e2 of a postcondition as a metavariable with a name of its own *)
(* (as PFS_META_EXISTS_TAC of the pk_from_sk proofs): META_EXISTS_TAC picks  *)
(* a primed name that is only fresh in its own goal, which can be the name   *)
(* of the events of a call on another path of the proof, so that its         *)
(* instantiation would also replace that variable there (and the composed    *)
(* justification fails with ABS). VERIF_DISCHARGE_TAC and                    *)
(* VERIF_H_DISCHARGE_TAC are DISCHARGE_SAFETY_PROPERTY_TAC and               *)
(* MLD_H_DISCHARGE_TAC with it.                                              *)
(* ------------------------------------------------------------------------- *)

(* Atomic, for proofs on several domains (see common/par.ml) *)
let verif_meta_count = par_counter ();;

let VERIF_META_EXISTS_TAC (asl,w) =
  let v = fst(dest_exists w) in
  let k = 1 + verif_meta_count () in
  let v' = mk_var("verif_" ^ fst(dest_var v) ^ "_" ^
                  string_of_int k,type_of v) in
  (CONV_TAC(GEN_ALPHA_CONV v') THEN SAFE_META_EXISTS_TAC allowed_vars_e)
  (asl,w);;

let VERIF_DISCHARGE_TAC =
  VERIF_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let VERIF_H_DISCHARGE_TAC =
  VERIF_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;
