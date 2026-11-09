(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa44_verify_internal,             *)
(* mldsa65_verify_internal and mldsa87_verify_internal (sign.c), with those  *)
(* of utils/mldsa_native_top.ml: the inline copies of c~ and of mu as        *)
(* 128-bit chunks, and the reduction of the vectorized constant-time         *)
(* comparison of c~ with its recomputation.                                  *)
(* ========================================================================= *)

needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;

(* ------------------------------------------------------------------------- *)
(* Bytes in memory from consecutive 128-bit chunks: those of a byte function *)
(* (mld_chunk128), and those of a number.                                    *)
(* ------------------------------------------------------------------------- *)

let VERIF_BYTES_OF_CHUNKS = prove
 (`!(a:int64) (f:num->byte) n s.
        (!i. i < n
             ==> read (memory :> bytes128(word_add a (word(16 * i)))) s =
                 mld_chunk128 f i)
        ==> read (memory :> bytes(a,16 * n)) s =
            num_of_bytelist(list_of_seq f (16 * n))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; num_of_bytelist;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  X_GEN_TAC `s:armstate` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[VAL_MLD_CHUNK128; BYTES128_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * SUC n = 16 * n + 16`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ_ADD_GEN; NUM_OF_BYTELIST_APPEND;
                  LENGTH_LIST_OF_SEQ]);;

let VERIF_BYTES128_OF_BYTES = prove
 (`!(a:int64) k x n s.
        read (memory :> bytes(a,k)) s = x /\ 16 * n + 16 <= k
        ==> read (memory :> bytes128(word_add a (word(16 * n)))) s =
            word((x DIV 2 EXP (128 * n)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    ASSUME_TAC) THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_READ_WBYTES; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `128 * n = 8 * 16 * n`;
              ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (k - 16 * n) 16 = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC]);;

let VERIF_BYTES_OF_BYTES128 = prove
 (`!(a:int64) x n s.
        (!i. i < n
             ==> read (memory :> bytes128(word_add a (word(16 * i)))) s =
                 word((x DIV 2 EXP (128 * i)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * n)) s = x MOD 2 EXP (128 * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  X_GEN_TAC `s:armstate` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * SUC n = 16 * n + 16`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 16 * n = 128 * n`] THEN
  REWRITE_TAC[ARITH_RULE `128 * SUC n = 128 * n + 128`; EXP_ADD;
              MOD_MULT_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

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

let VERIF_EVENTS_ONLY_TAC =
  VERIF_FILTER_ASM_TAC (fun c ->
    not(exists (fun v -> type_of v = `:armstate`) (frees c)) &&
    not(can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures"))
            c));;

let VERIF_IS_MEM_FACT c =
  let c = snd(strip_forall c) in
  let c = if is_imp c then rand c else c in
  is_eq c &&
  (try let l = lhand c in
       fst(dest_const(rator(rator l))) = "read" &&
       (match rand(rator l) with
          Comb(Comb(Const(":>",_),Const("memory",_)),_) -> true
        | _ -> false)
   with Failure _ -> false);;

let VERIF_DROP_MEM_TAC keep =
  VERIF_FILTER_ASM_TAC (fun c -> not(VERIF_IS_MEM_FACT c) || keep c);;

(*** The facts that the cleanup at the end of the code needs: those about
 *** the GOT, the guard, (ea,el), and the stack at offsets lo..hi or n0 ***)

let VERIF_KEEP_FRAME lo hi n0 c =
  try let l = lhand c in
      let comp = rand(rator l) in
      let a = rand(rand comp) in
      let a = if is_pair a then fst(dest_pair a) else a in
      if a = `guard:int64` || a = `ea:int64` then true
      else if can (term_match [] `word_add (word pc) (word n):int64`) a
      then true
      else if can (term_match [] `word_add stackpointer (word n):int64`) a
      then let n = dest_small_numeral(rand(rand a)) in
           (lo <= n && n <= hi) || n = n0
      else false
  with Failure _ -> false;;

(* ------------------------------------------------------------------------- *)
(* VERIF_PC_TAC cs resolves a conditional PC after a branch on the case      *)
(* conditions cs (assumed or refuted), VERIF_PTR_PC_TAC one after a test of  *)
(* the difference of two offsets of a pointer, VERIF_REG_RULE_TAC ths        *)
(* rewrites only the facts about registers, and VERIF_MP_CASE_TAC c applies  *)
(* every implication with antecedent c to the assumption c (each assumption  *)
(* c that it uses must be one of the goal, as VERIF_IMP_CASE_TAC c needs).   *)
(* ------------------------------------------------------------------------- *)

let VERIF_PC_TAC cs =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if mem c cs || (is_neg c && mem (rand c) cs) then th else fail()) asl in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = (if b then x else y):int64`)
             (concl th)
      then REWRITE_RULE(WORD_ZX_ZX_32_64_32::VAL_EQ_0::ths) th else th));;

let VERIF_PTR_SUB = prove
 (`!x:int64 a b. word_sub (word_add x a) (word_add x b) = word_sub a b`,
  CONV_TAC WORD_RULE);;

(*** A loop test on two offsets of the same pointer, as the PC gives it ***)

let VERIF_PTR_PC_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read PC s = (if b then x else y):int64`)
           (concl th)
    then REWRITE_RULE[]
          (CONV_RULE(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)
            (REWRITE_RULE[VERIF_PTR_SUB] th))
    else th);;

let VERIF_REG_RULE_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (R:(armstate,int64)component) s = x`)
                       c &&
       (match lhand c with Comb(Comb(_,r),_) -> is_const r | _ -> false)
    then REWRITE_RULE ths th else th);;

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

let VERIF_OLD_EVENTS_TAC =
  W(fun (asl,w) ->
    let ev_eqs = mapfilter (fun (_,th) ->
      if VERIF_IS_E2_EQ th then th else fail()) asl in
    MAP_EVERY (fun eqth ->
      let v = lhs(concl eqth) in
      MAP_EVERY (fun (_,mth) ->
        let c = concl mth in
        if (try fst(dest_const(fst(strip_comb c))) = "memaccess_inbounds" &&
                hd(snd(strip_comb c)) = v
            with Failure _ -> false)
        then STRIP_ASSUME_TAC
              (REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND] (SUBS [eqth] mth))
        else ALL_TAC) asl) ev_eqs);;

let VERIF_MEM_CONS = prove
 (`!(h:(64)address_uarch_event) t rr wr.
        memaccess_inbounds (CONS h t) rr wr <=>
        memaccess_inbounds (APPEND [h] t) rr wr`,
  REWRITE_TAC[APPEND]);;

let VERIF_HAS_OLD olds tm =
  exists (fun v -> free_in v tm) olds ||
  can (find_term (fun t -> is_const t && fst(dest_const t) = "ENUMERATEL"))
      tm;;

let rec VERIF_SPLIT_CONV olds tm =
  let x = hd(snd(strip_comb tm)) in
  let hd,args = strip_comb x in
  if not(VERIF_HAS_OLD olds x) then REFL tm
  else if is_const hd && fst(dest_const hd) = "APPEND" && length args = 2 then
    (REWR_CONV MEMACCESS_INBOUNDS_APPEND THENC
     BINOP_CONV (VERIF_SPLIT_CONV olds)) tm
  else if is_const hd && fst(dest_const hd) = "CONS" && length args = 2 &&
          VERIF_HAS_OLD olds (el 1 args) then
    (REWR_CONV VERIF_MEM_CONS THENC VERIF_SPLIT_CONV olds) tm
  else REFL tm;;

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

let verif_meta_count = ref 0;;

let VERIF_META_EXISTS_TAC (asl,w) =
  let v = fst(dest_exists w) in
  verif_meta_count := !verif_meta_count + 1;
  let v' = mk_var("verif_" ^ fst(dest_var v) ^ "_" ^
                  string_of_int !verif_meta_count,type_of v) in
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

let VERIF_EVENTS_TAC olds =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let select_tac =
    W(fun (asl,w) ->
      let conds = map (fun t -> rand(rator(rator t)))
                      (find_terms is_cond w) in
      let ths = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      REWRITE_TAC ths) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN select_tac THEN
  VERIF_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [W(fun (asl,w) ->
      REWRITE_TAC(mapfilter (fun (_,th) ->
        if VERIF_IS_E2_EQ th then th else fail()) asl)) THEN
    FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  beta_all THEN VERIF_OLD_EVENTS_TAC THEN
  CONV_TAC(VERIF_SPLIT_CONV olds) THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;
