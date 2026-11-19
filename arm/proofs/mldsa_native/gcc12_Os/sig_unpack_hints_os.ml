(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of mldsa{44,65,87}_sig_unpack_hints in the gcc  *)
(* 12 -Os image: the tactics of utils/mldsa_native_hints.ml                  *)
(* (GLUE_SUH_FULL_TAC, for the -O2 code), adapted to the -Os code. The first *)
(* loop of the -Os code tests at the top and its second loop loads before it *)
(* tests; the registers at the heads of the loops, the labels of the heads   *)
(* and of the return, and the address forms of the loads of the hints are    *)
(* parameters of the record glue_suh_os.                                     *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_hints.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* The iterations of the loops. glue_suh_n1 of utils/mldsa_native_hints.ml   *)
(* counts those of the first loop, as the -O2 and the -Os code run it. The   *)
(* second loop of the -Os code runs for the last polynomial (i = k - 1) when *)
(* the first loop has not failed. It starts at the test of the index against *)
(* omega, so an iteration is a pass through that test, and the last pass is  *)
(* the one that leaves the loop: the index is omega, or the byte loaded in   *)
(* the body is not zero (also for the first byte, which the -O2 code checks  *)
(* outside the loop). suo_n2 is glue_suh_n2 + 1 in that case and 0           *)
(* otherwise, and suo_steps the number of iterations of both loops, which    *)
(* the invariant of the proof counts.                                        *)
(* ------------------------------------------------------------------------- *)

let suo_n2 = new_definition
 `suo_n2 omega k (b:num->byte) i =
    if ~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1
    then glue_suh_n2 omega k b i + 1 else 0`;;

let suo_steps = new_definition
 `suo_steps omega k (b:num->byte) i =
    glue_suh_n1 omega b i + suo_n2 omega k b i`;;

let SUO_N2_LOOP = prove
 (`!omega k (b:num->byte) i.
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1
       ==> 0 < suo_n2 omega k b i /\
           (mld_unpack_hints_ok omega k b i <=> glue_suh_zeros omega b i) /\
           (!q. q + 1 < suo_n2 omega k b i
                ==> glue_suh_new omega b i + q < omega /\
                    b(glue_suh_new omega b i + q) = word 0) /\
           (glue_suh_zeros omega b i
            ==> glue_suh_new omega b i + suo_n2 omega k b i = omega + 1) /\
           (~glue_suh_zeros omega b i
            ==> glue_suh_new omega b i + suo_n2 omega k b i <= omega /\
                ~(b(glue_suh_new omega b i + suo_n2 omega k b i - 1) =
                  word 0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `suo_n2 omega k (b:num->byte) i = glue_suh_n2 omega k b i + 1`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[suo_n2]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[glue_suh_early; DE_MORGAN_THM; NOT_LT] o
    check (fun th -> free_in `glue_suh_early` (concl th))) THEN
  MP_TAC(SPECL [`omega:num`; `k:num`; `b:num->byte`; `i:num`]
             GLUE_SUH_FACTS) THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `glue_suh_new omega (b:num->byte) i = omega` THENL
   [SUBGOAL_THEN `glue_suh_n2 omega k (b:num->byte) i = 0 /\
                  mld_unpack_hints_ok omega k b i` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `glue_suh_zeros omega (b:num->byte) i` ASSUME_TAC THENL
     [REWRITE_TAC[glue_suh_zeros] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN GLUE_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [GLUE_ARITH_TAC;
      EQ_TAC THEN DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN GLUE_ARITH_TAC;
      DISCH_TAC THEN GLUE_ARITH_TAC;
      DISCH_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `b(glue_suh_new omega (b:num->byte) i) = word 0:byte` THENL
   [ALL_TAC;
    SUBGOAL_THEN `glue_suh_n2 omega k (b:num->byte) i = 0 /\
                  ~mld_unpack_hints_ok omega k b i` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~glue_suh_zeros omega (b:num->byte) i` ASSUME_TAC THENL
     [REWRITE_TAC[glue_suh_zeros; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `glue_suh_new omega (b:num->byte) i` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[LE_REFL]; GLUE_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [GLUE_ARITH_TAC;
      EQ_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN GLUE_ARITH_TAC;
      DISCH_TAC THEN ASM_MESON_TAC[];
      DISCH_TAC THEN CONJ_TAC THENL
       [GLUE_ARITH_TAC;
        SUBGOAL_THEN `glue_suh_new omega (b:num->byte) i +
                      (glue_suh_n2 omega k b i + 1) - 1 =
                      glue_suh_new omega b i` SUBST1_TAC THENL
         [GLUE_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]]] ] THEN
  SUBGOAL_THEN `glue_suh_loop2 omega k (b:num->byte) i /\
                (mld_unpack_hints_ok omega k b i <=>
                 glue_suh_zeros omega b i)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GLUE_SUH_N2) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [GLUE_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `q = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
      CONJ_TAC THENL [GLUE_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
      FIRST_X_ASSUM(MP_TAC o SPEC `q - 1` o check (fun th ->
        is_forall(concl th) && free_in `glue_suh_n2` (concl th))) THEN
      ANTS_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `glue_suh_new omega (b:num->byte) i + (q - 1) + 1 =
                    glue_suh_new omega b i + q` SUBST1_TAC THENL
       [GLUE_ARITH_TAC; REWRITE_TAC[]]];
    DISCH_TAC THEN
    SUBGOAL_THEN `glue_suh_new omega (b:num->byte) i +
                  glue_suh_n2 omega k b i = omega` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; GLUE_ARITH_TAC];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_imp(concl th) && is_neg(lhand(concl th)) &&
      free_in `glue_suh_zeros` (lhand(concl th)))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL
     [GLUE_ARITH_TAC;
      SUBGOAL_THEN `glue_suh_new omega (b:num->byte) i +
                    (glue_suh_n2 omega k b i + 1) - 1 =
                    glue_suh_new omega b i + glue_suh_n2 omega k b i`
      SUBST1_TAC THENL [GLUE_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]]]);;

let SUO_FACTS = prove
 (`!omega k (b:num->byte) i.
      (glue_suh_early omega b i
       ==> glue_suh_n1 omega b i = 0 /\ suo_n2 omega k b i = 0 /\
           ~mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\
       ~(mld_hints_start omega b i < glue_suh_new omega b i)
       ==> glue_suh_n1 omega b i = 0 /\ glue_suh_ok1 omega b i) /\
      (~glue_suh_ok1 omega b i
       ==> suo_n2 omega k b i = 0 /\ ~mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ ~(i = k - 1)
       ==> suo_n2 omega k b i = 0 /\ mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1
       ==> 0 < suo_n2 omega k b i /\
           (mld_unpack_hints_ok omega k b i <=> glue_suh_zeros omega b i) /\
           (!q. q + 1 < suo_n2 omega k b i
                ==> glue_suh_new omega b i + q < omega /\
                    b(glue_suh_new omega b i + q) = word 0) /\
           (glue_suh_zeros omega b i
            ==> glue_suh_new omega b i + suo_n2 omega k b i = omega + 1) /\
           (~glue_suh_zeros omega b i
            ==> glue_suh_new omega b i + suo_n2 omega k b i <= omega /\
                ~(b(glue_suh_new omega b i + suo_n2 omega k b i - 1) =
                  word 0)))`,
  REPEAT GEN_TAC THEN
  let f1::f2::f3::f4::_ = CONJUNCTS(SPEC_ALL GLUE_SUH_FACTS) in
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP f1) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[suo_n2];
    ACCEPT_TAC f2;
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP f3) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[suo_n2];
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP f4) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[suo_n2];
    ACCEPT_TAC(SPEC_ALL SUO_N2_LOOP)]);;

(* ------------------------------------------------------------------------- *)
(* The parameters of a function: the execution theorem and the name of the   *)
(* function, omega, k and the offset of the hints in the signature, the      *)
(* offsets in the function of the head of the first loop (the load of the    *)
(* coefficient index), the head of the second loop (the test of the index)   *)
(* and the epilogue, and the registers at the head of the first loop for the *)
(* position j (suhos_regs1).                                                 *)
(* ------------------------------------------------------------------------- *)

type glue_suh_os =
 { suhos_exec : thm * thm option array;
   suhos_fn : string;
   suhos_omega : int;
   suhos_k : int;
   suhos_sigh : int;
   suhos_l1 : int;
   suhos_l2 : int;
   suhos_ret : int;
   suhos_regs1 : term };;

let glue_suh_inst_os prm tm =
  let n = mk_small_numeral in
  let base = layout prm.suhos_fn in
  vsubst [n prm.suhos_omega,`OM:num`; n (prm.suhos_omega - 1),`OM1:num`;
          n prm.suhos_k,`KK:num`; n (prm.suhos_k - 1),`K1:num`;
          n prm.suhos_sigh,`SH:num`; n (prm.suhos_sigh - 1),`SH1:num`;
          n (prm.suhos_omega + prm.suhos_k),`HB:num`;
          n (base + prm.suhos_l1),`L1:num`; n (base + prm.suhos_l2),`L2:num`;
          n (base + prm.suhos_ret),`RT:num`] tm;;

let glue_suh_pcev_os =
  let pat = `read (c:(armstate,A)component) (s:armstate)` in
  fun th ->
    let c = concl th in
    (is_eq c || is_iff c) && can (term_match [] pat) (lhs c);;

let rec glue_base_off_os t =
  match t with
    Comb(Comb(Const("word_add",_),x),y) ->
      (try let e = glue_small_val y in
           let b,off = glue_base_off_os x in
           b,Some(match off with
                    None -> e
                  | Some e' -> glue_rassoc(mk_binary "+" (e',e)))
       with Failure _ -> t,None)
  | _ -> t,None;;

let GLUE_SMALL_REGS2_TAC_OS =
  let rd = `read:(armstate,int64)component->armstate->int64` in
  let regs = [`X0`;`X1`;`X2`;`X3`;`X4`;`X5`;`X6`;`X7`;`X19`;`X20`;`X21`;
              `X22`;`X23`] in
  let is_word t = is_comb t && is_const(rator t) &&
                  fst(dest_const(rator t)) = "word" in
  let one reg =
    TRY(FIRST_ASSUM(fun th ->
      let l,r = dest_eq(concl th) in
      if rator l <> mk_comb(rd,reg) || is_word r then NO_TAC else
      try let e = glue_rassoc(glue_small_val r) in
          let tm = mk_comb(`word:num->int64`,e) in
          SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
           [GLUE_WORD_SMALL2_TAC; ALL_TAC]
      with Failure _ ->
        match glue_base_off_os r with
          b,Some e ->
            let tm = list_mk_icomb "word_add"
                       [b; mk_comb(`word:num->int64`,e)] in
            if tm = r then NO_TAC else
            SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
             [GLUE_WORD_SMALL2_TAC; ALL_TAC]
        | _ -> NO_TAC)) in
  let uxtw reg =
    TRY(FIRST_ASSUM(fun th ->
      let l,r = dest_eq(concl th) in
      if rator l <> mk_comb(rd,reg) || not(is_word r) || is_numeral(rand r)
      then NO_TAC else
      let e = rand r in
      let vt = mk_eq(mk_comb(`val:int64->num`,
                 mk_comb(`word_zx:int32->int64`,
                   mk_comb(`word_zx:int64->int32`,r))),e) in
      W(fun (asl,w) ->
        if exists (fun (_,th) -> concl th = vt) asl then NO_TAC else
        MP_TAC(SPEC e VAL_WORD_ZX_UXTW) THEN
        MP_TAC(SPEC e WORD_ZX_ZX_SMALL) THEN
        REWRITE_TAC[ARITH_RULE `n < 2 EXP 32 <=> n < 4294967296`] THEN
        ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC] THEN
        ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC]))) in
  MAP_EVERY one regs THEN MAP_EVERY uxtw regs;;

let GLUE_SUH_ATOMS_TAC_OS =
  W(fun (asl,w) ->
    let eqs = filter (fun th ->
      let c = concl th in
      is_eq c &&
      (try fst(dest_const(rator(lhs c))) = "val" &&
           type_of(rand(lhs c)) = `:byte` && not(is_var(rand(lhs c)))
       with Failure _ -> false)) (map snd asl) in
    if eqs = [] then ALL_TAC else
    RULE_ASSUM_TAC(fun th ->
      if glue_suh_pcev_os th then REWRITE_RULE eqs th else th));;

let GLUE_EVENTS_ZX_TAC_OS =
  let pat = `word_zx(word_zx(word n:int64):int32):int64` in
  W(fun (asl,w) ->
    let eqs = filter (fun th ->
      let c = concl th in
      is_eq c && can (term_match [] pat) (lhs c)) (map snd asl) in
    if eqs = [] then ALL_TAC else
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read events s`) (lhs c)
      then REWRITE_RULE eqs th else th));;

(*** The carry of a 32-bit comparison with the constant 0 (the simulation ***)
(*** evaluates val(word 0) to 0)                                          ***)

let WORD_CMP_32_FLAGS2 = prove
 (`!x y. x < 4294967296 /\ y < 4294967296
         ==> ((&x:int) - &y = &(val (word_sub (word x:int32) (word y))) <=>
              y <= x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `y:num`] WORD_CMP_32_FLAGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT]);;

let GLUE_W32_FLAGS2_TAC =
  let pat = `read (c:(armstate,A)component) (s:armstate)` in
  let pcev th =
    let c = concl th in
    (is_eq c || is_iff c) && can (term_match [] pat) (lhs c) in
  let all_concls (asl,w) =
    list_mk_conj(`T` :: filter (fun t -> pcev(ASSUME t))
                                 (map (concl o snd) asl)) in
  let rewr th =
    RULE_ASSUM_TAC(fun th' ->
      if pcev th' then REWRITE_RULE[th] th' else th') in
  W(fun g ->
    let tms = setify(find_terms
      (can (term_match [] `word_sub (word x) (word y):int32`))
      (all_concls g)) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      TRY(MP_TAC(SPECL [x;y] WORD_CMP_32_FLAGS2) THEN
          ANTS_TAC THENL [CONJ_TAC THEN GLUE_ARITH_TAC; DISCH_THEN rewr]))
     tms);;

let GLUE_SUH_NORM_TAC_OS =
  GLUE_SMALL_REGS2_TAC_OS THEN GLUE_SUH_ATOMS_TAC_OS THEN
  GLUE_EVENTS_ZX_TAC_OS THEN
  GLUE_W32_FLAGS_TAC THEN GLUE_W32_FLAGS2_TAC;;


(*** Arithmetic with the counts, with the number of iterations as a sum ***)

let GLUE_STEPS_ARITH_TAC_OS =
  let isst t =
    try let f,args = strip_comb t in
        fst(dest_const f) = "suo_steps" && length args = 4
    with Failure _ -> false in
  W(fun (asl,w) ->
    let ts = setify(find_terms isst
                      (list_mk_conj(w::map (concl o snd) asl))) in
    MAP_EVERY (fun t -> MP_TAC(REWRITE_CONV[suo_steps] t)) ts THEN
    GLUE_ARITH_TAC);;


(*** The code decrements a 32-bit index: word_zx(word_sub (word (m+1)) 1) ***)

let GLUE_WORD_SUB1 = prove
 (`!m. m + 1 < 4294967296
       ==> word_zx(word_sub (word(m + 1):int32) (word 1)):int64 = word m`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_sub (word(m + 1):int32) (word 1) = word m`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_32] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let rec glue_dec1 n =
  match n with
    Comb(Comb(Const("+",_),x),y) ->
      if y = `1` then x else mk_binary "+" (x,glue_dec1 y)
  | _ -> failwith "glue_dec1";;

let GLUE_SUB1_TAC_OS =
  let pat = `word_zx(word_sub (word n:int32) (word 1)):int64` in
  let pcev th =
    let c = concl th in
    (is_eq c || is_iff c) &&
    can (term_match [] `read (c:(armstate,A)component) (s:armstate)`)
        (lhs c) in
  W(fun (asl,w) ->
    let isreg th =
      pcev th &&
      not(can (term_match [] `read events (s:armstate)`) (lhs(concl th))) in
    let tms = setify(flat(map (fun (_,th) ->
      if isreg th then
        find_terms (fun u -> can (term_match [] pat) u &&
                             not(is_numeral(rand(lhand(rand u)))))
                   (concl th)
      else [])
      asl)) in
    MAP_EVERY (fun t ->
      let n = rand(lhand(rand t)) in
      let m = glue_dec1 n in
      let th = SPEC m GLUE_WORD_SUB1 in
      let e1 = mk_eq(mk_binary "+" (m,`1`),n) in
      SUBGOAL_THEN e1 (fun eq ->
        SUBGOAL_THEN (lhand(concl th)) (fun a ->
          let eqth = REWRITE_RULE[eq] (MP th a) in
          RULE_ASSUM_TAC(fun h ->
            if pcev h then REWRITE_RULE[eqth] h else h))
        THENL [GLUE_ARITH_TAC; ALL_TAC])
      THENL [ARITH_TAC; ALL_TAC]) tms);;

(*** The byte of the hints at index t, at the address as the simulation ***)
(*** normalizes it                                                        ***)

let GLUE_INPUT_AT_TAC_OS prm t =
  let inst = glue_suh_inst_os prm in
  let pat = inst `!j. j < HB
                      ==> read(memory :> bytes8
                            (word_add sig (word(SH + j)))) s =
                          (b:num->byte) j` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th) then
      MP_TAC(SPEC t th) THEN
      ANTS_TAC THENL [GLUE_STEPS_ARITH_TAC_OS; DISCH_TAC]
    else NO_TAC);;

(*** Decide a branch from the facts, or split on one of the predicates of ***)
(*** the events template that it is equivalent to                         ***)

let GLUE_SUH_DECIDE_TAC_OS prm =
  let inst = glue_suh_inst_os prm in
  let canon eq =
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && (can (term_match [] `read PC s`) (lhs c) ||
                     can (term_match [] `read events s`) (lhs c))
      then REWRITE_RULE[eq; NOT_CLAUSES] th else th) in
  let cands =
   [`0 < i`; inst `glue_suh_early OM (b:num->byte) i`;
    inst `mld_hints_start OM (b:num->byte) i < glue_suh_new OM b i`;
    inst `i < K1`] in
  let hook p =
    if p = `0 < i` then
      W(fun (asl,w) ->
        if exists (fun (_,th) -> concl th = `0 < i`) asl then
          SUBGOAL_THEN
           (inst `val((b:num->byte)(i + OM1)) = mld_hints_start OM b i`)
          ASSUME_TAC THENL
           [REWRITE_TAC[mld_hints_start] THEN
            COND_CASES_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
            AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
            ALL_TAC]
        else
          SUBGOAL_THEN (inst `mld_hints_start OM (b:num->byte) i = 0`)
           ASSUME_TAC THENL
           [REWRITE_TAC[mld_hints_start] THEN
            COND_CASES_TAC THENL [REFL_TAC; SIMPLE_ARITH_TAC];
            ALL_TAC])
    else if p = el 1 cands then
      W(fun (asl,w) ->
        if exists (fun (_,th) -> concl th = mk_neg p) asl then
          SUBGOAL_THEN
           (inst `mld_hints_start OM (b:num->byte) i <=
                  glue_suh_new OM b i /\ glue_suh_new OM b i <= OM`)
          STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC (mk_neg p) THEN REWRITE_TAC[glue_suh_early] THEN
            ARITH_TAC;
            ALL_TAC]
        else ALL_TAC)
    else ALL_TAC in
  let equiv =
    REWRITE_TAC[glue_suh_early; COND_EXPAND; GSYM VAL_EQ_0] THEN
    GLUE_ARITH_TAC in
  let decide =
    (ASM_REWRITE_TAC[COND_EXPAND; VAL_EQ_0] THEN NO_TAC) ORELSE
    (REWRITE_TAC[COND_EXPAND] THEN GLUE_ARITH_TAC) in
  W(fun (asl,w) ->
    let c0,_ = dest_cond(glue_current_pc (asl,w)) in
    let split p =
      ((SUBGOAL_THEN (mk_iff(c0,p)) canon THENL [equiv; ALL_TAC]) ORELSE
       (SUBGOAL_THEN (mk_iff(c0,mk_neg p)) canon THENL
         [equiv; ALL_TAC])) THEN
      GLUE_PSH_CASES_TAC p THEN hook p in
    let addcands =
      MAP_EVERY (fun p ->
        W(fun (asl,w) ->
          if exists (fun (_,th) -> concl th = p || concl th = mk_neg p) asl
          then ALL_TAC else
          TRY(SUBGOAL_THEN p ASSUME_TAC THENL [equiv; ALL_TAC]) THEN
          TRY(SUBGOAL_THEN (mk_neg p) ASSUME_TAC THENL [equiv; ALL_TAC])))
       cands in
    ((((SUBGOAL_THEN c0 (canon o EQT_INTRO) THENL [decide; ALL_TAC]) ORELSE
       (SUBGOAL_THEN (mk_neg c0) (canon o EQF_INTRO) THENL
         [decide; ALL_TAC]))
      THEN addcands) ORELSE
     FIRST (map split cands)));;

(*** For i = 0, the code sets X22 to 0: state it as the start of the hints ***)

let GLUE_X22_TAC_OS prm =
  let inst = glue_suh_inst_os prm in
  let z = inst `mld_hints_start OM (b:num->byte) i = 0`
  and eq = inst `word 0:int64 = word(mld_hints_start OM (b:num->byte) i)` in
  W(fun (asl,w) ->
    if not(exists (fun (_,th) -> concl th = z) asl) then ALL_TAC else
    let ths = filter (fun th ->
      let c = concl th in
      is_eq c && rand c = `word 0:int64` &&
      (try rator(lhs c) = `read X22` with Failure _ ->
        (try can (term_match [] `read X22 (s:armstate)`) (lhs c)
         with Failure _ -> false))) (map snd asl) in
    if ths = [] then ALL_TAC else
    SUBGOAL_THEN eq (fun eqth ->
      RULE_ASSUM_TAC(fun th ->
        if mem th ths then REWRITE_RULE[eqth] th else th)) THENL
     [FIRST_ASSUM(fun th -> if concl th = z then
        REWRITE_TAC[th] else NO_TAC);
      ALL_TAC]);;

(*** The simulation from step n to the next checkpoint (the heads of the  ***)
(*** loops and the return), with the call of memset                       ***)

let rec GLUE_SUH_RUN_TAC_OS prm final n (asl,w) =
  let base = layout prm.suhos_fn in
  let off = glue_pc_offset base (glue_current_pc (asl,w)) in
  if n > 1 && mem off [prm.suhos_l1; prm.suhos_l2; prm.suhos_ret] then
    final (asl,w)
  else if off + base = layout "plt_memset" then
    (LIBC_PLT_TAC prm.suhos_exec (n - 1) THEN
     LIBC_SAFE_CALL_TAC "H_MEMSET" prm.suhos_exec
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] (ref glue_suh_vars) (n + 4) THEN
     GLUE_SUH_RUN_TAC_OS prm final (n + 5)) (asl,w)
  else
    (ARM_STEPS_TAC prm.suhos_exec [n] THEN GLUE_SUH_NORM_TAC_OS THEN
     GLUE_SUB1_TAC_OS THEN GLUE_X22_TAC_OS prm THEN
     (fun g -> if is_cond(glue_current_pc g)
               then GLUE_SUH_DECIDE_TAC_OS prm g else ALL_TAC g) THEN
     GLUE_SUH_RUN_TAC_OS prm final (n + 1)) (asl,w);;

(*** The invariant at checkpoint p, and the facts at the start ***)

let glue_suh_inv_os prm =
  let regs1 = vsubst [`mld_hints_start OM (b:num->byte) i + p`,`j:num`]
                     prm.suhos_regs1 in
  let mc = lhs(concl !mldsa_native_image) in
  let body = glue_suh_inst_os prm
    (subst [regs1,`REGS1:bool`; mc,`MC:byte list`]
 `aligned_bytes_loaded (s:armstate) (word pc) (MC:byte list) /\
   read SP s = stackpointer /\
   read (memory :> bytes64 stackpointer) s = x19_init /\
   read (memory :> bytes64 (word_add stackpointer (word 8))) s = x20_init /\
   read (memory :> bytes64 (word_add stackpointer (word 16))) s = x21_init /\
   read (memory :> bytes64 (word_add stackpointer (word 24))) s = x22_init /\
   read (memory :> bytes64 (word_add stackpointer (word 32))) s = x23_init /\
   read (memory :> bytes64 (word_add stackpointer (word 40))) s =
     returnaddress /\
   (!j. j < HB
        ==> read(memory :> bytes8(word_add sig (word(SH + j)))) s = b j) /\
   read PC s =
     word(if p < suo_steps OM KK b i
          then if p < glue_suh_n1 OM b i then pc + L1 else pc + L2
          else pc + RT) /\
   (p < suo_steps OM KK b i
    ==> read X21 s = word i /\
        read X22 s = word(mld_hints_start OM b i) /\
        read X23 s = word_add sig (word SH)) /\
   (p < glue_suh_n1 OM b i
    ==> REGS1 /\ read X3 s = h /\ read X4 s = word 1 /\
        read X19 s = word(glue_suh_new OM b i) /\ read X20 s = sig) /\
   (glue_suh_n1 OM b i <= p /\ p < suo_steps OM KK b i
    ==> read X19 s = word(glue_suh_new OM b i + (p - glue_suh_n1 OM b i)) /\
        read X20 s = word_add sig (word SH1)) /\
   (p = suo_steps OM KK b i
    ==> read X0 s = word_zx(mld_unpack_hints_ret OM KK b i)) /\
   (p < suo_steps OM KK b i \/ mld_unpack_hints_ok OM KK b i
    ==> !q. q < 256
            ==> read(memory :> bytes32(word_add h (word(4 * q)))) s =
                glue_suh_h OM b i (MIN (p:num) (glue_suh_n1 OM b i)) q)`) in
  list_mk_abs([`p:num`; `s:armstate`],body);;

(*** Zero coefficients from the zero bytes that memset gives ***)

let GLUE_ZERO32_OS = prove
 (`!a n s.
        (!j. j < 4 * n
             ==> read(memory :> bytes8(word_add a (word j))) s =
                 word_zx(word 0:int64))
        ==> !q. q < n
                ==> read(memory :> bytes32(word_add a (word(4 * q)))) s =
                    word 0`,
  REPEAT STRIP_TAC THEN
  CONV_TAC(LAND_CONV(READ_MEMORY_MERGE_CONV 2)) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  SUBGOAL_THEN `4 * q < 4 * n /\ 4 * q + 1 < 4 * n /\ 4 * q + 2 < 4 * n /\
                4 * q + 3 < 4 * n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV);;

let GLUE_ZERO32_TAC_OS =
  let lem = GEN `a:int64` (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
              (SPECL [`a:int64`; `256`] GLUE_ZERO32_OS)) in
  TRY(FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP lem th)));;


(*** The facts about the counts and the result in the cases of the tests ***)

let SUO_N2_POS = prove
 (`!omega k (b:num->byte) i.
        0 < suo_n2 omega k b i
        ==> ~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\
            i = k - 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[suo_n2] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[]; ARITH_TAC]);;

let SUO_STEPS_POS = prove
 (`!omega k (b:num->byte) i.
        0 < suo_steps omega k b i
        ==> mld_hints_start omega b i <= glue_suh_new omega b i /\
            glue_suh_new omega b i <= omega`,
  REPEAT GEN_TAC THEN REWRITE_TAC[suo_steps] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~glue_suh_early omega (b:num->byte) i` MP_TAC THENL
   [ASM_CASES_TAC `0 < glue_suh_n1 omega (b:num->byte) i` THENL
     [ASM_MESON_TAC[GLUE_SUH_N1_POS];
      SUBGOAL_THEN `0 < suo_n2 omega k (b:num->byte) i` MP_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(MP_TAC o MATCH_MP SUO_N2_POS) THEN SIMP_TAC[]]];
    REWRITE_TAC[glue_suh_early] THEN ARITH_TAC]);;

let GLUE_SUH_COUNTS_TAC_OS prm =
  let om = mk_small_numeral prm.suhos_omega
  and kk = mk_small_numeral prm.suhos_k in
  let facts = CONV_RULE NUM_REDUCE_CONV
                (SPECL [om; kk; `b:num->byte`; `i:num`] SUO_FACTS) in
  let ante = REPEAT CONJ_TAC THEN
             (FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_ARITH_TAC) in
  MAP_EVERY (fun th ->
    TRY(MP_TAC th THEN ANTS_TAC THENL [ante; STRIP_TAC])) (CONJUNCTS facts)
  THEN
  TRY(MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
      ANTS_TAC THENL [ante; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC);;

(*** The events so far in the goal, from the fact for them                ***)

let GLUE_EVENTS_REWRITE_TAC_OS =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read events s`) (lhs c)
    then REWRITE_TAC[th] else NO_TAC);;

(*** A conjunct of the invariant at a checkpoint ***)

let GLUE_SUH_CONJ_TAC_OS =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC_OS in
  GLUE_DECIDE_CONDS_TAC prover THEN
  ASM_REWRITE_TAC[suo_steps; mld_unpack_hints_ret; GLUE_SUH_H_0;
                  ARITH_RULE `MIN 0 n = 0`; VAL_WORD_0; ADD_CLAUSES] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN TRY(CONV_TAC WORD_RULE) THEN
  TRY GLUE_WORD_SMALL2_TAC;;

(*** For i = 0, the condition of the template that the start is below the ***)
(*** count appears as 0 < count                                           ***)

let GLUE_ZSTART_TAC prm =
  let inst = glue_suh_inst_os prm in
  let p = inst `0 < glue_suh_new OM (b:num->byte) i` in
  W(fun (asl,w) ->
    if exists (fun (_,th) -> concl th = p || concl th = mk_neg p) asl
    then ALL_TAC else
    (SUBGOAL_THEN p ASSUME_TAC THENL [GLUE_ARITH_TAC; ALL_TAC]) ORELSE
    (SUBGOAL_THEN (mk_neg p) ASSUME_TAC THENL
      [GLUE_ARITH_TAC; ALL_TAC]) ORELSE
    ALL_TAC);;

let GLUE_SUH_INIT_FINAL_TAC_OS prm =
  (GLUE_SUH_COUNTS_TAC_OS prm) THEN GLUE_ZERO32_TAC_OS THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    if is_exists w then
      GLUE_EVENTS_REWRITE_TAC_OS THEN
      REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN GLUE_ZSTART_TAC prm THEN
      GLUE_SELECT_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC
    else GLUE_SUH_CONJ_TAC_OS);;

(*** The bytes of the hints that an iteration may load, at the addresses  ***)
(*** in the forms that the simulation may give them                      ***)

let GLUE_INPUT_FORMS_TAC_OS prm extra t =
  let inst = glue_suh_inst_os prm in
  let canon = inst (vsubst [t,`t:num`]
                     `word_add sig (word(SH + t)):int64`) in
  let cands =
    map (fun a -> try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV a))
                  with Failure _ -> a)
     [inst (vsubst [t,`t:num`]
        `word_add (word_add sig (word t)) (word SH):int64`);
      inst (vsubst [t,`t:num`]
        `word_add (word_add sig (word SH)) (word t):int64`);
      inst (vsubst [t,`t:num`]
        `word_add (word_add sig (word SH1)) (word (t + 1)):int64`);
      inst (vsubst [t,`t:num`] `word_add sig (word(t + SH)):int64`)] @
    map (fun e -> list_mk_icomb "word_add"
                    [`sig:int64`; mk_comb(`word:num->int64`,inst e)])
      extra in
  let rass a =
    try let b,w = dest_binary "word_add" a in
        list_mk_icomb "word_add" [b; mk_comb(rator w,glue_rassoc(rand w))]
    with Failure _ -> a in
  let raws = [inst (vsubst [t,`t:num`]
        `word_add (word_add sig (word SH1)) (word (t + 1)):int64`);
      inst (vsubst [t,`t:num`]
        `word_add (word_add sig (word SH1))
                  (word_add (word t) (word 1)):int64`)] in
  let forms =
    setify(canon :: cands @ map rass cands @ raws @ map rass raws) in
  GLUE_INPUT_AT_TAC_OS prm t THEN
  MAP_EVERY (fun a ->
    if a = canon then ALL_TAC else
    TRY(FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes8 a) s`) (lhs c)
         && rand(rand(rand(rator(lhs c)))) = canon
      then
        SUBGOAL_THEN (mk_eq(a,canon)) (fun eq -> ASSUME_TAC
          (CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(REWR_CONV(SYM eq)))) th))
        THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
          ALL_TAC]
      else NO_TAC))) forms;;

let GLUE_SUH_INIT_PREP_TAC_OS prm =
  let inst = glue_suh_inst_os prm in
  STRIP_ASSUME_TAC(SPECL [mk_small_numeral prm.suhos_omega; `b:num->byte`;
                          `i:num`] GLUE_SUH_BOUNDS) THEN
  SUBGOAL_THEN (inst `val((b:num->byte)(i + OM)) = glue_suh_new OM b i`)
  ASSUME_TAC THENL
   [REWRITE_TAC[glue_suh_new] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  GLUE_INPUT_FORMS_TAC_OS prm [] (inst `i + OM1`) THEN
  GLUE_INPUT_FORMS_TAC_OS prm [] (inst `i + OM`);;

(*** The facts at the head of an iteration p of the first loop, for the  ***)
(*** position j = s + p: the bytes it loads, and the coefficients other   ***)
(*** than the one it sets                                                 ***)

let GLUE_SUH_PREP1_TAC_OS prm =
  let inst = glue_suh_inst_os prm in
  let j = inst `mld_hints_start OM (b:num->byte) i + p` in
  GLUE_INPUT_FORMS_TAC_OS prm [] j THEN
  GLUE_INPUT_FORMS_TAC_OS prm
   [`((mld_hints_start OM (b:num->byte) i + p) + SH) + 1`]
   (inst `mld_hints_start OM (b:num->byte) i + p + 1`) THEN
  ASSUME_TAC(SPEC (mk_comb(`b:num->byte`,j)) GLUE_VAL_BYTE) THEN
  SUBGOAL_THEN (subst [j,`j:num`] `val(word(val((b:num->byte) j)):int64) =
                                   val(b j)`) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPEC (mk_comb(`b:num->byte`,j)) GLUE_VAL_BYTE) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (inst `MIN p (glue_suh_n1 OM (b:num->byte) i) = p`)
  ASSUME_TAC THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN GLUE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!q. q < 256
              ==> read(memory :> bytes32(word_add h (word(4 * q)))) s =
                  glue_suh_h omega b i n q`) (concl th)
    then
      SUBGOAL_THEN
       (subst [j,`j:num`]
         (inst `!q. q < 256 /\ ~(q = val((b:num->byte) j))
                    ==> read(memory :> bytes32
                          (word_add h (word(4 * q)))) s0 =
                        glue_suh_h OM b i p q`))
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MP_TAC(SPEC `q:num` th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC]
    else NO_TAC);;

(*** The facts at the head of an iteration p of the second loop, for the ***)
(*** position u = w + (p - n1)                                            ***)

let GLUE_SUH_PREP2_TAC_OS prm =
  let inst = glue_suh_inst_os prm in
  GLUE_INPUT_FORMS_TAC_OS prm []
   (inst `glue_suh_new OM (b:num->byte) i + (p - glue_suh_n1 OM b i)`);;

(*** The coefficients after an iteration: one more set in the first loop ***)

let GLUE_SUH_H_TAC_OS =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC_OS ORELSE
               (ASM_REWRITE_TAC[] THEN GLUE_STEPS_ARITH_TAC_OS) in
  GLUE_DECIDE_CONDS_TAC prover THEN REWRITE_TAC[] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  REWRITE_TAC[MIN] THEN GLUE_DECIDE_CONDS_TAC prover THEN
  REWRITE_TAC[GLUE_SUH_H_ADD1] THEN
  FIRST
   [COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN FIRST_ASSUM ACCEPT_TAC]];
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in `glue_suh_h` (concl th) then
        MP_TAC(SPEC `q:num` th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MIN] THEN
        COND_CASES_TAC THEN GLUE_ARITH_TAC
      else NO_TAC)];;

let GLUE_SUH_BODY_CONJ_TAC_OS =
  W(fun (asl,w) ->
    if is_exists w then
      GLUE_EVENTS_REWRITE_TAC_OS THEN GLUE_PATH_DISCHARGE_TAC
    else if maychange_term w then GLUE_FRAME_TAC
    else if free_in `glue_suh_h` w then GLUE_SUH_H_TAC_OS
    else GLUE_SUH_CONJ_TAC_OS);;

let GLUE_SUH_BODY_FINAL_TAC_OS prm =
  (GLUE_SUH_COUNTS_TAC_OS prm) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  GLUE_SUH_BODY_CONJ_TAC_OS;;

(*** The iterations of the loops, in the cases of the paths of the code ***)

let GLUE_DECIDE_ASMS_TAC_OS prover =
  let bad t =
    can (find_term (fun u -> is_const u &&
                             fst(dest_const u) = "ENUMERATEL")) t in
  let ok th = let c = concl th in
              not(bad c) &&
              can (find_term (fun t -> is_cond t || is_imp t)) c in
  W(fun (asl,w) ->
    let conds = setify(flat(map (fun (_,th) ->
      map (fun t -> if is_cond t then rand(rator(rator t)) else lhand t)
          (find_terms (fun t -> is_cond t || is_imp t) (concl th)))
      (filter (fun (_,th) -> ok th) asl))) in
    let known c =
      exists (fun (_,th) -> concl th = c || concl th = mk_neg c) in
    MAP_EVERY (fun c ->
      W(fun (asl,w) ->
        if known c asl then ALL_TAC else
        TRY(SUBGOAL_THEN c ASSUME_TAC THENL [prover; ALL_TAC]) THEN
        TRY(SUBGOAL_THEN (mk_neg c) ASSUME_TAC THENL [prover; ALL_TAC])))
     conds THEN
    W(fun (asl,w) ->
      let eqs = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      RULE_ASSUM_TAC(fun th ->
        if ok th then REWRITE_RULE eqs th else th) THEN
      REPEAT(FIRST_X_ASSUM(fun th ->
        let c = concl th in
        if is_conj c && can (find_term (fun t ->
             try fst(dest_const(rator(rator t))) = "read" with Failure _ ->
             false)) c && not(bad c)
        then STRIP_ASSUME_TAC th else NO_TAC))));;

(*** In the last iteration of the second loop, the facts of the counts are ***)
(*** about the byte at w + n2 - 1: state them for w + (p - n1)            ***)

let GLUE_TERM_FIX_TAC_OS prm =
  let inst = glue_suh_inst_os prm in
  let n1 = inst `glue_suh_n1 OM (b:num->byte) i`
  and n2 = inst `suo_n2 OM KK (b:num->byte) i`
  and w = inst `glue_suh_new OM (b:num->byte) i` in
  let key = mk_eq(n2,mk_binary "+" (mk_binary "-" (`p:num`,n1),`1`)) in
  W(fun (asl,_) ->
    if not(exists (fun (_,th) -> concl th = key) asl) then ALL_TAC else
    SUBGOAL_THEN (mk_eq(mk_binary "+" (w,mk_binary "-" (n2,`1`)),
                        mk_binary "+" (w,mk_binary "-" (`p:num`,n1))))
     (fun th -> RULE_ASSUM_TAC(fun t ->
        if is_neg(concl t) && free_in `word 0:byte` (concl t)
        then REWRITE_RULE[th] t else t)) THENL
     [GLUE_STEPS_ARITH_TAC_OS; ALL_TAC]);;

let GLUE_SUH_ITER_TAC_OS prm prep =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC_OS in
  GLUE_SUH_COUNTS_TAC_OS prm THEN GLUE_TERM_FIX_TAC_OS prm THEN
  FULL_INIT_TAC THEN
  GLUE_DECIDE_ASMS_TAC_OS prover THEN prep THEN
  GLUE_SUH_RUN_TAC_OS prm (GLUE_SUH_BODY_FINAL_TAC_OS prm) 1;;

let GLUE_SUH_BODY_GEN_TAC_OS prm it1 it2 =
  let inst = glue_suh_inst_os prm in
  let om = mk_small_numeral prm.suhos_omega
  and kk = mk_small_numeral prm.suhos_k in
  let n1 = inst `glue_suh_n1 OM (b:num->byte) i`
  and n2 = inst `suo_n2 OM KK (b:num->byte) i`
  and st = inst `suo_steps OM KK (b:num->byte) i`
  and ok1 = inst `glue_suh_ok1 OM (b:num->byte) i`
  and zs = inst `glue_suh_zeros OM (b:num->byte) i`
  and ok = inst `mld_unpack_hints_ok OM KK (b:num->byte) i`
  and w = inst `glue_suh_new OM (b:num->byte) i` in
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_BOUNDS) THEN
  MP_TAC(SPECL [om; kk; `b:num->byte`; `i:num`] SUO_STEPS_POS) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC (mk_binary "<" (`p:num`,n1)) THENL
   [MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1_POS) THEN
    ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    ASM_CASES_TAC (mk_binary "<" (`p + 1`,n1)) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
        is_forall(concl th) && free_in n1 (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN it1;
      ASM_CASES_TAC ok1 THENL
       [FIRST_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok1 then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = ok1 then ASSUME_TAC(EQ_MP th th1) else NO_TAC)
          else NO_TAC) THEN
        ASM_CASES_TAC (inst `i < K1`) THEN it1;
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          is_imp(concl th) && is_neg(lhand(concl th)))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        SUBGOAL_THEN (inst `mld_hints_start OM (b:num->byte) i +
                            glue_suh_n1 OM b i =
                            mld_hints_start OM b i + p + 1 /\
                            (mld_hints_start OM b i +
                             glue_suh_n1 OM b i) - 1 =
                            mld_hints_start OM b i + p`)
         (fun th -> RULE_ASSUM_TAC(fun t ->
            if free_in `val:byte->num` (concl t) then REWRITE_RULE[th] t
            else t)) THENL
         [GLUE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN (inst `~(mld_hints_start OM (b:num->byte) i +
                              glue_suh_n1 OM b i = glue_suh_new OM b i)`)
        ASSUME_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN it1]];
    SUBGOAL_THEN (mk_binary "<" (`0`,n2)) ASSUME_TAC THENL
     [GLUE_STEPS_ARITH_TAC_OS; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SUO_N2_POS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    MP_TAC(SPECL [om; kk; `b:num->byte`; `i:num`] SUO_N2_LOOP) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN (inst `~(i < K1)`) ASSUME_TAC THENL
     [GLUE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && lhs c = `i:num` then ALL_TAC else NO_TAC) THEN
    ASM_CASES_TAC (mk_binary "<" (`p + 1`,st)) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC (mk_binary "-" (`p:num`,n1)) o
        check (fun th -> is_forall(concl th) && free_in n2 (concl th))) THEN
      ANTS_TAC THENL [GLUE_STEPS_ARITH_TAC_OS; STRIP_TAC] THEN it2;
      SUBGOAL_THEN (mk_eq(n2,mk_binary "+" (mk_binary "-" (`p:num`,n1),`1`)))
        ASSUME_TAC THENL [GLUE_STEPS_ARITH_TAC_OS; ALL_TAC] THEN
      ASM_CASES_TAC zs THENL
       [FIRST_ASSUM(fun th ->
          if is_imp(concl th) && lhand(concl th) = zs then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = zs then ASSUME_TAC(MP th th1) else NO_TAC)
          else NO_TAC) THEN
        FIRST_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = zs then ASSUME_TAC(EQ_MP (SYM th) th1)
              else NO_TAC)
          else NO_TAC) THEN
        SUBGOAL_THEN (mk_eq(mk_binary "+" (w,mk_binary "-" (`p:num`,n1)),om))
          ASSUME_TAC THENL [GLUE_STEPS_ARITH_TAC_OS; ALL_TAC] THEN
        it2;
        FIRST_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = mk_neg zs then
                ASSUME_TAC(REWRITE_RULE[GSYM th] th1)
              else NO_TAC)
          else NO_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          is_imp(concl th) && is_neg(lhand(concl th)) &&
          free_in `glue_suh_zeros` (concl th))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        SUBGOAL_THEN
         (mk_binary "<" (mk_binary "+" (w,mk_binary "-" (`p:num`,n1)),om))
          ASSUME_TAC THENL [GLUE_STEPS_ARITH_TAC_OS; ALL_TAC] THEN
        SUBGOAL_THEN (mk_eq(mk_binary "+" (w,mk_binary "-" (n2,`1`)),
                            mk_binary "+" (w,mk_binary "-" (`p:num`,n1))))
         (fun th -> RULE_ASSUM_TAC(fun t ->
            if is_neg(concl t) && free_in `word 0:byte` (concl t)
            then REWRITE_RULE[th] t else t)) THENL
         [GLUE_STEPS_ARITH_TAC_OS; ALL_TAC] THEN it2]]];;

let GLUE_SUH_BODY_TAC_OS prm =
  GLUE_SUH_BODY_GEN_TAC_OS prm
   (GLUE_SUH_ITER_TAC_OS prm (GLUE_SUH_PREP1_TAC_OS prm))
   (GLUE_SUH_ITER_TAC_OS prm (GLUE_SUH_PREP2_TAC_OS prm));;

(*** The return from the checkpoint at the end ***)

let GLUE_SUH_EXIT_TAC_OS prm =
  let inst = glue_suh_inst_os prm in
  let om = mk_small_numeral prm.suhos_omega
  and kk = mk_small_numeral prm.suhos_k in
  let ok = inst `mld_unpack_hints_ok OM KK (b:num->byte) i` in
  ASM_CASES_TAC ok THEN
  (ASM_REWRITE_TAC[LT_REFL]) THEN FULL_INIT_TAC THEN
  (ARM_STEPS_TAC prm.suhos_exec (1--4)) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    if is_exists w then
      GLUE_EVENTS_REWRITE_TAC_OS THEN GLUE_PATH_DISCHARGE_TAC
    else (
      ASM_REWRITE_TAC[mld_unpack_hints_ret] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN
          FIRST_ASSUM(fun th ->
            if is_forall(concl th) && free_in `glue_suh_h` (concl th)
            then MP_TAC(SPEC `q:num` th) THEN
                 ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]
            else NO_TAC) THEN
          SUBGOAL_THEN
           (inst `MIN (suo_steps OM KK (b:num->byte) i)
                      (glue_suh_n1 OM b i) = glue_suh_n1 OM b i`)
          SUBST1_TAC THENL
           [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN
            GLUE_STEPS_ARITH_TAC_OS;
            ALL_TAC] THEN
          MATCH_MP_TAC GLUE_SUH_H_FULL THEN
          MATCH_MP_TAC(SPECL [om; kk] GLUE_SUH_OK_N1) THEN
          FIRST_ASSUM ACCEPT_TAC)));;

(*** The events template: one function for each path of the code to the ***)
(*** first checkpoint, and for each path of an iteration                 ***)

let glue_suh_template_os prm = glue_suh_inst_os prm
 `\(b:num->byte) (i:num) (h:int64) (sig:int64) (mf:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND
    (if mld_unpack_hints_ok OM KK b i
     then f_ev_ok b i h sig mf pc stackpointer returnaddress
     else f_ev_bad b i h sig mf pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (suo_steps OM KK b i)
        (\p. if p < glue_suh_n1 OM b i
             then if p + 1 < glue_suh_n1 OM b i
                  then f_ev_a b i h sig mf pc stackpointer returnaddress p
                  else if glue_suh_ok1 OM b i
                  then if i < K1
                       then f_ev_ar b i h sig mf pc stackpointer
                                    returnaddress p
                       else f_ev_at b i h sig mf pc stackpointer
                                    returnaddress p
                  else f_ev_af b i h sig mf pc stackpointer returnaddress p
             else if p + 1 < suo_steps OM KK b i
             then f_ev_b b i h sig mf pc stackpointer returnaddress p
             else if glue_suh_zeros OM b i
             then f_ev_be b i h sig mf pc stackpointer returnaddress p
             else f_ev_bf b i h sig mf pc stackpointer returnaddress p))
      (if glue_suh_early OM b i
       then if 0 < i then f_ev_e1 b i h sig mf pc stackpointer returnaddress
            else f_ev_e0 b i h sig mf pc stackpointer returnaddress
       else if mld_hints_start OM b i < glue_suh_new OM b i
       then if 0 < i then f_ev_p1 b i h sig mf pc stackpointer returnaddress
            else f_ev_p0 b i h sig mf pc stackpointer returnaddress
       else if i < K1
       then if 0 < i then f_ev_r1 b i h sig mf pc stackpointer returnaddress
            else f_ev_r0 b i h sig mf pc stackpointer returnaddress
       else f_ev_t b i h sig mf pc stackpointer returnaddress))
   :(uarch_event)list`;;

(*** The whole proof ***)

let GLUE_SUH_FULL_TAC_OS prm =
  let inst = glue_suh_inst_os prm in
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_ret_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC (glue_suh_template_os prm) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst prm.suhos_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD])
  THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  GLUE_EVENTS_WHILE_TAC (inst `suo_steps OM KK (b:num->byte) i`)
    (glue_suh_inv_os prm) THEN
  REPEAT CONJ_TAC THENL
   [FULL_INIT_TAC THEN GLUE_SUH_INIT_PREP_TAC_OS prm THEN
    GLUE_SUH_RUN_TAC_OS prm (GLUE_SUH_INIT_FINAL_TAC_OS prm) 1;
    GLUE_SUH_BODY_TAC_OS prm;
    GLUE_SUH_EXIT_TAC_OS prm];;
