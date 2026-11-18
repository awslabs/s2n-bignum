(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SampleNTT (FIPS 203 Algorithm 7): the generated rejection-sampling loop  *)
(* agrees with mlkem_sample_ntt.                                            *)
(* Load from the repository root after base.ml, interface.ml and the        *)
(* earlier proof files.                                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Counting accepted positions: CARD {j | j < n /\ P j}.                     *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_CARD_MONO = prove
 (`!(P:num->bool) m n.
     m <= n ==> CARD {j | j < m /\ P j} <= CARD {j | j < n /\ P j}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_SUBSET THEN
  REWRITE_TAC[SAMPLE_CARD_FINITE; SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LTE_TRANS]);;

let SAMPLE_CARD_UNIQUE = prove
 (`!(P:num->bool) j1 j2.
     P j1 /\ P j2 /\ CARD {j | j < j1 /\ P j} = CARD {j | j < j2 /\ P j}
     ==> j1 = j2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. a < b /\ (P:num->bool) a
                      ==> CARD {j | j < a /\ P j} < CARD {j | j < b /\ P j}`
   (fun th -> REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
                (SPECL [`j1:num`; `j2:num`] LT_CASES) THEN
              ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[th; LT_REFL]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`P:num->bool`; `SUC a`; `b:num`] SAMPLE_CARD_MONO) THEN
  ASM_REWRITE_TAC[LE_SUC_LT; SAMPLE_CARD_SUC] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Total correctness of native_loop from an invariant and a measure.         *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_NATIVE_RESULT_DISTINCT = distinctness "native_result";;
let SAMPLE_NATIVE_RESULT_INJ = injectivity "native_result";;

let SAMPLE_ITERATE_LOOP = prove
 (`!(test:S->(bool)native_result) body (P:S->bool) (m:S->num).
     (!s. P s ==> ?b. test s = Value b) /\
     (!s. P s /\ test s = Value T
          ==> ?s'. body s = Value s' /\ P s' /\ m s' < m s)
     ==> !w s. m s < w /\ P s
             ==> ?N s'. P s' /\ test s' = Value F /\
                        !k. hol_light_iterate k (native_loop_step test body) s =
                            if N < k then Value s' else Nontermination`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "test") (LABEL_TAC "body")) THEN
  INDUCT_TAC THENL [REWRITE_TAC[LT]; POP_ASSUM(LABEL_TAC "ih")] THEN
  REWRITE_TAC[LT_SUC_LE] THEN X_GEN_TAC `s:S` THEN STRIP_TAC THEN
  USE_THEN "test" (fun th ->
    X_CHOOSE_THEN `b:bool` MP_TAC (MATCH_MP th (ASSUME `(P:S->bool) s`))) THEN
  BOOL_CASES_TAC `b:bool` THEN DISCH_TAC THENL
   [USE_THEN "body" (MP_TAC o SPEC `s:S`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:S` STRIP_ASSUME_TAC) THEN
    USE_THEN "ih" (MP_TAC o SPEC `s1:S`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_THEN `s2:S`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`SUC N`; `s2:S`];
    MAP_EVERY EXISTS_TAC [`0`; `s:S`]] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[hol_light_iterate_DEF; native_loop_step_DEF; LT; LT_0;
    native_bind_DEF; case_native_result_DEF; map_native_result_DEF;
    case_iteration_outcome_DEF; LT_SUC] THEN
  ASM_REWRITE_TAC[case_native_result_DEF; map_native_result_DEF;
    case_iteration_outcome_DEF]);;

let SAMPLE_COND_NONTERM = prove
 (`!b (x:A). ~((if b then Value x else Nontermination) = Nontermination) <=> b`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[SAMPLE_NATIVE_RESULT_DISTINCT]);;

let SAMPLE_NATIVE_LOOP = prove
 (`!(test:S->(bool)native_result) body (P:S->bool) (m:S->num) s.
     P s /\
     (!s. P s ==> ?b. test s = Value b) /\
     (!s. P s /\ test s = Value T
          ==> ?s'. body s = Value s' /\ P s' /\ m s' < m s)
     ==> ?s'. native_loop test body s = Value s' /\ P s' /\
              test s' = Value F`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`test:S->(bool)native_result`; `body:S->(S)native_result`;
                `P:S->bool`; `m:S->num`] SAMPLE_ITERATE_LOOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`SUC((m:S->num) s)`; `s:S`]) THEN
  ASM_REWRITE_TAC[LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_THEN `s':S`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s':S` THEN
  ASM_REWRITE_TAC[native_loop_DEF; native_iter_DEF; SAMPLE_COND_NONTERM] THEN
  SUBGOAL_THEN `?n. N < n` (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[LT]; ALL_TAC] THEN
  SUBGOAL_THEN `N < (@n. N < n)` (fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC SELECT_CONV THEN MESON_TAC[LT]);;

(* ------------------------------------------------------------------------- *)
(* The generated SampleNTT: the loop and one iteration of its body.          *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_LOOP_TERMS =
  let tm = rhs(snd(strip_forall(concl SampleNTT_hol_DEF))) in
  let lp = find_term (fun t -> is_comb t && is_comb(rator t) &&
             is_const(rator(rator t)) &&
             fst(dest_const(rator(rator t))) = "native_loop") tm in
  rand(rator lp), rand lp;;

(* new_definition, but returning the existing theorem when the file is     *)
(* loaded again into the same session.                                     *)

let SAMPLE_DEFINE tm =
  let l,r = dest_eq tm in
  let n = fst(dest_var l) in
  if can get_const_type n then
    find (fun th -> let l',r' = dest_eq(concl th) in
                    is_const l' && fst(dest_const l') = n && aconv r r')
         (definitions())
  else new_definition tm;;

let sample_loop_test = SAMPLE_DEFINE
  (mk_eq(mk_var("sample_loop_test", type_of(fst SAMPLE_LOOP_TERMS)),
         fst SAMPLE_LOOP_TERMS));;

let sample_loop_body = SAMPLE_DEFINE
  (mk_eq(mk_var("sample_loop_body", type_of(snd SAMPLE_LOOP_TERMS)),
         snd SAMPLE_LOOP_TERMS));;

let SAMPLE_NTT_HOL_LOOP = prove
 (`!B. SampleNTT_hol B =
       native_bind
        (native_loop sample_loop_test sample_loop_body
          ((B,(Absorbing,0)),
           (MAP FIPS203_Zq (REPLICATE 256 (residue_of_int_mod (&0))), &0)))
        (\s. Value (FIPS203_Poly (FST(SND s))))`,
  GEN_TAC THEN
  REWRITE_TAC[SampleNTT_hol_DEF; GSYM sample_loop_test; GSYM sample_loop_body] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[XOF_Init_semantic_DEF; NATIVE_BIND_VALUE; XOF_Absorb_semantic_DEF;
    UNCURRY_DEF; APPEND] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; UNCURRY_DEF]);;

let SAMPLE_SQUEEZE_3 = prove
 (`!B ph off.
     XOF_Squeeze_semantic 3 ((B,(ph,off)),&3) =
     Value((B,(Squeezing,off + 3)),
           [shake128 B off; shake128 B (off + 1); shake128 B (off + 2)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[XOF_Squeeze_semantic_DEF; UNCURRY_DEF; ISA_NAT_NUM; ISA_UPT;
    shake128_byte_DEF; ADD_SUB2] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP; ADD_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV);;

let SAMPLE_INDEX_3 = prove
 (`!x y z:A.
     typed_hol_read (native_list_index [x;y;z] (&0)) = Value x /\
     typed_hol_read (native_list_index [x;y;z] (&1)) = Value y /\
     typed_hol_read (native_list_index [x;y;z] (&2)) = Value z`,
  SIMP_TAC[NATIVE_LIST_INDEX; LENGTH; ARITH] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; EL; HD; TL]);;

let SAMPLE_LOOP_BODY = prove
 (`!B ph t a n.
     LENGTH a = 256 /\ n < 256
     ==> sample_loop_body ((B,(ph,3 * t)),(a,&n)) =
         let c = mlkem_xof_field (shake128 B) in
         let zq = \x. FIPS203_Zq(residue_of_int_mod(&x)) in
         if c(2 * t) < 3329 then
           if c(2 * t + 1) < 3329 /\ n + 1 < 256
           then Value((B,(Squeezing,3 * t + 3)),
                      (isa_list_update (isa_list_update a n (zq(c(2 * t))))
                                       (n + 1) (zq(c(2 * t + 1))), &(n + 2)))
           else Value((B,(Squeezing,3 * t + 3)),
                      (isa_list_update a n (zq(c(2 * t))), &(n + 1)))
         else if c(2 * t + 1) < 3329
         then Value((B,(Squeezing,3 * t + 3)),
                    (isa_list_update a n (zq(c(2 * t + 1))), &(n + 1)))
         else Value((B,(Squeezing,3 * t + 3)),(a,&n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[sample_loop_body; UNCURRY_DEF; SAMPLE_SQUEEZE_3;
    NATIVE_BIND_VALUE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SAMPLE_INDEX_3; NATIVE_BIND_VALUE; typed_hol_byte_value_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[ISA_INT_MOD_POS; INT_ARITH_ADIV; INT_ARITH `&0:int < &16`] THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; INT_OF_NUM_REM; INT_OF_NUM_DIV;
    INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_LT; TYPED_HOL_NONNEGATIVE;
    ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM SAMPLE_XOF_FIELD_EVEN; GSYM SAMPLE_XOF_FIELD_ODD] THEN
  ABBREV_TAC `c = mlkem_xof_field (shake128 B)` THEN
  ASM_SIMP_TAC[NATIVE_LIST_UPDATE; LENGTH_ISA_LIST_UPDATE; NATIVE_BIND_VALUE;
    UNCURRY_DEF; TYPED_HOL_NONNEGATIVE; INT_OF_NUM_ADD; INT_OF_NUM_LT] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[NATIVE_LIST_UPDATE; LENGTH_ISA_LIST_UPDATE; NATIVE_BIND_VALUE;
    UNCURRY_DEF; TYPED_HOL_NONNEGATIVE; INT_OF_NUM_ADD; INT_OF_NUM_LT;
    ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[NATIVE_LIST_UPDATE; LENGTH_ISA_LIST_UPDATE; NATIVE_BIND_VALUE;
    UNCURRY_DEF; TYPED_HOL_NONNEGATIVE; INT_OF_NUM_ADD; INT_OF_NUM_LT;
    ARITH_RULE `(n + 1) + 1 = n + 2`]);;

(* ------------------------------------------------------------------------- *)
(* Loop invariant for the generated rejection-sampling loop.                 *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_SEL = prove
 (`!(c:num->num) i j. c j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i
     ==> (@j. c j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i) = j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SELECT_RULE(EXISTS(`?j. (c:num->num) j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i`, `j:num`) (CONJ (ASSUME `(c:num->num) j < 3329`) (ASSUME `CARD {j' | j' < j /\ (c:num->num) j' < 3329} = i`)))) THEN
  ABBREV_TAC `k = @j. (c:num->num) j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\j. (c:num->num) j < 3329`; `k:num`; `j:num`] SAMPLE_CARD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_REWRITE_TAC[]);;

let SAMPLE_DEFINE2 tm =
  let l = fst(dest_eq tm) in
  let h = fst(strip_comb l) in
  let n = if is_const h then fst(dest_const h) else fst(dest_var h) in
  if can get_const_type n then
    find (fun th -> let l' = fst(dest_eq(concl th)) in
                    fst(dest_const(fst(strip_comb l'))) = n) (definitions())
  else new_definition tm;;

let sample_pos = SAMPLE_DEFINE2
 `sample_pos (c:num->num) i =
    @j. c j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i`;;

let SAMPLE_POS = prove
 (`!(c:num->num) i j. c j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i
     ==> sample_pos c i = j`,
  REWRITE_TAC[sample_pos; SAMPLE_SEL]);;

let sample_ok_inv = SAMPLE_DEFINE2
 `sample_ok_inv (B:byte list) N (s:((byte list#xof_phase#num)#fips203_zq list#int)) <=>
   ?t (ph:xof_phase) (a:fips203_zq list) n.
     t <= N /\ s = ((B,(ph,3 * t)),(a,&n)) /\ LENGTH a = 256 /\
     n = MIN 256 (CARD {j | j < 2 * t /\
                            mlkem_xof_field (shake128 B) j < 3329}) /\
     !i. i < n ==> EL i a =
         FIPS203_Zq(residue_of_int_mod
           (&(mlkem_xof_field (shake128 B)
                (sample_pos (mlkem_xof_field (shake128 B)) i))))`;;


let SAMPLE_INTRO = prove
 (`!(B:byte list) (c:num->num) N t (A:fips203_zq list) m.
     t + 1 <= N /\ LENGTH A = 256 /\
     m = MIN 256 (CARD {j | j < 2 * t + 2 /\ c j < 3329}) /\
     (!i. i < m ==> EL i A =
         FIPS203_Zq(residue_of_int_mod(&(c(sample_pos c i)))))
     ==> ?t' (ph:xof_phase) (a':fips203_zq list) n'.
           t' <= N /\ ((B,(Squeezing,3 * t + 3)),(A,(&m:int))) =
                      ((B,(ph,3 * t')),(a',(&n':int))) /\
           LENGTH a' = 256 /\
           n' = MIN 256 (CARD {j | j < 2 * t' /\ c j < 3329}) /\
           (!i. i < n' ==> EL i a' =
              FIPS203_Zq(residue_of_int_mod(&(c(sample_pos c i)))))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t + 1`; `Squeezing`; `A:fips203_zq list`; `m:num`] THEN
  ASM_REWRITE_TAC[PAIR_EQ; ARITH_RULE `3 * (t + 1) = 3 * t + 3`;
                  ARITH_RULE `2 * (t + 1) = 2 * t + 2`]);;

let SAMPLE_ENTRIES_TAC =
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < 256` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_ISA_LIST_UPDATE] THEN
  REPEAT COND_CASES_TAC THEN
  FIRST [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC);
         REPEAT AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
         MATCH_MP_TAC SAMPLE_POS THEN ASM_REWRITE_TAC[ADD_CLAUSES]];;

let SAMPLE_STEP = prove
 (`!(B:byte list) N (s:((byte list#xof_phase#num)#fips203_zq list#int)).
     256 <= CARD {j | j < 2 * N /\ mlkem_xof_field (shake128 B) j < 3329} /\
     sample_ok_inv B N s /\ sample_loop_test s = Value T
     ==> ?s'. sample_loop_body s = Value s' /\ sample_ok_inv B N s' /\
              N - SND(SND(FST s')) DIV 3 < N - SND(SND(FST s)) DIV 3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sample_ok_inv] THEN
  ABBREV_TAC `c = mlkem_xof_field (shake128 B)` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try fst(dest_var(lhs(concl th)))="s" with _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[sample_loop_test; UNCURRY_DEF; injectivity "native_result"; INT_OF_NUM_LT] o check (fun th -> free_in `sample_loop_test` (concl th))) THEN
  DISCH_TAC THEN
  ABBREV_TAC `K0 = CARD {j | j < 2 * t /\ (c:num->num) j < 3329}` THEN
  SUBGOAL_THEN `(n:num) = K0` ASSUME_TAC THENL
   [UNDISCH_TAC `(n:num) = MIN 256 K0` THEN UNDISCH_TAC `n < 256` THEN
    REWRITE_TAC[MIN] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t < N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\j. (c:num->num) j < 3329`; `2 * N`; `2 * t`] SAMPLE_CARD_MONO) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN BETA_TAC THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> free_in `MIN` (concl th))) THEN
  MP_TAC(SPECL [`B:(byte)list`; `ph:xof_phase`; `t:num`; `a:fips203_zq list`; `n:num`] SAMPLE_LOOP_BODY) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mlkem_xof] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\j. (c:num->num) j < 3329`; `2 * t`] SAMPLE_CARD_SUC) THEN
  MP_TAC(ISPECL [`\j. (c:num->num) j < 3329`; `2 * t + 1`] SAMPLE_CARD_SUC) THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * t) = 2 * t + 1`; ARITH_RULE `SUC(2 * t + 1) = 2 * t + 2`] THEN
  BETA_TAC THEN
  ABBREV_TAC `K1 = CARD {j | j < 2 * t + 1 /\ (c:num->num) j < 3329}` THEN
  ABBREV_TAC `K2 = CARD {j | j < 2 * t + 2 /\ (c:num->num) j < 3329}` THEN
  REPEAT DISCH_TAC THEN
  REPEAT COND_CASES_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  REWRITE_TAC[injectivity "native_result"; UNWIND_THM1] THEN
  (CONJ_TAC THENL [MATCH_MP_TAC SAMPLE_INTRO THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_ARITH_TAC;
      (ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE] THEN NO_TAC);
      ASM_CASES_TAC `(c:num->num) (2 * t + 1) < 3329` THEN ASM_REWRITE_TAC[MIN] THEN ASM_ARITH_TAC;
      SAMPLE_ENTRIES_TAC]; REWRITE_TAC[FST; SND] THEN ASM_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Main theorem.                                                             *)
(* ------------------------------------------------------------------------- *)

let SAMPLENTT_HOL_EQ = prove
 (SAMPLENTT_HOL_EQ_STMT,
  GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[sample_ok] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN `256 <= CARD {j | j < 2 * N /\ mlkem_xof_field (shake128 b) j < 3329}` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {j | j < N /\ mlkem_xof_field (mlkem_xof b) j < 3329}` THEN
    ASM_REWRITE_TAC[mlkem_xof] THEN
    MP_TAC(ISPECL [`\j. mlkem_xof_field (shake128 b) j < 3329`; `N:num`; `2 * N`] SAMPLE_CARD_MONO) THEN
    ANTS_TAC THENL [ARITH_TAC; BETA_TAC THEN REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[SAMPLE_NTT_HOL_LOOP] THEN
  MP_TAC(ISPECL [`sample_loop_test`; `sample_loop_body`; `sample_ok_inv (b:byte list) N`;
     `\s:(byte list#xof_phase#num)#fips203_zq list#int. N - SND(SND(FST s)) DIV 3`;
     `(((b:byte list),(Absorbing,0)),
        (MAP FIPS203_Zq (REPLICATE 256 (residue_of_int_mod (&0:int))), &0:int))`] SAMPLE_NATIVE_LOOP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[sample_ok_inv] THEN
      MAP_EVERY EXISTS_TAC [`0`; `Absorbing`;
        `MAP FIPS203_Zq (REPLICATE 256 (residue_of_int_mod (&0:int)))`; `0`] THEN
      REWRITE_TAC[LE_0; MULT_CLAUSES; LT; LENGTH_MAP; LENGTH_REPLICATE; INT_OF_NUM_EQ; PAIR_EQ] THEN
      REWRITE_TAC[ARITH_RULE `2 * 0 = 0`; LT; EMPTY_GSPEC; CARD_CLAUSES; MIN; INT_OF_NUM_EQ] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[sample_ok_inv] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:num` (X_CHOOSE_THEN `ph:xof_phase`
        (X_CHOOSE_THEN `a:fips203_zq list` (X_CHOOSE_THEN `n:num`
          STRIP_ASSUME_TAC)))) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try fst(dest_var(lhs(concl th)))="s" with _ -> false)) THEN
      REWRITE_TAC[sample_loop_test; UNCURRY_DEF] THEN EXISTS_TAC `&n:int < &256` THEN REWRITE_TAC[];
      GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
      MP_TAC(SPECL [`b:byte list`; `N:num`; `s:(byte list#xof_phase#num)#fips203_zq list#int`] SAMPLE_STEP) THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_THEN `s':(byte list#xof_phase#num)#fips203_zq list#int`
      (CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th; NATIVE_BIND_VALUE])
        (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[sample_ok_inv]) ASSUME_TAC))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num` (X_CHOOSE_THEN `ph:xof_phase`
        (X_CHOOSE_THEN `a:fips203_zq list` (X_CHOOSE_THEN `n:num`
          STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try fst(dest_var(lhs(concl th)))="s'" with _ -> false)) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[sample_loop_test; UNCURRY_DEF; injectivity "native_result"; INT_OF_NUM_LT; FST; SND] o check (fun th -> free_in `sample_loop_test` (concl th))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `n = 256` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `~(n < 256)` THEN
      UNDISCH_TAC `(n:num) = MIN 256 (CARD {j | j < 2 * t /\ mlkem_xof_field (shake128 b) j < 3329})` THEN
      REWRITE_TAC[MIN] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FST; SND; injectivity "native_result"; fips203_poly_INJECT] THEN
    REWRITE_TAC[LIST_EQ; LENGTH_ZQLIST] THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_ZQLIST] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[mlkem_sample_ntt; mlkem_xof; sample_pos] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]]);;
