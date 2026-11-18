(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the generated and the handwritten FIPS 204 hint and        *)
(* signature encodings: HintBitPack and HintBitUnpack (FIPS 204 Algorithms   *)
(* 20 and 21), CountOnes and FixedCountOnes_k, sigEncode and sigDecode       *)
(* (Algorithms 26 and 27), for ML-DSA-44, -65 and -87.                       *)
(*                                                                           *)
(* The handwritten hints are a predicate on the positions p = 256 * i + j    *)
(* (coefficient j of polynomial i). A generated hint vector is lifted as     *)
(* lift_vec (\i. lift_bitpoly (h i)) for a predicate h i j, the form that    *)
(* MakeHint returns and UseHint takes (rounding.ml), and corresponds to the  *)
(* handwritten predicate \p. h (p DIV 256) (p MOD 256). HintBitUnpack        *)
(* returns lift_vec (\i. lift_bitpoly (\j. h (256 * i + j))) for the h of    *)
(* mldsa_hintbitunpack, and Native_Bottom exactly when that is NONE.         *)
(*                                                                           *)
(* sigEncode and sigDecode use BitPack and BitUnpack for the coefficients of *)
(* z; these belong to encode.ml and are explicit hypotheses here (the terms  *)
(* hints_bitpack_hyp and hints_bitunpack_hyp below), discharged in           *)
(* sigcodec.ml with encode.ml's lemmas (see sigcodec.ml).                    *)
(*                                                                           *)
(* The lemmas HINTS_* are local (generic loop, list and byte-string facts    *)
(* that may also exist in core.ml or encode.ml).                             *)
(* ========================================================================= *)

needs "common/fips204/generated/core/common.ml";;
needs "common/fips204/generated/core/core.ml";;

(* ------------------------------------------------------------------------- *)
(* Local monad, list and loop lemmas (HINTS_ prefix).                        *)
(* ------------------------------------------------------------------------- *)


let HINTS_ISA_NAT_SUB = prove
 (`!a b. a <= b ==> isa_nat(&b - &a) = b - a`,
  SIMP_TAC[INT_OF_NUM_SUB; ISA_NAT_NUM]);;

let HINTS_ISA_LIST_UPDATE = prove
 (`!(l:A list) n a.
        isa_list_update l n a =
        list_of_seq (\j. if j = n then a else EL j l) (LENGTH l)`,
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_ISA_LIST_UPDATE] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; EL_ISA_LIST_UPDATE]);;

(* A counted loop of the generated code, from a to b - 1.                    *)

let HINTS_SCHEDULE_ADD = prove
 (`!L a n. L <= n
           ==> native_schedule n (\i:int. i < &(a + L)) (\i. i + &1) (&a) =
               list_of_seq (\j. &(a + j)) L`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[native_schedule_DEF; list_of_seq; ADD_CLAUSES; INT_LT_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[ARITH_RULE `~(SUC L <= 0)`; LE_SUC] THEN DISCH_TAC THEN
  REWRITE_TAC[native_schedule_DEF; LIST_OF_SEQ; INT_OF_NUM_LT;
              ARITH_RULE `a < a + SUC L`; INT_OF_NUM_ADD] THEN
  REWRITE_TAC[CONS_11; o_DEF; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `SUC(a + L) = (a + 1) + L`;
              ARITH_RULE `SUC(a + j) = (a + 1) + j`] THEN
  ASM_SIMP_TAC[]);;

let HINTS_SCHEDULE = prove
 (`!n a b. a <= b /\ b - a <= n
           ==> native_schedule n (\i:int. i < &b) (\i. i + &1) (&a) =
               list_of_seq (\j. &(a + j)) (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b - a:num`; `a:num`; `n:num`] HINTS_SCHEDULE_ADD) THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= b ==> a + (b - a) = b`]);;

(* native_foldl over such a loop, with the states S 0, ..., S L.             *)

let HINTS_FOLDL = prove
 (`!L (f:int->A->(A)native_result) (S:num->A) a.
        (!j. j < L ==> f (&(a + j)) (S j) = Value (S (SUC j)))
        ==> native_foldl f (list_of_seq (\j. &(a + j)) L) (S 0) =
            Value (S L)`,
  INDUCT_TAC THEN REWRITE_TAC[LIST_OF_SEQ; native_foldl_DEF] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[LT_0; ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; o_DEF] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(ISPECL
   [`f:int->A->(A)native_result`; `\j. (S:num->A) (SUC j)`; `a + 1`] th)) THEN
  REWRITE_TAC[ARITH_RULE `(a + 1) + j = SUC(a + j)`; ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC j`) THEN
  ASM_REWRITE_TAC[LT_SUC; ADD_CLAUSES]);;

let HINTS_FOLDL_EQ = prove
 (`!L (f:int->A->(A)native_result) (S:num->A) a s0 s1.
        S 0 = s0 /\ S L = s1 /\
        (!j. j < L ==> f (&(a + j)) (S j) = Value (S (SUC j)))
        ==> native_foldl f (list_of_seq (\j. &(a + j)) L) s0 = Value s1`,
  MESON_TAC[HINTS_FOLDL]);;

(* native_fold, whose body may leave the loop with Return_Value r s.         *)

let HINTS_FOLD = prove
 (`!L (body:int->A->((A,R)statement_outcome)native_result) (S:num->A)
     (ok:num->bool) (r:R) a.
        (!j. j < L /\ (!i. i < j ==> ok i)
             ==> (ok j ==> body (&(a + j)) (S j) =
                           Value (Continue (S (SUC j)))) /\
                 (~ok j ==> ?s. body (&(a + j)) (S j) =
                                Value (Return_Value r s)))
        ==> ((!j. j < L ==> ok j)
             ==> native_fold body (list_of_seq (\j. &(a + j)) L) (S 0) =
                 Value (Continue (S L))) /\
            (~(!j. j < L ==> ok j)
             ==> ?s. native_fold body (list_of_seq (\j. &(a + j)) L) (S 0) =
                     Value (Return_Value r s))`,
  INDUCT_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ; native_fold_DEF; CONJUNCT1 LT; native_seq_DEF] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "hyp") THEN
  USE_THEN "hyp" (MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[LT_0; ADD_CLAUSES; CONJUNCT1 LT] THEN
  ASM_CASES_TAC `(ok:num->bool) 0` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[native_continue_bind_DEF; case_native_result_DEF;
                case_statement_outcome_DEF; o_DEF] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(ISPECL
     [`body:int->A->((A,R)statement_outcome)native_result`;
      `\j. (S:num->A) (SUC j)`; `\j. (ok:num->bool) (SUC j)`; `r:R`;
      `a + 1`] th)) THEN
    REWRITE_TAC[ARITH_RULE `(a + 1) + j = SUC(a + j)`; ADD_CLAUSES] THEN
    SUBGOAL_THEN `(!j. j < SUC L ==> (ok:num->bool) j) <=>
                  (!j. j < L ==> ok (SUC j))` SUBST1_TAC THENL
     [EQ_TAC THEN DISCH_TAC THENL
       [ASM_MESON_TAC[LT_SUC]; INDUCT_TAC THEN ASM_MESON_TAC[LT_SUC]];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    USE_THEN "hyp" (MP_TAC o SPEC `SUC j`) THEN
    REWRITE_TAC[LT_SUC; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN INDUCT_TAC THEN ASM_MESON_TAC[LT_SUC];
    DISCH_THEN(X_CHOOSE_THEN `s:A` SUBST1_TAC) THEN
    REWRITE_TAC[native_continue_bind_DEF; case_native_result_DEF;
                case_statement_outcome_DEF] THEN
    CONJ_TAC THENL [DISCH_THEN(MP_TAC o SPEC `0`); MESON_TAC[]] THEN
    ASM_REWRITE_TAC[LT_0]]);;

let HINTS_FOLD_EQ = prove
 (`!L (body:int->A->((A,R)statement_outcome)native_result) (S:num->A)
     (ok:num->bool) (r:R) a s0.
        S 0 = s0 /\
        (!j. j < L /\ (!i. i < j ==> ok i)
             ==> (ok j ==> body (&(a + j)) (S j) =
                           Value (Continue (S (SUC j)))) /\
                 (~ok j ==> ?s. body (&(a + j)) (S j) =
                                Value (Return_Value r s)))
        ==> ((!j. j < L ==> ok j)
             ==> native_fold body (list_of_seq (\j. &(a + j)) L) s0 =
                 Value (Continue (S L))) /\
            (~(!j. j < L ==> ok j)
             ==> ?s. native_fold body (list_of_seq (\j. &(a + j)) L) s0 =
                     Value (Return_Value r s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  REWRITE_TAC[HINTS_FOLD]);;

(* The loops from 0, and tactics that rewrite a loop of the goal given the   *)
(* states S j (and, for native_fold, the condition ok j of not leaving it).  *)


let HINTS_FOLDL0_EQ = prove
 (`!L (f:int->A->(A)native_result) (S:num->A) s0 s1.
        S 0 = s0 /\ S L = s1 /\
        (!j. j < L ==> f (&j) (S j) = Value (S (SUC j)))
        ==> native_foldl f (list_of_seq (\j. &j) L) s0 = Value s1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:num`; `f:int->A->(A)native_result`; `S:num->A`; `0`;
                 `s0:A`; `s1:A`] HINTS_FOLDL_EQ) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; ETA_AX]);;

let HINTS_FOLD0_EQ = prove
 (`!L (body:int->A->((A,R)statement_outcome)native_result) (S:num->A)
     (ok:num->bool) (r:R) s0.
        S 0 = s0 /\
        (!j. j < L /\ (!i. i < j ==> ok i)
             ==> (ok j ==> body (&j) (S j) = Value (Continue (S (SUC j)))) /\
                 (~ok j ==> ?s. body (&j) (S j) = Value (Return_Value r s)))
        ==> ((!j. j < L ==> ok j)
             ==> native_fold body (list_of_seq (\j. &j) L) s0 =
                 Value (Continue (S L))) /\
            (~(!j. j < L ==> ok j)
             ==> ?s. native_fold body (list_of_seq (\j. &j) L) s0 =
                     Value (Return_Value r s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:num`; `body:int->A->((A,R)statement_outcome)native_result`;
                 `S:num->A`; `ok:num->bool`; `r:R`; `0`; `s0:A`]
         HINTS_FOLD_EQ) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

(* A loop native_schedule n (\i. i < &m) (\i. i + &1) (&0) with numerals.    *)

let HINTS_SCHEDULE_CONV tm =
  let th = PART_MATCH (lhand o rand) NATIVE_SCHEDULE_NUM tm in
  let ant = lhand(concl th) in
  MP th (EQT_ELIM(NUM_REDUCE_CONV ant));;

let hints_is_list_of_seq t =
  match strip_comb t with (Const("list_of_seq",_),[_;_]) -> true | _ -> false;;

(* HINTS_FOLDL_TAC S s1 rewrites the first native_foldl f l s0 of the goal   *)
(* over l = list_of_seq (\j. &(a + j)) L (or (\j. &j)) with Value s1, after  *)
(* the subgoal S 0 = s0 /\ S L = s1 /\ (each step goes from S j to S(j+1)).  *)

let HINTS_FOLDL_TAC stm s1tm (asl,w as gl) =
  let tm = find_term (fun t -> match strip_comb t with
      (Const("native_foldl",_),[_;l;_]) -> hints_is_list_of_seq l
    | _ -> false) w in
  let f,l,s0 = match snd(strip_comb tm) with
      [f;l;s0] -> f,l,s0 | _ -> failwith "HINTS_FOLDL_TAC" in
  let lam,ltm = match snd(strip_comb l) with
      [lam;ltm] -> lam,ltm | _ -> failwith "HINTS_FOLDL_TAC" in
  let bod = body lam in
  let th =
    if is_var(rand bod) then ISPECL [ltm; f; stm; s0; s1tm] HINTS_FOLDL0_EQ
    else ISPECL [ltm; f; stm; lhand(rand bod); s0; s1tm] HINTS_FOLDL_EQ in
  (SUBGOAL_THEN (lhand(concl th))
    (fun ath -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [MP th ath])) gl;;

(* HINTS_FOLD_TAC S ok r does the same for the first native_fold, and then   *)
(* splits the goal on (!j. j < L ==> ok j): if so the loop gives             *)
(* Value (Continue (S L)), and if not Value (Return_Value r s) for some s.   *)

let HINTS_FOLD_TAC stm oktm rtm (asl,w as gl) =
  let tm = find_term (fun t -> match strip_comb t with
      (Const("native_fold",_),[_;l;_]) -> hints_is_list_of_seq l
    | _ -> false) w in
  let f,l,s0 = match snd(strip_comb tm) with
      [f;l;s0] -> f,l,s0 | _ -> failwith "HINTS_FOLD_TAC" in
  let lam,ltm = match snd(strip_comb l) with
      [lam;ltm] -> lam,ltm | _ -> failwith "HINTS_FOLD_TAC" in
  let bod = body lam in
  let th =
    if is_var(rand bod) then ISPECL [ltm; f; stm; oktm; rtm; s0] HINTS_FOLD0_EQ
    else ISPECL [ltm; f; stm; oktm; rtm; lhand(rand bod); s0] HINTS_FOLD_EQ in
  let bconv = DEPTH_CONV BETA_CONV in
  (SUBGOAL_THEN (lhand(concl th))
    (fun ath ->
       let th2 = MP th ath in
       let c1 = CONV_RULE (RATOR_CONV(RAND_CONV bconv) THENC
                           RAND_CONV(RAND_CONV bconv)) (CONJUNCT1 th2)
       and c2 = CONV_RULE (RATOR_CONV(RAND_CONV bconv)) (CONJUNCT2 th2) in
       let okall = lhand(concl c1) in
       ASM_CASES_TAC okall THENL
        [FIRST_ASSUM(fun a -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [MP c1 a]);
         FIRST_ASSUM(fun a ->
           let eth = MP c2 a in
           let v = fst(dest_exists(concl eth)) in
           X_CHOOSE_THEN (genvar(type_of v))
             (fun e -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [e]) eth)])) gl;;

(* ------------------------------------------------------------------------- *)
(* The number of hints before a position.                                    *)
(* ------------------------------------------------------------------------- *)

let HINTS_COUNT_0 = prove
 (`!h. mldsa_hint_count h 0 = 0`,
  REWRITE_TAC[mldsa_hint_count; LT; EMPTY_GSPEC; CARD_CLAUSES]);;

let HINTS_COUNT_SUC = prove
 (`!h p. mldsa_hint_count h (SUC p) =
         mldsa_hint_count h p + (if h p then 1 else 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_hint_count; LT] THEN
  SUBGOAL_THEN `FINITE {p' | p' < p /\ h p'}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p':num | p' < p}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `{p' | (p' = p \/ p' < p) /\ h p'} =
                  p INSERT {p' | p' < p /\ h p'}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM; LT_REFL] THEN ARITH_TAC];
    REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let HINTS_COUNT_MONO = prove
 (`!h p q. p <= q ==> mldsa_hint_count h p <= mldsa_hint_count h q`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_REFL];
    STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[HINTS_COUNT_SUC] THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= b + c`) THEN ASM_SIMP_TAC[]]);;

let HINTS_COUNT_STRICT = prove
 (`!h p q. h p /\ p < q ==> mldsa_hint_count h p < mldsa_hint_count h q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:num->bool`; `SUC p`; `q:num`] HINTS_COUNT_MONO) THEN
  ASM_REWRITE_TAC[LE_SUC_LT; HINTS_COUNT_SUC] THEN ARITH_TAC);;

let HINTS_COUNT_LE = prove
 (`!h p. mldsa_hint_count h p <= p`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[HINTS_COUNT_0; HINTS_COUNT_SUC; LE_REFL] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let HINTS_COUNT_EXISTS = prove
 (`!h q t. (?p. p < q /\ h p /\ mldsa_hint_count h p = t) <=>
           t < mldsa_hint_count h q`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[CONJUNCT1 LT; HINTS_COUNT_0] THEN
  ASM_REWRITE_TAC[LT; HINTS_COUNT_SUC; LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB; EXISTS_OR_THM;
                  UNWIND_THM2] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let HINTS_COUNT_INJ = prove
 (`!h p p'. h p /\ h p' /\ mldsa_hint_count h p = mldsa_hint_count h p'
            ==> p = p'`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`p:num`; `p':num`] LT_CASES) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HINTS_COUNT_STRICT; LT_REFL]);;

let HINTS_COUNT_SELECT = prove
 (`!h p q. h p /\ p < q
           ==> (@p'. p' < q /\ h p' /\
                     mldsa_hint_count h p' = mldsa_hint_count h p) = p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[HINTS_COUNT_INJ]);;

(* ------------------------------------------------------------------------- *)
(* The lifts of hint vectors.                                                *)
(* ------------------------------------------------------------------------- *)


let HINTS_RESIDUE_REP_BIT = prove
 (`!b. residue_rep (residue_of_int_mod (if b then &1 else &0):(2)residue) =
       if b then 1 else 0`,
  GEN_TAC THEN REWRITE_TAC[residue_of_int_mod_DEF; residue_SEL_CTR] THEN
  REWRITE_TAC[DIMINDEX_2; isa_int_mod] THEN CONV_TAC INT_REDUCE_CONV THEN
  COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[ISA_NAT_NUM]);;

(* ------------------------------------------------------------------------- *)
(* HintBitPack. hints_pack_buf k omega h p m is the byte string of the       *)
(* generated code after the positions before p have been visited and the     *)
(* counts of the first m polynomials have been written.                      *)
(* ------------------------------------------------------------------------- *)

let hints_pack_buf = new_definition
 `hints_pack_buf k omega (h:num->bool) p m =
    list_of_seq
     (\t. if t < omega then
            if t < mldsa_hint_count h p
            then word((@q. q < 256 * k /\ h q /\ mldsa_hint_count h q = t)
                      MOD 256)
            else word 0
          else if t - omega < m
          then word(mldsa_hint_count h (256 * (t - omega + 1)))
          else word 0:byte)
     (omega + k)`;;

let LENGTH_HINTS_PACK_BUF = prove
 (`!k omega h p m. LENGTH(hints_pack_buf k omega h p m) = omega + k`,
  REWRITE_TAC[hints_pack_buf; LENGTH_LIST_OF_SEQ]);;

let HINTS_PACK_BUF_0 = prove
 (`!k omega h. hints_pack_buf k omega h 0 0 = REPLICATE (omega + k) (word 0)`,
  REWRITE_TAC[LIST_EQ; LENGTH_HINTS_PACK_BUF; LENGTH_REPLICATE] THEN
  SIMP_TAC[hints_pack_buf; EL_LIST_OF_SEQ; EL_REPLICATE_LT; HINTS_COUNT_0;
           LT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let HINTS_PACK_BUF_NOHINT = prove
 (`!k omega h p m. ~h p
        ==> hints_pack_buf k omega h (SUC p) m = hints_pack_buf k omega h p m`,
  SIMP_TAC[hints_pack_buf; HINTS_COUNT_SUC; ADD_CLAUSES]);;

let HINTS_PACK_BUF_HINT = prove
 (`!k omega h p m.
        h p /\ p < 256 * k /\ mldsa_hint_count h (256 * k) <= omega
        ==> isa_list_update (hints_pack_buf k omega h p m)
                            (mldsa_hint_count h p) (word (p MOD 256)) =
            hints_pack_buf k omega h (SUC p) m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mldsa_hint_count h p < omega` ASSUME_TAC THENL
   [MP_TAC(SPECL [`h:num->bool`; `p:num`; `256 * k`] HINTS_COUNT_STRICT) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_HINTS_PACK_BUF; LENGTH_ISA_LIST_UPDATE] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_HINTS_PACK_BUF] THEN
  ASM_SIMP_TAC[hints_pack_buf; EL_LIST_OF_SEQ; HINTS_COUNT_SUC] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `t:num < t + 1`; HINTS_COUNT_SELECT];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let HINTS_PACK_BUF_COUNT = prove
 (`!k omega h i.
        hints_pack_buf k omega h (256 * (i + 1)) (i + 1) =
        isa_list_update (hints_pack_buf k omega h (256 * (i + 1)) i)
                        (omega + i)
                        (word (mldsa_hint_count h (256 * (i + 1))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_HINTS_PACK_BUF; LENGTH_ISA_LIST_UPDATE] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_HINTS_PACK_BUF] THEN
  ASM_SIMP_TAC[hints_pack_buf; EL_LIST_OF_SEQ] THEN
  ASM_CASES_TAC `t = omega + i` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(omega + i < omega:num)`; ADD_SUB2;
                  ARITH_RULE `i < i + 1`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let HINTS_PACK_BUF_FINAL = prove
 (`!k omega h.
        hints_pack_buf k omega h (256 * k) k = mldsa_hintbitpack k omega h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_HINTS_PACK_BUF; mldsa_hintbitpack;
              LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[hints_pack_buf; EL_LIST_OF_SEQ; HINTS_COUNT_EXISTS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The proof of HintBitPack for one parameter set (k,omega).                 *)
(* ------------------------------------------------------------------------- *)

let HINTS_HINTBITPACK_PROVE (k,omega,def) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let cname = fst(dest_const(fst(strip_comb(lhs(snd(dest_forall(concl def))))))) in
  let n = 256 * k in
  let goal = pt(sp
    "!h. mldsa_hint_count h %d <= %d
         ==> %s (lift_vec (\\i. lift_bitpoly (\\j. h (256 * i + j)))) =
             Value (mldsa_hintbitpack %d %d h)" n omega cname k omega) in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    REWRITE_TAC[typed_hol_int_to_byte_DEF] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[NATIVE_BIND_VALUE; GSYM WORD_IWORD] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV HINTS_SCHEDULE_CONV) THEN
    HINTS_FOLDL_TAC
     (pt(sp "\\i. (&(mldsa_hint_count h (256 * i)):int,
                   hints_pack_buf %d %d h (256 * i) i)" k omega))
     (pt(sp "(&(mldsa_hint_count h %d):int, hints_pack_buf %d %d h %d %d)"
            n k omega n k)) THENL
     [ALL_TAC;
      REWRITE_TAC[NATIVE_BIND_VALUE; UNCURRY_DEF; GSYM HINTS_PACK_BUF_FINAL] THEN
      CONV_TAC NUM_REDUCE_CONV] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; HINTS_COUNT_0; HINTS_PACK_BUF_0] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[UNCURRY_DEF] THEN
    HINTS_FOLDL_TAC
     (pt(sp "\\j. (&(mldsa_hint_count h (256 * i + j)):int,
                   hints_pack_buf %d %d h (256 * i + j) i, &i:int)" k omega))
     (pt(sp "(&(mldsa_hint_count h (256 * i + 256)):int,
              hints_pack_buf %d %d h (256 * i + 256) i, &i:int)" k omega)) THENL
     [ALL_TAC;
      (* The count byte after polynomial i. *)
      REWRITE_TAC[ARITH_RULE `256 * i + 256 = 256 * (i + 1)`;
                  ARITH_RULE `256 * SUC i = 256 * (i + 1)`; ADD1] THEN
      SUBGOAL_THEN (pt(sp "mldsa_hint_count h (256 * (i + 1)) <= %d" omega))
      ASSUME_TAC THENL
       [TRANS_TAC LE_TRANS (pt(sp "mldsa_hint_count h %d" n)) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HINTS_COUNT_MONO THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[NATIVE_BIND_VALUE; UNCURRY_DEF; typed_hol_nonnegative_DEF;
                  INT_OF_NUM_ADD; INT_POS; INT_OF_NUM_LT] THEN
      ASM_SIMP_TAC[ARITH_RULE(pt(sp "x <= %d ==> x < 256" omega));
                   NATIVE_BIND_VALUE; GSYM WORD_IWORD; NATIVE_LIST_UPDATE_LT;
                   LENGTH_HINTS_PACK_BUF;
                   ARITH_RULE(pt(sp "i < %d ==> %d + i < %d + %d"
                                    k omega omega k));
                   TYPED_HOL_READ_SOME; HINTS_PACK_BUF_COUNT]] THEN
    CONJ_TAC THENL [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    (* One coefficient. *)
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[UNCURRY_DEF] THEN
    REWRITE_TAC[typed_hol_bit_value_DEF; typed_hol_int_arithmetic_DEF;
                NATIVE_BIND_VALUE; INT_POW_ONE; INT_OF_NUM_LT; CONJUNCT1 LT;
                INT_MUL_LID; INT_ADD_LID; COMMON_VEC_ENTRIES_LIFT;
                DIMINDEX_CONV(pt(sp "dimindex(:%d)" k))] THEN
    ASM_SIMP_TAC[NATIVE_LIST_INDEX_LT; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
                 TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; FIPS204_BITPOLY_COEFFICIENTS_LIFT;
                 HINTS_RESIDUE_REP_BIT] THEN
    REWRITE_TAC[ADD_CLAUSES; HINTS_COUNT_SUC] THEN
    ASM_CASES_TAC `(h:num->bool)(256 * i + j)` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    ASM_SIMP_TAC[NATIVE_BIND_VALUE; UNCURRY_DEF; HINTS_PACK_BUF_NOHINT;
                 ADD_CLAUSES] THEN
    SUBGOAL_THEN (pt(sp "mldsa_hint_count h (256 * i + j) < %d" omega))
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`h:num->bool`; `256 * i + j`; mk_small_numeral n]
        HINTS_COUNT_STRICT) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[typed_hol_nonnegative_DEF; INT_POS; NATIVE_BIND_VALUE;
                GSYM WORD_IWORD] THEN
    ASM_SIMP_TAC[NATIVE_LIST_UPDATE_LT; LENGTH_HINTS_PACK_BUF;
                 ARITH_RULE(pt(sp "x < %d ==> x < %d + %d" omega omega k));
                 TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; UNCURRY_DEF;
                 INT_OF_NUM_ADD] THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    SUBGOAL_THEN `word j:byte = word((256 * i + j) MOD 256)` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]; ALL_TAC] THEN
    MATCH_MP_TAC HINTS_PACK_BUF_HINT THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let HINTS_HINTBITPACK_FLAT_MLDSA44 =
  HINTS_HINTBITPACK_PROVE (4,80,HintBitPack_MLDSA44_Configuration_hol_DEF);;
let HINTS_HINTBITPACK_FLAT_MLDSA65 =
  HINTS_HINTBITPACK_PROVE (6,55,HintBitPack_MLDSA65_Configuration_hol_DEF);;
let HINTS_HINTBITPACK_FLAT_MLDSA87 =
  HINTS_HINTBITPACK_PROVE (8,75,HintBitPack_MLDSA87_Configuration_hol_DEF);;

(* ------------------------------------------------------------------------- *)
(* FixedCountOnes_k and CountOnes: the number of hints.                      *)
(* ------------------------------------------------------------------------- *)

let HINTS_FIXEDCOUNTONES_PROVE (k,def) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let cname = fst(dest_const(fst(strip_comb(lhs(snd(dest_forall(concl def))))))) in
  let n = 256 * k in
  let goal = pt(sp
    "!h. %s (lift_vec (\\i. lift_bitpoly (\\j. h (256 * i + j)))) =
         Value (&(mldsa_hint_count h %d))" cname n) in
  prove(goal,
    GEN_TAC THEN REWRITE_TAC[def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV HINTS_SCHEDULE_CONV) THEN
    HINTS_FOLDL_TAC `\i. &(mldsa_hint_count h (256 * i)):int`
                    (pt(sp "&(mldsa_hint_count h %d):int" n)) THEN
    REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[MULT_CLAUSES; HINTS_COUNT_0]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    HINTS_FOLDL_TAC `\j. &(mldsa_hint_count h (256 * i + j)):int`
                    `&(mldsa_hint_count h (256 * SUC i)):int` THEN
    REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[typed_hol_bit_value_DEF; typed_hol_int_arithmetic_DEF;
                NATIVE_BIND_VALUE; INT_POW_ONE; INT_OF_NUM_LT; CONJUNCT1 LT;
                INT_MUL_LID; INT_ADD_LID; COMMON_VEC_ENTRIES_LIFT;
                DIMINDEX_CONV(pt(sp "dimindex(:%d)" k))] THEN
    ASM_SIMP_TAC[NATIVE_LIST_INDEX_LT; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
                 TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; FIPS204_BITPOLY_COEFFICIENTS_LIFT;
                 HINTS_RESIDUE_REP_BIT] THEN
    REWRITE_TAC[ADD_CLAUSES; HINTS_COUNT_SUC] THEN AP_TERM_TAC THEN
    ASM_CASES_TAC `(h:num->bool)(256 * i + j)` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_OF_NUM_ADD; ADD_CLAUSES]);;

let HINTS_FIXEDCOUNTONES_FLAT_4 =
  HINTS_FIXEDCOUNTONES_PROVE (4,FixedCountOnes_4_hol_DEF);;
let HINTS_FIXEDCOUNTONES_FLAT_6 =
  HINTS_FIXEDCOUNTONES_PROVE (6,FixedCountOnes_6_hol_DEF);;
let HINTS_FIXEDCOUNTONES_FLAT_8 =
  HINTS_FIXEDCOUNTONES_PROVE (8,FixedCountOnes_8_hol_DEF);;

(* CountOnes on a list of n coefficient lists (it is not used by the         *)
(* generated algorithms, which use FixedCountOnes_k): it counts the          *)
(* coefficients equal to 1.                                                  *)


let EQ_COUNTONES = prove
 (`!a n. CountOnes_hol
          (list_of_seq (\i. list_of_seq (\j. lift_zq (a (256 * i + j))) 256)
                       n) =
         Value (&(mldsa_hint_count (\p. a p rem &8380417 = &1) (256 * n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CountOnes_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; ISA_NAT_NUM] THEN
  REWRITE_TAC[MATCH_MP (SPECL [`SUC n`; `n:num`] NATIVE_SCHEDULE_NUM)
                       (ARITH_RULE `n <= SUC n`)] THEN
  CONV_TAC(ONCE_DEPTH_CONV HINTS_SCHEDULE_CONV) THEN
  HINTS_FOLDL_TAC
   `\i. &(mldsa_hint_count (\p. a p rem &8380417 = &1) (256 * i)):int`
   `&(mldsa_hint_count (\p. a p rem &8380417 = &1) (256 * n)):int` THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[MULT_CLAUSES; HINTS_COUNT_0]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  HINTS_FOLDL_TAC
   `\j. &(mldsa_hint_count (\p. a p rem &8380417 = &1) (256 * i + j)):int`
   `&(mldsa_hint_count (\p. a p rem &8380417 = &1) (256 * SUC i)):int` THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[typed_hol_bit_value_DEF; typed_hol_int_arithmetic_DEF;
              NATIVE_BIND_VALUE; INT_POW_ONE; INT_OF_NUM_LT; CONJUNCT1 LT;
              INT_MUL_LID; INT_ADD_LID; CoefficientToInteger_hol_DEF] THEN
  ASM_SIMP_TAC[NATIVE_LIST_INDEX_LT; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
               TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; LIFT_ZQ_REP] THEN
  REWRITE_TAC[ADD_CLAUSES; HINTS_COUNT_SUC] THEN AP_TERM_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; ADD_CLAUSES]);;

let EQ_COUNTONES_HINTS = prove
 (`!h n. CountOnes_hol
          (list_of_seq
            (\i. list_of_seq
                  (\j. lift_zq (if h (256 * i + j) then &1 else &0)) 256)
            n) =
         Value (&(mldsa_hint_count h (256 * n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EQ_COUNTONES] THEN
  REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* HintBitUnpack. hints_unpack_pred omega y i t i' j says that the generated *)
(* code has set coefficient j of h[i'] once it has read the indices of the   *)
(* polynomials before i and those of polynomial i before position t of y.    *)
(* ------------------------------------------------------------------------- *)

let hints_unpack_pred = new_definition
 `hints_unpack_pred omega (y:byte list) i t i' j <=>
    (i' < i /\
     ?t'. mldsa_hint_start omega y i' <= t' /\
          t' < val(EL (omega + i') y) /\ val(EL t' y) = j) \/
    (i' = i /\
     ?t'. mldsa_hint_start omega y i <= t' /\ t' < t /\ val(EL t' y) = j)`;;

let HINTS_HINT_START_0 = prove
 (`!omega y. mldsa_hint_start omega y 0 = 0`,
  REWRITE_TAC[mldsa_hint_start]);;

let HINTS_HINT_START_SUC = prove
 (`!omega y i. mldsa_hint_start omega y (i + 1) = val(EL (omega + i) y)`,
  REWRITE_TAC[mldsa_hint_start; ADD_EQ_0; ARITH_EQ;
              ARITH_RULE `omega + (i + 1) - 1 = omega + i`]);;

let HINTS_UNPACK_PRED_0 = prove
 (`!omega y i' j. ~hints_unpack_pred omega y 0 0 i' j`,
  REWRITE_TAC[hints_unpack_pred; CONJUNCT1 LT; HINTS_HINT_START_0] THEN
  ARITH_TAC);;

let HINTS_UNPACK_PRED_STEP = prove
 (`!omega y i t.
        mldsa_hint_start omega y i <= t
        ==> hints_unpack_pred omega y i (t + 1) =
            \i' j. hints_unpack_pred omega y i t i' j \/
                   i' = i /\ j = val(EL t y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; hints_unpack_pred] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i':num = i` THEN ASM_REWRITE_TAC[LT_REFL] THEN
  REWRITE_TAC[ARITH_RULE `t' < t + 1 <=> t' < t \/ t' = t`] THEN
  ASM_MESON_TAC[LE_REFL]);;

let HINTS_EMPTY_RANGE = prove
 (`!a t:num P. (a <= t /\ t < a /\ P) <=> F`,
  MESON_TAC[NOT_LT]);;

let HINTS_UNPACK_PRED_NEXT = prove
 (`!omega y i.
        hints_unpack_pred omega y i (val(EL (omega + i) y)) =
        hints_unpack_pred omega y (i + 1) (mldsa_hint_start omega y (i + 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; hints_unpack_pred] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HINTS_EMPTY_RANGE] THEN
  REWRITE_TAC[ARITH_RULE `i' < i + 1 <=> i' < i \/ i' = i`] THEN
  ASM_CASES_TAC `i':num = i` THEN ASM_REWRITE_TAC[LT_REFL] THEN
  ASM_MESON_TAC[LT_REFL]);;

let HINTS_UNPACK_PRED_FINAL = prove
 (`!k omega y i' j.
        i' < k /\ j < 256
        ==> (hints_unpack_pred omega y k (mldsa_hint_start omega y k) i' j <=>
             256 * i' + j < 256 * k /\
             ?t. mldsa_hint_start omega y ((256 * i' + j) DIV 256) <= t /\
                 t < val(EL (omega + (256 * i' + j) DIV 256) y) /\
                 val(EL t y) = (256 * i' + j) MOD 256)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(256 * i' + j) DIV 256 = i' /\ (256 * i' + j) MOD 256 = j`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ARITH_EQ;
                 ADD_CLAUSES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[hints_unpack_pred] THEN
  REWRITE_TAC[HINTS_EMPTY_RANGE] THEN
  ASM_SIMP_TAC[ARITH_RULE `i' < k /\ j < 256 ==> 256 * i' + j < 256 * k`] THEN
  ASM_MESON_TAC[LT_REFL]);;

(* The value of the h vector of the generated code.                          *)


let HINTS_LIFT_HINTS_0 = prove
 (`!P. (!i j. ~P i j)
       ==> (lift_vec (\i. lift_bitpoly (P i)):(N,fips204_bitpoly)common_vec) =
           Common_Vec (MAP FIPS204_BitPoly
                        (REPLICATE (dimindex(:N))
                          (REPLICATE 256 (residue_of_int_mod (&0)))))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lift_vec; lift_bitpoly] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP; LENGTH_REPLICATE] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP; LENGTH_REPLICATE; EL_REPLICATE_LT] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_REPLICATE] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; EL_REPLICATE_LT]);;

let HINTS_LIFT_HINTS_UPDATE = prove
 (`!P i j0.
        i < dimindex(:N) /\ j0 < 256
        ==> typed_hol_read
             (typed_hol_nominal_update Common_Vec common_vec_entries
               (\nf. typed_hol_nested_update
                      (typed_hol_nominal_update FIPS204_BitPoly
                        fips204_bitpoly_coefficients
                        (\nfa. native_list_update nfa (&j0)
                                (residue_of_int_mod (&1))))
                      nf (&i))
               (lift_vec (\i'. lift_bitpoly (P i'))
                 :(N,fips204_bitpoly)common_vec)) =
            Value (lift_vec (\i'. lift_bitpoly (\j. P i' j \/ i' = i /\ j = j0)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[typed_hol_nominal_update_DEF; COMMON_VEC_ENTRIES_LIFT;
              typed_hol_nested_update_DEF; LENGTH_LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[INT_POS; INT_OF_NUM_LT; ISA_NAT_NUM] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; FIPS204_BITPOLY_COEFFICIENTS_LIFT; NATIVE_LIST_UPDATE_LT;
               LENGTH_LIST_OF_SEQ; isa_map_option; TYPED_HOL_READ_SOME] THEN
  AP_TERM_TAC THEN REWRITE_TAC[lift_vec] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i':num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ;
               EL_LIST_OF_SEQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[lift_bitpoly; ETA_AX] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ;
               EL_LIST_OF_SEQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* When the generated checks of HintBitUnpack succeed: mldsa_hint_ok.        *)
(* ------------------------------------------------------------------------- *)

let HINTS_FORALL_RANGE_LT = prove
 (`!P a b. (!t. a < t /\ t < b ==> P t) <=>
           (!j. j < b - a ==> 0 < j ==> P (a + j))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `t - a:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `a < t ==> a + (t - a) = t:num`] THEN
    DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ASM_ARITH_TAC]);;

let HINTS_FORALL_RANGE_LE = prove
 (`!P a b. (!t. a <= t /\ t < b ==> P t) <=> (!j. j < b - a ==> P (a + j))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `t - a:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `a <= t ==> a + (t - a) = t:num`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let HINTS_UNPACK_OK = prove
 (`!k omega y.
        (!i. i < k
             ==> (mldsa_hint_start omega y i <= val(EL (omega + i) y) /\
                  val(EL (omega + i) y) <= omega) /\
                 (!j. j < val(EL (omega + i) y) - mldsa_hint_start omega y i
                      ==> 0 < j
                      ==> val(EL ((mldsa_hint_start omega y i + j) - 1) y) <
                          val(EL (mldsa_hint_start omega y i + j) y))) /\
        (!j. j < omega - mldsa_hint_start omega y k
             ==> val(EL (mldsa_hint_start omega y k + j) y) = 0)
        <=> mldsa_hint_ok k omega y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_hint_ok; VAL_EQ_0] THEN
  REWRITE_TAC[GSYM HINTS_FORALL_RANGE_LE; GSYM HINTS_FORALL_RANGE_LT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[AND_FORALL_THM; TAUT `(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)`]
  THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The proof of HintBitUnpack for one parameter set (k,omega), first with    *)
(* the h vector given by hints_unpack_pred.                                  *)
(* ------------------------------------------------------------------------- *)

let HINTS_RESULT_REWRS =
  [case_native_result_DEF; case_statement_outcome_DEF;
   map_native_result_DEF; map_statement_outcome_DEF; native_continue_bind_DEF];;

let HINTS_EXISTS_REFL = prove(`!a:A. ?x. a = x`, MESON_TAC[]);;

let HINTS_RETURN_TAC =
  REWRITE_TAC[NATIVE_RESULT_INJ; STATEMENT_OUTCOME_INJ; I_THM; HINTS_EXISTS_REFL];;

let HINTS_VAL_BYTE = prove
 (`!w:byte. val w < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `w:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let HINTS_HINTBITUNPACK_CORE (k,omega,def,recths) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let cname = fst(dest_const(fst(strip_comb(lhs(snd(dest_forall(concl def))))))) in
  let ext = String.sub cname 0 (String.length cname - 4) ^ "_hol_emitted_state_ext" in
  let ext = if can get_const_type ext then ext
            else cname ^ "_emitted_state_ext" in
  let vty = sp "(%d,fips204_bitpoly)common_vec" k in
  let bot = sp "Native_Bottom:(%s)native_bottom" vty in
  let dimth = DIMINDEX_CONV(pt(sp "dimindex(:%d)" k)) in
  let goal = pt(sp
    "!y. LENGTH y = %d
         ==> %s y =
             Value (if mldsa_hint_ok %d %d y
                    then Native_Value
                          (lift_vec (\\i. lift_bitpoly (\\j.
                             hints_unpack_pred %d y %d
                              (mldsa_hint_start %d y %d) i j)))
                    else Native_Bottom)"
    (omega + k) cname k omega omega k omega k) in
  let s_out = pt(sp
    "\\i. (Native_Assigned (lift_vec (\\i'. lift_bitpoly
             (hints_unpack_pred %d y i (mldsa_hint_start %d y i) i')):%s),
          Native_Assigned (&(mldsa_hint_start %d y i):int))"
    omega omega vty omega)
  and ok_out = pt(sp
    "\\i. (mldsa_hint_start %d y i <= val(EL (%d + i) y) /\\
          val(EL (%d + i) y) <= %d) /\\
         (!j. j < val(EL (%d + i) y) - mldsa_hint_start %d y i
              ==> 0 < j
              ==> val(EL ((mldsa_hint_start %d y i + j) - 1) y) <
                  val(EL (mldsa_hint_start %d y i + j) y))"
    omega omega omega omega omega omega omega omega)
  and s_in = pt(sp
    "\\j. %s
          (Native_Assigned (lift_vec (\\i'. lift_bitpoly
             (hints_unpack_pred %d y i (mldsa_hint_start %d y i + j) i')):%s))
          (Native_Assigned (&(mldsa_hint_start %d y i + j):int))
          (Native_Assigned (&i:int))"
    ext omega omega vty omega)
  and ok_in = pt(sp
    "\\j. 0 < j ==> val(EL ((mldsa_hint_start %d y i + j) - 1) y) <
                   val(EL (mldsa_hint_start %d y i + j) y)" omega omega)
  and s_zero = pt(sp
    "\\j:num. (Native_Assigned (lift_vec (\\i'. lift_bitpoly
             (hints_unpack_pred %d y %d (mldsa_hint_start %d y %d) i')):%s),
          Native_Assigned (&(mldsa_hint_start %d y %d):int))"
    omega k omega k vty omega k)
  and ok_zero = pt(sp
    "\\j. val(EL (mldsa_hint_start %d y %d + j) (y:byte list)) = 0" omega k)
  and r = pt bot in
  let s_ij = pt(sp "mldsa_hint_start %d y i + j" omega) in
  let UPDATE_TAC =
    REWRITE_TAC(HINTS_RESULT_REWRS @ recths @
                [typed_hol_slot_read_DEF; case_native_slot_DEF;
                 NATIVE_BIND_VALUE]) THEN
    SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,s_ij),
                          `LENGTH(y:byte list)`)) ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NATIVE_LIST_INDEX_LT; TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE;
                 HINTS_LIFT_HINTS_UPDATE; dimth; HINTS_VAL_BYTE;
                 INT_OF_NUM_ADD] THEN
    REWRITE_TAC[ARITH_RULE `s + SUC j = (s + j) + 1`] THEN
    SIMP_TAC[HINTS_UNPACK_PRED_STEP; LE_ADD] in
  let NOT_OK_TAC =
    REWRITE_TAC[GSYM HINTS_UNPACK_OK] THEN ASM_REWRITE_TAC[] in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV HINTS_SCHEDULE_CONV) THEN
    HINTS_FOLD_TAC s_out ok_out r THENL
     [ALL_TAC;
      (* All polynomials are well formed: the zero bytes. *)
      REWRITE_TAC[native_finish_DEF; case_native_result_DEF;
                  case_statement_outcome_DEF] THEN
      REWRITE_TAC[typed_hol_slot_read_DEF; case_native_slot_DEF;
                  NATIVE_BIND_VALUE] THEN
      SUBGOAL_THEN (pt(sp "mldsa_hint_start %d y %d <= %d" omega k omega))
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC (mk_small_numeral(k - 1))) THEN
        REWRITE_TAC[ARITH_RULE(pt(sp "%d = %d + 1" k (k - 1)));
                    HINTS_HINT_START_SUC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[HINTS_ISA_NAT_SUB] THEN
      ASM_SIMP_TAC[HINTS_SCHEDULE; ARITH_RULE `x <= SUC x`] THEN
      HINTS_FOLD_TAC s_zero ok_zero r THENL
       [REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        REWRITE_TAC[UNCURRY_DEF] THEN
        SUBGOAL_THEN (pt(sp "mldsa_hint_start %d y %d + j < LENGTH(y:byte list)"
                            omega k)) ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[NATIVE_LIST_INDEX_LT; TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE;
                     typed_hol_byte_value_DEF; INT_OF_NUM_EQ] THEN
        ASM_CASES_TAC (pt(sp "val(EL (mldsa_hint_start %d y %d + j)
                                 (y:byte list)) = 0" omega k)) THEN
        ASM_REWRITE_TAC(HINTS_RESULT_REWRS @ recths @ [I_THM]) THEN
        HINTS_RETURN_TAC;
        REWRITE_TAC[case_native_result_DEF; case_statement_outcome_DEF;
                    typed_hol_slot_read_DEF; case_native_slot_DEF;
                    NATIVE_BIND_VALUE; ETA_AX] THEN
        SUBGOAL_THEN (pt(sp "mldsa_hint_ok %d %d y" k omega))
         (fun th -> REWRITE_TAC[th]) THEN
        NOT_OK_TAC;
        REWRITE_TAC[case_native_result_DEF; case_statement_outcome_DEF] THEN
        SUBGOAL_THEN (pt(sp "~mldsa_hint_ok %d %d y" k omega))
         (fun th -> REWRITE_TAC[th]) THEN
        NOT_OK_TAC];
      (* Some polynomial is malformed. *)
      REWRITE_TAC[native_finish_DEF; case_native_result_DEF;
                  case_statement_outcome_DEF] THEN
      SUBGOAL_THEN (pt(sp "~mldsa_hint_ok %d %d y" k omega))
       (fun th -> REWRITE_TAC[th]) THEN
      NOT_OK_TAC] THEN
    (* The initial state and one polynomial. *)
    CONJ_TAC THENL
     [REWRITE_TAC[HINTS_HINT_START_0; PAIR_EQ] THEN AP_TERM_TAC THEN
      MP_TAC(INST_TYPE [parse_type(string_of_int k),`:N`]
        (ISPEC (pt(sp "hints_unpack_pred %d y 0 0" omega))
          HINTS_LIFT_HINTS_0)) THEN
      REWRITE_TAC[HINTS_UNPACK_PRED_0; dimth];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[UNCURRY_DEF] THEN
    SUBGOAL_THEN (pt(sp "%d + i < LENGTH(y:byte list)" omega)) ASSUME_TAC
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[INT_OF_NUM_ADD; NATIVE_LIST_INDEX_LT; TYPED_HOL_READ_SOME;
                 NATIVE_BIND_VALUE; typed_hol_byte_value_DEF;
                 typed_hol_slot_read_DEF; case_native_slot_DEF;
                 INT_OF_NUM_LT; INT_SUB_LT] THEN
    REWRITE_TAC[ARITH_RULE(pt(sp "e < s \\/ %d < e <=> ~(s <= e /\\ e <= %d)"
                                 omega omega))] THEN
    ASM_CASES_TAC (pt(sp "mldsa_hint_start %d y i <= val (EL (%d + i) y) /\\
                          val (EL (%d + i) y) <= %d" omega omega omega omega))
    THEN ASM_REWRITE_TAC HINTS_RESULT_REWRS THENL [ALL_TAC; HINTS_RETURN_TAC] THEN
    REWRITE_TAC recths THEN
    REWRITE_TAC[INT_OF_NUM_ADD; NATIVE_BIND_VALUE; typed_hol_byte_value_DEF;
                typed_hol_slot_read_DEF; case_native_slot_DEF;
                case_native_result_DEF] THEN
    ASM_SIMP_TAC[NATIVE_LIST_INDEX_LT; TYPED_HOL_READ_SOME] THEN
    REWRITE_TAC[NATIVE_BIND_VALUE; typed_hol_byte_value_DEF;
                case_native_result_DEF] THEN
    ASM_SIMP_TAC[HINTS_ISA_NAT_SUB] THEN
    ASM_SIMP_TAC[HINTS_SCHEDULE; ARITH_RULE `x <= SUC x`] THEN
    HINTS_FOLD_TAC s_in ok_in r THENL
     [ALL_TAC;
      ASM_REWRITE_TAC HINTS_RESULT_REWRS THEN
      REWRITE_TAC(recths @ [I_THM; NATIVE_RESULT_INJ; STATEMENT_OUTCOME_INJ;
                            PAIR_EQ; NATIVE_SLOT_INJ]) THEN
      ASM_SIMP_TAC[ARITH_RULE `a <= b ==> a + (b - a) = b:num`] THEN
      REWRITE_TAC[ADD1; HINTS_UNPACK_PRED_NEXT] THEN
      REWRITE_TAC[HINTS_HINT_START_SUC];
      ASM_REWRITE_TAC HINTS_RESULT_REWRS THEN HINTS_RETURN_TAC] THEN
    (* One index of polynomial i. *)
    REWRITE_TAC[] THEN CONJ_TAC THENL [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(HINTS_RESULT_REWRS @ recths) THEN
    REWRITE_TAC[INT_ADD_SUB2; INT_OF_NUM_LT; INT_SUB_LT] THEN
    REWRITE_TAC[ARITH_RULE `a < a + j <=> 0 < j`] THEN
    ASM_CASES_TAC `0 < j` THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; UPDATE_TAC] THEN
    SUBGOAL_THEN (pt(sp "(&(mldsa_hint_start %d y i + j):int) - &1 =
                         &((mldsa_hint_start %d y i + j) - 1)" omega omega))
    SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_SUB THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,s_ij),
                          `LENGTH(y:byte list)`)) ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NATIVE_LIST_INDEX_LT; ARITH_RULE `x < n ==> x - 1 < n`;
                 TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE;
                 INT_SUB_LE; INT_OF_NUM_LE; GSYM NOT_LT] THEN
    ASM_CASES_TAC (pt(sp "val (EL ((mldsa_hint_start %d y i + j) - 1) y) <
                          val (EL (mldsa_hint_start %d y i + j)
                                  (y:byte list))" omega omega)) THEN
    ASM_REWRITE_TAC[] THENL
     [UPDATE_TAC; REWRITE_TAC HINTS_RESULT_REWRS THEN HINTS_RETURN_TAC]);;

let HINTS_REC44 =
  HintBitUnpack_MLDSA44_Configuration_hol_emitted_state_SELECTORS @
  [HintBitUnpack_MLDSA44_Configuration_hol_emitted_h_update_EXT;
   HintBitUnpack_MLDSA44_Configuration_hol_emitted_Index_update_EXT;
   HintBitUnpack_MLDSA44_Configuration_hol_emitted_i_update_EXT];;

let HINTS_REC65 =
  HintBitUnpack_MLDSA65_Configuration_hol_emitted_state_SELECTORS @
  [HintBitUnpack_MLDSA65_Configuration_hol_emitted_h_update_EXT;
   HintBitUnpack_MLDSA65_Configuration_hol_emitted_Index_update_EXT;
   HintBitUnpack_MLDSA65_Configuration_hol_emitted_i_update_EXT];;

let HINTS_REC87 =
  HintBitUnpack_MLDSA87_Configuration_hol_emitted_state_SELECTORS @
  [HintBitUnpack_MLDSA87_Configuration_hol_emitted_h_update_EXT;
   HintBitUnpack_MLDSA87_Configuration_hol_emitted_Index_update_EXT;
   HintBitUnpack_MLDSA87_Configuration_hol_emitted_i_update_EXT];;

let HINTS_HINTBITUNPACK_MLDSA44 = HINTS_HINTBITUNPACK_CORE
  (4,80,HintBitUnpack_MLDSA44_Configuration_hol_DEF,HINTS_REC44);;
let HINTS_HINTBITUNPACK_MLDSA65 = HINTS_HINTBITUNPACK_CORE
  (6,55,HintBitUnpack_MLDSA65_Configuration_hol_DEF,HINTS_REC65);;
let HINTS_HINTBITUNPACK_MLDSA87 = HINTS_HINTBITUNPACK_CORE
  (8,75,HintBitUnpack_MLDSA87_Configuration_hol_DEF,HINTS_REC87);;

(* ------------------------------------------------------------------------- *)
(* HintBitUnpack against mldsa_hintbitunpack: Native_Bottom is NONE.         *)
(* ------------------------------------------------------------------------- *)

let HINTS_HINTBITUNPACK_FINAL (k,omega,core) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let cname = fst(dest_const(fst(strip_comb(lhs(rand(snd(dest_forall(concl core)))))))) in
  let dimth = DIMINDEX_CONV(pt(sp "dimindex(:%d)" k)) in
  let goal = pt(sp
    "!y. LENGTH y = %d
         ==> %s y =
             Value (match mldsa_hintbitunpack %d %d y with
                      NONE -> Native_Bottom
                    | SOME h ->
                        Native_Value
                         (lift_vec (\\i. lift_bitpoly (\\j. h (256 * i + j)))))"
    (omega + k) cname k omega) in
  prove(goal,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[core] THEN
    REWRITE_TAC[mldsa_hintbitunpack] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV MATCH_CONV) THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LIFT_BITPOLY_VEC_CONG THEN REWRITE_TAC[dimth] THEN
    SIMP_TAC[HINTS_UNPACK_PRED_FINAL]);;

let EQ_HINTBITUNPACK_MLDSA44 =
  HINTS_HINTBITUNPACK_FINAL (4,80,HINTS_HINTBITUNPACK_MLDSA44);;
let EQ_HINTBITUNPACK_MLDSA65 =
  HINTS_HINTBITUNPACK_FINAL (6,55,HINTS_HINTBITUNPACK_MLDSA65);;
let EQ_HINTBITUNPACK_MLDSA87 =
  HINTS_HINTBITUNPACK_FINAL (8,75,HINTS_HINTBITUNPACK_MLDSA87);;

(* The two cases, for callers that split on mldsa_hintbitunpack.             *)

let HINTS_HINTBITUNPACK_CASES (k,omega,th) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let cname = fst(dest_const(fst(strip_comb(lhs(rand(snd(dest_forall(concl th)))))))) in
  let some = prove(pt(sp
   "!y h. LENGTH y = %d /\\ mldsa_hintbitunpack %d %d y = SOME h
          ==> %s y =
              Value (Native_Value
                      (lift_vec (\\i. lift_bitpoly (\\j. h (256 * i + j)))))"
   (omega + k) k omega cname),
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[th] THEN
   CONV_TAC(TOP_DEPTH_CONV MATCH_CONV) THEN REWRITE_TAC[])
  and none = prove(pt(sp
   "!y. LENGTH y = %d /\\ mldsa_hintbitunpack %d %d y = NONE
        ==> %s y = Value Native_Bottom"
   (omega + k) k omega cname),
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[th] THEN
   CONV_TAC(TOP_DEPTH_CONV MATCH_CONV) THEN REWRITE_TAC[]) in
  some,none;;

let EQ_HINTBITUNPACK_MLDSA44_SOME,EQ_HINTBITUNPACK_MLDSA44_NONE =
  HINTS_HINTBITUNPACK_CASES (4,80,EQ_HINTBITUNPACK_MLDSA44);;
let EQ_HINTBITUNPACK_MLDSA65_SOME,EQ_HINTBITUNPACK_MLDSA65_NONE =
  HINTS_HINTBITUNPACK_CASES (6,55,EQ_HINTBITUNPACK_MLDSA65);;
let EQ_HINTBITUNPACK_MLDSA87_SOME,EQ_HINTBITUNPACK_MLDSA87_NONE =
  HINTS_HINTBITUNPACK_CASES (8,75,EQ_HINTBITUNPACK_MLDSA87);;

(* ------------------------------------------------------------------------- *)
(* Hint vectors given by a predicate h i j on (polynomial, coefficient), as  *)
(* MakeHint returns them, and the flat predicate \p. h (p DIV 256) (p MOD    *)
(* 256) on the positions p = 256 * i + j of common/fips204/fips204.ml.       *)
(* ------------------------------------------------------------------------- *)


let HINTS_LIFT_HINTS_FLAT = prove
 (`!h. (lift_vec (\i. lift_bitpoly
                       (\j. (\p. h (p DIV 256) (p MOD 256)) (256 * i + j)))
        :(N,fips204_bitpoly)common_vec) =
       lift_vec (\i. lift_bitpoly (h i))`,
  GEN_TAC THEN MATCH_MP_TAC LIFT_BITPOLY_VEC_CONG THEN
  SIMP_TAC[DIV_MOD_256_SMALL]);;

let HINTS_HINT_COUNT_CONG = prove
 (`!h h' n. (!p. p < n ==> (h p <=> h' p))
            ==> mldsa_hint_count h n = mldsa_hint_count h' n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_hint_count] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let HINTS_HINTBITPACK_CONG = prove
 (`!k omega h h'.
        (!p. p < 256 * k ==> (h p <=> h' p))
        ==> mldsa_hintbitpack k omega h = mldsa_hintbitpack k omega h'`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mldsa_hintbitpack; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `!q. q <= 256 * k
                    ==> mldsa_hint_count h q = mldsa_hint_count h' q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HINTS_HINT_COUNT_CONG THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p < 256 * k /\ h p /\ mldsa_hint_count h p = t <=>
        p < 256 * k /\ h' p /\ mldsa_hint_count h' p = t`
   (fun th -> REWRITE_TAC[th])
  THENL [ASM_MESON_TAC[LT_IMP_LE]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let HINTS_TWOARG_PACK (k,omega,flat) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let n = 256 * k in
  let cname = fst(dest_const(fst(strip_comb(lhand(rand(snd(dest_forall(concl flat)))))))) in
  prove(pt(sp
   "!h. mldsa_hint_count (\\p. h (p DIV 256) (p MOD 256)) %d <= %d
        ==> %s (lift_vec (\\i. lift_bitpoly (h i))) =
            Value (mldsa_hintbitpack %d %d (\\p. h (p DIV 256) (p MOD 256)))"
   n omega cname k omega),
   GEN_TAC THEN
   DISCH_THEN(MP_TAC o MATCH_MP (SPEC `\p. (h:num->num->bool) (p DIV 256) (p MOD 256)` flat)) THEN
   REWRITE_TAC[HINTS_LIFT_HINTS_FLAT]);;

let HINTS_TWOARG_COUNT (k,flat) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let n = 256 * k in
  let cname = fst(dest_const(fst(strip_comb(lhs(snd(dest_forall(concl flat))))))) in
  prove(pt(sp
   "!h. %s (lift_vec (\\i. lift_bitpoly (h i))) =
        Value (&(mldsa_hint_count (\\p. h (p DIV 256) (p MOD 256)) %d))"
   cname n),
   GEN_TAC THEN
   MP_TAC(SPEC `\p. (h:num->num->bool) (p DIV 256) (p MOD 256)` flat) THEN
   REWRITE_TAC[HINTS_LIFT_HINTS_FLAT]);;

let EQ_HINTBITPACK_MLDSA44 =
  HINTS_TWOARG_PACK (4,80,HINTS_HINTBITPACK_FLAT_MLDSA44);;
let EQ_HINTBITPACK_MLDSA65 =
  HINTS_TWOARG_PACK (6,55,HINTS_HINTBITPACK_FLAT_MLDSA65);;
let EQ_HINTBITPACK_MLDSA87 =
  HINTS_TWOARG_PACK (8,75,HINTS_HINTBITPACK_FLAT_MLDSA87);;

let EQ_FIXEDCOUNTONES_4 = HINTS_TWOARG_COUNT (4,HINTS_FIXEDCOUNTONES_FLAT_4);;
let EQ_FIXEDCOUNTONES_6 = HINTS_TWOARG_COUNT (6,HINTS_FIXEDCOUNTONES_FLAT_6);;
let EQ_FIXEDCOUNTONES_8 = HINTS_TWOARG_COUNT (8,HINTS_FIXEDCOUNTONES_FLAT_8);;

(* ------------------------------------------------------------------------- *)
(* Byte strings: concatenated encodings and the fields of a sub-list.        *)
(* ------------------------------------------------------------------------- *)


let HINTS_SLICE_SPLIT = prove
 (`!s n (b:byte list).
        s + n <= LENGTH b
        ==> b = APPEND (mldsa_slice 0 s b)
                 (APPEND (mldsa_slice s n b)
                         (mldsa_slice (s + n) (LENGTH b - (s + n)) b))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_APPEND; LENGTH_MLDSA_SLICE] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_APPEND; LENGTH_APPEND; LENGTH_MLDSA_SLICE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[EL_MLDSA_SLICE]) THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_MLDSA_SLICE o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let HINTS_NUM_OF_BYTELIST_SLICE = prove
 (`!s n b.
        s + n <= LENGTH b
        ==> num_of_bytelist (mldsa_slice s n b) =
            (num_of_bytelist b DIV 256 EXP s) MOD 256 EXP n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV o
                                          RAND_CONV)
                         [MATCH_MP HINTS_SLICE_SPLIT th]) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_MLDSA_SLICE] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; NUM_OF_BYTELIST_BOUND;
           LENGTH_MLDSA_SLICE; DIV_LT; ADD_CLAUSES] THEN
  MP_TAC(ISPEC `mldsa_slice 0 s (b:byte list)` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_MLDSA_SLICE] THEN SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  SIMP_TAC[MOD_MULT_ADD] THEN
  MP_TAC(ISPEC `mldsa_slice s n (b:byte list)` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_MLDSA_SLICE] THEN SIMP_TAC[MOD_LT]);;

let HINTS_MOD_DIV_MOD_EXP = prove
 (`!A M a c. a + c <= M
             ==> ((A MOD 2 EXP M) DIV 2 EXP a) MOD 2 EXP c =
                 (A DIV 2 EXP a) MOD 2 EXP c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP M = 2 EXP a * 2 EXP c * 2 EXP (M - a - c)` SUBST1_TAC
  THENL [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
         ALL_TAC] THEN
  SIMP_TAC[GSYM DIV_MOD; MOD_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let HINTS_FIELD_BOUND_256 = prove
 (`!c j. j < 256 ==> c * j + c <= 8 * 32 * c`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `c * j + c = c * (j + 1)`;
              ARITH_RULE `8 * 32 * c = c * 256`; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let HINTS_FIELD_SUBSLICE = prove
 (`!c b i j.
        32 * c * (i + 1) <= LENGTH b /\ j < 256
        ==> mldsa_field c (mldsa_slice (32 * c * i) (32 * c) b) j =
            mldsa_field c b (256 * i + j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_field; INT_OF_NUM_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HINTS_NUM_OF_BYTELIST_SLICE o
    lhand o lhand o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
  ASM_SIMP_TAC[HINTS_MOD_DIV_MOD_EXP; HINTS_FIELD_BOUND_256] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

let HINTS_FIELD_SLICE = prove
 (`!c a l b i j.
        i < l /\ j < 256
        ==> mldsa_field c (mldsa_slice (a + 32 * c * i) (32 * c) b) j =
            mldsa_field c (mldsa_slice a (32 * c * l) b) (256 * i + j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `32 * c * (i + 1) <= 32 * c * l` ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`32 * c * i`; `32 * c`; `a:num`; `32 * c * l`;
                 `b:byte list`] MLDSA_SLICE_SLICE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC HINTS_FIELD_SUBSLICE THEN
  ASM_REWRITE_TAC[LENGTH_MLDSA_SLICE]);;

(* ------------------------------------------------------------------------- *)
(* The generated sub-lists are mldsa_slice.                                  *)
(* ------------------------------------------------------------------------- *)


let HINTS_TAKE_DROP = prove
 (`!(l:byte list) a n.
        a + n <= LENGTH l ==> isa_take n (isa_drop a l) = mldsa_slice a n l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_MLDSA_SLICE; LENGTH_ISA_TAKE_LIST_FIRST;
              LENGTH_ISA_DROP_LIST_FIRST] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_ISA_TAKE_LIST_FIRST o lhand o snd) THEN
  REWRITE_TAC[LENGTH_ISA_DROP_LIST_FIRST] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[EL_MLDSA_SLICE] THEN MATCH_MP_TAC EL_ISA_DROP_LIST_FIRST THEN
  ASM_ARITH_TAC);;

let HINTS_LIST_SLICE = prove
 (`!(l:byte list) a b.
        typed_hol_list_slice l (&a) (&b) =
        if a <= b /\ b <= LENGTH l then SOME(mldsa_slice a (b - a) l)
        else NONE`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[typed_hol_list_slice_DEF; INT_POS; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; ISA_NAT_NUM] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC HINTS_TAKE_DROP THEN ASM_ARITH_TAC);;

let HINTS_SLICE_LENGTH_EQ = prove
 (`!a n (l:byte list).
        typed_hol_sequence_extent n (mldsa_slice a n l) =
        Value (mldsa_slice a n l)`,
  REWRITE_TAC[typed_hol_sequence_extent_DEF; LENGTH_MLDSA_SLICE]);;

let HINTS_SLICE_0 = prove
 (`!n (l:byte list). mldsa_slice 0 n (mldsa_slice 0 n l) = mldsa_slice 0 n l`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[MLDSA_SLICE_SLICE; ADD_CLAUSES; LE_REFL]);;

(* The bit lengths computed by the generated code.                           *)

let HINTS_BITLEN_CONV =
  let rec conv tm =
    (REWR_CONV bitlen_DEF THENC NUM_REDUCE_CONV THENC
     REWRITE_CONV[] THENC TRY_CONV(RAND_CONV conv) THENC NUM_REDUCE_CONV) tm in
  conv;;

let HINTS_BITLEN_SEMANTIC = prove
 (`!n. bitlen_semantic (&n) = Value (&(bitlen n))`,
  REWRITE_TAC[bitlen_semantic_DEF; INT_OF_NUM_LT; CONJUNCT1 LT;
              ISA_NAT_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Updates of lifted vectors.                                                *)
(* ------------------------------------------------------------------------- *)


let HINTS_LIFT_VEC_UPDATE = prove
 (`!(v:num->B) i w.
        i < dimindex(:N)
        ==> typed_hol_read
             (typed_hol_nominal_update Common_Vec common_vec_entries
               (\nf. native_list_update nf (&i) w)
               (lift_vec v:(N,B)common_vec)) =
            Value (lift_vec (\i'. if i' = i then w else v i'):(N,B)common_vec)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[typed_hol_nominal_update_DEF; COMMON_VEC_ENTRIES_LIFT] THEN
  ASM_SIMP_TAC[NATIVE_LIST_UPDATE_LT; LENGTH_LIST_OF_SEQ; isa_map_option;
               TYPED_HOL_READ_SOME] THEN
  AP_TERM_TAC THEN REWRITE_TAC[lift_vec] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let HINTS_LIFT_INTVEC_0 = prove
 (`(lift_vec (\i. lift_intpoly (\j. &0)):(N,fips204_intpoly)common_vec) =
   Common_Vec (MAP FIPS204_IntPoly
                (REPLICATE (dimindex(:N)) (REPLICATE 256 (&0))))`,
  REWRITE_TAC[lift_vec; lift_intpoly] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP; LENGTH_REPLICATE] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP; LENGTH_REPLICATE; EL_REPLICATE_LT] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_REPLICATE] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; EL_REPLICATE_LT]);;

(* ------------------------------------------------------------------------- *)
(* sigEncode, given BitPack for the coefficients of z (FIPS 204 Algorithm    *)
(* 17 with a = gamma1 - 1 and b = gamma1, c = 1 + bitlen(gamma1 - 1) bits),  *)
(* which encode.ml proves; here an explicit hypothesis, discharged           *)
(* in sigcodec.ml.                                                        *)
(* ------------------------------------------------------------------------- *)

let HINTS_8_DIVIDES = prove
 (`!c m. 8 divides (c * 256 * m) /\ 8 divides (c * 256)`,
  REWRITE_TAC[divides] THEN REPEAT GEN_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `c * 32 * m`; EXISTS_TAC `c * 32`] THEN ARITH_TAC);;

let HINTS_ENCODE_STEP = prove
 (`!c i f g.
        (!j. j < 256 ==> g j = f (256 * i + j))
        ==> APPEND (mldsa_encode c (256 * i) f) (mldsa_encode c 256 g) =
            mldsa_encode c (256 * SUC i) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 * SUC i = 256 * i + 256`] THEN
  SIMP_TAC[MLDSA_ENCODE_APPEND; ARITH_RULE `c * 256 * i = c * (256 * i)`;
           REWRITE_RULE[GSYM MULT_ASSOC] HINTS_8_DIVIDES] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MLDSA_ENCODE_EQ THEN ASM_SIMP_TAC[]);;

let hints_bitpack_hyp (g1,c) =
  let pt s = parse_term s and sp = Printf.sprintf in
  pt(sp "!w. (!j. j < 256 ==> --(&%d) <= w j /\\ w j <= &%d)
             ==> BitPack_%d_%d_hol (lift_intpoly w) (&%d) (&%d) =
                 Value (mldsa_encode %d 256 (\\j. &%d - w j))"
        (g1 - 1) g1 (g1 - 1) g1 (g1 - 1) g1 c g1);;

let HINTS_SIGENCODE_PROVE (k,l,omega,g1,c,def,packth) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let cname = fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl def))))))) in
  let bpname = sp "BitPack_%d_%d_hol" (g1 - 1) g1 in
  let hyp = hints_bitpack_hyp (g1,c) in
  let goal = mk_imp(hyp, pt(sp
   "!ct z h.
      (!i j. i < %d /\\ j < 256 ==> --(&%d) <= z i j /\\ z i j <= &%d) /\\
      mldsa_hint_count (\\p. h (p DIV 256) (p MOD 256)) %d <= %d
      ==> %s ct (lift_vec (\\i. lift_intpoly (z i)))
                (lift_vec (\\i. lift_bitpoly (h i))) =
          Value (APPEND ct
                  (APPEND (mldsa_encode %d %d
                            (\\n. &%d - z (n DIV 256) (n MOD 256)))
                          (mldsa_hintbitpack %d %d
                            (\\p. h (p DIV 256) (p MOD 256)))))"
   l (g1 - 1) g1 (256 * k) omega cname c (256 * l) g1 k omega)) in
  prove(goal,
    DISCH_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[ISA_NAT_NUM; REPLICATE; typed_hol_list_slice_DEF;
                LENGTH; INT_LE_REFL; INT_SUB_REFL; isa_drop; isa_take;
                TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE] THEN
    CONV_TAC(ONCE_DEPTH_CONV HINTS_SCHEDULE_CONV) THEN
    HINTS_FOLDL_TAC
     (pt(sp "\\i. APPEND ct (mldsa_encode %d (256 * i)
                     (\\n. &%d - z (n DIV 256) (n MOD 256)))" c g1))
     (pt(sp "APPEND ct (mldsa_encode %d %d
                     (\\n. &%d - z (n DIV 256) (n MOD 256)))" c (256 * l) g1))
    THENL
     [ALL_TAC;
      ASM_SIMP_TAC[packth; NATIVE_BIND_VALUE; APPEND_ASSOC]] THEN
    REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; MLDSA_ENCODE_0; APPEND_NIL]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMMON_VEC_ENTRIES_LIFT;
                DIMINDEX_CONV(pt(sp "dimindex(:%d)" l))] THEN
    ASM_SIMP_TAC[NATIVE_LIST_INDEX_LT; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
                 TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE] THEN
    TRY(FIRST_X_ASSUM(fun th -> W(fun (asl,w) ->
          let t = find_term (fun t -> match strip_comb t with
                     (Const(n,_),_) -> n = bpname | _ -> false) w in
          MP_TAC(PART_MATCH (lhand o rand) th t))) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          DISCH_THEN SUBST1_TAC]) THEN
    REWRITE_TAC[NATIVE_BIND_VALUE; GSYM APPEND_ASSOC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC HINTS_ENCODE_STEP THEN
    SIMP_TAC[DIV_MOD_256_SMALL]);;

let EQ_SIGENCODE_MLDSA44 = HINTS_SIGENCODE_PROVE
  (4,4,80,131072,18,sigEncode_MLDSA44_Configuration_hol_DEF,
   EQ_HINTBITPACK_MLDSA44);;
let EQ_SIGENCODE_MLDSA65 = HINTS_SIGENCODE_PROVE
  (6,5,55,524288,20,sigEncode_MLDSA65_Configuration_hol_DEF,
   EQ_HINTBITPACK_MLDSA65);;
let EQ_SIGENCODE_MLDSA87 = HINTS_SIGENCODE_PROVE
  (8,7,75,524288,20,sigEncode_MLDSA87_Configuration_hol_DEF,
   EQ_HINTBITPACK_MLDSA87);;

(* ------------------------------------------------------------------------- *)
(* sigDecode, given BitUnpack for the coefficients of z (FIPS 204 Algorithm  *)
(* 19), which encode.ml proves; here an explicit hypothesis,                 *)
(* discharged in sigcodec.ml.                                             *)
(* ------------------------------------------------------------------------- *)

let HINTS_AQUOT = prove
 (`!m n. ~(n = 0) /\ n divides m
         ==> typed_hol_int_arithmetic AQuot (&m) (&n) = Value(&(m DIV n))`,
  REWRITE_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
              case_aop_DEF; distinctness "aop"] THEN
  REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT; isa_int_mod; isa_int_div;
              INT_OF_NUM_REM; INT_OF_NUM_DIV; ARITH_RULE `~(n < 0)`] THEN
  SIMP_TAC[GSYM DIVIDES_MOD]);;

let HINTS_APOW_1 = prove
 (`!n. typed_hol_int_arithmetic APow (&1) n =
       if n < &0 then Fault Bounds_Error else Value (&1)`,
  REWRITE_TAC[typed_hol_int_arithmetic_DEF; INT_POW_ONE]);;

let hints_bitunpack_hyp (g1,c) =
  let pt s = parse_term s and sp = Printf.sprintf in
  pt(sp "!v. LENGTH v = %d
             ==> BitUnpack_%d_%d_hol v (&%d) (&%d) =
                 Value (lift_intpoly (\\j. &%d - mldsa_field %d v j))"
        (32 * c) (g1 - 1) g1 (g1 - 1) g1 g1 c);;

let HINTS_SIGDECODE_PROVE (k,l,omega,g1,c,lam,def,unpackth) =
  let pt s = parse_term s and sp = Printf.sprintf in
  let cname = fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl def))))))) in
  let lamq = lam / 4 and pb = 32 * c in
  let zlen = pb * l in
  let ho = lamq + zlen in
  let total = ho + omega + k in
  let hyp = hints_bitunpack_hyp (g1,c) in
  let vty = sp "(%d,fips204_intpoly)common_vec" l in
  let dimth = DIMINDEX_CONV(pt(sp "dimindex(:%d)" l)) in
  let goal = mk_imp(hyp, pt(sp
   "!sg. %d <= LENGTH sg
         ==> %s sg =
             Value (mldsa_slice 0 %d sg,
                    lift_vec (\\i. lift_intpoly (\\j. &%d -
                      mldsa_field %d (mldsa_slice %d %d sg) (256 * i + j))),
                    (match mldsa_hintbitunpack %d %d (mldsa_slice %d %d sg)
                     with NONE -> Native_Bottom
                        | SOME h -> Native_Value
                            (lift_vec (\\i. lift_bitpoly
                                             (\\j. h (256 * i + j))))))"
   total cname lamq g1 c lamq zlen k omega ho (omega + k))) in
  let sfun = pt(sp
   "\\j. lift_vec (\\i. if i < j
                       then lift_intpoly (\\jj. &%d - mldsa_field %d
                              (mldsa_slice (%d + %d * i) %d sg) jj)
                       else lift_intpoly (\\jj. &0)):%s"
   g1 c lamq pb pb vty)
  and s1 = pt(sp
   "lift_vec (\\i. lift_intpoly (\\j. &%d -
      mldsa_field %d (mldsa_slice %d %d sg) (256 * i + j))):%s"
   g1 c lamq zlen vty) in
  let fieldth = CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE[MULT_ASSOC]
     (SPECL [mk_small_numeral c; mk_small_numeral lamq; mk_small_numeral l]
            HINTS_FIELD_SLICE)) in
  let listth = SYM(LIST_OF_SEQ_CONV(pt(sp "list_of_seq (\\j. &j:int) %d" l))) in
  prove(goal,
    DISCH_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[ISA_NAT_NUM; HINTS_BITLEN_SEMANTIC; HINTS_APOW_1;
                ISA_INT_DIV_NUM_NUM] THEN
    SIMP_TAC[HINTS_AQUOT; ARITH_EQ;
             DIVIDES_CONV(pt(sp "4 divides %d" lam))] THEN
    CONV_TAC(DEPTH_CONV HINTS_BITLEN_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[NATIVE_BIND_VALUE] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[HINTS_LIST_SLICE; LENGTH_REPLICATE; LE_REFL; TYPED_HOL_READ_SOME;
                NATIVE_BIND_VALUE] THEN
    REWRITE_TAC[listth] THEN
    REWRITE_TAC[INT_MUL_RID] THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_SIMP_TAC[HINTS_LIST_SLICE;
                 ARITH_RULE(pt(sp "%d <= l ==> %d <= l" total lamq));
                 LE_0; SUB_0; TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE;
                 HINTS_SLICE_LENGTH_EQ; LENGTH_MLDSA_SLICE; LE_REFL;
                 HINTS_SLICE_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[HINTS_SLICE_LENGTH_EQ; NATIVE_BIND_VALUE] THEN
    HINTS_FOLDL_TAC sfun s1 THENL
     [ALL_TAC;
      REWRITE_TAC[NATIVE_BIND_VALUE; TYPED_HOL_READ_SOME; HINTS_SLICE_LENGTH_EQ] THEN
      SIMP_TAC[unpackth; LENGTH_MLDSA_SLICE] THEN
      REWRITE_TAC[NATIVE_BIND_VALUE]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONJUNCT1 LT; HINTS_LIFT_INTVEC_0; dimth]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC LIFT_VEC_CONG THEN
      REWRITE_TAC[dimth] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LIFT_INTPOLY_CONG THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC fieldth THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[typed_hol_nonnegative_DEF; INT_POS; NATIVE_BIND_VALUE;
                INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_LT; CONJUNCT1 LT;
                INT_MUL_RID] THEN
    SUBGOAL_THEN (pt(sp "%d + %d * (i + 1) <= LENGTH(sg:byte list)" lamq pb))
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_SIMP_TAC[HINTS_LIST_SLICE;
                 ARITH_RULE(pt(sp "%d + %d * i <= %d + %d * (i + 1)"
                                  lamq pb lamq pb));
                 ARITH_RULE(pt(sp "(%d + %d * (i + 1)) - (%d + %d * i) = %d"
                                  lamq pb lamq pb pb));
                 TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; HINTS_SLICE_LENGTH_EQ;
                 LENGTH_MLDSA_SLICE] THEN
    ASM_SIMP_TAC[HINTS_LIFT_VEC_UPDATE; dimth] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; LT] THEN
    X_GEN_TAC `i':num` THEN ASM_CASES_TAC `i':num = i` THEN
    ASM_REWRITE_TAC[]);;

let EQ_SIGDECODE_MLDSA44 = HINTS_SIGDECODE_PROVE
  (4,4,80,131072,18,128,sigDecode_MLDSA44_Configuration_hol_DEF,
   EQ_HINTBITUNPACK_MLDSA44);;
let EQ_SIGDECODE_MLDSA65 = HINTS_SIGDECODE_PROVE
  (6,5,55,524288,20,192,sigDecode_MLDSA65_Configuration_hol_DEF,
   EQ_HINTBITUNPACK_MLDSA65);;
let EQ_SIGDECODE_MLDSA87 = HINTS_SIGDECODE_PROVE
  (8,7,75,524288,20,256,sigDecode_MLDSA87_Configuration_hol_DEF,
   EQ_HINTBITUNPACK_MLDSA87);;
