(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the generated NTT-domain arithmetic (MultiplyNTTs and the  *)
(* T_q vector/matrix operations) with the handwritten model.                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Generic facts about residues mod q and about lists.                       *)
(* ------------------------------------------------------------------------- *)

let TQ_REP_RINM = prove
 (`!v. &(residue_rep (residue_of_int_mod v:(3329)residue)) = v rem &3329`,
  REWRITE_TAC[RESIDUE_OF_INT_MOD_REP] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS_EQ; INT_OF_NUM_EQ; ARITH_EQ]);;

let TQ_RINM_CONG = prove
 (`!v w. v rem &3329 = w rem &3329
         ==> (residue_of_int_mod v:(3329)residue) = residue_of_int_mod w`,
  REWRITE_TAC[residue_of_int_mod_DEF; isa_int_mod] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]);;

let TQ_LIST_OF_SEQ_EL = prove
 (`!(s:A list) n. LENGTH s = n ==> list_of_seq (\j. EL j s) n = s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let TQ_LIST_OF_SEQ_EQ = prove
 (`!(f:num->A) g n. (!j. j < n ==> f j = g j)
                    ==> list_of_seq f n = list_of_seq g n`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let TQ_MEM_LIST_OF_SEQ = prove
 (`!(f:num->A) n x. MEM x (list_of_seq f n) ==> ?i. i < n /\ x = f i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM_EXISTS_EL; LENGTH_LIST_OF_SEQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let TQ_UPDATE2_EQ = prove
 (`!t a b (x:A) x' y y'.
     x = x' /\ y = y'
     ==> isa_list_update (isa_list_update t a x) b y =
         isa_list_update (isa_list_update t a x') b y'`,
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Loops that fill a list: one entry per step (possibly under a wrapper      *)
(* like FIPS203_Poly or Common_Vec), or two entries per step as in           *)
(* MultiplyNTTs.                                                             *)
(* ------------------------------------------------------------------------- *)

let TQ_EQUIV_FOLDL_WRAP = prove
 (`!(wrap:A->B) (g:I->A->A) (h:I->B->B) s l.
     (!x t. h x (wrap t) = wrap (g x t))
     ==> equiv_foldl h (wrap s) l = wrap (equiv_foldl g s l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`s:A`] THEN
  SPEC_TAC(`l:I list`,`l:I list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[equiv_foldl]);;

let TQ_EQUIV_FOLDL_FILL1 = prove
 (`!(f:num->A) n m a s.
     LENGTH s = n /\ a + m <= n
     ==> equiv_foldl (\i t. isa_list_update t (num_of_int i) (f (num_of_int i))) s
                     (list_of_seq (\i. &(a + i)) m) =
         list_of_seq (\j. if a <= j /\ j < a + m then f j else EL j s) n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[LIST_OF_SEQ; equiv_foldl; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `~(a <= j /\ j < a)`] THEN
    ASM_SIMP_TAC[TQ_LIST_OF_SEQ_EL];
    STRIP_TAC THEN
    REWRITE_TAC[LIST_OF_SEQ; equiv_foldl; o_DEF; ADD_CLAUSES] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`SUC a`; `isa_list_update (s:A list) a ((f:num->A) a)`] th)) THEN
    ASM_SIMP_TAC[LENGTH_ISA_LIST_UPDATE; ADD_CLAUSES; ARITH_RULE
     `a + SUC m <= n ==> SUC a + m <= n`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC TQ_LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN
    ASM_CASES_TAC `j:num = a` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let TQ_EQUIV_FOLDL_FILL2 = prove
 (`!(f:num->A) n m a s.
     LENGTH s = n /\ 2 * (a + m) <= n
     ==> equiv_foldl
          (\i t. isa_list_update
                  (isa_list_update t (2 * num_of_int i) (f (2 * num_of_int i)))
                  (2 * num_of_int i + 1) (f (2 * num_of_int i + 1))) s
          (list_of_seq (\i. &(a + i)) m) =
         list_of_seq (\j. if 2 * a <= j /\ j < 2 * (a + m) then f j else EL j s) n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[LIST_OF_SEQ; equiv_foldl; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `~(2 * a <= j /\ j < 2 * a)`] THEN
    ASM_SIMP_TAC[TQ_LIST_OF_SEQ_EL];
    STRIP_TAC THEN
    REWRITE_TAC[LIST_OF_SEQ; equiv_foldl; o_DEF; ADD_CLAUSES] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`SUC a`;
        `isa_list_update (isa_list_update (s:A list) (2 * a) (f (2 * a)))
                         (2 * a + 1) ((f:num->A) (2 * a + 1))` ] th)) THEN
    ASM_SIMP_TAC[LENGTH_ISA_LIST_UPDATE; ADD_CLAUSES; ARITH_RULE
     `2 * (a + SUC m) <= n ==> 2 * (SUC a + m) <= n`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC TQ_LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_ISA_LIST_UPDATE] THEN
    ASM_CASES_TAC `j = 2 * a + 1` THEN ASM_REWRITE_TAC[] THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `j = 2 * a` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let TQ_NATIVE_FOLDL_FILL2 = prove
 (`!(body:int->(A)list->((A)list)native_result) (f:num->A) n m (s:A list).
     LENGTH s = n /\ 2 * m <= n /\
     (!i t. i < m /\ LENGTH t = n
            ==> body (&i) t =
                Value (isa_list_update
                        (isa_list_update t (2 * i) (f (2 * i)))
                        (2 * i + 1) (f (2 * i + 1))))
     ==> native_foldl body (list_of_seq (\i. &i) m) s =
         Value (list_of_seq (\j. if j < 2 * m then f j else EL j s) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`body:int->(A)list->((A)list)native_result`;
    `\i (t:A list). isa_list_update
             (isa_list_update t (2 * num_of_int i) (f (2 * num_of_int i)))
             (2 * num_of_int i + 1) (f (2 * num_of_int i + 1))`;
    `\t:A list. LENGTH t = n`;
    `list_of_seq (\i. &i) m :int list`;
    `s:A list`] NATIVE_FOLDL_VALUE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:int`; `t:A list`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP TQ_MEM_LIST_OF_SEQ) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[NUM_OF_INT_OF_NUM; LENGTH_ISA_LIST_UPDATE];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`f:num->A`; `n:num`; `m:num`; `0`; `s:A list`]
               TQ_EQUIV_FOLDL_FILL2) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LE_0] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let TQ_NATIVE_FOLDL_FILL_WRAP = prove
 (`!(body:int->S->(S)native_result) (wrap:(A)list->S) unwrap (f:num->A) n m s.
     (!l. unwrap (wrap l) = l) /\ LENGTH s = n /\ m <= n /\
     (!i t. i < m /\ LENGTH t = n
            ==> body (&i) (wrap t) = Value (wrap (isa_list_update t i (f i))))
     ==> native_foldl body (list_of_seq (\i. &i) m) (wrap s) =
         Value (wrap (list_of_seq (\j. if j < m then f j else EL j s) n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`body:int->S->(S)native_result`;
    `\i (p:S). (wrap:(A)list->S)
                 (isa_list_update (unwrap p) (num_of_int i) (f (num_of_int i)))`;
    `\p:S. ?t:A list. LENGTH t = n /\ p = wrap t`;
    `list_of_seq (\i. &i) m :int list`;
    `(wrap:(A)list->S) s`] NATIVE_FOLDL_VALUE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `p:S`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP TQ_MEM_LIST_OF_SEQ)
                               (X_CHOOSE_THEN `t:A list` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[NUM_OF_INT_OF_NUM] THEN
    ASM_MESON_TAC[LENGTH_ISA_LIST_UPDATE];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) (ISPECL
    [`wrap:(A)list->S`;
     `\i (t:A list). isa_list_update t (num_of_int i) (f (num_of_int i))`]
    TQ_EQUIV_FOLDL_WRAP) o rand o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`f:num->A`; `n:num`; `m:num`; `0`; `s:A list`]
               TQ_EQUIV_FOLDL_FILL1) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LE_0] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* Apply one of the two loop lemmas to the (unique, outermost) native_foldl  *)
(* in the goal; `args` supplies every parameter but the loop body.           *)

let tq_find_foldl w =
  find_term
    (fun t -> try let h,a = strip_comb t in
                  is_const h && fst(dest_const h) = "native_foldl" &&
                  length a = 3
              with Failure _ -> false) w;;

let TQ_FOLDL_TAC fill args =
  W(fun (asl,w) ->
      MP_TAC(ISPECL (hd(snd(strip_comb(tq_find_foldl w))) :: args) fill));;

(* The same, for a state of the form `wrap s`: `s` is read off the goal.     *)

let TQ_FOLDL_WRAP_TAC fill args =
  W(fun (asl,w) ->
      let a = snd(strip_comb(tq_find_foldl w)) in
      MP_TAC(ISPECL (hd a :: args @ [rand(last a)]) fill));;

(* Numeral side conditions of NATIVE_SCHEDULE_UPTO, for a loop over 0..k-1.  *)

let tq_sub0_lt n m = ARITH_RULE
  (subst [mk_small_numeral n,`n:num`; mk_small_numeral m,`m:num`] `n - 0 < m`);;

let tq_sub0 n = ARITH_RULE
  (subst [mk_small_numeral n,`n:num`] `n - 0 = n`);;

(* The loops over 1..k-1 of TqVectorDot and the matrix products.             *)

let TQ_SCHED_DOT = prove
 (`native_schedule 2 (\i. int_lt i (&2)) (\i. int_add i (&1)) (&1) = [&1] /\
   native_schedule 3 (\i. int_lt i (&3)) (\i. int_add i (&1)) (&1) = [&1; &2] /\
   native_schedule 4 (\i. int_lt i (&4)) (\i. int_add i (&1)) (&1) =
   [&1; &2; &3]`,
  REWRITE_TAC[MATCH_MP NATIVE_SCHEDULE_UPTO (ARITH_RULE `2 - 1 < 2`);
              MATCH_MP NATIVE_SCHEDULE_UPTO (ARITH_RULE `3 - 1 < 3`);
              MATCH_MP NATIVE_SCHEDULE_UPTO (ARITH_RULE `4 - 1 < 4`)] THEN
  REWRITE_TAC[ARITH_RULE
   `2 - 1 = SUC 0 /\ 3 - 1 = SUC(SUC 0) /\ 4 - 1 = SUC(SUC(SUC 0))`] THEN
  REWRITE_TAC[LIST_OF_SEQ; o_THM] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Z_q facts for the handwritten side: ring_sum over {j | j < k} expanded.   *)
(* ------------------------------------------------------------------------- *)

let TQ_SET_LT_2 = prove
 (`{j | j < 2} = {0,1}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let TQ_SET_LT_3 = prove
 (`{j | j < 3} = {0,1,2}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let TQ_SET_LT_4 = prove
 (`{j | j < 4} = {0,1,2,3}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let TQ_RING_SUM_TAC setth bnd =
  REPEAT STRIP_TAC THEN REWRITE_TAC[setth] THEN
  SUBGOAL_THEN bnd STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[RING_SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] THEN
  ASM_SIMP_TAC[RING_ADD_RZERO];;

let TQ_RING_SUM_2 = prove
 (`!(r:A ring) f. (!j. j < 2 ==> f j IN ring_carrier r)
                  ==> ring_sum r {j | j < 2} f = ring_add r (f 0) (f 1)`,
  TQ_RING_SUM_TAC TQ_SET_LT_2
   `(f:num->A) 0 IN ring_carrier (r:A ring) /\ f 1 IN ring_carrier r`);;

let TQ_RING_SUM_3 = prove
 (`!(r:A ring) f. (!j. j < 3 ==> f j IN ring_carrier r)
                  ==> ring_sum r {j | j < 3} f =
                      ring_add r (f 0) (ring_add r (f 1) (f 2))`,
  TQ_RING_SUM_TAC TQ_SET_LT_3
   `(f:num->A) 0 IN ring_carrier (r:A ring) /\ f 1 IN ring_carrier r /\
    f 2 IN ring_carrier r`);;

let TQ_RING_SUM_4 = prove
 (`!(r:A ring) f. (!j. j < 4 ==> f j IN ring_carrier r)
                  ==> ring_sum r {j | j < 4} f =
                      ring_add r (f 0) (ring_add r (f 1) (ring_add r (f 2) (f 3)))`,
  TQ_RING_SUM_TAC TQ_SET_LT_4
   `(f:num->A) 0 IN ring_carrier (r:A ring) /\ f 1 IN ring_carrier r /\
    f 2 IN ring_carrier r /\ f 3 IN ring_carrier r`);;

(* The vector and matrix wrappers, per parameter set.                        *)

let tq_vec_wrap k = match k with
    2 -> `Common_Vec:ty_fips203_poly_1 list->ty_common_vec_1`
  | 3 -> `Common_Vec:ty_fips203_poly_1 list->ty_common_vec_2`
  | _ -> `Common_Vec:ty_fips203_poly_1 list->ty_common_vec_3`;;

let tq_vec_unwrap k = match k with
    2 -> `common_vec_entries:ty_common_vec_1->ty_fips203_poly_1 list`
  | 3 -> `common_vec_entries:ty_common_vec_2->ty_fips203_poly_1 list`
  | _ -> `common_vec_entries:ty_common_vec_3->ty_fips203_poly_1 list`;;

(* ------------------------------------------------------------------------- *)
(* MultiplyNTTs (Algorithms 11 and 12).                                      *)
(* ------------------------------------------------------------------------- *)

let TQ_BASECASEMULTIPLY = prove
 (`!a0 a1 b0 b1 g.
     BaseCaseMultiply_hol a0 a1 b0 b1 g =
     Value (FIPS203_Zq (residue_of_int_mod (fz a0 * fz b0 + fz a1 * fz b1 * fz g)),
            FIPS203_Zq (residue_of_int_mod (fz a0 * fz b1 + fz a1 * fz b0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BaseCaseMultiply_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[TQ_REP_RINM; GSYM fz] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "fips203_zq"] THEN
  CONJ_TAC THEN MATCH_MP_TAC TQ_RINM_CONG THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_MUL_ASSOC]);;

let MULTIPLYNTTS_HOL_EQ = prove
 (MULTIPLYNTTS_HOL_EQ_STMT,
  REWRITE_TAC[zq_list_ok] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[MultiplyNTTs_hol_DEF] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MATCH_MP NATIVE_SCHEDULE_UPTO (ARITH_RULE `128 - 0 < 129`)] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `128 - 0 = 128`] THEN
  TQ_FOLDL_TAC TQ_NATIVE_FOLDL_FILL2
   [`\j. FIPS203_Zq (residue_of_int_mod
            (fips203_multiply_ntts (zarr f) (zarr g) j))`; `256`; `128`;
    `MAP FIPS203_Zq (REPLICATE 256 (residue_of_int_mod (&0)))`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `t:fips203_zq list`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 * i < 256 /\ 2 * i + 1 < 256` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[fips203_poly_SEL_CTR; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
                 NATIVE_BIND_VALUE; TYPED_HOL_NONNEGATIVE; NATIVE_LIST_INDEX;
                 BITREV7_HOL; TYPED_HOL_POW_MOD; TQ_BASECASEMULTIPLY;
                 NATIVE_LIST_UPDATE; LENGTH_ISA_LIST_UPDATE; ARITH_EQ;
                 ARITH_RULE `0 < 3329`] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC TQ_UPDATE2_EQ THEN
    CONJ_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC TQ_RINM_CONG THEN
    REWRITE_TAC[fips203_multiply_ntts; EVEN_ADD; EVEN_MULT; ARITH; ADD_SUB] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
    REWRITE_TAC[mlkem_zq; INTEGER_MOD_RING_CLAUSES; zarr;
                FZ_RESIDUE_OF_INT_MOD] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_MUL_ASSOC];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; zqlist] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC TQ_LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `j < 256 ==> j < 2 * 128`]);;

(* ------------------------------------------------------------------------- *)
(* Coefficientwise addition in T_q.                                          *)
(* ------------------------------------------------------------------------- *)

let TQPOLYADD_HOL_EQ = prove
 (TQPOLYADD_HOL_EQ_STMT,
  REWRITE_TAC[zq_list_ok] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TqPolyAdd_hol_DEF] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MATCH_MP NATIVE_SCHEDULE_UPTO (ARITH_RULE `256 - 0 < 257`)] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `256 - 0 = 256`] THEN
  TQ_FOLDL_TAC TQ_NATIVE_FOLDL_FILL_WRAP
   [`FIPS203_Poly:fips203_zq list->ty_fips203_poly_1`;
    `fips203_poly_coefficients:ty_fips203_poly_1->fips203_zq list`;
    `\j. FIPS203_Zq (residue_of_int_mod
            (ring_add mlkem_zq (zarr f j) (zarr g j)))`; `256`; `256`;
    `MAP FIPS203_Zq (REPLICATE 256 (residue_of_int_mod (&0)))`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[fips203_poly_SEL_CTR; LENGTH_MAP; LENGTH_REPLICATE; LE_REFL] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `t:fips203_zq list`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[fips203_poly_SEL_CTR; NATIVE_BIND_VALUE; NATIVE_LIST_INDEX;
                 NOMINAL_UPDATE_POLY; GSYM fz] THEN
    REPLICATE_TAC 4 AP_TERM_TAC THEN MATCH_MP_TAC TQ_RINM_CONG THEN
    REWRITE_TAC[mlkem_zq; INTEGER_MOD_RING_CLAUSES; zarr] THEN
    CONV_TAC INT_REM_DOWN_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[zqlist] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC TQ_LIST_OF_SEQ_EQ THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Vector addition.                                                          *)
(* ------------------------------------------------------------------------- *)

let TQ_VECTORADD_TAC def k =
  REPEAT STRIP_TAC THEN REWRITE_TAC[def; zvec] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MATCH_MP NATIVE_SCHEDULE_UPTO (tq_sub0_lt k (k+1)); ADD_CLAUSES;
              tq_sub0 k] THEN
  TQ_FOLDL_WRAP_TAC TQ_NATIVE_FOLDL_FILL_WRAP
   [tq_vec_wrap k; tq_vec_unwrap k;
    `\(i:num). (FIPS203_Poly:fips203_zq list->ty_fips203_poly_1)
            (zqlist (\n. ring_add mlkem_zq (zarr (u i) n) (zarr (v i) n)))`;
    mk_small_numeral k; mk_small_numeral k] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[common_vec_SEL_CTR; LENGTH_MAP; LENGTH_REPLICATE; LE_REFL] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `t:ty_fips203_poly_1 list`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[common_vec_SEL_CTR; NATIVE_BIND_VALUE; TYPED_HOL_NONNEGATIVE;
                 NATIVE_LIST_INDEX; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
                 TQPOLYADD_HOL_EQ; NOMINAL_UPDATE_VEC];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC TQ_LIST_OF_SEQ_EQ THEN
  SIMP_TAC[];;

let TQVECTORADD_2 = prove
 (TQVECTORADD_2_STMT,
  TQ_VECTORADD_TAC TqVectorAdd_2_MLKEM512_Configuration_hol_DEF 2);;

let TQVECTORADD_3 = prove
 (TQVECTORADD_3_STMT,
  TQ_VECTORADD_TAC TqVectorAdd_3_MLKEM768_Configuration_hol_DEF 3);;

let TQVECTORADD_4 = prove
 (TQVECTORADD_4_STMT,
  TQ_VECTORADD_TAC TqVectorAdd_4_MLKEM1024_Configuration_hol_DEF 4);;

(* ------------------------------------------------------------------------- *)
(* The inner product of two vectors in T_q.                                  *)
(* ------------------------------------------------------------------------- *)

let TQ_VECTORDOT_TAC def sumth =
  REPEAT STRIP_TAC THEN REWRITE_TAC[def; zvec] THEN
  REWRITE_TAC[TQ_SCHED_DOT] THEN
  ASM_SIMP_TAC[common_vec_SEL_CTR; NATIVE_BIND_VALUE; NATIVE_LIST_INDEX;
               LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; MULTIPLYNTTS_HOL_EQ;
               TQPOLYADD_HOL_EQ; ZQ_LIST_OK_ZQLIST; native_foldl_DEF; ARITH] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ZQLIST_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SIMP_TAC[sumth; TQ_MULTIPLY_NTTS_IN_ZQ] THEN
  ASM_SIMP_TAC[ZARR_ZQLIST; MLKEM_ZQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;;

let TQVECTORDOT_2 = prove
 (TQVECTORDOT_2_STMT,
  TQ_VECTORDOT_TAC TqVectorDot_2_MLKEM512_Configuration_hol_DEF TQ_RING_SUM_2);;

let TQVECTORDOT_3 = prove
 (TQVECTORDOT_3_STMT,
  TQ_VECTORDOT_TAC TqVectorDot_3_MLKEM768_Configuration_hol_DEF TQ_RING_SUM_3);;

let TQVECTORDOT_4 = prove
 (TQVECTORDOT_4_STMT,
  TQ_VECTORDOT_TAC TqVectorDot_4_MLKEM1024_Configuration_hol_DEF TQ_RING_SUM_4);;

(* ------------------------------------------------------------------------- *)
(* Matrix-vector products. Both the matrix index arithmetic and the loops    *)
(* over 0..k-1 are unrolled, so every index becomes a numeral; TQ_RED_TAC    *)
(* alternates simplification with numeral reduction until nothing changes.   *)
(* ------------------------------------------------------------------------- *)

let TQ_RED_TAC ths =
  REPEAT(CHANGED_TAC(ASM_SIMP_TAC ths THEN
                     CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV)));;

let tq_red_ths =
  [common_vec_SEL_CTR; common_mat_entries_DEF; fips_matrix_SEL_CTR;
   TYPED_HOL_BIT_VALUE; BITVAL_CLAUSES; INT_ARITH_APOW; ISA_NAT_NUM;
   INT_POW_ONE; INT_POW; INT_MUL_LZERO; INT_MUL_RZERO; INT_MUL_LID;
   INT_ADD_LID; INT_ADD_RID; NATIVE_BIND_VALUE; NATIVE_LIST_INDEX;
   LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; MULTIPLYNTTS_HOL_EQ; TQPOLYADD_HOL_EQ;
   ZQ_LIST_OK_ZQLIST; NOMINAL_UPDATE_VEC; LENGTH_ISA_LIST_UPDATE; LENGTH_MAP;
   LENGTH_REPLICATE; native_foldl_DEF; ARITH];;

let TQ_MATMUL_TAC def sumth =
  REPEAT STRIP_TAC THEN REWRITE_TAC[def; zvec; zmat] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[TQ_SCHED_DOT; native_foldl_DEF] THEN
  TQ_RED_TAC tq_red_ths THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  SIMP_TAC[LENGTH_ISA_LIST_UPDATE; LENGTH_MAP; LENGTH_REPLICATE;
           LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  SIMP_TAC[EL_ISA_LIST_UPDATE; EL_LIST_OF_SEQ; LENGTH_ISA_LIST_UPDATE;
           LENGTH_MAP; LENGTH_REPLICATE; ARITH] THEN
  REPEAT CONJ_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ZQLIST_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SIMP_TAC[sumth; TQ_MULTIPLY_NTTS_IN_ZQ] THEN
  ASM_SIMP_TAC[ZARR_ZQLIST; MLKEM_ZQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;;

let TQMATRIXVECTORMUL_2 = prove
 (TQMATRIXVECTORMUL_2_STMT,
  TQ_MATMUL_TAC TqMatrixVectorMul_2_MLKEM512_Configuration_hol_DEF
                TQ_RING_SUM_2);;

let TQMATRIXTRANSPOSEVECTORMUL_2 = prove
 (TQMATRIXTRANSPOSEVECTORMUL_2_STMT,
  TQ_MATMUL_TAC TqMatrixTransposeVectorMul_2_MLKEM512_Configuration_hol_DEF
                TQ_RING_SUM_2);;

let TQMATRIXVECTORMUL_3 = prove
 (TQMATRIXVECTORMUL_3_STMT,
  TQ_MATMUL_TAC TqMatrixVectorMul_3_MLKEM768_Configuration_hol_DEF
                TQ_RING_SUM_3);;

let TQMATRIXTRANSPOSEVECTORMUL_3 = prove
 (TQMATRIXTRANSPOSEVECTORMUL_3_STMT,
  TQ_MATMUL_TAC TqMatrixTransposeVectorMul_3_MLKEM768_Configuration_hol_DEF
                TQ_RING_SUM_3);;

let TQMATRIXVECTORMUL_4 = prove
 (TQMATRIXVECTORMUL_4_STMT,
  TQ_MATMUL_TAC TqMatrixVectorMul_4_MLKEM1024_Configuration_hol_DEF
                TQ_RING_SUM_4);;

let TQMATRIXTRANSPOSEVECTORMUL_4 = prove
 (TQMATRIXTRANSPOSEVECTORMUL_4_STMT,
  TQ_MATMUL_TAC TqMatrixTransposeVectorMul_4_MLKEM1024_Configuration_hol_DEF
                TQ_RING_SUM_4);;
