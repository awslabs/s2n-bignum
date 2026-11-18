(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The NTT as explicit sums, and that it is a bijection from R_q onto         *)
(* Z_q^256.                                                                   *)
(* ========================================================================= *)

needs "common/fips203/properties/rq_ring.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The NTT as explicit sums (as in FIPS 203 Algorithm 9's specification and  *)
(* Cryptol's NaiveNTT), and it is a bijection from R_q onto Z_q^256, so that *)
(* mlkem_ntt_inv really is its inverse.                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NTT_EXPLICIT = prove
 (`!f k. f IN ring_carrier mlkem_rq
         ==> mlkem_ntt f k =
             ring_sum mlkem_zq {j | j < 128}
              (\j. ring_mul mlkem_zq (coeff (2 * j + k MOD 2) f)
                     (ring_pow mlkem_zq
                        (ring_pow mlkem_zq (&17)
                                  (2 * bitreverse7(k DIV 2) + 1))
                        j))`,
  REWRITE_TAC[IN_MLKEM_RQ] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[mlkem_ntt; mlkem_zqx; mlkem_X] THEN
  ABBREV_TAC `c = ring_pow mlkem_zq (&17) (2 * bitreverse7(k DIV 2) + 1)` THEN
  SUBGOAL_THEN `c IN ring_carrier mlkem_zq` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC RING_POW THEN
    REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mlkem_zqx]) THEN
  MP_TAC(ISPECL [`mlkem_zq`; `f:(1->num)->int`; `c:int`; `128`]
                POLY_REM_QUADRATIC) THEN
  ASM_REWRITE_TAC[MLKEM_ZQ; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD; COEFF_POLY_CONST] THEN
  SIMP_TAC[COEFF_POLY_MUL_VAR; RING_POWERSERIES_CONST; RING_SUM] THEN
  REWRITE_TAC[COEFF_POLY_CONST] THEN
  DISJ_CASES_TAC(ARITH_RULE `k MOD 2 = 0 \/ k MOD 2 = 1`) THEN
  ASM_REWRITE_TAC[ARITH; ADD_CLAUSES] THEN
  SIMP_TAC[RING_ADD_RZERO; RING_ADD_LZERO; RING_SUM]);;

let MLKEM_NTT_PAIR = prove
 (`!f i b. f IN ring_carrier mlkem_rq /\ b < 2
           ==> mlkem_ntt f (2 * i + b) =
               ring_sum mlkem_zq {j | j < 128}
                (\j. ring_mul mlkem_zq (coeff (2 * j + b) f)
                       (ring_pow mlkem_zq
                          (ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1))
                          j))`,
  SIMP_TAC[MLKEM_NTT_EXPLICIT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(2 * i + b) MOD 2 = b /\ (2 * i + b) DIV 2 = i`
   (fun th -> REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
  ASM_SIMP_TAC[MOD_LT; DIV_LT; ADD_CLAUSES]);;

let POLY_ROOTS_IMP_ZERO = prove
 (`!(r:A ring) p n (g:num->A).
        integral_domain r /\ p IN ring_carrier(poly_ring r (:1)) /\
        poly_deg r p < n /\
        (!i. i < n
             ==> g i IN ring_carrier r /\ poly_eval r p (g i) = ring_0 r) /\
        (!i j. i < n /\ j < n /\ g i = g j ==> i = j)
        ==> p = ring_0(poly_ring r (:1))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`] POLY_ROOT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (g:num->A) {i | i < n}`;
                 `{x | x IN ring_carrier r /\
                       poly_eval r p x = ring_0 (r:A ring)}`]
                CARD_SUBSET) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`g:num->A`; `{i:num | i < n}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IN_ELIM_THM; FINITE_NUMSEG_LT] THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[CARD_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_ARITH_TAC]);;

let MLKEM_POLY_IN_ZQX = prove
 (`!a. mlkem_poly a IN ring_carrier(poly_ring mlkem_zq (:1))`,
  MESON_TAC[MLKEM_POLY_IN_RQ; IN_MLKEM_RQ; mlkem_zqx]);;

let POLY_DEG_MLKEM_POLY_LT = prove
 (`!a n. ~(n = 0) /\ (!j. n <= j /\ j < 256 ==> a j rem &3329 = &0)
         ==> poly_deg mlkem_zq (mlkem_poly a) < n`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `~(n = 0) /\ x <= n - 1 ==> x < n`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `a:num->int` MLKEM_POLY_IN_ZQX) THEN
  SIMP_TAC[GSYM RING_POLYNOMIAL; POLY_DEG_LE_COEFF_EQ] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[COEFF_MLKEM_POLY; MLKEM_ZQ] THEN
  X_GEN_TAC `d:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LE] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

let MLKEM_NTT_PART = prove
 (`!f b i.
        f IN ring_carrier mlkem_rq /\ b < 2 /\ i < 128
        ==> mlkem_ntt f (2 * i + b) =
            poly_eval mlkem_zq
              (mlkem_poly (\j. if j < 128 then coeff (2 * j + b) f else &0))
              (ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_NTT_PAIR] THEN
  ABBREV_TAC
   `p = mlkem_poly (\j. if j < 128 then coeff (2 * j + b) f else &0)` THEN
  ABBREV_TAC `x = ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1)` THEN
  SUBGOAL_THEN `x IN ring_carrier mlkem_zq` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC RING_POW THEN
    REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p IN ring_carrier(poly_ring mlkem_zq (:1)) /\
                poly_deg mlkem_zq p < 128`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[MLKEM_POLY_IN_ZQX] THEN
    MATCH_MP_TAC POLY_DEG_MLKEM_POLY_LT THEN REWRITE_TAC[ARITH_EQ] THEN
    SIMP_TAC[GSYM NOT_LT] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_EVAL_EXPAND] THEN
  CONV_TAC SYM_CONV THEN TRANS_TAC EQ_TRANS
   `ring_sum mlkem_zq {j | j < 128}
      (\j. ring_mul mlkem_zq (coeff j p) (ring_pow mlkem_zq x j))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`mlkem_zq`; `p:(1->num)->int`; `j:num`]
                  COEFF_ABOVE_DEG) THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_MUL_LZERO THEN ASM_SIMP_TAC[RING_POW];
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    EXPAND_TAC "p" THEN
    ASM_SIMP_TAC[COEFF_MLKEM_POLY; ARITH_RULE `j < 128 ==> j < 256`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INT_REM_LT THEN
    MP_TAC(ISPECL [`mlkem_zq`; `f:(1->num)->int`; `2 * j + b`]
                  COEFF_IN_CARRIER_ALT) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_MLKEM_RQ; mlkem_zqx]) THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL; IN_MLKEM_ZQ] THEN INT_ARITH_TAC]);;

let MLKEM_NTT_INJ = prove
 (`!f g. f IN ring_carrier mlkem_rq /\ g IN ring_carrier mlkem_rq /\
         (!k. k < 256 ==> mlkem_ntt f k = mlkem_ntt g k)
         ==> f = g`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_RQ_EQ] THEN
  SUBGOAL_THEN
   `!b j. b < 2 /\ j < 128
          ==> coeff (2 * j + b) (f:(1->num)->int) = coeff (2 * j + b) g`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`i:num`; `2`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `i = i DIV 2 * 2 + i MOD 2` THEN DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC] THEN
  X_GEN_TAC `b:num` THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `pf = mlkem_poly (\j. if j < 128 then coeff (2 * j + b) f else &0)` THEN
  ABBREV_TAC
   `pg = mlkem_poly (\j. if j < 128 then coeff (2 * j + b) g else &0)` THEN
  SUBGOAL_THEN `pf:(1->num)->int = pg` MP_TAC THENL
   [SUBGOAL_THEN `pf IN ring_carrier(poly_ring mlkem_zq (:1)) /\
                  pg IN ring_carrier(poly_ring mlkem_zq (:1))`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["pf"; "pg"] THEN REWRITE_TAC[MLKEM_POLY_IN_ZQX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`poly_ring mlkem_zq (:1)`; `pf:(1->num)->int`;
                   `pg:(1->num)->int`] RING_SUB_EQ_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC POLY_ROOTS_IMP_ZERO THEN
    MAP_EVERY EXISTS_TAC
     [`128`; `\i. ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1)`] THEN
    REWRITE_TAC[MLKEM_GAMMA_INJ] THEN
    REWRITE_TAC[MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN (CONJUNCT1 MLKEM_ZQ)] THEN
    ASM_SIMP_TAC[RING_SUB] THEN CONJ_TAC THENL
     [REWRITE_TAC[POLY_RING_CLAUSES] THEN
      MP_TAC(ISPECL [`mlkem_zq`; `pf:(1->num)->int`; `pg:(1->num)->int`]
                    POLY_DEG_SUB_LE) THEN
      ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN
      MATCH_MP_TAC(ARITH_RULE
       `a < 128 /\ b < 128 ==> x <= MAX a b ==> x < 128`) THEN
      MAP_EVERY EXPAND_TAC ["pf"; "pg"] THEN
      CONJ_TAC THEN MATCH_MP_TAC POLY_DEG_MLKEM_POLY_LT THEN
      REWRITE_TAC[ARITH_EQ] THEN SIMP_TAC[GSYM NOT_LT] THEN
      CONV_TAC INT_REDUCE_CONV;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1) IN
        ring_carrier mlkem_zq`
      ASSUME_TAC THENL
       [MATCH_MP_TAC RING_POW THEN REWRITE_TAC[IN_MLKEM_ZQ] THEN
        INT_ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[POLY_RING_CLAUSES] THEN
      ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_SUB_EQ_0 o snd) THEN
      REWRITE_TAC[POLY_EVAL] THEN DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY EXPAND_TAC ["pf"; "pg"] THEN
      ASM_SIMP_TAC[GSYM MLKEM_NTT_PART] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `(pf:(1->num)->int) = pg` THEN
    DISCH_THEN(MP_TAC o AP_TERM `coeff (j:num):((1->num)->int)->int`) THEN
    MAP_EVERY EXPAND_TAC ["pf"; "pg"] THEN
    ASM_SIMP_TAC[COEFF_MLKEM_POLY; ARITH_RULE `j < 128 ==> j < 256`] THEN
    SUBGOAL_THEN
     `!h. h IN ring_carrier mlkem_rq
          ==> coeff (2 * j + b) h rem &3329 = coeff (2 * j + b) h`
     (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[IN_MLKEM_RQ; mlkem_zqx] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INT_REM_LT THEN
    MP_TAC(ISPECL [`mlkem_zq`; `h:(1->num)->int`; `2 * j + b`]
                  COEFF_IN_CARRIER_ALT) THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL; IN_MLKEM_ZQ] THEN INT_ARITH_TAC]);;

let MLKEM_NTT_IN_ZQ = prove
 (`!f k. f IN ring_carrier mlkem_zqx
         ==> mlkem_ntt f k IN ring_carrier mlkem_zq`,
  REWRITE_TAC[mlkem_ntt; mlkem_zqx] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COEFF_POLY_IN_CARRIER THEN MATCH_MP_TAC POLY_REM THEN
  ASM_REWRITE_TAC[mlkem_X] THEN MATCH_MP_TAC RING_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_POW THEN REWRITE_TAC[POLY_VAR_UNIV];
    REWRITE_TAC[POLY_CONST] THEN MATCH_MP_TAC RING_POW THEN
    REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC]);;

let MLKEM_NTT_SURJ = prove
 (`!a. (!k. k < 256 ==> &0 <= a k /\ a k < &3329)
       ==> ?f. f IN ring_carrier mlkem_rq /\
               !k. k < 256 ==> mlkem_ntt f k = a k`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = {a:num->int | (!k. k IN {k | k < 256}
                                     ==> a k IN ring_carrier mlkem_zq) /\
                                (!k. ~(k IN {k | k < 256}) ==> a k = &0)}` THEN
  SUBGOAL_THEN `FINITE(t:(num->int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC FINITE_FUNSPACE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; mlkem_zq; FINITE_INTEGER_MOD_RING; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_carrier mlkem_rq = IMAGE mlkem_poly t /\
    (!x y. x IN t /\ y IN t /\ mlkem_poly x = mlkem_poly y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `p:(1->num)->int` THEN
      EQ_TAC THENL
       [DISCH_TAC THEN
        EXISTS_TAC `\k. if k < 256 then coeff k (p:(1->num)->int) else &0` THEN
        CONJ_TAC THENL
         [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
           [SYM(MATCH_MP MLKEM_POLY_COEFF th)]) THEN
          REWRITE_TAC[mlkem_poly; FUN_EQ_THM] THEN GEN_TAC THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[];
          EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN
          SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC COEFF_POLY_IN_CARRIER THEN
          ASM_MESON_TAC[IN_MLKEM_RQ; mlkem_zqx]];
        STRIP_TAC THEN ASM_REWRITE_TAC[MLKEM_POLY_IN_RQ]];
      EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_MLKEM_ZQ] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
      ASM_CASES_TAC `k < 256` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `coeff (k:num):((1->num)->int)->int`) THEN
      ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
      ASM_SIMP_TAC[INT_REM_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\f k. if k < 256 then mlkem_ntt f k else &0)
          (ring_carrier mlkem_rq) = t`
  MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `x:num->int` THEN DISCH_TAC THEN SIMP_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NTT_IN_ZQ THEN
      REWRITE_TAC[mlkem_zqx; MLKEM_POLY_IN_ZQX];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`p:(1->num)->int`; `q:(1->num)->int`] THEN
        STRIP_TAC THEN MATCH_MP_TAC MLKEM_NTT_INJ THEN
        ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o C AP_THM `k:num` o
          check (fun th -> is_eq(concl th) && not(is_var(lhs(concl th))))) THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[FINITE_IMAGE]];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `\k. if k < 256 then (a:num->int) k else &0`) THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_MLKEM_ZQ] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:(1->num)->int` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o C AP_THM `k:num`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[EQ_SYM_EQ]]);;

let MLKEM_NTT_INV = prove
 (`!a. (!k. k < 256 ==> &0 <= a k /\ a k < &3329)
       ==> mlkem_ntt_inv a IN ring_carrier mlkem_rq /\
           !k. k < 256 ==> mlkem_ntt (mlkem_ntt_inv a) k = a k`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MLKEM_NTT_SURJ) THEN
  REWRITE_TAC[mlkem_ntt_inv] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  REWRITE_TAC[]);;

let MLKEM_NTT_INV_NTT = prove
 (`!f. f IN ring_carrier mlkem_rq ==> mlkem_ntt_inv (mlkem_ntt f) = f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NTT_INJ THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MLKEM_NTT_INV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_MLKEM_RQ]) THEN
  ASM_MESON_TAC[MLKEM_NTT_IN_ZQ; IN_MLKEM_ZQ]);;

(* ------------------------------------------------------------------------- *)
(* The NTT and its inverse map into the ranges of Z_q and R_q.               *)
(* ------------------------------------------------------------------------- *)

let KPKE_NTT_BOUNDS = prove
 (`!f n. f IN ring_carrier mlkem_rq
         ==> &0 <= mlkem_ntt f n /\ mlkem_ntt f n < &3329`,
  REWRITE_TAC[GSYM IN_MLKEM_ZQ] THEN
  SIMP_TAC[IN_MLKEM_RQ; MLKEM_NTT_IN_ZQ]);;

let KPKE_NTT_POLY_BOUNDS = prove
 (`!a n. &0 <= mlkem_ntt (mlkem_poly a) n /\
         mlkem_ntt (mlkem_poly a) n < &3329`,
  SIMP_TAC[KPKE_NTT_BOUNDS; MLKEM_POLY_IN_RQ]);;

let KPKE_NTT_INV_IN_RQ = prove
 (`!a. (!n. n < 256 ==> &0 <= a n /\ a n < &3329)
       ==> mlkem_ntt_inv a IN ring_carrier mlkem_rq`,
  SIMP_TAC[MLKEM_NTT_INV]);;

let KPKE_NTT_INV_SUM_IN_RQ = prove
 (`!f. mlkem_ntt_inv (\n. ring_sum mlkem_zq (s:A->bool) (f n))
         IN ring_carrier mlkem_rq`,
  GEN_TAC THEN MATCH_MP_TAC KPKE_NTT_INV_IN_RQ THEN
  REWRITE_TAC[KPKE_RING_SUM_BOUNDS]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
