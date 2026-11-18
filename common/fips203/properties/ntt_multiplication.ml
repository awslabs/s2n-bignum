(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The NTT is a ring homomorphism from R_q to T_q (FIPS 203 Algorithms 11     *)
(* and 12), and MultiplyNTTs.                                                 *)
(* ========================================================================= *)

needs "common/fips203/properties/ntt_sums.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The NTT is a ring homomorphism from R_q to T_q: it is additive, and it    *)
(* maps products in R_q to the BaseCaseMultiply products of FIPS 203         *)
(* Algorithms 11 and 12. So FIPS 203's NTT-domain computations agree with    *)
(* the R_q formulation of the specification.                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_ZQ_FIELD = CONJUNCT1 MLKEM_ZQ;;

let MLKEM_ZQ_NONTRIVIAL = CONJUNCT1(CONJUNCT2 MLKEM_ZQ);;

let CARRIER_TAC =
  REPEAT(FIRST
   [CONJ_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_ACCEPT_TAC RING_0; MATCH_ACCEPT_TAC RING_1;
    MATCH_ACCEPT_TAC RING_SUM; MATCH_ACCEPT_TAC POLY_VAR_UNIV;
    MATCH_MP_TAC RING_ADD THEN CONJ_TAC;
    MATCH_MP_TAC RING_MUL THEN CONJ_TAC;
    MATCH_MP_TAC RING_SUB THEN CONJ_TAC;
    MATCH_MP_TAC RING_NEG;
    MATCH_MP_TAC RING_POW;
    GEN_REWRITE_TAC I [POLY_CONST];
    MATCH_MP_TAC COEFF_POLY_IN_CARRIER;
    MATCH_MP_TAC POLY_REM THEN CONJ_TAC]);;

let POLY_REM_REM_DIVIDES = prove
 (`!(r:A ring) p m mm.
        p IN ring_carrier(poly_ring r (:1)) /\
        m IN ring_carrier(poly_ring r (:1)) /\
        mm IN ring_carrier(poly_ring r (:1)) /\
        ring_unit r (coeff (poly_deg r m) m) /\
        ring_divides (poly_ring r (:1)) m mm
        ==> poly_rem r (poly_rem r p mm) m = poly_rem r p m`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_EQ o snd) THEN
  ASM_SIMP_TAC[POLY_REM] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_sub (poly_ring r (:1)) (poly_rem r p mm) p =
    ring_neg (poly_ring r (:1))
      (ring_sub (poly_ring r (:1)) p (poly_rem (r:A ring) p mm))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `mm:(1->num)->A`]
                  POLY_REM) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`poly_rem (r:A ring) p mm`,`t:(1->num)->A`) THEN
    UNDISCH_TAC `(p:(1->num)->A) IN ring_carrier(poly_ring r (:1))` THEN
    SPEC_TAC(`poly_ring (r:A ring) (:1)`,`s:((1->num)->A)ring`) THEN
    RING_TAC;
    MATCH_MP_TAC RING_DIVIDES_NEG THEN
    MATCH_MP_TAC RING_DIVIDES_TRANS THEN
    EXISTS_TAC `mm:(1->num)->A` THEN
    ASM_SIMP_TAC[POLY_REM_DIVIDES_SUB]]);;

let POLY_LINEAR = prove
 (`!(r:A ring) u v.
        u IN ring_carrier r /\ v IN ring_carrier r
        ==> ring_add (poly_ring r (:1)) (poly_const r u)
              (ring_mul (poly_ring r (:1)) (poly_const r v) (poly_var r one))
            IN ring_carrier(poly_ring r (:1)) /\
            poly_deg r (ring_add (poly_ring r (:1)) (poly_const r u)
              (ring_mul (poly_ring r (:1)) (poly_const r v) (poly_var r one)))
            < 2 /\
            coeff 0 (ring_add (poly_ring r (:1)) (poly_const r u)
              (ring_mul (poly_ring r (:1)) (poly_const r v) (poly_var r one)))
            = u /\
            coeff 1 (ring_add (poly_ring r (:1)) (poly_const r u)
              (ring_mul (poly_ring r (:1)) (poly_const r v) (poly_var r one)))
            = v`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[RING_ADD; RING_MUL; POLY_CONST; POLY_VAR_UNIV];
    MATCH_MP_TAC(ARITH_RULE `x <= 1 ==> x < 2`) THEN
    MATCH_MP_TAC POLY_DEG_RING_ADD_LE THEN
    ASM_SIMP_TAC[RING_MUL; POLY_CONST; POLY_VAR_UNIV; POLY_DEG_CONST;
                 LE_0] THEN
    REWRITE_TAC[POLY_RING_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
    SIMP_TAC[RING_POLYNOMIAL_CONST; RING_POLYNOMIAL_VAR] THEN
    ASM_REWRITE_TAC[POLY_DEG_CONST; POLY_DEG_VAR] THEN
    COND_CASES_TAC THEN ARITH_TAC;
    REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD; COEFF_POLY_CONST] THEN
    ASM_SIMP_TAC[COEFF_POLY_MUL_VAR; RING_POWERSERIES_CONST; RING_ADD_RZERO];
    REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD; COEFF_POLY_CONST] THEN
    ASM_SIMP_TAC[COEFF_POLY_MUL_VAR; RING_POWERSERIES_CONST] THEN
    REWRITE_TAC[ARITH; COEFF_POLY_CONST] THEN
    ASM_SIMP_TAC[RING_ADD_LZERO]]);;

let POLY_LINEAR_EXPAND = prove
 (`!(r:A ring) p.
        p IN ring_carrier(poly_ring r (:1)) /\ poly_deg r p < 2
        ==> p = ring_add (poly_ring r (:1)) (poly_const r (coeff 0 p))
                  (ring_mul (poly_ring r (:1)) (poly_const r (coeff 1 p))
                            (poly_var r one))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `2`] POLY_EXPAND_LT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  SUBGOAL_THEN `{i:num | i < 2} = {0,1}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[RING_SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY; ARITH_EQ] THEN
  SUBGOAL_THEN `!i. ring_mul (poly_ring r (:1)) (poly_const r (coeff i p))
                 (ring_pow (poly_ring r (:1)) (poly_var r one) i) IN
                 ring_carrier (poly_ring (r:A ring) (:1))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC RING_MUL THEN
    ASM_SIMP_TAC[POLY_CONST; COEFF_POLY_IN_CARRIER; RING_POW; POLY_VAR_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[ring_pow] THEN
  ASM_SIMP_TAC[RING_MUL_RID; POLY_CONST; COEFF_POLY_IN_CARRIER;
               POLY_VAR_UNIV; RING_MUL] THEN
  ASM_SIMP_TAC[RING_POW_1; POLY_VAR_UNIV; RING_ADD_RZERO; RING_MUL;
               POLY_CONST; COEFF_POLY_IN_CARRIER]);;

let QUADRATIC_MUL_ID = prove
 (`!(s:A ring) a0 a1 b0 b1 c x.
      a0 IN ring_carrier s /\ a1 IN ring_carrier s /\
      b0 IN ring_carrier s /\ b1 IN ring_carrier s /\
      c IN ring_carrier s /\ x IN ring_carrier s
      ==> ring_sub s
           (ring_mul s (ring_add s a0 (ring_mul s a1 x))
                       (ring_add s b0 (ring_mul s b1 x)))
           (ring_add s
             (ring_add s (ring_mul s a0 b0) (ring_mul s (ring_mul s a1 b1) c))
             (ring_mul s (ring_add s (ring_mul s a0 b1) (ring_mul s a1 b0))
                         x)) =
          ring_mul s (ring_mul s a1 b1) (ring_sub s (ring_pow s x 2) c)`,
  RING_TAC);;

let POLY_CONST_ADD_RING = prove
 (`!(r:A ring) x y.
        poly_const r (ring_add r x y) =
        ring_add (poly_ring r (:1)) (poly_const r x) (poly_const r y)`,
  REWRITE_TAC[POLY_RING_CLAUSES; POLY_CONST_ADD]);;

let POLY_REM_LINEAR_MUL = prove
 (`!(r:A ring) c a0 a1 b0 b1.
     ~trivial_ring r /\ c IN ring_carrier r /\
     a0 IN ring_carrier r /\ a1 IN ring_carrier r /\
     b0 IN ring_carrier r /\ b1 IN ring_carrier r
     ==> poly_rem r
          (ring_mul (poly_ring r (:1))
            (ring_add (poly_ring r (:1)) (poly_const r a0)
              (ring_mul (poly_ring r (:1)) (poly_const r a1) (poly_var r one)))
            (ring_add (poly_ring r (:1)) (poly_const r b0)
              (ring_mul (poly_ring r (:1)) (poly_const r b1)
                        (poly_var r one))))
          (ring_sub (poly_ring r (:1))
             (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
             (poly_const r c)) =
         ring_add (poly_ring r (:1))
          (poly_const r (ring_add r (ring_mul r a0 b0)
                                    (ring_mul r (ring_mul r a1 b1) c)))
          (ring_mul (poly_ring r (:1))
            (poly_const r (ring_add r (ring_mul r a0 b1) (ring_mul r a1 b0)))
            (poly_var r one))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `c:A`] POLY_QUADRATIC_MODULUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CARRIER_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[RING_UNIT_1] THEN CONJ_TAC THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`r:A ring`;
      `ring_add r (ring_mul r a0 b0) (ring_mul r (ring_mul r a1 b1) (c:A))`;
      `ring_add r (ring_mul r a0 b1) (ring_mul r a1 (b0:A))`] POLY_LINEAR) THEN
    ANTS_TAC THENL [CONJ_TAC THEN CARRIER_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_add r (ring_mul r a0 b0) (ring_mul r (ring_mul r a1 b1) c)
                IN ring_carrier r /\
                ring_add r (ring_mul r a0 b1) (ring_mul r a1 b0)
                IN ring_carrier (r:A ring)`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN CARRIER_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_CONST_ADD_RING; POLY_CONST_MUL_RING; RING_MUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) QUADRATIC_MUL_ID o rand o snd) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN CARRIER_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_DIVIDES_LMUL THEN
  ASM_SIMP_TAC[RING_DIVIDES_REFL] THEN CARRIER_TAC);;

let POLY_REM_QUADRATIC_MUL = prove
 (`!(r:A ring) c m p q.
     ~trivial_ring r /\ c IN ring_carrier r /\
     p IN ring_carrier(poly_ring r (:1)) /\
     q IN ring_carrier(poly_ring r (:1)) /\
     m = ring_sub (poly_ring r (:1))
           (ring_pow (poly_ring r (:1)) (poly_var r one) 2) (poly_const r c)
     ==> coeff 0 (poly_rem r (ring_mul (poly_ring r (:1)) p q) m) =
         ring_add r
          (ring_mul r (coeff 0 (poly_rem r p m)) (coeff 0 (poly_rem r q m)))
          (ring_mul r (ring_mul r (coeff 1 (poly_rem r p m))
                                  (coeff 1 (poly_rem r q m))) c) /\
         coeff 1 (poly_rem r (ring_mul (poly_ring r (:1)) p q) m) =
         ring_add r
          (ring_mul r (coeff 0 (poly_rem r p m)) (coeff 1 (poly_rem r q m)))
          (ring_mul r (coeff 1 (poly_rem r p m)) (coeff 0 (poly_rem r q m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th)))) THEN
  MP_TAC(ISPECL [`r:A ring`; `c:A`] POLY_QUADRATIC_MODULUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `poly_rem r (ring_mul (poly_ring r (:1)) p q) m =
    poly_rem r (ring_mul (poly_ring r (:1)) (poly_rem r p m)
                                            (poly_rem (r:A ring) q m)) m`
  SUBST1_TAC THENL [ASM_SIMP_TAC[POLY_REM_ABSORB; POLY_REM]; ALL_TAC] THEN
  ABBREV_TAC `a0 = coeff 0 (poly_rem r p (m:(1->num)->A))` THEN
  ABBREV_TAC `a1 = coeff 1 (poly_rem r p (m:(1->num)->A))` THEN
  ABBREV_TAC `b0 = coeff 0 (poly_rem r q (m:(1->num)->A))` THEN
  ABBREV_TAC `b1 = coeff 1 (poly_rem r q (m:(1->num)->A))` THEN
  SUBGOAL_THEN
   `poly_rem r p m =
    ring_add (poly_ring r (:1)) (poly_const r a0)
      (ring_mul (poly_ring r (:1)) (poly_const r a1) (poly_var r one)) /\
    poly_rem r q m =
    ring_add (poly_ring r (:1)) (poly_const r b0)
      (ring_mul (poly_ring r (:1)) (poly_const r b1)
                (poly_var (r:A ring) one))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["a0"; "a1"; "b0"; "b1"] THEN
    CONJ_TAC THEN MATCH_MP_TAC POLY_LINEAR_EXPAND THEN
    ASM_SIMP_TAC[POLY_REM] THENL
     [MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `m:(1->num)->A`]
                    POLY_DEG_REM);
      MP_TAC(ISPECL [`r:A ring`; `q:(1->num)->A`; `m:(1->num)->A`]
                    POLY_DEG_REM)] THEN
    ASM_SIMP_TAC[RING_UNIT_1] THEN
    MATCH_MP_TAC(TAUT `(q ==> p) ==> p \/ q ==> p`) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[POLY_RING_CLAUSES; POLY_DEG_0] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a0 IN ring_carrier r /\ a1 IN ring_carrier r /\
                b0 IN ring_carrier r /\ b1 IN ring_carrier (r:A ring)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a0"; "a1"; "b0"; "b1"] THEN
    ASM_SIMP_TAC[COEFF_POLY_IN_CARRIER; POLY_REM];
    ALL_TAC] THEN
  EXPAND_TAC "m" THEN ASM_SIMP_TAC[POLY_REM_LINEAR_MUL] THEN
  MP_TAC(ISPECL [`r:A ring`;
      `ring_add r (ring_mul r a0 b0) (ring_mul r (ring_mul r a1 b1) (c:A))`;
      `ring_add r (ring_mul r a0 b1) (ring_mul r a1 (b0:A))`] POLY_LINEAR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN CARRIER_TAC; SIMP_TAC[]]);;

let MLKEM_GAMMA_POW_128 = prove
 (`!i. ring_pow mlkem_zq
        (ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1)) 128 =
       ring_neg mlkem_zq (ring_1 mlkem_zq)`,
  GEN_TAC THEN REWRITE_TAC[MLKEM_ZQ] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_POW_REM; INT_POW_POW] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(2 * n + 1) * 128 = 128 * (2 * n + 1)`] THEN
  REWRITE_TAC[GSYM INT_POW_POW] THEN
  ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV INT_REDUCE_CONV))) THEN
  SUBGOAL_THEN `&3328:int = --(&1) rem &3329` SUBST1_TAC THENL
   [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[INT_POW_REM; INT_POW_NEG; INT_POW_ONE] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let RING_ADD_1_SUB_NEG_1 = prove
 (`!(s:A ring) x. x IN ring_carrier s
                  ==> ring_add s x (ring_1 s) =
                      ring_sub s x (ring_neg s (ring_1 s))`,
  RING_TAC);;

let ZQX_CLAUSES = map (fun th -> GSYM(ISPECL [`mlkem_zq`; `(:1)`] th))
                      (tl(CONJUNCTS POLY_RING_CLAUSES));;

let MLKEM_GAMMA_DIVIDES = prove
 (`!i. ring_divides mlkem_zqx
         (ring_sub mlkem_zqx (ring_pow mlkem_zqx mlkem_X 2)
            (poly_const mlkem_zq
               (ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1))))
         (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                             (ring_1 mlkem_zqx))`,
  GEN_TAC THEN REWRITE_TAC[mlkem_zqx; mlkem_X] THEN
  ABBREV_TAC `g = ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1)` THEN
  SUBGOAL_THEN `g IN ring_carrier mlkem_zq` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC RING_POW THEN
    REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_add (poly_ring mlkem_zq (:1))
      (ring_pow (poly_ring mlkem_zq (:1)) (poly_var mlkem_zq one) 256)
      (ring_1 (poly_ring mlkem_zq (:1))) =
    ring_sub (poly_ring mlkem_zq (:1))
      (ring_pow (poly_ring mlkem_zq (:1))
         (ring_pow (poly_ring mlkem_zq (:1)) (poly_var mlkem_zq one) 2) 128)
      (ring_pow (poly_ring mlkem_zq (:1)) (poly_const mlkem_zq g) 128)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM POLY_CONST_POW] THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[MLKEM_GAMMA_POW_128] THEN
    REWRITE_TAC[POLY_CONST_NEG; POLY_CONST_1] THEN REWRITE_TAC ZQX_CLAUSES THEN
    SIMP_TAC[RING_POW_POW; POLY_VAR_UNIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC RING_ADD_1_SUB_NEG_1 THEN
    SIMP_TAC[RING_POW; POLY_VAR_UNIV];
    MATCH_MP_TAC RING_DIVIDES_SUB_POW THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_SIMP_TAC[RING_POW; POLY_VAR_UNIV; POLY_CONST]]);;

let MLKEM_NTT_EVEN_ODD = prove
 (`!f i. mlkem_ntt f (2 * i) =
         coeff 0 (poly_rem mlkem_zq f
          (ring_sub mlkem_zqx (ring_pow mlkem_zqx mlkem_X 2)
            (poly_const mlkem_zq
              (ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1))))) /\
         mlkem_ntt f (2 * i + 1) =
         coeff 1 (poly_rem mlkem_zq f
          (ring_sub mlkem_zqx (ring_pow mlkem_zqx mlkem_X 2)
            (poly_const mlkem_zq
              (ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1)))))`,
  REWRITE_TAC[mlkem_ntt] THEN
  SUBGOAL_THEN `!i. (2 * i) MOD 2 = 0 /\ (2 * i) DIV 2 = i /\
                    (2 * i + 1) MOD 2 = 1 /\ (2 * i + 1) DIV 2 = i`
   (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ] THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES]);;

let MLKEM_NTT_MUL = prove
 (`!f g i.
        f IN ring_carrier mlkem_rq /\ g IN ring_carrier mlkem_rq
        ==> mlkem_ntt (ring_mul mlkem_rq f g) (2 * i) =
            ring_add mlkem_zq
             (ring_mul mlkem_zq (mlkem_ntt f (2 * i)) (mlkem_ntt g (2 * i)))
             (ring_mul mlkem_zq
               (ring_mul mlkem_zq (mlkem_ntt f (2 * i + 1))
                                  (mlkem_ntt g (2 * i + 1)))
               (ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1))) /\
            mlkem_ntt (ring_mul mlkem_rq f g) (2 * i + 1) =
            ring_add mlkem_zq
             (ring_mul mlkem_zq (mlkem_ntt f (2 * i))
                                (mlkem_ntt g (2 * i + 1)))
             (ring_mul mlkem_zq (mlkem_ntt f (2 * i + 1))
                                (mlkem_ntt g (2 * i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MLKEM_RQ] THEN STRIP_TAC THEN
  REWRITE_TAC[MLKEM_NTT_EVEN_ODD; MLKEM_RQ] THEN
  ABBREV_TAC `c = ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1)` THEN
  SUBGOAL_THEN `c IN ring_carrier mlkem_zq` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC RING_POW THEN
    REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = ring_sub mlkem_zqx (ring_pow mlkem_zqx mlkem_X 2)
                    (poly_const mlkem_zq c)` THEN
  MP_TAC(ISPECL [`mlkem_zq`; `c:int`] POLY_QUADRATIC_MODULUS) THEN
  ASM_REWRITE_TAC[MLKEM_ZQ_NONTRIVIAL; GSYM mlkem_zqx; GSYM mlkem_X] THEN
  STRIP_TAC THEN MP_TAC MLKEM_RQ_MODULUS THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_REM_DIVIDES o
    rand o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM mlkem_zqx] THEN ASM_REWRITE_TAC[RING_UNIT_1] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_MUL THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["m"; "c"] THEN REWRITE_TAC[MLKEM_GAMMA_DIVIDES]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mlkem_zqx] THEN
  MATCH_MP_TAC POLY_REM_QUADRATIC_MUL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mlkem_zqx; mlkem_X]) THEN
  ASM_REWRITE_TAC[MLKEM_ZQ_NONTRIVIAL] THEN
  CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC);;

let MLKEM_RQ_SUB = prove
 (`!f g. f IN ring_carrier mlkem_rq /\ g IN ring_carrier mlkem_rq
         ==> ring_sub mlkem_rq f g = ring_sub mlkem_zqx f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sub] THEN
  ASM_SIMP_TAC[MLKEM_RQ; RING_NEG]);;

let MLKEM_NTT_ADD = prove
 (`!f g k. f IN ring_carrier mlkem_rq /\ g IN ring_carrier mlkem_rq
           ==> mlkem_ntt (ring_add mlkem_rq f g) k =
               ring_add mlkem_zq (mlkem_ntt f k) (mlkem_ntt g k)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MLKEM_NTT_EXPLICIT; RING_ADD; MLKEM_RQ] THEN
  REWRITE_TAC[mlkem_zqx; POLY_RING_CLAUSES; COEFF_POLY_ADD] THEN
  ABBREV_TAC `x = ring_pow mlkem_zq (&17) (2 * bitreverse7 (k DIV 2) + 1)` THEN
  SUBGOAL_THEN `x IN ring_carrier mlkem_zq` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC RING_POW THEN
    REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_MLKEM_RQ; mlkem_zqx]) THEN
  ASM_SIMP_TAC[RING_ADD_RDISTRIB; COEFF_POLY_IN_CARRIER; RING_POW] THEN
  MATCH_MP_TAC RING_SUM_ADD THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; RING_MUL; COEFF_POLY_IN_CARRIER; RING_POW]);;

let MLKEM_NTT_SUB = prove
 (`!f g k. f IN ring_carrier mlkem_rq /\ g IN ring_carrier mlkem_rq
           ==> mlkem_ntt (ring_sub mlkem_rq f g) k =
               ring_sub mlkem_zq (mlkem_ntt f k) (mlkem_ntt g k)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MLKEM_NTT_EXPLICIT; RING_SUB; MLKEM_RQ_SUB] THEN
  REWRITE_TAC[mlkem_zqx; POLY_RING_CLAUSES; COEFF_POLY_SUB] THEN
  ABBREV_TAC `x = ring_pow mlkem_zq (&17) (2 * bitreverse7 (k DIV 2) + 1)` THEN
  SUBGOAL_THEN `x IN ring_carrier mlkem_zq` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC RING_POW THEN
    REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_MLKEM_RQ; mlkem_zqx]) THEN
  ASM_SIMP_TAC[RING_SUB_RDISTRIB; COEFF_POLY_IN_CARRIER; RING_POW] THEN
  MATCH_MP_TAC RING_SUM_SUB THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; RING_MUL; COEFF_POLY_IN_CARRIER; RING_POW]);;

let MLKEM_NTT_0 = prove
 (`!k. mlkem_ntt (ring_0 mlkem_rq) k = ring_0 mlkem_zq`,
  GEN_TAC THEN SIMP_TAC[MLKEM_NTT_EXPLICIT; RING_0] THEN
  REWRITE_TAC[MLKEM_RQ; mlkem_zqx; POLY_RING_CLAUSES; COEFF_POLY_0] THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_MUL_LZERO THEN MATCH_MP_TAC RING_POW THEN
  MATCH_MP_TAC RING_POW THEN REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC);;

let MLKEM_NTT_SUM = prove
 (`!(s:K->bool) f k.
        FINITE s /\ (!j. j IN s ==> f j IN ring_carrier mlkem_rq)
        ==> mlkem_ntt (ring_sum mlkem_rq s f) k =
            ring_sum mlkem_zq s (\j. mlkem_ntt (f j) k)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; MLKEM_NTT_0; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_NTT_ADD; RING_SUM] THEN
  ASM_SIMP_TAC[MLKEM_NTT_IN_ZQ; IN_MLKEM_RQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_MLKEM_RQ]) THEN
  ASM_SIMP_TAC[MLKEM_NTT_IN_ZQ]);;


(* ------------------------------------------------------------------------- *)
(* FIPS 203's MultiplyNTTs (Algorithms 11 and 12, with the products taken in *)
(* the order of Algorithm 12) computes the NTT of a product.                 *)
(* ------------------------------------------------------------------------- *)

let fips203_multiply_ntts = new_definition
 `fips203_multiply_ntts (a:num->int) (b:num->int) n =
    if EVEN n then
      ring_add mlkem_zq (ring_mul mlkem_zq (a n) (b n))
       (ring_mul mlkem_zq (ring_mul mlkem_zq (a(n + 1)) (b(n + 1)))
          (ring_pow mlkem_zq (&17) (2 * bitreverse7(n DIV 2) + 1)))
    else
      ring_add mlkem_zq (ring_mul mlkem_zq (a(n - 1)) (b n))
                        (ring_mul mlkem_zq (a n) (b(n - 1)))`;;

let MLKEM_NTT_MULTIPLY = prove
 (`!f g n. f IN ring_carrier mlkem_rq /\ g IN ring_carrier mlkem_rq
           ==> mlkem_ntt (ring_mul mlkem_rq f g) n =
               fips203_multiply_ntts (mlkem_ntt f) (mlkem_ntt g) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fips203_multiply_ntts] THEN
  DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
  ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS]) THEN
  ASM_SIMP_TAC[MLKEM_NTT_MUL; ADD1; ADD_SUB] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* fips203_multiply_ntts a b n is an element of Z_q.                         *)
(* ------------------------------------------------------------------------- *)

let TQ_MULTIPLY_NTTS_IN_ZQ = prove
 (`!a b n. fips203_multiply_ntts a b n IN ring_carrier mlkem_zq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fips203_multiply_ntts] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[MLKEM_ZQ; IN_ELIM_THM; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
