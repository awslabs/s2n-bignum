(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Supporting theory for the ML-KEM specification in common/fips203.ml.      *)
(* ========================================================================= *)

needs "common/fips203.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Remainders modulo a polynomial, and the ring poly_mod_ring.               *)
(* ------------------------------------------------------------------------- *)

let RING_SUB_SUB_SUB_CANCEL = prove
 (`!(s:A ring) a b c.
        a IN ring_carrier s /\ b IN ring_carrier s /\ c IN ring_carrier s
        ==> ring_sub s a b = ring_sub s (ring_sub s a c) (ring_sub s b c)`,
  RING_TAC);;

let RING_SUB_ADD_SUB = prove
 (`!(s:A ring) a b c.
        a IN ring_carrier s /\ b IN ring_carrier s /\ c IN ring_carrier s
        ==> ring_sub s a c = ring_add s (ring_sub s a b) (ring_sub s b c)`,
  RING_TAC);;

let POLY_REM_NONUNIT = prove
 (`!(r:A ring) p m.
        p IN ring_carrier(poly_ring r (:1)) /\
        m IN ring_carrier(poly_ring r (:1)) /\
        ~ring_unit r (coeff (poly_deg r m) m)
        ==> poly_rem r p m = p`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[poly_rem; poly_div] THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_SUB_RZERO]);;

let POLY_REM_DIVIDES_SUB = prove
 (`!(r:A ring) p m.
        p IN ring_carrier(poly_ring r (:1)) /\
        m IN ring_carrier(poly_ring r (:1))
        ==> ring_divides (poly_ring r (:1)) m
              (ring_sub (poly_ring r (:1)) p (poly_rem r p m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_divides] THEN
  ASM_SIMP_TAC[RING_SUB; POLY_REM] THEN
  EXISTS_TAC `poly_div (r:A ring) p m` THEN ASM_SIMP_TAC[POLY_DIV] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `m:(1->num)->A`]
                POLY_DIV_REM_SIMP) THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `m:(1->num)->A`] POLY_DIV) THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `m:(1->num)->A`] POLY_REM) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`poly_div (r:A ring) p m`,`d:(1->num)->A`) THEN
  SPEC_TAC(`poly_rem (r:A ring) p m`,`t:(1->num)->A`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  SPEC_TAC(`poly_ring (r:A ring) (:1)`,`s:((1->num)->A)ring`) THEN
  RING_TAC);;

let POLY_REM_EQ = prove
 (`!(r:A ring) p q m.
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        m IN ring_carrier(poly_ring r (:1))
        ==> (poly_rem r p m = poly_rem r q m <=>
             if ring_unit r (coeff (poly_deg r m) m)
             then ring_divides (poly_ring r (:1)) m
                    (ring_sub (poly_ring r (:1)) p q)
             else p = q)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[POLY_REM_NONUNIT]] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `m:(1->num)->A`]
                POLY_REM_DIVIDES_SUB) THEN
  MP_TAC(ISPECL [`r:A ring`; `q:(1->num)->A`; `m:(1->num)->A`]
                POLY_REM_DIVIDES_SUB) THEN
  MP_TAC(ISPECL [`r:A ring`; `q:(1->num)->A`; `m:(1->num)->A`] POLY_REM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC RAND_CONV
       [MATCH_MP RING_SUB_SUB_SUB_CANCEL
          (CONJ (ASSUME `(p:(1->num)->A) IN ring_carrier(poly_ring r (:1))`)
           (CONJ (ASSUME `(q:(1->num)->A) IN ring_carrier(poly_ring r (:1))`)
                 th))]) THEN
    MATCH_MP_TAC RING_DIVIDES_SUB THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `m:(1->num)->A`;
                   `poly_rem (r:A ring) q m`] POLY_REM_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[POLY_DEG_REM] THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC RAND_CONV
       [MATCH_MP RING_SUB_ADD_SUB
          (CONJ (ASSUME `(p:(1->num)->A) IN ring_carrier(poly_ring r (:1))`)
           (CONJ (ASSUME `(q:(1->num)->A) IN ring_carrier(poly_ring r (:1))`)
                 th))]) THEN
    MATCH_MP_TAC RING_DIVIDES_ADD THEN ASM_REWRITE_TAC[]]);;

let POLY_REM_REM = prove
 (`!(r:A ring) p m.
        p IN ring_carrier(poly_ring r (:1)) /\
        m IN ring_carrier(poly_ring r (:1))
        ==> poly_rem r (poly_rem r p m) m = poly_rem r p m`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o snd) THEN
  ASM_SIMP_TAC[POLY_REM] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[POLY_DEG_REM] THEN
  ASM_SIMP_TAC[RING_SUB_REFL; POLY_REM; RING_DIVIDES_0]);;

let POLY_REM_CONG = prove
 (`!(r:A ring) m p p' q q'.
        m IN ring_carrier(poly_ring r (:1)) /\
        p IN ring_carrier(poly_ring r (:1)) /\
        p' IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        q' IN ring_carrier(poly_ring r (:1)) /\
        poly_rem r p m = poly_rem r p' m /\ poly_rem r q m = poly_rem r q' m
        ==> poly_rem r (ring_add (poly_ring r (:1)) p q) m =
            poly_rem r (ring_add (poly_ring r (:1)) p' q') m /\
            poly_rem r (ring_mul (poly_ring r (:1)) p q) m =
            poly_rem r (ring_mul (poly_ring r (:1)) p' q') m /\
            poly_rem r (ring_neg (poly_ring r (:1)) p) m =
            poly_rem r (ring_neg (poly_ring r (:1)) p') m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
  ASM_SIMP_TAC[POLY_REM_EQ; RING_ADD; RING_MUL; RING_NEG] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN
     `ring_sub (poly_ring r (:1)) (ring_add (poly_ring r (:1)) p q)
                                 (ring_add (poly_ring r (:1)) p' q') =
      ring_add (poly_ring r (:1)) (ring_sub (poly_ring r (:1)) p p')
                                  (ring_sub (poly_ring (r:A ring) (:1)) q q')`
    SUBST1_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN
      SPEC_TAC(`poly_ring (r:A ring) (:1)`,`s:((1->num)->A)ring`) THEN
      RING_TAC;
      MATCH_MP_TAC RING_DIVIDES_ADD THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `ring_sub (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) p q)
                                 (ring_mul (poly_ring r (:1)) p' q') =
      ring_add (poly_ring r (:1))
        (ring_mul (poly_ring r (:1)) (ring_sub (poly_ring r (:1)) p p') q)
        (ring_mul (poly_ring r (:1)) p'
                  (ring_sub (poly_ring (r:A ring) (:1)) q q'))`
    SUBST1_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN
      SPEC_TAC(`poly_ring (r:A ring) (:1)`,`s:((1->num)->A)ring`) THEN
      RING_TAC;
      MATCH_MP_TAC RING_DIVIDES_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC RING_DIVIDES_RMUL; MATCH_MP_TAC RING_DIVIDES_LMUL] THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `ring_sub (poly_ring r (:1)) (ring_neg (poly_ring r (:1)) p)
                                 (ring_neg (poly_ring r (:1)) p') =
      ring_neg (poly_ring r (:1)) (ring_sub (poly_ring (r:A ring) (:1)) p p')`
    SUBST1_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN
      SPEC_TAC(`poly_ring (r:A ring) (:1)`,`s:((1->num)->A)ring`) THEN
      RING_TAC;
      MATCH_MP_TAC RING_DIVIDES_NEG THEN ASM_REWRITE_TAC[]]]);;

let POLY_REM_ABSORB = prove
 (`!(r:A ring) m p q.
        m IN ring_carrier(poly_ring r (:1)) /\
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1))
        ==> poly_rem r (ring_add (poly_ring r (:1)) (poly_rem r p m) q) m =
            poly_rem r (ring_add (poly_ring r (:1)) p q) m /\
            poly_rem r (ring_add (poly_ring r (:1)) p (poly_rem r q m)) m =
            poly_rem r (ring_add (poly_ring r (:1)) p q) m /\
            poly_rem r (ring_mul (poly_ring r (:1)) (poly_rem r p m) q) m =
            poly_rem r (ring_mul (poly_ring r (:1)) p q) m /\
            poly_rem r (ring_mul (poly_ring r (:1)) p (poly_rem r q m)) m =
            poly_rem r (ring_mul (poly_ring r (:1)) p q) m /\
            poly_rem r (ring_neg (poly_ring r (:1)) (poly_rem r p m)) m =
            poly_rem r (ring_neg (poly_ring r (:1)) p) m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `m:(1->num)->A`; `poly_rem (r:A ring) p m`;
                 `p:(1->num)->A`; `q:(1->num)->A`; `q:(1->num)->A`]
                POLY_REM_CONG) THEN
  MP_TAC(ISPECL [`r:A ring`; `m:(1->num)->A`; `p:(1->num)->A`;
                 `p:(1->num)->A`; `poly_rem (r:A ring) q m`; `q:(1->num)->A`]
                POLY_REM_CONG) THEN
  ASM_SIMP_TAC[POLY_REM; POLY_REM_REM]);;

let POLY_MOD_RING = prove
 (`!(r:A ring) m.
     m IN ring_carrier(poly_ring r (:1))
     ==> ring_carrier(poly_mod_ring r m) =
           {p | p IN ring_carrier(poly_ring r (:1)) /\ poly_rem r p m = p} /\
         ring_0(poly_mod_ring r m) = poly_rem r (ring_0(poly_ring r (:1))) m /\
         ring_1(poly_mod_ring r m) = poly_rem r (ring_1(poly_ring r (:1))) m /\
         ring_neg(poly_mod_ring r m) =
           (\p. poly_rem r (ring_neg (poly_ring r (:1)) p) m) /\
         ring_add(poly_mod_ring r m) =
           (\p q. poly_rem r (ring_add (poly_ring r (:1)) p q) m) /\
         ring_mul(poly_mod_ring r m) =
           (\p q. poly_rem r (ring_mul (poly_ring r (:1)) p q) m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl poly_mod_ring)))))
   (CONJUNCT2 ring_tybij)))) THEN
  REWRITE_TAC[GSYM poly_mod_ring] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[POLY_REM; POLY_REM_REM; RING_0; RING_1; RING_NEG;
                 RING_ADD; RING_MUL; POLY_REM_ABSORB] THEN
    TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN
    ASM_SIMP_TAC[RING_ADD_LZERO; RING_MUL_LID; RING_ADD_LNEG] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_eq o concl))) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`poly_ring (r:A ring) (:1)`,`s:((1->num)->A)ring`) THEN
    RING_TAC;
    DISCH_TAC THEN
    ASM_REWRITE_TAC[ring_carrier; ring_0; ring_1;
                    ring_neg; ring_add; ring_mul]]);;

(* The remainder ring is indeed the quotient ring when lc(m) is a unit.      *)

let POLY_MOD_RING_ISOMORPHIC_QUOTIENT = prove
 (`!(r:A ring) m.
        m IN ring_carrier(poly_ring r (:1)) /\
        ring_unit r (coeff (poly_deg r m) m)
        ==> quotient_ring (poly_ring r (:1))
                          (ideal_generated (poly_ring r (:1)) {m})
            isomorphic_ring poly_mod_ring r m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`poly_ring (r:A ring) (:1)`; `poly_mod_ring (r:A ring) m`;
                 `\p. poly_rem (r:A ring) p m`]
                FIRST_RING_EPIMORPHISM_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ring_epimorphism; ring_homomorphism; POLY_MOD_RING] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[POLY_REM; POLY_REM_REM; POLY_REM_ABSORB; RING_NEG; RING_ADD;
                 RING_MUL] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:(1->num)->A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:A ring`; `m:(1->num)->A`; `x:(1->num)->A`;
                     `poly_rem (r:A ring) x m`; `x:(1->num)->A`;
                     `x:(1->num)->A`] POLY_REM_CONG) THEN
      ASM_SIMP_TAC[POLY_REM; POLY_REM_REM];
      GEN_TAC THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_SIMP_TAC[POLY_REM; POLY_REM_REM];
        STRIP_TAC THEN EXISTS_TAC `x:(1->num)->A` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[ring_kernel; IDEAL_GENERATED_SING; POLY_MOD_RING] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:(1->num)->A` THEN
  ASM_CASES_TAC `p IN ring_carrier(poly_ring (r:A ring) (:1))` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[POLY_REM_EQ; RING_0; RING_SUB_RZERO];
    ASM_MESON_TAC[ring_divides]]);;


(* ------------------------------------------------------------------------- *)
(* Remainder modulo a quadratic X^2 - c: the even and odd parts of the       *)
(* polynomial evaluated at c.                                                *)
(* ------------------------------------------------------------------------- *)

let POLY_QUADRATIC_MODULUS = prove
 (`!(r:A ring) c.
        ~trivial_ring r /\ c IN ring_carrier r
        ==> ring_sub (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) 2) (poly_const r c)
            IN ring_carrier(poly_ring r (:1)) /\
            poly_deg r (ring_sub (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
              (poly_const r c)) = 2 /\
            coeff 2 (ring_sub (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
              (poly_const r c)) = ring_1 r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TRIVIAL_RING_10] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_SUB; RING_POW; POLY_VAR_UNIV; POLY_CONST] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_SUB; COEFF_POLY_VARPOW;
                COEFF_POLY_CONST; ARITH_EQ] THEN
    ASM_SIMP_TAC[RING_SUB_RZERO; RING_1];
    DISCH_TAC THEN MATCH_MP_TAC POLY_DEG_EQ_COEFF THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL; RING_SUB; RING_POW; POLY_VAR_UNIV;
                   POLY_CONST];
      X_GEN_TAC `d:num` THEN
      REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_SUB; COEFF_POLY_VARPOW;
                  COEFF_POLY_CONST] THEN
      ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[] THENL
       [ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `d = 2` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RING_SUB_REFL; RING_0] THEN ARITH_TAC]]);;

let RING_SUM_PAIRS = prove
 (`!(r:A ring) g n.
        (!i. i < 2 * n ==> g i IN ring_carrier r)
        ==> ring_sum r {i | i < 2 * n} g =
            ring_sum r {j | j < n} (\j. ring_add r (g(2 * j)) (g(2 * j + 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{i | i < 2 * n} = IMAGE (\j. 2 * j) {j | j < n} UNION
                      IMAGE (\j. 2 * j + 1) {j | j < n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN DISJ_CASES_TAC(SPEC `i:num` EVEN_OR_ODD) THENL
       [DISJ1_TAC; DISJ2_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS; ODD_EXISTS]) THEN
      REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS; ADD1] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[prove(`!j k. ~(2 * j = 2 * k + 1)`,
      REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH])];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `\j:num. 2 * j`; `g:num->A`; `{j:num | j < n}`]
                RING_SUM_IMAGE) THEN
  MP_TAC(ISPECL [`r:A ring`; `\j:num. 2 * j + 1`; `g:num->A`;
                 `{j:num | j < n}`] RING_SUM_IMAGE) THEN
  REWRITE_TAC[ARITH_RULE `2 * j = 2 * k <=> j = k`;
              ARITH_RULE `2 * j + 1 = 2 * k + 1 <=> j = k`] THEN
  SIMP_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[o_DEF] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_ADD THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let POLY_EXPAND_LT = prove
 (`!(r:A ring) p n.
        p IN ring_carrier(poly_ring r (:1)) /\ poly_deg r p < n
        ==> p = ring_sum (poly_ring r (:1)) {i | i < n}
                 (\i. ring_mul (poly_ring r (:1)) (poly_const r (coeff i p))
                       (ring_pow (poly_ring r (:1)) (poly_var r one) i))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC LAND_CONV [MATCH_MP POLY_EXPAND th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `i:num`] COEFF_ABOVE_DEG) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL] THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[POLY_CONST_0] THEN
  REWRITE_TAC[GSYM(ISPECL [`r:A ring`; `(:1)`]
                   (CONJUNCT1(CONJUNCT2 POLY_RING_CLAUSES)))] THEN
  MATCH_MP_TAC RING_MUL_LZERO THEN SIMP_TAC[RING_POW; POLY_VAR_UNIV]);;

let COEFF_POLY_IN_CARRIER = prove
 (`!(r:A ring) p d.
        p IN ring_carrier(poly_ring r (:1)) ==> coeff d p IN ring_carrier r`,
  MESON_TAC[RING_POLYNOMIAL; COEFF_IN_CARRIER_ALT]);;

let POLY_CONST_RING_SUM = prove
 (`!(r:A ring) (k:K->bool) (h:K->A).
        FINITE k /\ (!i. i IN k ==> h i IN ring_carrier r)
        ==> poly_const r (ring_sum r k h) =
            ring_sum (poly_ring r (:1)) k (\i. poly_const r (h i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `(:1)`] RING_HOMOMORPHISM_POLY_CONST) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_HOMOMORPHISM_SUM) THEN
  DISCH_THEN(MP_TAC o SPECL [`h:K->A`; `k:K->bool`]) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let POLY_CONST_POW = prove
 (`!(r:A ring) c n.
        c IN ring_carrier r
        ==> poly_const r (ring_pow r c n) =
            ring_pow (poly_ring r (:1)) (poly_const r c) n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `(:1)`] RING_HOMOMORPHISM_POLY_CONST) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_HOMOMORPHISM_POW) THEN
  ASM_SIMP_TAC[]);;

let POLY_CONST_MUL_RING = prove
 (`!(r:A ring) x y.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> poly_const r (ring_mul r x y) =
            ring_mul (poly_ring r (:1)) (poly_const r x) (poly_const r y)`,
  SIMP_TAC[POLY_RING_CLAUSES; POLY_CONST_MUL]);;

let QUADRATIC_REM_ID = prove
 (`!(s:A ring) f0 f1 x x2j cj.
      f0 IN ring_carrier s /\ f1 IN ring_carrier s /\ x IN ring_carrier s /\
      x2j IN ring_carrier s /\ cj IN ring_carrier s
      ==> ring_sub s (ring_add s (ring_mul s f0 x2j)
                                 (ring_mul s f1 (ring_mul s x2j x)))
                     (ring_add s (ring_mul s f0 cj)
                                 (ring_mul s (ring_mul s f1 cj) x)) =
          ring_add s (ring_mul s f0 (ring_sub s x2j cj))
                     (ring_mul s (ring_mul s f1 x) (ring_sub s x2j cj))`,
  RING_TAC);;

let POLY_REM_QUADRATIC = prove
 (`!(r:A ring) f c n.
     ~trivial_ring r /\ c IN ring_carrier r /\
     f IN ring_carrier(poly_ring r (:1)) /\ poly_deg r f < 2 * n
     ==> poly_rem r f
           (ring_sub (poly_ring r (:1))
             (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
             (poly_const r c)) =
         ring_add (poly_ring r (:1))
          (poly_const r (ring_sum r {j | j < n}
             (\j. ring_mul r (coeff (2 * j) f) (ring_pow r c j))))
          (ring_mul (poly_ring r (:1))
            (poly_const r (ring_sum r {j | j < n}
               (\j. ring_mul r (coeff (2 * j + 1) f) (ring_pow r c j))))
            (poly_var r one))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `c:A`] POLY_QUADRATIC_MODULUS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = ring_sub (poly_ring r (:1))
                   (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
                   (poly_const r (c:A))` THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o snd) THEN
  ASM_SIMP_TAC[RING_ADD; RING_MUL; POLY_CONST; RING_SUM; POLY_VAR_UNIV;
               RING_UNIT_1] THEN
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC(ARITH_RULE `x <= 1 ==> x < 2`) THEN
    MATCH_MP_TAC POLY_DEG_RING_ADD_LE THEN
    SIMP_TAC[RING_MUL; POLY_CONST; RING_SUM; POLY_VAR_UNIV; POLY_DEG_CONST;
             LE_0] THEN
    REWRITE_TAC[POLY_RING_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
    SIMP_TAC[RING_POLYNOMIAL_CONST; RING_SUM; RING_POLYNOMIAL_VAR] THEN
    REWRITE_TAC[POLY_DEG_CONST; POLY_DEG_VAR] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `f:(1->num)->A`; `2 * n`] POLY_EXPAND_LT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_PAIRS o
    lhand o rand o snd) THEN
  ASM_SIMP_TAC[RING_MUL; POLY_CONST; COEFF_POLY_IN_CARRIER; RING_POW;
               POLY_VAR_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_add (poly_ring r (:1))
     (poly_const r (ring_sum r {j | j < n}
        (\j. ring_mul r (coeff (2 * j) f) (ring_pow r c j))))
     (ring_mul (poly_ring r (:1))
        (poly_const r (ring_sum r {j | j < n}
           (\j. ring_mul r (coeff (2 * j + 1) f) (ring_pow r c j))))
        (poly_var r one)) =
    ring_sum (poly_ring r (:1)) {j | j < n}
     (\j. ring_add (poly_ring r (:1))
           (poly_const r (ring_mul r (coeff (2 * j) f) (ring_pow r c j)))
           (ring_mul (poly_ring r (:1))
              (poly_const r (ring_mul r (coeff (2 * j + 1) f)
                                        (ring_pow r (c:A) j)))
              (poly_var r one)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_SUM_ADD; RING_SUM_RMUL; POLY_CONST_RING_SUM;
                 FINITE_NUMSEG_LT; RING_MUL; RING_POW; COEFF_POLY_IN_CARRIER;
                 POLY_CONST; POLY_VAR_UNIV] THEN
    CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_ADD o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; RING_MUL; RING_POW; COEFF_POLY_IN_CARRIER;
                   POLY_CONST; POLY_VAR_UNIV];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_RMUL THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; RING_MUL; RING_POW; COEFF_POLY_IN_CARRIER;
                 POLY_CONST; POLY_VAR_UNIV];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC RING_ADD ORELSE MATCH_MP_TAC RING_MUL ORELSE
           MATCH_MP_TAC RING_POW ORELSE CONJ_TAC) THEN
    ASM_SIMP_TAC[POLY_CONST; POLY_VAR_UNIV; COEFF_POLY_IN_CARRIER; RING_POW;
                 RING_MUL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RING_SUM_CLOSED THEN
  ASM_SIMP_TAC[RING_DIVIDES_0; RING_DIVIDES_ADD] THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_divides (poly_ring r (:1)) m
      (ring_sub (poly_ring r (:1))
        (ring_pow (poly_ring r (:1)) (poly_var r one) (2 * j))
        (poly_const r (ring_pow r (c:A) j)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLY_CONST_POW; GSYM RING_POW_POW; POLY_VAR_UNIV] THEN
    ASM_CASES_TAC `j = 0` THENL
     [ASM_REWRITE_TAC[ring_pow] THEN
      ASM_SIMP_TAC[RING_SUB_REFL; RING_1; RING_DIVIDES_0];
      EXPAND_TAC "m" THEN MATCH_MP_TAC RING_DIVIDES_SUB_POW THEN
      ASM_SIMP_TAC[RING_POW; POLY_VAR_UNIV; POLY_CONST]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_CONST_MUL_RING; COEFF_POLY_IN_CARRIER; RING_POW] THEN
  SIMP_TAC[RING_POW_ADD; RING_POW_1; POLY_VAR_UNIV] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) QUADRATIC_REM_ID o rand o snd) THEN
  ASM_SIMP_TAC[POLY_CONST; COEFF_POLY_IN_CARRIER; RING_POW; POLY_VAR_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_DIVIDES_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC RING_DIVIDES_LMUL THEN
  ASM_SIMP_TAC[POLY_CONST; COEFF_POLY_IN_CARRIER; RING_MUL; POLY_VAR_UNIV]);;


(* ------------------------------------------------------------------------- *)
(* Z_q and R_q: R_q consists of the polynomials of degree < 256, which are   *)
(* in bijection with their coefficient arrays.                               *)
(* ------------------------------------------------------------------------- *)

let PRIME_3329 = prove
 (`prime 3329`,
  CONV_TAC PRIME_CONV);;

let MLKEM_ZQ = prove
 (`field mlkem_zq /\ ~trivial_ring mlkem_zq /\
   ring_carrier mlkem_zq = {x | &0 <= x /\ x < &3329} /\
   ring_0 mlkem_zq = &0 /\ ring_1 mlkem_zq = &1 /\
   ring_neg mlkem_zq = (\a. --a rem &3329) /\
   ring_add mlkem_zq = (\a b. (a + b) rem &3329) /\
   ring_sub mlkem_zq = (\a b. (a - b) rem &3329) /\
   ring_mul mlkem_zq = (\a b. (a * b) rem &3329) /\
   ring_pow mlkem_zq = (\a k. a pow k rem &3329)`,
  REWRITE_TAC[mlkem_zq; FIELD_INTEGER_MOD_RING; TRIVIAL_INTEGER_MOD_RING;
              PRIME_3329] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH_RULE `0 < 3329`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let IN_MLKEM_ZQ = prove
 (`!x. x IN ring_carrier mlkem_zq <=> &0 <= x /\ x < &3329`,
  REWRITE_TAC[MLKEM_ZQ; IN_ELIM_THM]);;

let MLKEM_ZQ_UNIT_1 = prove
 (`ring_unit mlkem_zq (&1)`,
  MESON_TAC[RING_UNIT_1; MLKEM_ZQ]);;

let POLY_REM_SMALL = prove
 (`!(r:A ring) p m.
        p IN ring_carrier(poly_ring r (:1)) /\
        m IN ring_carrier(poly_ring r (:1)) /\
        (poly_deg r p < poly_deg r m \/ p = ring_0(poly_ring r (:1)))
        ==> poly_rem r p m = p`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o snd) THEN
  ASM_SIMP_TAC[RING_SUB_REFL; RING_DIVIDES_0; COND_ID]);;

let POLY_XN_PLUS_1 = prove
 (`!(r:A ring) n.
        ~trivial_ring r /\ ~(n = 0)
        ==> ring_add (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) n)
              (ring_1 (poly_ring r (:1)))
            IN ring_carrier(poly_ring r (:1)) /\
            poly_deg r (ring_add (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) n)
              (ring_1 (poly_ring r (:1)))) = n /\
            coeff n (ring_add (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) n)
              (ring_1 (poly_ring r (:1)))) = ring_1 r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TRIVIAL_RING_10] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_ADD; RING_POW; POLY_VAR_UNIV; RING_1] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD; COEFF_POLY_VARPOW;
                COEFF_POLY_1] THEN
    ASM_SIMP_TAC[RING_ADD_RZERO; RING_1];
    DISCH_TAC THEN MATCH_MP_TAC POLY_DEG_EQ_COEFF THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL; RING_ADD; RING_POW; POLY_VAR_UNIV; RING_1];
      X_GEN_TAC `d:num` THEN
      REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD; COEFF_POLY_VARPOW;
                  COEFF_POLY_1] THEN
      ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[] THENL
       [ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `d:num = n` THEN ASM_REWRITE_TAC[LE_REFL] THEN
      ASM_SIMP_TAC[RING_ADD_RZERO; RING_0]]]);;

let MLKEM_RQ_MODULUS = prove
 (`ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256) (ring_1 mlkem_zqx)
   IN ring_carrier mlkem_zqx /\
   poly_deg mlkem_zq
    (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256) (ring_1 mlkem_zqx)) =
   256 /\
   coeff 256
    (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256) (ring_1 mlkem_zqx)) =
   &1`,
  REWRITE_TAC[mlkem_zqx; mlkem_X] THEN
  MP_TAC(ISPECL [`mlkem_zq`; `256`] POLY_XN_PLUS_1) THEN
  REWRITE_TAC[MLKEM_ZQ; ARITH_EQ]);;

(* So R_q is (isomorphic to) Z_q[X]/(X^256 + 1).                             *)

let MLKEM_RQ_ISOMORPHIC_QUOTIENT = prove
 (`quotient_ring mlkem_zqx
     (ideal_generated mlkem_zqx
       {ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                 (ring_1 mlkem_zqx)})
   isomorphic_ring mlkem_rq`,
  REWRITE_TAC[mlkem_rq] THEN REWRITE_TAC[mlkem_zqx] THEN
  MATCH_MP_TAC POLY_MOD_RING_ISOMORPHIC_QUOTIENT THEN
  REWRITE_TAC[GSYM mlkem_zqx; MLKEM_RQ_MODULUS] THEN
  MP_TAC(ISPEC `mlkem_zq` RING_UNIT_1) THEN REWRITE_TAC[MLKEM_ZQ]);;

let MLKEM_RQ_REM = prove
 (`!p. p IN ring_carrier mlkem_zqx
       ==> (poly_rem mlkem_zq p
              (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                  (ring_1 mlkem_zqx)) = p <=>
            poly_deg mlkem_zq p < 256)`,
  REPEAT STRIP_TAC THEN MP_TAC MLKEM_RQ_MODULUS THEN
  ABBREV_TAC `m = ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                     (ring_1 mlkem_zqx)` THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o lhand o snd) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mlkem_zqx]) THEN
  ASM_SIMP_TAC[RING_SUB_REFL; RING_DIVIDES_0; MLKEM_ZQ_UNIT_1] THEN
  DISCH_THEN SUBST1_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[POLY_DEG_0; POLY_RING_CLAUSES] THEN
  ARITH_TAC);;

let MLKEM_RQ_CARRIER = prove
 (`ring_carrier mlkem_rq =
     {p | p IN ring_carrier mlkem_zqx /\ poly_deg mlkem_zq p < 256}`,
  MP_TAC(ISPECL [`mlkem_zq`;
                 `ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                     (ring_1 mlkem_zqx)`] POLY_MOD_RING) THEN
  REWRITE_TAC[GSYM mlkem_zqx; GSYM mlkem_rq; MLKEM_RQ_MODULUS] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[MLKEM_RQ_REM]);;

let IN_MLKEM_RQ = prove
 (`!p. p IN ring_carrier mlkem_rq <=>
       p IN ring_carrier mlkem_zqx /\ poly_deg mlkem_zq p < 256`,
  REWRITE_TAC[MLKEM_RQ_CARRIER; IN_ELIM_THM]);;

let MLKEM_RQ = prove
 (`ring_0 mlkem_rq = ring_0 mlkem_zqx /\
   ring_1 mlkem_rq = ring_1 mlkem_zqx /\
   (!p. p IN ring_carrier mlkem_rq
        ==> ring_neg mlkem_rq p = ring_neg mlkem_zqx p) /\
   (!p q. p IN ring_carrier mlkem_rq /\ q IN ring_carrier mlkem_rq
          ==> ring_add mlkem_rq p q = ring_add mlkem_zqx p q) /\
   (!p q. ring_mul mlkem_rq p q =
          poly_rem mlkem_zq (ring_mul mlkem_zqx p q)
            (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                (ring_1 mlkem_zqx)))`,
  MP_TAC(ISPECL [`mlkem_zq`;
                 `ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                     (ring_1 mlkem_zqx)`] POLY_MOD_RING) THEN
  REWRITE_TAC[GSYM mlkem_zqx; GSYM mlkem_rq; MLKEM_RQ_MODULUS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_MLKEM_RQ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_RQ_REM; RING_0; RING_1; RING_NEG;
                                     RING_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mlkem_zqx; GSYM RING_POLYNOMIAL]) THEN
  REWRITE_TAC[mlkem_zqx; POLY_RING_CLAUSES; POLY_DEG_0; POLY_DEG_1] THEN
  ASM_SIMP_TAC[POLY_DEG_NEG; ARITH] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_ADD_LE o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let COEFF_MLKEM_POLY = prove
 (`!a i. coeff i (mlkem_poly a) = if i < 256 then a i rem &3329 else &0`,
  REWRITE_TAC[coeff; mlkem_poly]);;

let MLKEM_POLY_IN_RQ = prove
 (`!a. mlkem_poly a IN ring_carrier mlkem_rq`,
  GEN_TAC THEN
  SUBGOAL_THEN `ring_polynomial mlkem_zq (mlkem_poly a)` ASSUME_TAC THENL
   [REWRITE_TAC[ring_polynomial; ring_powerseries; FINITE_MONOMIAL_VARS_1;
                INFINITE; IN_MLKEM_ZQ] THEN
    REWRITE_TAC[mlkem_poly] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[INT_LE_REFL; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      CONV_TAC INT_REDUCE_CONV;
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\i (v:1). i) {i | i < 256}` THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
      REWRITE_TAC[FORALL_FUN_FROM_1; IN_IMAGE; IN_ELIM_THM; MLKEM_ZQ] THEN
      X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_MLKEM_RQ; mlkem_zqx; POLY_RING; SUBSET_UNIV;
                  IN_ELIM_THM] THEN
  MATCH_MP_TAC(ARITH_RULE `x <= 255 ==> x < 256`) THEN
  ASM_SIMP_TAC[POLY_DEG_LE_COEFF_EQ; COEFF_MLKEM_POLY; MLKEM_ZQ] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MLKEM_POLY_COEFF = prove
 (`!p. p IN ring_carrier mlkem_rq ==> mlkem_poly (\i. coeff i p) = p`,
  REWRITE_TAC[IN_MLKEM_RQ; mlkem_zqx; POLY_RING; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_FUN_FROM_1] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[mlkem_poly] THEN
  REWRITE_TAC[GSYM COEFF] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN
    MP_TAC(ISPECL [`mlkem_zq`; `p:(1->num)->int`; `i:num`]
                  COEFF_IN_CARRIER_ALT) THEN
    ASM_REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC;
    MP_TAC(ISPECL [`mlkem_zq`; `p:(1->num)->int`; `i:num`]
                  COEFF_ABOVE_DEG) THEN
    ASM_REWRITE_TAC[MLKEM_ZQ] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC]]);;

let MLKEM_RQ_EQ = prove
 (`!p q. p IN ring_carrier mlkem_rq /\ q IN ring_carrier mlkem_rq
         ==> (p = q <=> !i. i < 256 ==> coeff i p = coeff i q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `p:(1->num)->int` MLKEM_POLY_COEFF) THEN
  MP_TAC(SPEC `q:(1->num)->int` MLKEM_POLY_COEFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mlkem_poly; FUN_EQ_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* zeta = 17 is a primitive 256-th root of unity mod q, so the 128 values    *)
(* zeta^(2 * BitRev7(i) + 1) are distinct.                                   *)
(* ------------------------------------------------------------------------- *)

let BITREVERSE7_BOUND = prove
 (`!i. bitreverse7 i < 128`,
  GEN_TAC THEN REWRITE_TAC[bitreverse7] THEN
  MP_TAC(ISPEC `word_reversefields 1 (word i:7 word)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:7)`] THEN ARITH_TAC);;

let BITREVERSE7_INJ = prove
 (`!i j. i < 128 /\ j < 128 /\ bitreverse7 i = bitreverse7 j ==> i = j`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bitreverse7; VAL_EQ]) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `word_reversefields 1:7 word->7 word`) THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_CONV `dimindex(:7)`; CONG] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 128 ==> x < 2 EXP 7`]);;

let MLKEM_ZETA_ORDER = prove
 (`order 3329 17 = 256`,
  MP_TAC(SPECL [`3329`; `17`; `256`] ORDER_DIVIDES) THEN
  MP_TAC(SPECL [`3329`; `17`; `128`] ORDER_DIVIDES) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; ARITH_RULE `128 = 2 EXP 7`] THEN
  SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2] THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MLKEM_ZETA_EXP_INJ = prove
 (`!a b. a < 256 /\ b < 256 /\ (17 EXP a == 17 EXP b) (mod 3329)
         ==> a = b`,
  let lemma = prove
   (`!a b. a <= b /\ b < 256 /\ (17 EXP a == 17 EXP b) (mod 3329)
           ==> a = b`,
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(17 EXP a == 17 EXP b) (mod 3329)` THEN
    SUBGOAL_THEN `17 EXP b = 17 EXP a * 17 EXP (b - a)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `coprime(17 EXP a,3329)` MP_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
      CONV_TAC COPRIME_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `!a x n. coprime(a,n) /\ (a == a * x) (mod n) ==> (x == 1) (mod n)`)) THEN
    REWRITE_TAC[ORDER_DIVIDES; MLKEM_ZETA_ORDER] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `a:num <= b \/ b <= a`) THEN
  ASM_MESON_TAC[lemma; CONG_SYM]);;

let MLKEM_GAMMA_INJ = prove
 (`!i j. i < 128 /\ j < 128 /\
         ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1) =
         ring_pow mlkem_zq (&17) (2 * bitreverse7 j + 1)
         ==> i = j`,
  REWRITE_TAC[MLKEM_ZQ; INT_OF_NUM_POW; INT_OF_NUM_REM; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[GSYM CONG] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BITREVERSE7_INJ THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 * x + 1 = 2 * y + 1 ==> x = y`) THEN
  MATCH_MP_TAC MLKEM_ZETA_EXP_INJ THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `i:num` BITREVERSE7_BOUND) THEN
  MP_TAC(SPEC `j:num` BITREVERSE7_BOUND) THEN ARITH_TAC);;


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
(* The NTT and its inverse as single sums of integers mod q. These are the   *)
(* functions forward_ntt and (up to the Montgomery factor 2^16, which turns  *)
(* 3303 = 1 / 128 into 512) inverse_ntt of common/mlkem_mldsa.ml and of the  *)
(* mlkem-native HOL Light proofs, applied to coefficient arrays. Note that   *)
(* 1175 = 1 / 17 mod q.                                                      *)
(* ------------------------------------------------------------------------- *)

let RING_SUM_INTEGER_MOD_RING = prove
 (`!n (s:K->bool) f.
        FINITE s /\ ~(n = 0) /\
        (!i. i IN s ==> f i IN ring_carrier(integer_mod_ring n))
        ==> ring_sum (integer_mod_ring n) s f = isum s f rem &n`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; ISUM_CLAUSES; FORALL_IN_INSERT] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; INT_REM_ZERO] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REFL_TAC);;

let INT_CONG_POW = prove
 (`!x y n k. (x:int == y) (mod n) ==> (x pow k == y pow k) (mod n)`,
  REWRITE_TAC[GSYM INT_REM_EQ] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN ASM_REWRITE_TAC[]);;

let INT_CONG_ISUM = prove
 (`!n f g (s:A->bool).
        FINITE s /\ (!x. x IN s ==> (f x == g x) (mod n))
        ==> (isum s f == isum s g) (mod n)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPEC `(\x y:int. (x == y) (mod n))`
    ISUM_RELATED)) THEN
  ASM_REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`;
   INTEGER_RULE
   `(x:int == y) (mod n) /\ (x' == y') (mod n)
    ==> (x + x' == y + y') (mod n)`]);;

let INT_POW_POW_SWAP = prove
 (`!x:int a b. (x pow a) pow b = (x pow b) pow a`,
  REWRITE_TAC[INT_POW_POW] THEN REWRITE_TAC[MULT_SYM]);;

let INT_GEOM_SERIES = prove
 (`!y:int n. (y - &1) * isum (0..n) (\j. y pow j) = y pow (SUC n) - &1`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ISUM_CLAUSES_NUMSEG; LE_0; INT_ADD_LDISTRIB] THEN
  REWRITE_TAC[INT_POW] THEN INT_ARITH_TAC);;

let BITREVERSE7_BOUND = prove
 (`!n. bitreverse7 n < 128`,
  GEN_TAC THEN REWRITE_TAC[bitreverse7] THEN
  MP_TAC(ISPEC `word_reversefields 1 (word n:7 word)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:7)`] THEN ARITH_TAC);;

let BITREVERSE7_BITREVERSE7 = prove
 (`!n. n < 128 ==> bitreverse7(bitreverse7 n) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bitreverse7; WORD_VAL] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:7)`] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 128 ==> n < 2 EXP 7`]);;

let MLKEM_NTT_FORWARD = prove
 (`!f k. f IN ring_carrier mlkem_rq
         ==> mlkem_ntt f k =
             isum (0..127)
              (\j. coeff (2 * j + k MOD 2) f *
                   &17 pow ((2 * bitreverse7 (k DIV 2) + 1) * j)) rem &3329`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_NTT_EXPLICIT] THEN
  REWRITE_TAC[mlkem_zq] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_INTEGER_MOD_RING o
    lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; ARITH_EQ] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM mlkem_zq] THEN MATCH_MP_TAC COEFF_POLY_IN_CARRIER THEN
      ASM_MESON_TAC[IN_MLKEM_RQ; mlkem_zqx];
      REPEAT(MATCH_MP_TAC RING_POW) THEN
      REWRITE_TAC[GSYM mlkem_zq; IN_MLKEM_ZQ] THEN INT_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  SUBGOAL_THEN `{j:num | j < 128} = 0..127` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_POW_POW; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG; INT_CONG_LREM; INTEGER_RULE
   `(x:int == x) (mod n)`]);;

(* The sums over j of (zeta^(2 * r + 1) / zeta^(2 * m + 1))^j.               *)

let MLKEM_ZETA_ORTHOGONAL = prove
 (`!r m. r < 128 /\ m < 128
         ==> (isum (0..127)
               (\j. (&1175 pow (2 * m + 1) * &17 pow (2 * r + 1)) pow j) ==
              if m = r then &128 else &0) (mod &3329)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y:int = &1175 pow (2 * m + 1) * &17 pow (2 * r + 1)` THEN
  SUBGOAL_THEN `!n. ((&17 * &1175:int) pow n == &1) (mod &3329)` ASSUME_TAC
  THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`&17 * &1175:int`; `&1:int`; `&3329:int`]
      INT_CONG_POW) THEN
    REWRITE_TAC[INT_POW_ONE] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&17 pow (2 * m + 1) * y:int == &17 pow (2 * r + 1)) (mod &3329)`
  ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[INT_MUL_ASSOC; GSYM INT_POW_MUL] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!a b n:int. (a == &1) (mod n) ==> (a * b == b) (mod n)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((y:int) pow 128 == &1) (mod &3329)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[INT_POW_MUL] THEN
    ONCE_REWRITE_TAC[INT_POW_POW_SWAP] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!a b n:int. (a == -- &1) (mod n) /\ (b == -- &1) (mod n)
                  ==> (a * b == &1) (mod n)`) THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `2 * m + 1` (MATCH_MP INT_CONG_POW
       (prove(`(&1175 pow 128 == -- &1:int) (mod &3329)`,
              REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))));
      MP_TAC(SPEC `2 * r + 1` (MATCH_MP INT_CONG_POW
       (prove(`(&17 pow 128 == -- &1:int) (mod &3329)`,
              REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))))]
    THEN REWRITE_TAC[INT_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH; INT_POW_ONE];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(y:int == &1) (mod &3329)` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[GSYM INT_POW_MUL] THEN
      ONCE_REWRITE_TAC[INT_MUL_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!z. (x:int == z) (mod n) /\ (z == y) (mod n) ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `isum (0..127) (\j. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      UNDISCH_TAC `(y:int == &1) (mod &3329)` THEN
      DISCH_THEN(MP_TAC o SPEC `j:num` o MATCH_MP INT_CONG_POW) THEN
      REWRITE_TAC[INT_POW_ONE];
      REWRITE_TAC[ISUM_CONST_NUMSEG] THEN
      CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
      REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:int == &1) (mod &3329))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(17 EXP (2 * m + 1) == 17 EXP (2 * r + 1)) (mod 3329)`
    MP_TAC THENL
     [REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `!a b y n:int. (a * y == b) (mod n) /\ (y == &1) (mod n)
                      ==> (a == b) (mod n)`) THEN
      EXISTS_TAC `y:int` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(SPECL [`2 * m + 1`; `2 * r + 1`] MLKEM_ZETA_EXP_INJ) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`y:int`; `127`] INT_GEOM_SERIES) THEN
  REWRITE_TAC[ARITH_RULE `SUC 127 = 128`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&3329 divides ((y - &1) * isum (0..127) (\j. (y:int) pow j))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(INTEGER_RULE
     `!x n:int. (x == &1) (mod n) ==> n divides (x - &1)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[PRIME_INT_DIVPROD_EQ; PRIME_3329] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `!x n:int. n divides (x - &1) <=> (x == &1) (mod n)`] THEN
  REWRITE_TAC[INTEGER_RULE `!s n:int. n divides s ==> (s == &0) (mod n)`]);;

let MLKEM_NTT_INV_EXPLICIT = prove
 (`!a. (!i. i < 256 ==> &0 <= a i /\ a i < &3329)
       ==> mlkem_ntt_inv a =
           mlkem_poly
            (\k. &3303 * isum (0..127)
                          (\j. a(2 * bitreverse7 j + k MOD 2) *
                               &1175 pow ((2 * j + 1) * k DIV 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NTT_INJ THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_NTT_INV) THEN
  ASM_SIMP_TAC[MLKEM_POLY_IN_RQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SIMP_TAC[MLKEM_NTT_FORWARD; MLKEM_POLY_IN_RQ; COEFF_MLKEM_POLY] THEN
  REWRITE_TAC[ARITH_RULE `(2 * x + i MOD 2) DIV 2 = x`;
              MOD_MULT_ADD; MOD_MOD_REFL] THEN
  SUBGOAL_THEN `(a:num->int) k = a k rem &3329` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INT_REM_EQ] THEN ONCE_REWRITE_TAC[INTEGER_RULE
   `(x:int == y) (mod n) <=> (y == x) (mod n)`] THEN
  ABBREV_TAC `b = k MOD 2` THEN ABBREV_TAC `r = bitreverse7 (k DIV 2)` THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!y. (x:int == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`) THEN
  EXISTS_TAC
   `isum (0..127)
     (\j. &3303 *
          isum (0..127)
           (\m. a (2 * bitreverse7 m + b) *
                &1175 pow ((2 * m + 1) * j) * &17 pow ((2 * r + 1) * j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 * j + b < 256` (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "b" THEN MP_TAC(SPECL [`k:num`; `2`] MOD_LT_EQ) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!x x' y n:int. (x == x') (mod n) /\ x' * y = z
                     ==> (x * y == z) (mod n)`) THEN
    EXISTS_TAC
     `&3303 * isum (0..127)
               (\m. a (2 * bitreverse7 m + b) * &1175 pow ((2 * m + 1) * j))`
    THEN REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`] THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC; GSYM ISUM_RMUL];
    ALL_TAC] THEN
  REWRITE_TAC[ISUM_LMUL] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [ISUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[ISUM_LMUL] THEN
  REWRITE_TAC[GSYM INT_POW_POW; GSYM INT_POW_MUL] THEN
  SUBGOAL_THEN `r < 128` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[BITREVERSE7_BOUND]; ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!y. (x:int == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`) THEN
  EXISTS_TAC
   `&3303 * isum (0..127)
             (\m. a (2 * bitreverse7 m + b) * (if m = r then &128 else &0))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INTEGER_RULE
     `(x:int == y) (mod n) ==> (c * x == c * y) (mod n)`) THEN
    MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(x:int == y) (mod n) ==> (c * x == c * y) (mod n)`) THEN
    MATCH_MP_TAC MLKEM_ZETA_ORTHOGONAL THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `isum (0..127)
     (\m. a (2 * bitreverse7 m + b) * (if m = r then &128 else &0)) =
    isum (0..127)
     (\m. if m = r then a (2 * bitreverse7 r + b) * &128 else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ISUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[ISUM_DELTA; IN_NUMSEG; LE_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `r < 128 ==> r <= 127`] THEN
  SUBGOAL_THEN `2 * bitreverse7 r + b = k` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "b"] THEN
    ASM_SIMP_TAC[BITREVERSE7_BITREVERSE7; RDIV_LT_EQ; ARITH_EQ;
                 ARITH_RULE `k < 256 ==> k < 2 * 128`] THEN
    MP_TAC(SPECL [`k:num`; `2`] DIVISION) THEN EXPAND_TAC "b" THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_RULE `!x:int. (&3303 * x * &128 == x) (mod &3329)`]]);;

let MLKEM_NTT_INV_COEFF = prove
 (`!a k. (!i. i < 256 ==> &0 <= a i /\ a i < &3329) /\ k < 256
         ==> coeff k (mlkem_ntt_inv a) =
             (&3303 * isum (0..127)
                       (\j. a(2 * bitreverse7 j + k MOD 2) *
                            &1175 pow ((2 * j + 1) * k DIV 2))) rem &3329`,
  SIMP_TAC[MLKEM_NTT_INV_EXPLICIT; COEFF_MLKEM_POLY]);;


(* ------------------------------------------------------------------------- *)
(* Rounding, compression and decompression.                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_ROUND_UNIQUE = prove
 (`!a b n. &0 < b
           ==> (mlkem_round(a,b) = n <=>
                &2 * b * n <= &2 * a + b /\ &2 * a + b < &2 * b * (n + &1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_round] THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`&2 * a + b:int`; `&2 * b:int`] INT_DIVISION) THEN
    ASM_SIMP_TAC[INT_ARITH `&0 < b ==> ~(&2 * b:int = &0)`;
                 INT_ARITH `&0 < b ==> abs(&2 * b:int) = &2 * b`] THEN
    INT_ARITH_TAC;
    STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
    EXISTS_TAC `(&2 * a + b) - &2 * b * n:int` THEN
    ASM_SIMP_TAC[INT_ARITH `&0 < b ==> abs(&2 * b:int) = &2 * b`] THEN
    ASM_INT_ARITH_TAC]);;

let MLKEM_COMPRESS_DECOMPRESS = prove
 (`!d y. d < 12 /\ &0 <= y /\ y < &2 pow d
         ==> mlkem_compress d (mlkem_decompress d y) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_compress; mlkem_decompress] THEN
  SUBGOAL_THEN `&1:int <= &2 pow d /\ &2 pow d <= &2048:int`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(x = 0) ==> 1 <= x`) THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 11` THEN
      CONJ_TAC THENL [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
                      CONV_TAC NUM_REDUCE_CONV]];
    ALL_TAC] THEN
  ABBREV_TAC `x = mlkem_round(&3329 * y,&2 pow d)` THEN
  MP_TAC(SPECL [`&3329 * y:int`; `(&2 pow d):int`; `x:int`]
               MLKEM_ROUND_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `mlkem_round(&2 pow d * x,&3329) = y` SUBST1_TAC THENL
   [MP_TAC(SPECL [`&2 pow d * x:int`; `&3329:int`; `y:int`]
                 MLKEM_ROUND_UNIQUE) THEN
    REWRITE_TAC[INT_ARITH `&0:int < &3329`] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_INT_ARITH_TAC;
    MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Byte strings, encoding and decoding. The first four theorems are also in  *)
(* common/words2.ml, with the same statements.                               *)
(* ------------------------------------------------------------------------- *)

let LENGTH_BYTELIST_OF_NUM = prove
 (`!k n. LENGTH(bytelist_of_num k n) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bytelist_of_num; LENGTH]);;

let NUM_OF_BYTELIST_OF_NUM = prove
 (`!k n. num_of_bytelist(bytelist_of_num k n) = n MOD 256 EXP k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bytelist_of_num; num_of_bytelist] THEN
  REWRITE_TAC[EXP; MOD_1] THEN GEN_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN ARITH_TAC);;

let NUM_OF_BYTELIST_BOUND = prove
 (`!l. num_of_bytelist l < 256 EXP (LENGTH l)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; num_of_bytelist; ARITH; EXP] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC);;

let BYTELIST_OF_NUM_OF_BYTELIST = prove
 (`!l. bytelist_of_num (LENGTH l) (num_of_bytelist l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; bytelist_of_num; LENGTH] THEN FIRST_X_ASSUM
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  SIMP_TAC[CONS_11; MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; WORD_VAL_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_8; MOD_EQ_SELF; ARITH; MOD_MOD_REFL] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let MLKEM_ENCODE_LENGTH = prove
 (`!d n f. LENGTH(mlkem_encode d n f) = (d * n) DIV 8`,
  REWRITE_TAC[mlkem_encode; LENGTH_BYTELIST_OF_NUM]);;

let MLKEM_ENCODE_DIGIT = prove
 (`!d (f:num->int) i. num_of_int(f i rem &2 pow d) < 2 EXP d /\
                      &(num_of_int(f i rem &2 pow d)) = f i rem &2 pow d`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 <= (f:num->int) i rem &2 pow d` ASSUME_TAC THENL
   [REWRITE_TAC[INT_REM_POS_EQ; INT_POW_EQ_0] THEN CONV_TAC INT_REDUCE_CONV;
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT]] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_LT_REM_EQ; INT_LT_POW2]);;

let NUM_OF_BYTELIST_MLKEM_ENCODE = prove
 (`!d n f. 8 divides (d * n)
           ==> num_of_bytelist(mlkem_encode d n f) =
               nsum {i | i < n}
                    (\i. num_of_int(f i rem &2 pow d) * 2 EXP (d * i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_encode; NUM_OF_BYTELIST_OF_NUM] THEN
  MATCH_MP_TAC MOD_LT THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` MP_TAC o REWRITE_RULE[divides]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(8 * m) DIV 8 = m`] THEN
  SUBGOAL_THEN `256 EXP m = (2 EXP d) EXP n` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_EXP; ARITH_RULE `256 = 2 EXP 8`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (d * i) = (2 EXP d) EXP i * b`] THEN
  MATCH_MP_TAC DIGITSUM_BOUND THEN REWRITE_TAC[MLKEM_ENCODE_DIGIT]);;

let MLKEM_DECODE_ENCODE = prove
 (`!d n f i.
        8 divides (d * n) /\ i < n
        ==> mlkem_decode d (mlkem_encode d n f) i =
            if d = 12 then (f i rem &2 pow d) rem &3329 else f i rem &2 pow d`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mlkem_decode; NUM_OF_BYTELIST_MLKEM_ENCODE] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (d * i) = (2 EXP d) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`2 EXP d`; `\i. num_of_int ((f:num->int) i rem &2 pow d)`;
                 `{i:num | i < n}`; `i:num`] DIGITSUM_DIV_MOD) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; MLKEM_ENCODE_DIGIT] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MLKEM_ENCODE_DIGIT] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let MLKEM_DECODE_ENCODE_SMALL = prove
 (`!d n f i.
        8 divides (d * n) /\ i < n /\ ~(d = 12) /\ &0 <= f i /\ f i < &2 pow d
        ==> mlkem_decode d (mlkem_encode d n f) i = f i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_DECODE_ENCODE] THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[]);;

let MLKEM_DECODE_ENCODE_12 = prove
 (`!n f i.
        8 divides (12 * n) /\ i < n /\ &0 <= f i /\ f i < &3329
        ==> mlkem_decode 12 (mlkem_encode 12 n f) i = f i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_DECODE_ENCODE] THEN
  SUBGOAL_THEN `(f:num->int) i rem &2 pow 12 = f i` SUBST1_TAC THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The K-PKE algorithms in the NTT-domain form of FIPS 203 Algorithms 13, 14 *)
(* and 15. Key generation and encryption need the assumption that the        *)
(* SampleNTT values used are < q, which holds whenever SampleNTT is          *)
(* well-defined, i.e. whenever the loop of FIPS 203 Algorithm 7 terminates.  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_ENCODE_EQ = prove
 (`!d n f g. (!i. i < n ==> f i = g i)
             ==> mlkem_encode d n f = mlkem_encode d n g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_encode] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let MLKEM_NTT_INV_EQ = prove
 (`!a b. (!i. i < 256 ==> a i = b i) ==> mlkem_ntt_inv a = mlkem_ntt_inv b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_ntt_inv] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]);;

let FIPS203_MULTIPLY_NTTS_EQ = prove
 (`!a a' b b' n.
        (!i. i < 256 ==> a i = a' i /\ b i = b' i) /\ n < 256
        ==> fips203_multiply_ntts a b n = fips203_multiply_ntts a' b' n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fips203_multiply_ntts] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    SUBGOAL_THEN `m < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `m < 128 ==> 2 * m + 1 < 256`];
    ASM_SIMP_TAC[ARITH_RULE `n < 256 ==> n - 1 < 256`]]);;

let MLKEM_CBD_IN_RQ = prove
 (`!eta b. mlkem_cbd eta b IN ring_carrier mlkem_rq`,
  REWRITE_TAC[mlkem_cbd] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLKEM_POLY_IN_RQ]);;

let MLKEM_DOT_IN_RQ = prove
 (`!k u v. mlkem_dot k u v IN ring_carrier mlkem_rq`,
  REWRITE_TAC[mlkem_dot; RING_SUM]);;

let MLKEM_SAMPLE_NTT_POS = prove
 (`!b i. &0 <= mlkem_sample_ntt b i`,
  REWRITE_TAC[mlkem_sample_ntt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_POS]);;

let MLKEM_DECODE_12_BOUNDS = prove
 (`!b i. &0 <= mlkem_decode 12 b i /\ mlkem_decode 12 b i < &3329`,
  REWRITE_TAC[mlkem_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let MLKEM_RQ_COEFF_ADD = prove
 (`!p q k. p IN ring_carrier mlkem_rq /\ q IN ring_carrier mlkem_rq
           ==> coeff k (ring_add mlkem_rq p q) =
               ring_add mlkem_zq (coeff k p) (coeff k q)`,
  SIMP_TAC[MLKEM_RQ; mlkem_zqx; POLY_RING_CLAUSES; COEFF_POLY_ADD]);;

let MLKEM_RQ_COEFF_SUB = prove
 (`!p q k. p IN ring_carrier mlkem_rq /\ q IN ring_carrier mlkem_rq
           ==> coeff k (ring_sub mlkem_rq p q) =
               ring_sub mlkem_zq (coeff k p) (coeff k q)`,
  SIMP_TAC[MLKEM_RQ_SUB; mlkem_zqx; POLY_RING_CLAUSES; COEFF_POLY_SUB]);;

let MLKEM_NTT_DOT = prove
 (`!k u v n.
        (!j. j < k ==> u j IN ring_carrier mlkem_rq /\
                       v j IN ring_carrier mlkem_rq)
        ==> mlkem_ntt (mlkem_dot k u v) n =
            ring_sum mlkem_zq {j | j < k}
             (\j. fips203_multiply_ntts (mlkem_ntt (u j))
                                         (mlkem_ntt (v j)) n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_dot] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLKEM_NTT_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; MLKEM_NTT_MULTIPLY]);;

let MLKEM_DOT_NTT_INV = prove
 (`!k a v.
        (!j n. j < k /\ n < 256 ==> &0 <= a j n /\ a j n < &3329) /\
        (!j. j < k ==> v j IN ring_carrier mlkem_rq)
        ==> mlkem_dot k (\j. mlkem_ntt_inv (a j)) v =
            mlkem_ntt_inv
             (\n. ring_sum mlkem_zq {j | j < k}
                   (\j. fips203_multiply_ntts (a j) (mlkem_ntt (v j)) n))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [GSYM(MATCH_MP MLKEM_NTT_INV_NTT (SPEC_ALL MLKEM_DOT_IN_RQ))] THEN
  MATCH_MP_TAC MLKEM_NTT_INV_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLKEM_NTT_DOT o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MLKEM_NTT_INV]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_SIMP_TAC[MLKEM_NTT_INV]);;

let KPKE_KEYGEN_FIPS = prove
 (`!k eta1 eta2 du dv d.
        (!i j n. i < k /\ j < k /\ n < 256
                 ==> mlkem_sample_ntt
                      (APPEND (FST(mlkem_g(APPEND d [word k])))
                              [word j; word i]) n < &3329)
        ==> kpke_keygen (k,eta1,eta2,du,dv) d =
            let rho,sigma = mlkem_g (APPEND d [word k]) in
            let Ahat = \i j. mlkem_sample_ntt (APPEND rho [word j; word i]) in
            let shat = \i. mlkem_ntt
                            (mlkem_cbd eta1 (mlkem_prf eta1 sigma (word i))) in
            let ehat = \i. mlkem_ntt
                            (mlkem_cbd eta1
                              (mlkem_prf eta1 sigma (word(k + i)))) in
            let that = \i n. ring_add mlkem_zq
                              (ring_sum mlkem_zq {j | j < k}
                                (\j. fips203_multiply_ntts
                                      (Ahat i j) (shat j) n))
                              (ehat i n) in
            APPEND (mlkem_encode 12 (256 * k)
                     (\n. that (n DIV 256) (n MOD 256))) rho,
            mlkem_encode 12 (256 * k) (\n. shat (n DIV 256) (n MOD 256))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kpke_keygen] THEN
  SPEC_TAC(`mlkem_g (APPEND d [word k])`,`p:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`rho:byte list`; `sigma:byte list`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC `i = n DIV 256` THEN ABBREV_TAC `m = n MOD 256` THEN
  SUBGOAL_THEN `i < k /\ m < 256` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["i"; "m"] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < k
        ==> mlkem_ntt_inv (mlkem_sample_ntt (APPEND rho [word j; word i]))
            IN ring_carrier mlkem_rq /\
            !n'. n' < 256
                 ==> mlkem_ntt (mlkem_ntt_inv
                       (mlkem_sample_ntt (APPEND rho [word j; word i]))) n' =
                     mlkem_sample_ntt (APPEND rho [word j; word i]) n'`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MLKEM_NTT_INV THEN
    ASM_SIMP_TAC[MLKEM_SAMPLE_NTT_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MLKEM_NTT_ADD; MLKEM_DOT_IN_RQ; MLKEM_CBD_IN_RQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLKEM_NTT_DOT o lhand o snd) THEN
  ASM_SIMP_TAC[MLKEM_CBD_IN_RQ] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_SIMP_TAC[]);;

let KPKE_ENCRYPT_FIPS = prove
 (`!k eta1 eta2 du dv ek m r.
        (!i j n. i < k /\ j < k /\ n < 256
                 ==> mlkem_sample_ntt
                      (APPEND (mlkem_slice (384 * k) 32 ek) [word j; word i])
                      n < &3329)
        ==> kpke_encrypt (k,eta1,eta2,du,dv) ek m r =
            let that = \i n. mlkem_decode 12 ek (256 * i + n) in
            let rho = mlkem_slice (384 * k) 32 ek in
            let Ahat = \i j. mlkem_sample_ntt (APPEND rho [word j; word i]) in
            let y = \i. mlkem_cbd eta1 (mlkem_prf eta1 r (word i)) in
            let e1 = \i. mlkem_cbd eta2 (mlkem_prf eta2 r (word(k + i))) in
            let e2 = mlkem_cbd eta2 (mlkem_prf eta2 r (word(2 * k))) in
            let yhat = \i. mlkem_ntt (y i) in
            let u = \i. ring_add mlkem_rq
                         (mlkem_ntt_inv
                           (\n. ring_sum mlkem_zq {j | j < k}
                                 (\j. fips203_multiply_ntts
                                       (Ahat j i) (yhat j) n)))
                         (e1 i) in
            let mu = mlkem_poly(\j. mlkem_decompress 1 (mlkem_decode 1 m j)) in
            let v = ring_add mlkem_rq
                     (ring_add mlkem_rq
                       (mlkem_ntt_inv
                         (\n. ring_sum mlkem_zq {j | j < k}
                               (\j. fips203_multiply_ntts
                                     (that j) (yhat j) n)))
                       e2) mu in
            APPEND
             (mlkem_encode du (256 * k)
               (\n. mlkem_compress du (coeff (n MOD 256) (u(n DIV 256)))))
             (mlkem_encode dv 256 (\n. mlkem_compress dv (coeff n v)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[kpke_encrypt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  SIMP_TAC[MLKEM_DOT_NTT_INV; MLKEM_DECODE_12_BOUNDS; MLKEM_CBD_IN_RQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLKEM_DOT_NTT_INV THEN REWRITE_TAC[MLKEM_CBD_IN_RQ] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLKEM_SAMPLE_NTT_POS] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]);;

let KPKE_DECRYPT_FIPS = prove
 (`!k eta1 eta2 du dv dk c.
        kpke_decrypt (k,eta1,eta2,du,dv) dk c =
        let c2 = mlkem_slice (32 * du * k) (32 * dv) c in
        let u = \i. mlkem_poly
                     (\j. mlkem_decompress du
                           (mlkem_decode du c (256 * i + j))) in
        let v = mlkem_poly(\j. mlkem_decompress dv (mlkem_decode dv c2 j)) in
        let shat = \i n. mlkem_decode 12 dk (256 * i + n) in
        let w = ring_sub mlkem_rq v
                 (mlkem_ntt_inv
                   (\n. ring_sum mlkem_zq {j | j < k}
                         (\j. fips203_multiply_ntts
                               (shat j) (mlkem_ntt (u j)) n))) in
        mlkem_encode 1 256 (\j. mlkem_compress 1 (coeff j w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kpke_decrypt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  SIMP_TAC[MLKEM_DOT_NTT_INV; MLKEM_DECODE_12_BOUNDS; MLKEM_POLY_IN_RQ]);;

(* ------------------------------------------------------------------------- *)
(* The input checks: the modulus check of FIPS 203 Section 7.2 says exactly  *)
(* that ek has the right length and all its 12-bit fields (except those of   *)
(* rho) are < q.                                                             *)
(* ------------------------------------------------------------------------- *)

let LIST_OF_SEQ_EL_BYTELIST = prove
 (`!n l. n <= LENGTH l
         ==> list_of_seq (\i. EL i l) n =
             bytelist_of_num n (num_of_bytelist l)`,
  INDUCT_TAC THEN REWRITE_TAC[LIST_OF_SEQ; bytelist_of_num] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n <= 0)`] THEN
  REWRITE_TAC[LE_SUC; num_of_bytelist; o_DEF; EL; HD; TL] THEN
  DISCH_TAC THEN REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_MULT_ADD; MOD_LT; WORD_VAL];
    MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[DIV_MULT_ADD; DIV_LT; ARITH_EQ; ADD_CLAUSES] THEN
    DISCH_THEN(K ALL_TAC) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let MLKEM_SLICE_0 = prove
 (`!n l. n <= LENGTH l
         ==> mlkem_slice 0 n l = bytelist_of_num n (num_of_bytelist l)`,
  REWRITE_TAC[mlkem_slice; ADD_CLAUSES; LIST_OF_SEQ_EL_BYTELIST]);;

let BYTELIST_OF_NUM_EQ = prove
 (`!m a b. bytelist_of_num m a = bytelist_of_num m b <=>
           a MOD 256 EXP m = b MOD 256 EXP m`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `num_of_bytelist`) THEN
    REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM];
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM]]);;

let NUM_OF_INT_MLKEM_DECODE_12 = prove
 (`!b i. num_of_int(mlkem_decode 12 b i rem &2 pow 12) =
         ((num_of_bytelist b DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329`,
  REWRITE_TAC[mlkem_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_POW; NUM_OF_INT_OF_NUM] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC(ARITH_RULE `x < 3329 ==> x < 2 EXP 12`) THEN
  REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]);;

let MLKEM_EK_CHECK = prove
 (`!k eta1 eta2 du dv ek.
        mlkem_ek_check (k,eta1,eta2,du,dv) ek <=>
        LENGTH ek = 384 * k + 32 /\
        !i. i < 256 * k
            ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_ek_check] THEN
  ASM_CASES_TAC `LENGTH(ek:byte list) = 384 * k + 32` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MLKEM_SLICE_0; ARITH_RULE `384 * k <= 384 * k + 32`] THEN
  REWRITE_TAC[mlkem_encode; ARITH_RULE `(12 * 256 * k) DIV 8 = 384 * k`] THEN
  REWRITE_TAC[BYTELIST_OF_NUM_EQ; NUM_OF_INT_MLKEM_DECODE_12] THEN
  SUBGOAL_THEN `256 EXP (384 * k) = (2 EXP 12) EXP (256 * k)` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_EXP; ARITH_RULE `256 = 2 EXP 8`] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (12 * i) = (2 EXP 12) EXP i * b`] THEN
  W(fun (_,w) ->
      let stm = lhand(lhand(lhand w)) in
      SUBGOAL_THEN (mk_binop `(<):num->num->bool` stm
                             `(2 EXP 12) EXP (256 * k)`) ASSUME_TAC) THENL
   [MATCH_MP_TAC DIGITSUM_BOUND THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < 3329 ==> x < 2 EXP 12`) THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    ASM_SIMP_TAC[MOD_LT]] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM DIGITSUM_WORKS_GEN] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_UNIQUE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < 3329 ==> x < 2 EXP 12`) THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; EXP_EXP; MOD_EQ_SELF; ARITH_EQ]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
