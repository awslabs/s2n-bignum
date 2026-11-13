(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The inverse NTT: the generated NTTInv_hol (FIPS 203 Algorithm 10)         *)
(* computes the handwritten mlkem_ntt_inv, and the TqVectorNTTInv wrappers   *)
(* apply it to each entry of a vector.                                       *)
(*                                                                           *)
(* The proof is algebraic and runs the forward NTT backwards. Let a be the   *)
(* coefficients of mlkem_ntt_inv b, so that the forward stage 2 of a is b.   *)
(* One inverse layer with half-block size L maps c * (forward stage L a) to  *)
(* 2 c * (forward stage 2L a), because the generated zeta for it is minus    *)
(* the inverse of the forward zeta (NTTINV_IZETA_FACT). After the seven      *)
(* layers the array is 128 * a, and ScaleCoefficients by 3303 = 1/128 gives  *)
(* a. The forward stage lemmas are re-derived here with the tag NTTINV_.     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The stage invariant and one layer of butterflies, as integer arrays.      *)
(* ------------------------------------------------------------------------- *)

let nttinv_exp = new_definition
 `nttinv_exp L m = (2 * bitreverse7 (m * (L DIV 2)) + 1) * (L DIV 2)`;;

let nttinv_stage = new_definition
 `nttinv_stage L (a:num->int) k =
    isum (0..256 DIV L - 1)
         (\t. a (k MOD L + L * t) * &17 pow (nttinv_exp L (k DIV L) * t))`;;

let nttinv_zeta = new_definition
 `nttinv_zeta L M = (&17:int) pow (bitreverse7 (128 DIV L + M))`;;

let nttinv_layer = new_definition
 `nttinv_layer L (b:num->int) k =
    if k MOD (2 * L) < L
    then b k + nttinv_zeta L (k DIV (2 * L)) * b (k + L)
    else b (k - L) - nttinv_zeta L (k DIV (2 * L)) * b k`;;

let NTTINV_EXP_FACTS = prove
 (`!L M. L IN {2,4,8,16,32,64,128} /\ M < 128 DIV L
         ==> (2 * nttinv_exp L (2 * M)) MOD 256 = nttinv_exp (2 * L) M MOD 256 /\
             (2 * nttinv_exp L (2 * M + 1)) MOD 256 = nttinv_exp (2 * L) M MOD 256 /\
             nttinv_exp L (2 * M) MOD 256 = bitreverse7 (128 DIV L + M) /\
             nttinv_exp L (2 * M + 1) MOD 256 =
             bitreverse7 (128 DIV L + M) + 128`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
              NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[nttinv_exp] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[bitreverse7] THEN CONV_TAC(DEPTH_CONV BITMAP_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let NTTINV_BR_BOUND = prove
 (`!L M. L IN {2,4,8,16,32,64,128} /\ M < 128 DIV L
         ==> bitreverse7 (128 DIV L + M) < 128`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
              NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC BITREVERSE7_BOUND THEN
  ASM_ARITH_TAC);;

let NTTINV_POW17_MOD = prove
 (`!x. ((&17:int) pow x == &17 pow (x MOD 256)) (mod &3329)`,
  GEN_TAC THEN
  SUBGOAL_THEN `x = 256 * x DIV 256 + x MOD 256` (fun th ->
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o RAND_CONV) [th])
  THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_POW_ADD; GSYM INT_POW_POW] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a:int == &1) (mod n) ==> (a * b == b) (mod n)`) THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
   [GSYM(SPEC `x DIV 256` INT_POW_ONE)] THEN
  MATCH_MP_TAC INT_CONG_POW THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let NTTINV_L_FACTS = prove
 (`!L. L IN {2,4,8,16,32,64,128}
       ==> 0 < L /\ 256 DIV L - 1 = 2 * (128 DIV L - 1) + 1 /\
           256 DIV (2 * L) - 1 = 128 DIV L - 1 /\
           2 * L * (128 DIV L) = 256 /\ 0 < 128 DIV L /\
           EVEN L /\ 2 * L <= 256`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let NTTINV_ISUM_PAIR = INT_OF_REAL_THM SUM_PAIR;;

let NTTINV_POW17_CONG = prove
 (`!x y. x MOD 256 = y MOD 256 ==> ((&17:int) pow x == &17 pow y) (mod &3329)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
  ONCE_REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] NTTINV_POW17_MOD] THEN
  ASM_REWRITE_TAC[]);;

let NTTINV_STAGE_SPLIT = prove
 (`!L a M c r. L IN {2,4,8,16,32,64,128} /\ M < 128 DIV L /\ c < 2 /\ r < L
   ==> nttinv_stage L a (2 * L * M + c * L + r) =
       isum (0..128 DIV L - 1)
            (\s. a (r + L * 2 * s) * &17 pow (nttinv_exp L (2 * M + c) * 2 * s)) +
       isum (0..128 DIV L - 1)
            (\s. a (r + L * (2 * s + 1)) *
                 &17 pow (nttinv_exp L (2 * M + c) * (2 * s + 1)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_L_FACTS) THEN
  REWRITE_TAC[nttinv_stage] THEN
  SUBGOAL_THEN `(2 * L * M + c * L + r) MOD L = r /\
                (2 * L * M + c * L + r) DIV L = 2 * M + c`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL [MATCH_MP_TAC MOD_UNIQ; MATCH_MP_TAC DIV_UNIQ] THENL
     [EXISTS_TAC `2 * M + c`; EXISTS_TAC `r:num`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\t. (a:num->int) (r + L * t) *
                      &17 pow (nttinv_exp L (2 * M + c) * t)`;
                 `0`; `128 DIV L - 1`] NTTINV_ISUM_PAIR) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ISUM_ADD_NUMSEG]);;

let NTTINV_STAGE_LOWER = prove
 (`!L a M c r. L IN {2,4,8,16,32,64,128} /\ M < 128 DIV L /\ c < 2 /\ r < L
   ==> nttinv_stage (2 * L) a (2 * L * M + c * L + r) =
       isum (0..128 DIV L - 1)
            (\s. a (c * L + r + 2 * L * s) * &17 pow (nttinv_exp (2 * L) M * s))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_L_FACTS) THEN
  REWRITE_TAC[nttinv_stage] THEN
  SUBGOAL_THEN `(2 * L * M + c * L + r) MOD (2 * L) = c * L + r /\
                (2 * L * M + c * L + r) DIV (2 * L) = M`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [SUBGOAL_THEN `c * L + r < 2 * L` ASSUME_TAC THENL
     [UNDISCH_TAC `c < 2` THEN SPEC_TAC(`c:num`,`c:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOD_UNIQ; MATCH_MP_TAC DIV_UNIQ] THENL
     [EXISTS_TAC `M:num`; EXISTS_TAC `c * L + r`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC; GSYM MULT_ASSOC]);;

let NTTINV_STAGE_STEP_CORE = prove
 (`!L a M c r.
     L IN {2,4,8,16,32,64,128} /\ M < 128 DIV L /\ c < 2 /\ r < L
     ==> (nttinv_stage L a (2 * L * M + c * L + r) ==
          nttinv_stage (2 * L) a (2 * L * M + r) +
          (if c = 0 then nttinv_zeta L M else --nttinv_zeta L M) *
          nttinv_stage (2 * L) a (2 * L * M + L + r)) (mod &3329)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NTTINV_STAGE_SPLIT] THEN
  MP_TAC(SPECL [`L:num`; `a:num->int`; `M:num`; `0`; `r:num`]
    NTTINV_STAGE_LOWER) THEN
  MP_TAC(SPECL [`L:num`; `a:num->int`; `M:num`; `1`; `r:num`]
    NTTINV_STAGE_LOWER) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 2 /\ 1 < 2`; MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `(2 * nttinv_exp L (2 * M + c)) MOD 256 = nttinv_exp (2 * L) M MOD 256 /\
    nttinv_exp L (2 * M + c) MOD 256 = bitreverse7 (128 DIV L + M) + 128 * c`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
     (ARITH_RULE `c < 2 ==> c = 0 \/ c = 1`)) THEN
    ASM_SIMP_TAC[NTTINV_EXP_FACTS; ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&17:int) pow nttinv_exp L (2 * M + c) ==
     (if c = 0 then nttinv_zeta L M else --nttinv_zeta L M)) (mod &3329)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(INTEGER_RULE
     `!y. (x:int == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`) THEN
    EXISTS_TAC `(&17:int) pow (bitreverse7 (128 DIV L + M) + 128 * c)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NTTINV_POW17_CONG THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      MP_TAC(SPECL [`L:num`; `M:num`] NTTINV_BR_BOUND) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `c < 2` THEN ARITH_TAC;
      REWRITE_TAC[nttinv_zeta] THEN
      FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
       (ARITH_RULE `c < 2 ==> c = 0 \/ c = 1`)) THEN
      REWRITE_TAC[ARITH_EQ; MULT_CLAUSES; ADD_CLAUSES; INT_POW_ADD] THENL
       [REWRITE_TAC[CONJUNCT1 INT_POW; INT_MUL_RID;
                    INTEGER_RULE `(x:int == x) (mod n)`];
        MATCH_MP_TAC(INTEGER_RULE
         `(b:int == -- &1) (mod n) ==> (a * b == -- a) (mod n)`) THEN
        REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV]];
    ALL_TAC] THEN
  ABBREV_TAC `Z = if c = 0 then nttinv_zeta L M else --nttinv_zeta L M` THEN
  ABBREV_TAC `e1 = nttinv_exp L (2 * M + c)` THEN
  ABBREV_TAC `e2 = nttinv_exp (2 * L) M` THEN
  REWRITE_TAC[GSYM ISUM_LMUL; GSYM ISUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `s:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `r + L * 2 * s = r + 2 * L * s`;
              ARITH_RULE `r + L * (2 * s + 1) = L + r + 2 * L * s`] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(p1:int == q1) (mod n) /\ (p2 == Z * q1) (mod n)
    ==> (x * p1 + y * p2 == x * q1 + Z * (y * q1)) (mod n)`) THEN
  SUBGOAL_THEN `((&17:int) pow (e1 * 2 * s) == &17 pow (e2 * s)) (mod &3329)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NTTINV_POW17_CONG THEN
    ONCE_REWRITE_TAC[ARITH_RULE `e1 * 2 * s = (2 * e1) * s`] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `e1 * (2 * s + 1) = e1 + e1 * 2 * s`;
                  INT_POW_ADD] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(x:int == z) (mod n) /\ (y == w) (mod n)
    ==> (x * y == z * w) (mod n)`) THEN
  ASM_REWRITE_TAC[]);;

let NTTINV_STAGE_STEP = prove
 (`!L a b k.
     L IN {2,4,8,16,32,64,128} /\ k < 256 /\
     (!i. i < 256 ==> (b i == nttinv_stage (2 * L) a i) (mod &3329))
     ==> (nttinv_layer L b k == nttinv_stage L a k) (mod &3329)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_L_FACTS) THEN
  MP_TAC(SPECL [`k:num`; `2 * L`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[nttinv_layer] THEN
  ABBREV_TAC `M = k DIV (2 * L)` THEN ABBREV_TAC `q = k MOD (2 * L)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `M < 128 DIV L` ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[LT_MULT_LCANCEL]
     `2 * L * M < 2 * L * N ==> M < N`) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * L * M + 2 * L <= 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2 * L`; `M + 1`; `128 DIV L`] LE_MULT_LCANCEL) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k = 2 * L * M + q` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`L:num`; `a:num->int`; `M:num`; `0`; `q:num`]
      NTTINV_STAGE_STEP_CORE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 2`]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `(x + q) + L:num = x + L + q`] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(b1:int == A) (mod n) /\ (b2 == B) (mod n)
      ==> (S == A + Z * B) (mod n) ==> (b1 + Z * b2 == S) (mod n)`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`L:num`; `a:num->int`; `M:num`; `1`; `q - L`]
      NTTINV_STAGE_STEP_CORE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_EQ; MULT_CLAUSES] THEN
    SUBGOAL_THEN `2 * L * M + L + q - L = 2 * L * M + q /\
                  (2 * L * M + q) - L = 2 * L * M + q - L`
     (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(b1:int == A) (mod n) /\ (b2 == B) (mod n)
      ==> (S == A + --Z * B) (mod n) ==> (b1 - Z * b2 == S) (mod n)`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One inverse layer, and the stage it maps to.                              *)
(* ------------------------------------------------------------------------- *)

let nttinv_izeta = new_definition
 `nttinv_izeta L M = (&17:int) pow bitreverse7 (2 * (128 DIV L) - 1 - M)`;;

let nttinv_ilayer = new_definition
 `nttinv_ilayer L (b:num->int) k =
    if k MOD (2 * L) < L
    then b k + b (k + L)
    else nttinv_izeta L (k DIV (2 * L)) * (b k - b (k - L))`;;

let NTTINV_IZETA_FACT = prove
 (`!L M. L IN {2,4,8,16,32,64,128} /\ M < 128 DIV L
         ==> (nttinv_izeta L M * nttinv_zeta L M == --(&1)) (mod &3329)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nttinv_izeta; nttinv_zeta] THEN
  REWRITE_TAC[GSYM INT_POW_ADD] THEN
  ASM_SIMP_TAC[NTTINV_BR_FACT] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let NTTINV_COMB_LOW = INTEGER_RULE
 `!b1 b2 s1 s2 A B Z c n:int.
    (b1 == c * s1) (mod n) /\ (b2 == c * s2) (mod n) /\
    (s1 == A + Z * B) (mod n) /\ (s2 == A + --Z * B) (mod n)
    ==> (b1 + b2 == (&2 * c) * A) (mod n)`;;

let NTTINV_COMB_HIGH = INTEGER_RULE
 `!b1 b2 s1 s2 A B Z iz c n:int.
    (b1 == c * s1) (mod n) /\ (b2 == c * s2) (mod n) /\
    (s1 == A + Z * B) (mod n) /\ (s2 == A + --Z * B) (mod n) /\
    (iz * Z == --(&1)) (mod n)
    ==> (iz * (b2 - b1) == (&2 * c) * B) (mod n)`;;

let NTTINV_LAYER_STEP = prove
 (`!L a b c k.
     L IN {2,4,8,16,32,64,128} /\ k < 256 /\
     (!i. i < 256 ==> (b i == c * nttinv_stage L a i) (mod &3329))
     ==> (nttinv_ilayer L b k == (&2 * c) * nttinv_stage (2 * L) a k)
         (mod &3329)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_L_FACTS) THEN
  MP_TAC(SPECL [`k:num`; `2 * L`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[nttinv_ilayer] THEN
  ABBREV_TAC `M = k DIV (2 * L)` THEN ABBREV_TAC `q = k MOD (2 * L)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `M < 128 DIV L` ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[LT_MULT_LCANCEL]
     `2 * L * M < 2 * L * N ==> M < N`) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * L * M + 2 * L <= 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2 * L`; `M + 1`; `128 DIV L`] LE_MULT_LCANCEL) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k = 2 * L * M + q` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try rand(concl th) = `M * 2 * L + q` with Failure _ -> false)) THEN
  MP_TAC(SPEC `M:num` (SPEC `L:num` NTTINV_IZETA_FACT)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`L:num`; `a:num->int`; `M:num`; `0`; `q:num`]
      NTTINV_STAGE_STEP_CORE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 2`]; ALL_TAC] THEN
    MP_TAC(SPECL [`L:num`; `a:num->int`; `M:num`; `1`; `q:num`]
      NTTINV_STAGE_STEP_CORE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `1 < 2`]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ARITH_EQ] THEN
    SUBGOAL_THEN
     `(b (2 * L * M + L + q) ==
       c * nttinv_stage L a (2 * L * M + L + q)) (mod &3329) /\
      (b (2 * L * M + q) ==
       c * nttinv_stage L a (2 * L * M + q)) (mod &3329)`
    MP_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(2 * L * M + q) + L = 2 * L * M + L + q`] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`(b:num->int) (2 * L * M + q)`;
                         `(b:num->int) (2 * L * M + L + q)`;
                         `nttinv_stage L a (2 * L * M + q)`;
                         `nttinv_stage L a (2 * L * M + L + q)`;
                         `nttinv_stage (2 * L) a (2 * L * M + q)`;
                         `nttinv_stage (2 * L) a (2 * L * M + L + q)`;
                         `nttinv_zeta L M`; `c:int`; `&3329:int`]
                  NTTINV_COMB_LOW) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. q = L + r /\ r < L` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `q - L` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`L:num`; `a:num->int`; `M:num`; `0`; `r:num`]
    NTTINV_STAGE_STEP_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 2`]; ALL_TAC] THEN
  MP_TAC(SPECL [`L:num`; `a:num->int`; `M:num`; `1`; `r:num`]
    NTTINV_STAGE_STEP_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `1 < 2`]; ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ARITH_EQ] THEN
  SUBGOAL_THEN
   `(b (2 * L * M + L + r) ==
     c * nttinv_stage L a (2 * L * M + L + r)) (mod &3329) /\
    (b (2 * L * M + r) ==
     c * nttinv_stage L a (2 * L * M + r)) (mod &3329)`
  MP_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * L * M + (L + r)) - L = 2 * L * M + r /\
                2 * L * M + (L + r) = 2 * L * M + L + r`
   (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`(b:num->int) (2 * L * M + r)`;
                       `(b:num->int) (2 * L * M + L + r)`;
                       `nttinv_stage L a (2 * L * M + r)`;
                       `nttinv_stage L a (2 * L * M + L + r)`;
                       `nttinv_stage (2 * L) a (2 * L * M + r)`;
                       `nttinv_stage (2 * L) a (2 * L * M + L + r)`;
                       `nttinv_zeta L M`; `nttinv_izeta L M`; `c:int`;
                       `&3329:int`]
                NTTINV_COMB_HIGH) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Folding the generated loops: a state function for each iteration.         *)
(* ------------------------------------------------------------------------- *)

let NTTINV_NATIVE_BIND_ASSOC = prove
 (`!m (f:A->(B)native_result) (g:B->(C)native_result).
     native_bind (native_bind m f) g =
     native_bind m (\x. native_bind (f x) g)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `m:(A)native_result` (cases "native_result")) THEN
  REWRITE_TAC[native_bind_DEF; case_native_result_DEF]);;

let NTTINV_NATIVE_FOLDL_APPEND = prove
 (`!(body:I->S->(S)native_result) l1 l2 s.
     native_foldl body (APPEND l1 l2) s =
     native_bind (native_foldl body l1 s) (native_foldl body l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; native_foldl_DEF; NATIVE_BIND_VALUE;
                  NTTINV_NATIVE_BIND_ASSOC] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ASM_REWRITE_TAC[]);;

let NTTINV_FOLDL_SEQ = prove
 (`!(body:I->S->(S)native_result) h (st:num->S) n s t.
     st 0 = s /\ st n = t /\
     (!k. k < n ==> body (h k) (st k) = Value (st (SUC k)))
     ==> native_foldl body (list_of_seq h n) s = Value t`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_var o rhs o concl))) THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; native_foldl_DEF] THEN
  REWRITE_TAC[NTTINV_NATIVE_FOLDL_APPEND] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[NATIVE_BIND_VALUE; native_foldl_DEF; ARITH_RULE `n < SUC n`]);;

(* ------------------------------------------------------------------------- *)
(* The three loops of NTTInv_hol as named functions.                         *)
(* ------------------------------------------------------------------------- *)

let NTTINV_OUTER_TM, NTTINV_MID_TM, NTTINV_INNER_TM =
  let tm = rhs(snd(strip_forall(concl NTTInv_hol_DEF))) in
  let named s t = is_abs t && fst(dest_var(bndvar t)) = s in
  let outer = find_term (named "len") tm in
  let mid = find_term (named "start") outer in
  let inner = find_term (named "j") mid in
  outer, mid, inner;;

(* Replace every subterm alpha-equivalent to pat by rep, also under binders  *)
(* that bind free variables of pat (unlike subst).                           *)

let rec nttinv_replace pat rep tm =
  if aconv tm pat then rep else
  match tm with
    Comb(f,x) -> mk_comb(nttinv_replace pat rep f, nttinv_replace pat rep x)
  | Abs(v,b) -> mk_abs(v, nttinv_replace pat rep b)
  | _ -> tm;;

(* new_definition's benignity check cannot match bodies this large, so       *)
(* reloading this file into a session that already has it would fail with    *)
(* "constant ... has already been declared". Reuse the stored definition.    *)

let nttinv_define tm =
  let name = fst(dest_var(fst(strip_comb(lhs(snd(strip_forall tm)))))) in
  if can get_const_type name then
    find (fun th ->
            try fst(dest_const
                   (fst(strip_comb(lhs(snd(strip_forall(concl th))))))) = name
            with Failure _ -> false)
         (!the_definitions)
  else new_definition tm;;

let nttinv_inner_loop = nttinv_define
  (mk_eq(list_mk_comb(mk_var("nttinv_inner_loop",
           itlist (mk_fun_ty o type_of) [`len:int`; `vd:fips203_zq`]
                  (type_of NTTINV_INNER_TM)),
                      [`len:int`; `vd:fips203_zq`]),
         NTTINV_INNER_TM));;

let nttinv_mid_loop = nttinv_define
  (let lhs_inner = lhs(snd(strip_forall(concl nttinv_inner_loop))) in
   mk_eq(mk_comb(mk_var("nttinv_mid_loop", mk_fun_ty `:int` (type_of NTTINV_MID_TM)),
                 `len:int`),
         nttinv_replace NTTINV_INNER_TM lhs_inner NTTINV_MID_TM));;

let nttinv_outer_loop = nttinv_define
  (let lhs_mid = lhs(snd(strip_forall(concl nttinv_mid_loop))) in
   mk_eq(mk_var("nttinv_outer_loop", type_of NTTINV_OUTER_TM),
         nttinv_replace NTTINV_MID_TM lhs_mid NTTINV_OUTER_TM));;

let NTTINV_HOL_ALT = prove
 (let th = SPEC_ALL NTTInv_hol_DEF in
  let f = rand(lhs(concl th)) in
  mk_forall(f, mk_eq(lhs(concl th),
       nttinv_replace NTTINV_OUTER_TM (lhs(concl nttinv_outer_loop)) (rhs(concl th)))),
  REWRITE_TAC[NTTInv_hol_DEF; nttinv_outer_loop; nttinv_mid_loop; nttinv_inner_loop]);;
let NTTINV_UPDATE_ZQLIST = prove
 (`!b n x.
     n < 256
     ==> isa_list_update (zqlist b) n (FIPS203_Zq (residue_of_int_mod x)) =
         zqlist (\k. if k = n then x else b k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_ISA_LIST_UPDATE; LENGTH_ZQLIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_ZQLIST; EL_ZQLIST] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* One butterfly: the innermost loop body.                                   *)
(* ------------------------------------------------------------------------- *)

let NTTINV_REP = prove
 (`!v. &(residue_rep (residue_of_int_mod v:(3329)residue)) = v rem &3329`,
  GEN_TAC THEN
  MP_TAC(SPEC `v:int` FZ_RESIDUE_OF_INT_MOD) THEN
  REWRITE_TAC[fz; fips203_zq_residue_DEF]);;

let nttinv_bfly = new_definition
 `nttinv_bfly L Z start n (b:num->int) k =
    if start <= k /\ k < start + n then b k + b (k + L)
    else if start + L <= k /\ k < start + L + n then Z * (b k - b (k - L))
    else b k`;;

let NTTINV_BFLY_STEP = prove
 (`!L Z start n b.
     0 < L /\ n < L
     ==> (\k. if k = start + n
              then nttinv_bfly L Z start n b (start + n) +
                   nttinv_bfly L Z start n b ((start + n) + L)
              else if k = (start + n) + L
              then Z * (nttinv_bfly L Z start n b ((start + n) + L) -
                        nttinv_bfly L Z start n b (start + n))
              else nttinv_bfly L Z start n b k) =
         nttinv_bfly L Z start (SUC n) b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[nttinv_bfly] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY ASM_ARITH_TAC THEN
  REWRITE_TAC[GSYM ADD_ASSOC; ARITH_RULE `((s + n) + L) - L = s + n`]);;

let NTTINV_INNER_BODY = prove
 (`!L z b j.
     0 < L /\ j + L < 256
     ==> nttinv_inner_loop (&L) z (&j) (zqlist b) =
         Value (zqlist (\k. if k = j then b j + b (j + L)
                            else if k = j + L then fz z * (b (j + L) - b j)
                            else b k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nttinv_inner_loop] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[NTTINV_REP; GSYM fz] THEN REWRITE_TAC[INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `j < 256 /\ ~(j = j + L) /\ ~(j + L = j)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_LIST_UPDATE; LENGTH_ZQLIST;
               NATIVE_BIND_VALUE; EL_ZQLIST; FZ_RESIDUE_OF_INT_MOD;
               NTTINV_UPDATE_ZQLIST] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC ZQLIST_EQ THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC `k:num = j` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = j + L` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let NTTINV_INNER_LOOP = prove
 (`!L z start n b.
     0 < L /\ start + 2 * L <= 256 /\ n <= L
     ==> native_foldl (nttinv_inner_loop (&L) z)
                      (list_of_seq (\m. &(start + m)) n) (zqlist b) =
         Value (zqlist (nttinv_bfly L (fz z) start n b))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NTTINV_FOLDL_SEQ THEN
  EXISTS_TAC `\m. zqlist (nttinv_bfly L (fz z) start m b)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; nttinv_bfly] THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`L:num`; `z:fips203_zq`; `nttinv_bfly L (fz z) start m b`;
                `start + m`] NTTINV_INNER_BODY) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`L:num`; `fz z`; `start:num`; `m:num`; `b:num->int`]
    NTTINV_BFLY_STEP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let NTTINV_CONG_SCALE = INTEGER_RULE
 `!Z Z' x n:int. (Z == Z') (mod n) ==> (Z * x == Z' * x) (mod n)`;;

let NTTINV_ZQLIST_BFLY_CONG = prove
 (`!L Z Z' start n b.
     (Z == Z') (mod &3329)
     ==> zqlist (nttinv_bfly L Z start n b) =
         zqlist (nttinv_bfly L Z' start n b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ZQLIST_EQ THEN
  REWRITE_TAC[GSYM INT_REM_EQ; nttinv_bfly] THEN X_GEN_TAC `k:num` THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `start <= k /\ k < start + n` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `start + L <= k /\ k < start + L + n` THEN
  ASM_REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`] THEN
  REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC NTTINV_CONG_SCALE THEN
  ASM_REWRITE_TAC[]);;

let NTTINV_MID_BODY = prove
 (`!L i start b.
     0 < L /\ 0 < i /\ i < 128 /\ start + 2 * L <= 256
     ==> nttinv_mid_loop (&L) (&start) (&i, zqlist b) =
         Value (&(i - 1),
                zqlist (nttinv_bfly L (&17 pow bitreverse7 i) start L b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nttinv_mid_loop; UNCURRY_DEF] THEN
  ASM_SIMP_TAC[BITREV7_HOL; NATIVE_BIND_VALUE; TYPED_HOL_POW_MOD; ARITH] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_ADD; ISA_NAT_NUM] THEN
  MP_TAC(SPECL [`SUC L`; `start:num`; `start + L`] NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(start + L) - start = L`] THEN
  ASM_SIMP_TAC[NTTINV_INNER_LOOP; LE_REFL; NATIVE_BIND_VALUE] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; ARITH_RULE `0 < i ==> 1 <= i`];
    ALL_TAC] THEN
  MATCH_MP_TAC NTTINV_ZQLIST_BFLY_CONG THEN
  REWRITE_TAC[FZ_RESIDUE_OF_INT_MOD] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`]);;

(* ------------------------------------------------------------------------- *)
(* One block of butterflies: the middle loop, and its partial layers.        *)
(* ------------------------------------------------------------------------- *)

let nttinv_part = new_definition
 `nttinv_part L (b:num->int) M k =
    if k < 2 * L * M then nttinv_ilayer L b k else b k`;;

let NTTINV_BFLY_PART = prove
 (`!L b M. 0 < L
           ==> nttinv_bfly L (nttinv_izeta L M) (2 * L * M) L
                             (nttinv_part L b M) =
               nttinv_part L b (SUC M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[nttinv_bfly; nttinv_part] THEN
  ASM_CASES_TAC `k < 2 * L * M` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(2 * L * M <= k) /\ ~(2 * L * M + L <= k) /\
                  k < 2 * L * SUC M`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k + L < 2 * L * M)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k < 2 * L * SUC M` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `k DIV (2 * L) = M /\ k MOD (2 * L) = k - 2 * L * M`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC DIV_UNIQ; MATCH_MP_TAC MOD_UNIQ] THENL
       [EXISTS_TAC `k - 2 * L * M`; EXISTS_TAC `M:num`] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[nttinv_ilayer] THEN
    ASM_CASES_TAC `2 * L * M <= k /\ k < 2 * L * M + L` THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `k - 2 * L * M < L` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `2 * L * M + L <= k /\ k < 2 * L * M + L + L /\
                  ~(k - 2 * L * M < L) /\ ~(k - L < 2 * L * M)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `~(2 * L * M <= k /\ k < 2 * L * M + L) /\
                  ~(2 * L * M + L <= k /\ k < 2 * L * M + L + L)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let NTTINV_N_FACTS = prove
 (`!L. L IN {2,4,8,16,32,64,128}
       ==> 128 DIV L <= 64 /\ 2 * L * (128 DIV L) = 256`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let NTTINV_MID_LOOP = prove
 (`!L b N.
     L IN {2,4,8,16,32,64,128} /\ N <= 128 DIV L
     ==> native_foldl (nttinv_mid_loop (&L)) (list_of_seq (\M. &(2 * L * M)) N)
                      (&(2 * (128 DIV L) - 1), zqlist b) =
         Value (&(2 * (128 DIV L) - 1 - N), zqlist (nttinv_part L b N))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_L_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_N_FACTS) THEN
  MATCH_MP_TAC NTTINV_FOLDL_SEQ THEN
  EXISTS_TAC `\M. (&(2 * (128 DIV L) - 1 - M):int,
                   zqlist (nttinv_part L b M))` THEN
  REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUB_0] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; nttinv_part] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `~(k < 0)`];
    ALL_TAC] THEN
  X_GEN_TAC `M:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `M < 128 DIV L` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 * L * M + 2 * L <= 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2 * L`; `M + 1`; `128 DIV L`] LE_MULT_LCANCEL) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`L:num`; `2 * (128 DIV L) - 1 - M`; `2 * L * M`;
                `nttinv_part L b M`] NTTINV_MID_BODY) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GSYM nttinv_izeta; NTTINV_BFLY_PART] THEN
  REWRITE_TAC[ARITH_RULE `x - M - 1 = x - SUC M`]);;

(* ------------------------------------------------------------------------- *)
(* One layer: the outer loop body.                                           *)
(* ------------------------------------------------------------------------- *)

let NTTINV_DIV_FACTS = prove
 (`!L. L IN {2,4,8,16,32,64,128}
       ==> (256 + 2 * L - 1) DIV (2 * L) = 128 DIV L /\ 0 < 2 * L`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let NTTINV_OUTER_BODY = prove
 (`!L b. L IN {2,4,8,16,32,64,128}
         ==> nttinv_outer_loop (&L) (&(2 * (128 DIV L) - 1), zqlist b) =
             Value (&(128 DIV L - 1), zqlist (nttinv_ilayer L b))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_L_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_N_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTTINV_DIV_FACTS) THEN
  REWRITE_TAC[nttinv_outer_loop; INT_OF_NUM_MUL] THEN
  MP_TAC(SPECL [`257`; `256`; `2 * L`] NATIVE_SCHEDULE_STEP) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 < 257`] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MULT_ASSOC] THEN
  ASM_SIMP_TAC[NTTINV_MID_LOOP; LE_REFL] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ZQLIST_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[nttinv_part]);;

let NTTINV_OUTER_STEP = prove
 (`!L a c. L IN {2,4,8,16,32,64,128}
         ==> nttinv_outer_loop (&L) (&(2 * (128 DIV L) - 1),
                                    zqlist (\k. c * nttinv_stage L a k)) =
             Value (&(128 DIV L - 1),
                    zqlist (\k. (&2 * c) * nttinv_stage (2 * L) a k))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NTTINV_OUTER_BODY] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  MATCH_MP_TAC ZQLIST_EQ THEN REWRITE_TAC[INT_REM_EQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC NTTINV_LAYER_STEP THEN
  ASM_REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`]);;

(* ------------------------------------------------------------------------- *)
(* The final scaling by 3303 = 1/128 (mod 3329).                             *)
(* ------------------------------------------------------------------------- *)

let NTTINV_EL_REPLICATE = prove
 (`!n i (x:A). i < n ==> EL i (REPLICATE n x) = x`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; EL; HD; TL; LT_SUC] THEN
  ASM_MESON_TAC[LT_SUC]);;

let NTTINV_ZERO_LIST = prove
 (`!b. MAP FIPS203_Zq (REPLICATE 256 (residue_of_int_mod (&0):(3329)residue)) =
       zqlist (\k. if k < 0 then &3303 * b k else &0)`,
  GEN_TAC THEN
  REWRITE_TAC[zqlist; LIST_EQ; LENGTH_MAP; LENGTH_REPLICATE;
              LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_MAP; NTTINV_EL_REPLICATE; EL_LIST_OF_SEQ; LT; LENGTH_REPLICATE]);;

let NTTINV_SCALE = prove
 (`!b. ScaleCoefficients_hol (zqlist b) (&3303) =
       Value (zqlist (\k. &3303 * b k))`,
  GEN_TAC THEN REWRITE_TAC[ScaleCoefficients_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[ISA_INT_MOD_POS; ARITH_RULE `&0 < &3329:int`] THEN
  REWRITE_TAC[NTTINV_ZERO_LIST] THEN
  MP_TAC(SPECL [`257`; `0`; `256`] NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH_RULE `256 - 0 = 256`] THEN
  MATCH_MP_TAC NTTINV_FOLDL_SEQ THEN
  EXISTS_TAC `\m. zqlist (\k. if k < m then &3303 * b k else &0)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ZQLIST_EQ THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; GSYM fz] THEN
  ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_LIST_UPDATE; LENGTH_ZQLIST;
               NATIVE_BIND_VALUE; EL_ZQLIST; FZ_RESIDUE_OF_INT_MOD;
               NTTINV_UPDATE_ZQLIST] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC ZQLIST_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j:num = k` THEN ASM_REWRITE_TAC[LT; LT_REFL] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  ASM_CASES_TAC `j < k` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The ends of the chain: stage 256 and stage 2.                             *)
(* ------------------------------------------------------------------------- *)

let NTTINV_STAGE_TOP = prove
 (`!a k. k < 256 ==> nttinv_stage 256 a k = a k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nttinv_stage] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ISUM_SING_NUMSEG; MULT_CLAUSES; ADD_CLAUSES;
              CONJUNCT1 INT_POW; INT_MUL_RID] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let NTTINV_EXP_2 = prove
 (`!m. nttinv_exp 2 m = 2 * bitreverse7 m + 1`,
  REWRITE_TAC[nttinv_exp] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES]);;

let NTTINV_STAGE_2_MLKEM = prove
 (`!f k. f IN ring_carrier mlkem_rq /\ k < 256
         ==> (nttinv_stage 2 (\n. coeff n f) k == mlkem_ntt f k) (mod &3329)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MLKEM_NTT_FORWARD; INT_CONG_RREM] THEN
  REWRITE_TAC[nttinv_stage; NTTINV_EXP_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `k MOD 2 + 2 * t = 2 * t + k MOD 2`] THEN
  REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`]);;

(* ------------------------------------------------------------------------- *)
(* NTTInv_hol computes mlkem_ntt_inv (FIPS 203 Algorithm 10).                *)
(* ------------------------------------------------------------------------- *)

let NTTINV_OUTER_STEPS =
  end_itlist CONJ
   (map (fun (l,c) ->
      let th = SPECL [mk_small_numeral l; `a:num->int`;
                      mk_comb(`int_of_num`, mk_small_numeral c)]
                     NTTINV_OUTER_STEP in
      let th = MP th (EQT_ELIM(REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ]
                                (lhand(concl th)))) in
      CONV_RULE (ONCE_DEPTH_CONV INT_REDUCE_CONV)
        (CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) th))
    [2,1; 4,2; 8,4; 16,8; 32,16; 64,32; 128,64]);;

let NTTINV_HOL_EQ = prove
 (NTTINV_HOL_EQ_STMT,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. i < 256 ==> &0 <= zarr l i /\ zarr l i < &3329`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[zarr; FZ_POS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[zq_list_ok]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `zarr l` MLKEM_NTT_INV) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN STRIP_TAC THEN
  ABBREV_TAC `f = mlkem_ntt_inv (zarr l)` THEN
  ABBREV_TAC `a = \n. coeff n (f:(1->num)->int)` THEN
  SUBGOAL_THEN
   `NTTInv_hol (FIPS203_Poly l) =
    Value (FIPS203_Poly (zqlist (\k. &3303 * (&128 * nttinv_stage 256 a k))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[NTTINV_HOL_ALT; fips203_poly_SEL_CTR] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `l:(fips203_zq)list = zqlist (\k. &1 * nttinv_stage 2 a k)`
    SUBST1_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP ZQLIST_ZARR) THEN
      MATCH_MP_TAC ZQLIST_EQ THEN REWRITE_TAC[INT_REM_EQ] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `zarr l k = mlkem_ntt f k` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `(y:int == x) (mod n) ==> (x == &1 * y) (mod n)`) THEN
      EXPAND_TAC "a" THEN ASM_SIMP_TAC[NTTINV_STAGE_2_MLKEM];
      ALL_TAC] THEN
    REWRITE_TAC[NATIVE_SCHEDULE_NTTINV; native_foldl_DEF;
                NTTINV_OUTER_STEPS; NATIVE_BIND_VALUE] THEN
    REWRITE_TAC[UNCURRY_DEF; NTTINV_SCALE; NATIVE_BIND_VALUE];
    ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ZQLIST_EQ THEN REWRITE_TAC[INT_REM_EQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[NTTINV_STAGE_TOP] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `((a:int) * b == &1) (mod n) ==> (a * (b * x) == x) (mod n)`) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The vector wrappers: NTTInv_hol applied to every entry.                   *)
(* ------------------------------------------------------------------------- *)

let NTTINV_ISA_UPDATE_SEQ = prove
 (`!(f:num->A) n m x.
     m < n
     ==> isa_list_update (list_of_seq f n) m x =
         list_of_seq (\i. if i = m then x else f i) n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let NTTINV_VEC_FOLD = prove
 (`!k (v:num->fips203_zq list) (out:((fips203_time)fips203_poly)list) n.
     (!i. i < k ==> zq_list_ok (v i)) /\ LENGTH out = k /\ n <= k
     ==> native_foldl
          (\i output.
             native_bind (typed_hol_nonnegative i)
              (\vd. native_bind
                     (typed_hol_read
                       (native_list_index
                         (common_vec_entries
                           (zvec k v:(A,(fips203_ntt)fips203_poly)common_vec))
                         i))
                     (\ve. native_bind (NTTInv_hol ve)
                            (\vf. typed_hol_read
                                   (typed_hol_nominal_update Common_Vec
                                     common_vec_entries
                                     (\nf. native_list_update nf vd vf)
                                     output)))))
          (list_of_seq (\i. &(0 + i)) n)
          (Common_Vec out:(B,(fips203_time)fips203_poly)common_vec) =
         Value (Common_Vec
                 (list_of_seq
                   (\i. if i < n
                        then FIPS203_Poly (zqlist (\n. coeff n (mlkem_ntt_inv (zarr (v i)))))
                        else EL i out) k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NTTINV_FOLDL_SEQ THEN
  EXISTS_TAC
   `\m. Common_Vec
         (list_of_seq
           (\i. if i < m
                then FIPS203_Poly (zqlist (\n. coeff n (mlkem_ntt_inv (zarr (v i)))))
                else EL i out) k):(B,(fips203_time)fips203_poly)common_vec` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `~(i < 0)`];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `m:num < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE] THEN
  REWRITE_TAC[zvec; common_vec_SEL_CTR] THEN
  ASM_SIMP_TAC[NATIVE_LIST_INDEX; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
               NATIVE_BIND_VALUE; NTTINV_HOL_EQ] THEN
  ASM_SIMP_TAC[NOMINAL_UPDATE_VEC; LENGTH_LIST_OF_SEQ] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[NTTINV_ISA_UPDATE_SEQ; LENGTH_LIST_OF_SEQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[LT_REFL; LT] THEN
  ASM_MESON_TAC[]);;

(* The zero vector that the generated code starts from, for k entries.       *)

let NTTINV_INIT_VEC k =
  let f = `\n. MAP (\element. FIPS203_Poly (MAP FIPS203_Zq element))
                   (REPLICATE n
                     (REPLICATE 256 (residue_of_int_mod (&0):(3329)residue)))
               :((fips203_time)fips203_poly)list` in
  rhs(concl(BETA_CONV(mk_comb(f,mk_small_numeral k))));;

let NTTINV_TQVECTOR_TAC def k =
  let cnst = lhs(snd(strip_forall(concl def))) in
  let kty = hd(snd(dest_type(type_of(rand cnst)))) in
  let kn = mk_small_numeral k in
  REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [mk_small_numeral(k + 1); `0`; kn] NATIVE_SCHEDULE_UPTO) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(INST_TYPE [kty,mk_vartype "A"; kty,mk_vartype "B"]
   (SPECL [kn; `v:num->fips203_zq list`; NTTINV_INIT_VEC k; kn]
          NTTINV_VEC_FOLD)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE; LE_REFL]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[zvec] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ];;

let TQVECTORNTTINV_2 = prove
 (TQVECTORNTTINV_2_STMT,
  NTTINV_TQVECTOR_TAC TqVectorNTTInv_2_MLKEM512_Configuration_hol_DEF 2);;

let TQVECTORNTTINV_3 = prove
 (TQVECTORNTTINV_3_STMT,
  NTTINV_TQVECTOR_TAC TqVectorNTTInv_3_MLKEM768_Configuration_hol_DEF 3);;

let TQVECTORNTTINV_4 = prove
 (TQVECTORNTTINV_4_STMT,
  NTTINV_TQVECTOR_TAC TqVectorNTTInv_4_MLKEM1024_Configuration_hol_DEF 4);;
