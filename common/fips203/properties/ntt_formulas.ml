(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The NTT and its inverse as single sums of integers mod q.                  *)
(* ========================================================================= *)

needs "common/fips203/properties/ntt_multiplication.ml";;
needs "Library/isum.ml";;

type_invention_error := true;;

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
 (`!n. n < 128 ==> bitreverse7 n < 128`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[BITREVERSE7_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BITREVERSE7_BITREVERSE7 = prove
 (`!n. n < 128 ==> bitreverse7(bitreverse7 n) = n`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[BITREVERSE7_CLAUSES]);;

(* The bound for the twiddle-factor indices 128 / L + M of the layer of     *)
(* length L of the NTT and of its inverse.                                  *)

let BITREVERSE7_BOUND_LAYER = prove
 (`!L M. L IN {2,4,8,16,32,64,128} /\ M < 128 DIV L
         ==> bitreverse7 (128 DIV L + M) < 128`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
              NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BITREVERSE7_BOUND THEN ASM_ARITH_TAC);;

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
   [EXPAND_TAC "r" THEN MATCH_MP_TAC BITREVERSE7_BOUND THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
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
(* Bit reversals of the twiddle-factor indices of the inverse NTT.           *)
(* ------------------------------------------------------------------------- *)

let NTTINV_BR_FACT = prove
 (`!L M. L IN {2,4,8,16,32,64,128} /\ M < 128 DIV L
         ==> bitreverse7 (2 * (128 DIV L) - 1 - M) +
             bitreverse7 (128 DIV L + M) = 128`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
              NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITREVERSE7_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
