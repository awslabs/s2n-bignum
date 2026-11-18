(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "Library/prime.ml";;
needs "common/fips202/fips202.ml";;

(* ========================================================================= *)
(* KECCAK_THETA_INJ: the Keccak theta step is injective on 5x5 lanes.        *)
(*                                                                           *)
(* Proof idea (no SAT, no bit-blasting).  Write C_x for the column          *)
(* parities of a difference d = a XOR b with theta d = 0.  Every lane of     *)
(* column x then equals D_x = C_{x-1} XOR rol(C_{x+1},1); XORing the five    *)
(* lanes (5 is odd) gives C_x = D_x, i.e. M C = 0 for                        *)
(*    (M_{s,r} c)_x = c_x XOR c_{x-s} XOR rol(c_{x+s}, r),  (s,r) = (1,1).   *)
(* In characteristic 2, M_{s,r} o M_{s,r} = M_{2s mod 5, 2r}.  Six squarings  *)
(* reach (s,r) = (4,64), where rol by 64 is the identity, so c_x XOR c_{x+1} *)
(* XOR c_{x+4} = 0 for all x; this circulant system is invertible over       *)
(* GF(2) and gives C = 0, hence D = 0 and d = 0.                             *)
(* Helper names are prefixed KECCAKTB_ (definitions: kthb_). This is the    *)
(* part of the Keccak-f permutation proof that needs real algebra; the      *)
(* other four steps are in keccak_permutation.ml.                           *)
(* ========================================================================= *)

let KECCAKTB_ROL_XOR = prove(`!(x:int64) y n. word_rol (word_xor x y) n = word_xor (word_rol x n) (word_rol y n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ROL; BIT_WORD_XOR; DIMINDEX_64] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `n MOD 64 < 64` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `i + 64 - n MOD 64 < 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[BIT_WORD_XOR; DIMINDEX_64];
    SUBGOAL_THEN `i - n MOD 64 < 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[BIT_WORD_XOR; DIMINDEX_64]]);;

let KECCAKTB_ROL_0 = prove(`!n. word_rol (word 0:int64) n = word 0`,
  GEN_TAC THEN
  MP_TAC(SPECL [`word 0:int64`; `word 0:int64`; `n:num`] KECCAKTB_ROL_XOR) THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_REFL] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN REWRITE_TAC[WORD_XOR_REFL]);;

let kthb_m = new_definition
 `kthb_m (s:num) (r:num) (c:num->int64) (x:num) =
    word_xor (c x) (word_xor (c ((x + 5 - s) MOD 5))
                             (word_rol (c ((x + s) MOD 5)) r))`;;

let kthb_col = new_definition
 `kthb_col (a:num->num->int64) (x:num) =
    word_xor (a x 0) (word_xor (a x 1) (word_xor (a x 2)
             (word_xor (a x 3) (a x 4))))`;;

let KECCAKTB_THETA_UNF = prove(`!(a:num->num->int64) x y.
   keccak_theta a x y =
   word_xor (a x y) (word_xor (kthb_col a ((x + 4) MOD 5))
                              (word_rol (kthb_col a ((x + 1) MOD 5)) 1))`,
  REWRITE_TAC[keccak_theta; kthb_col; LET_DEF; LET_END_DEF]);;

let KECCAKTB_SQ_TAC =
  GEN_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[kthb_m] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[KECCAKTB_ROL_XOR; WORD_ROL_COMPOSE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE;;

let KECCAKTB_SQ1 = prove(`!c:num->int64 x. x < 5 ==>
   kthb_m 2 2 c x = kthb_m 1 1 (kthb_m 1 1 c) x`, KECCAKTB_SQ_TAC);;

let KECCAKTB_SQ2 = prove(`!c:num->int64 x. x < 5 ==>
   kthb_m 4 4 c x = kthb_m 2 2 (kthb_m 2 2 c) x`, KECCAKTB_SQ_TAC);;
let KECCAKTB_SQ3 = prove(`!c:num->int64 x. x < 5 ==>
   kthb_m 3 8 c x = kthb_m 4 4 (kthb_m 4 4 c) x`, KECCAKTB_SQ_TAC);;
let KECCAKTB_SQ4 = prove(`!c:num->int64 x. x < 5 ==>
   kthb_m 1 16 c x = kthb_m 3 8 (kthb_m 3 8 c) x`, KECCAKTB_SQ_TAC);;
let KECCAKTB_SQ5 = prove(`!c:num->int64 x. x < 5 ==>
   kthb_m 2 32 c x = kthb_m 1 16 (kthb_m 1 16 c) x`, KECCAKTB_SQ_TAC);;
let KECCAKTB_SQ6 = prove(`!c:num->int64 x. x < 5 ==>
   kthb_m 4 64 c x = kthb_m 2 32 (kthb_m 2 32 c) x`, KECCAKTB_SQ_TAC);;

let KECCAKTB_ZERO_STEP = prove(`!s r (c:num->int64).
   (!x. x < 5 ==> kthb_m s r c x = word 0)
   ==> (!x. x < 5 ==> kthb_m s r (kthb_m s r c) x = word 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [kthb_m] THEN
  SUBGOAL_THEN `!n. n MOD 5 < 5` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[KECCAKTB_ROL_0; WORD_XOR_0]);;

let KECCAKTB_CHAIN_STEP = prove(`!s r s' r' (c:num->int64).
   (!c x. x < 5 ==> kthb_m s' r' c x = kthb_m s r (kthb_m s r c) x)
   ==> (!x. x < 5 ==> kthb_m s r c x = word 0)
   ==> (!x. x < 5 ==> kthb_m s' r' c x = word 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`s:num`; `r:num`; `c:num->int64`] KECCAKTB_ZERO_STEP) THEN
  ASM_SIMP_TAC[]);;

let KECCAKTB_M6 = prove(`!c:num->int64.
   (!x. x < 5 ==> kthb_m 1 1 c x = word 0)
   ==> (!x. x < 5 ==> kthb_m 4 64 c x = word 0)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP KECCAKTB_CHAIN_STEP KECCAKTB_SQ1)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP KECCAKTB_CHAIN_STEP KECCAKTB_SQ2)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP KECCAKTB_CHAIN_STEP KECCAKTB_SQ3)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP KECCAKTB_CHAIN_STEP KECCAKTB_SQ4)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP KECCAKTB_CHAIN_STEP KECCAKTB_SQ5)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP KECCAKTB_CHAIN_STEP KECCAKTB_SQ6)) THEN
  REWRITE_TAC[]);;

let KECCAKTB_ROL_64 = prove(`!w:int64. word_rol w 64 = w`,
  GEN_TAC THEN MATCH_MP_TAC WORD_ROL_EQ_SELF THEN
  REWRITE_TAC[DIMINDEX_64] THEN REWRITE_TAC[DIVIDES_REFL]);;

let KECCAKTB_N_ALGEBRA = prove(`!c0 c1 c2 c3 c4:int64.
   word_xor c0 (word_xor c1 c4) = word 0 /\
   word_xor c1 (word_xor c2 c0) = word 0 /\
   word_xor c2 (word_xor c3 c1) = word 0 /\
   word_xor c3 (word_xor c4 c2) = word 0 /\
   word_xor c4 (word_xor c0 c3) = word 0
   ==> c0 = word 0 /\ c1 = word 0 /\ c2 = word 0 /\ c3 = word 0 /\ c4 = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `c0:int64 = word_xor (word_xor c0 (word_xor c1 c4))
      (word_xor (word_xor c2 (word_xor c3 c1)) (word_xor c3 (word_xor c4 c2)))`
      MP_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC];
    SUBGOAL_THEN `c1:int64 = word_xor (word_xor c1 (word_xor c2 c0))
      (word_xor (word_xor c3 (word_xor c4 c2)) (word_xor c4 (word_xor c0 c3)))`
      MP_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC];
    SUBGOAL_THEN `c2:int64 = word_xor (word_xor c0 (word_xor c1 c4))
      (word_xor (word_xor c2 (word_xor c3 c1)) (word_xor c4 (word_xor c0 c3)))`
      MP_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC];
    SUBGOAL_THEN `c3:int64 = word_xor (word_xor c0 (word_xor c1 c4))
      (word_xor (word_xor c1 (word_xor c2 c0)) (word_xor c3 (word_xor c4 c2)))`
      MP_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC];
    SUBGOAL_THEN `c4:int64 = word_xor (word_xor c1 (word_xor c2 c0))
      (word_xor (word_xor c2 (word_xor c3 c1)) (word_xor c4 (word_xor c0 c3)))`
      MP_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC]] THEN
  ASM_REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let KECCAKTB_N = prove(`!c:num->int64.
   (!x. x < 5 ==> kthb_m 4 64 c x = word 0)
   ==> (!x. x < 5 ==> c x = word 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `c 0 = word 0 /\ c 1 = word 0 /\ c 2 = word 0 /\
                (c:num->int64) 3 = word 0 /\ c 4 = word 0` ASSUME_TAC THENL
   [MATCH_MP_TAC(SPECL [`(c:num->int64) 0`; `(c:num->int64) 1`; `(c:num->int64) 2`;
                        `(c:num->int64) 3`; `(c:num->int64) 4`] KECCAKTB_N_ALGEBRA) THEN
    REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
      MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th)) THEN
    REWRITE_TAC[kthb_m] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[KECCAKTB_ROL_64] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[]]);;

let KECCAKTB_LANE = prove(`!d:num->num->int64 x y.
   keccak_theta d x y = word 0 /\
   kthb_col d ((x + 4) MOD 5) = word 0 /\
   kthb_col d ((x + 1) MOD 5) = word 0
   ==> d x y = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[KECCAKTB_THETA_UNF] (ASSUME `keccak_theta (d:num->num->int64) x y = word 0`)) THEN
  ASM_REWRITE_TAC[KECCAKTB_ROL_0; WORD_XOR_0]);;

let KECCAKTB_ZERO = prove(`!d:num->num->int64.
   (!x y. x < 5 /\ y < 5 ==> keccak_theta d x y = word 0)
   ==> (!x y. x < 5 /\ y < 5 ==> d x y = word 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. x < 5 ==> kthb_col (d:num->num->int64) x = word 0` ASSUME_TAC THENL
   [(* Step 1: every lane equals the theta correction of its column. *)
    SUBGOAL_THEN `!x y. x < 5 /\ y < 5 ==>
        (d:num->num->int64) x y =
        word_xor (kthb_col d ((x + 4) MOD 5)) (word_rol (kthb_col d ((x + 1) MOD 5)) 1)`
      ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`]) THEN
      ASM_REWRITE_TAC[KECCAKTB_THETA_UNF; WORD_XOR_EQ_0];
      ALL_TAC] THEN
    (* Step 2: so the column parity equals that correction (5 is odd). *)
    SUBGOAL_THEN `!x. x < 5 ==>
        kthb_col (d:num->num->int64) x =
        word_xor (kthb_col d ((x + 4) MOD 5)) (word_rol (kthb_col d ((x + 1) MOD 5)) 1)`
      ASSUME_TAC THENL
     [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [kthb_col] THEN
      ASM_SIMP_TAC[ARITH] THEN CONV_TAC WORD_BITWISE_RULE;
      ALL_TAC] THEN
    (* Step 3: the squaring chain M_0 .. M_6 forces all parities to be zero. *)
    MATCH_MP_TAC KECCAKTB_N THEN MATCH_MP_TAC KECCAKTB_M6 THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    REWRITE_TAC[kthb_m; ARITH_RULE `x + 5 - 1 = x + 4`] THEN
    ASM_SIMP_TAC[WORD_XOR_EQ_0];
    ALL_TAC] THEN
  (* Step 4: with zero parities, theta d = 0 says every lane is zero. *)
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KECCAKTB_LANE THEN
  SUBGOAL_THEN `!n. n MOD 5 < 5` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let KECCAKTB_COL_LIN = prove(`!(a:num->num->int64) b x.
   kthb_col (\x y. word_xor (a x y) (b x y)) x =
   word_xor (kthb_col a x) (kthb_col b x)`,
  REWRITE_TAC[kthb_col] THEN CONV_TAC WORD_BITWISE_RULE);;

let KECCAKTB_THETA_LIN = prove(`!(a:num->num->int64) b x y.
   keccak_theta (\x y. word_xor (a x y) (b x y)) x y =
   word_xor (keccak_theta a x y) (keccak_theta b x y)`,
  REWRITE_TAC[KECCAKTB_THETA_UNF; KECCAKTB_COL_LIN; KECCAKTB_ROL_XOR] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let KECCAK_THETA_INJ = prove(
 `!(a:num->num->int64) (b:num->num->int64).
    (!x y. x < 5 /\ y < 5 ==> keccak_theta a x y = keccak_theta b x y)
    ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `\x y. word_xor ((a:num->num->int64) x y) (b x y)` KECCAKTB_ZERO) THEN
  REWRITE_TAC[KECCAKTB_THETA_LIN] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_XOR_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_EQ_0] THEN SIMP_TAC[]);;

