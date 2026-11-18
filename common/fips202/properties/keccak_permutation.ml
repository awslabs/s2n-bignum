(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "common/fips202/properties/keccak_lanes.ml";;
needs "common/fips202/properties/keccak_theta_injective.ml";;

(* ========================================================================= *)
(* Keccak-f[1600] is injective, hence a permutation of the 1600-bit state.   *)
(*                                                                           *)
(* Each step mapping is injective on the lanes (x,y) with x,y < 5, which is  *)
(* all that the step mappings depend on; for theta this is                   *)
(* keccak_theta_injective.ml. The steps are then composed over the 24        *)
(* rounds.                                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* iota: XOR with a constant on lane (0,0).                                  *)
(* ------------------------------------------------------------------------- *)

let KECCAK_XOR_CANCEL = prove
 (`!(a:int64) b c. word_xor a c = word_xor b c ==> a = b`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR_ALT] THEN MESON_TAC[]);;

let KECCAK_IOTA_INJ = prove
 (`!i a b. (!x y. x < 5 /\ y < 5
                  ==> keccak_iota i a x y = keccak_iota i b x y)
           ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[keccak_iota] THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x = 0 /\ y = 0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP KECCAK_XOR_CANCEL) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* rho: a per-lane rotation, undone by the complementary rotation.           *)
(* ------------------------------------------------------------------------- *)

let KECCAK_ROL_INJ = prove
 (`!(a:int64) b k. word_rol a k = word_rol b k ==> a = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!w:int64. word_rol (word_rol w k) (64 - k MOD 64) = w`
   (fun th -> ONCE_REWRITE_TAC[GSYM(SPEC `a:int64` th);
                               GSYM(SPEC `b:int64` th)]) THENL
   [GEN_TAC THEN REWRITE_TAC[WORD_ROL_COMPOSE] THEN
    MATCH_MP_TAC WORD_ROL_EQ_SELF THEN
    REWRITE_TAC[DIMINDEX_64; divides] THEN EXISTS_TAC `k DIV 64 + 1` THEN
    MP_TAC(SPECL [`k:num`; `64`] DIVISION) THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* pi: a permutation of the 25 positions; lane (x,y) of the input appears    *)
(* as lane (y, (2x + 3y) mod 5) of the output.                               *)
(* ------------------------------------------------------------------------- *)

let KECCAK_PI_INDEX = prove
 (`!x. x < 5 ==> !y. y < 5 ==>
        (2 * x + 3 * y) MOD 5 < 5 /\
        (y + 3 * ((2 * x + 3 * y) MOD 5)) MOD 5 = x`,
  CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KECCAK_PI_INJ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> keccak_pi a x y = keccak_pi b x y)
         ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REWRITE_TAC[keccak_pi] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:num`; `(2 * x + 3 * y) MOD 5`]) THEN
  MP_TAC(SPEC `x:num` KECCAK_PI_INDEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let KECCAK_RHO_INJ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> keccak_rho a x y = keccak_rho b x y)
         ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REWRITE_TAC[keccak_rho] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC KECCAK_ROL_INJ);;

(* ------------------------------------------------------------------------- *)
(* chi: bitwise on rows of five lanes. For each bit position, the 5-bit map  *)
(* is injective (checked by a propositional tautology).                      *)
(* ------------------------------------------------------------------------- *)

let KECCAK_CHI_ROW = prove
 (`!(u:num->int64) v.
     (!x. x < 5
          ==> word_xor (u x) (word_and (word_not (u ((x + 1) MOD 5)))
                                       (u ((x + 2) MOD 5))) =
              word_xor (v x) (word_and (word_not (v ((x + 1) MOD 5)))
                                       (v ((x + 2) MOD 5))))
     ==> (!x. x < 5 ==> u x = v x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. i < 64
        ==> (bit i ((u:num->int64) 0) <=> bit i ((v:num->int64) 0)) /\
            (bit i (u 1) <=> bit i (v 1)) /\
            (bit i (u 2) <=> bit i (v 2)) /\ (bit i (u 3) <=> bit i (v 3)) /\
            (bit i (u 4) <=> bit i (v 4))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_THEN(fun ilt ->
    FIRST_ASSUM(fun th ->
      MP_TAC(end_itlist CONJ
        (map (fun n -> SPEC (mk_small_numeral n) th) (0--4)))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      MP_TAC(end_itlist CONJ
        (map (AP_TERM `bit i:int64->bool`) (CONJUNCTS th)))) THEN
    REWRITE_TAC[BIT_WORD_XOR_ALT; BIT_WORD_AND_ALT; BIT_WORD_NOT;
                DIMINDEX_64; ilt] THEN
    CONV_TAC TAUT);
    ALL_TAC] THEN
  POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let KECCAK_CHI_INJ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> keccak_chi a x y = keccak_chi b x y)
         ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REWRITE_TAC[keccak_chi] THEN REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\x. (a:num->num->int64) x y`; `\x. (b:num->num->int64) x y`]
   KECCAK_CHI_ROW)) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `z:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:num`; `y:num`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A round, any number of rounds, and Keccak-f[1600].                        *)
(* ------------------------------------------------------------------------- *)

let KECCAK_RND_INJ = prove
 (`!i a b. (!x y. x < 5 /\ y < 5 ==> keccak_rnd i a x y = keccak_rnd i b x y)
           ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[keccak_rnd] THEN DISCH_TAC THEN
  MATCH_MP_TAC KECCAK_THETA_INJ THEN MATCH_MP_TAC KECCAK_RHO_INJ THEN
  MATCH_MP_TAC KECCAK_PI_INJ THEN MATCH_MP_TAC KECCAK_CHI_INJ THEN
  MATCH_MP_TAC KECCAK_IOTA_INJ THEN EXISTS_TAC `i:num` THEN
  REWRITE_TAC[ETA_AX] THEN FIRST_ASSUM ACCEPT_TAC);;

let KECCAK_ROUNDS_INJ = prove
 (`!n a b. (!x y. x < 5 /\ y < 5
                  ==> keccak_rounds n a x y = keccak_rounds n b x y)
           ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[keccak_rounds];
    REWRITE_TAC[keccak_rounds] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP KECCAK_RND_INJ) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN ACCEPT_TAC th)]);;

let KECCAK_F1600_INJ = prove
 (`!(s:1600 word) t. keccak_f1600 s = keccak_f1600 t ==> s = t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[keccak_f1600] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`24`; `keccak_lanes s`; `keccak_lanes t`]
                KECCAK_ROUNDS_INJ) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `keccak_lanes`) THEN
    DISCH_THEN(MP_TAC o C AP_THM `x:num`) THEN
    DISCH_THEN(MP_TAC o C AP_THM `y:num`) THEN
    ASM_SIMP_TAC[KECCAK_LANES_STATE];
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM KECCAK_STATE_LANES] THEN
    MATCH_MP_TAC KECCAK_STATE_EQ THEN ASM_REWRITE_TAC[]]);;
