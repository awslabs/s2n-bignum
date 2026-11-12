(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f[1600] is a permutation of the 1600-bit states, so the squeezing  *)
(* of a sponge is periodic: from any state s, keccak_squeeze q s = s for     *)
(* some q > 0. When the padded message is a single block, the output blocks  *)
(* q - 1, 2 * q - 1, ... of keccak_sponge are therefore that block itself.   *)
(* This gives the termination of rejection sampling from the output of      *)
(* SHAKE (cf. Barbosa and Schwabe, "Kyber terminates", ePrint 2023/708),     *)
(* with no useful bound on the time.                                         *)
(*                                                                           *)
(* The step mappings are injective on the 5 x 5 lanes: rho, pi and iota      *)
(* obviously, chi because it is a permutation of each row at each bit        *)
(* position, and theta because the map keccak_theta_parity 4 1 1 that it     *)
(* induces on the column parities is. In terms of polynomials over GF(2) in  *)
(* x (the column, x^5 = 1) and z (the bit position, z^64 = 1), that map is   *)
(* multiplication by 1 + x + x^4 z, whose 64th power, by six squarings       *)
(* (KECCAK_THETA_PARITY_SQUARE), is 1 + x^4 + x, which has order 3.          *)
(* ========================================================================= *)

needs "common/fips202.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

let FINITE_WORD = prove
 (`FINITE(:N word)`,
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (word:num->N word) {n | n < 2 EXP dimindex(:N)}` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_UNIV; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[WORD_VAL; VAL_BOUND]);;

let WORD_ROL_XOR = prove
 (`!(x:N word) y n.
        word_rol (word_xor x y) n = word_xor (word_rol x n) (word_rol y n)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ROL; BIT_WORD_XOR] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < n /\ n <= d ==> i + d - n < d`;
               ARITH_RULE `i < d ==> i - n < d`;
               MOD_LT_EQ; DIMINDEX_NONZERO; LT_IMP_LE] THEN
  CONV_TAC TAUT);;

let WORD_ROL_INJ = prove
 (`!(p:N word) q n. word_rol p n = word_rol q n <=> p = q`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `\w:N word. word_rol w ((dimindex(:N) - 1) * n)`) THEN
  REWRITE_TAC[WORD_ROL_COMPOSE] THEN
  MATCH_MP_TAC(MESON[]
   `(x:N word) = p /\ (y:N word) = q ==> x = y ==> p = q`) THEN
  CONJ_TAC THEN MATCH_MP_TAC WORD_ROL_EQ_SELF THEN
  REWRITE_TAC[divides] THEN EXISTS_TAC `n:num` THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN
  SPEC_TAC(`dimindex(:N)`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[SUC_SUB1] THEN ARITH_TAC);;

let WORD_XOR_EQ_CANCEL_IMP = prove
 (`!p q d e:N word. d = e ==> word_xor p d = word_xor q e ==> p = q`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN WORD_BITWISE_TAC);;

let WORD_XOR_RCANCEL = prove
 (`!p q d:N word. word_xor p d = word_xor q d <=> p = q`,
  MESON_TAC[WORD_XOR_EQ_CANCEL_IMP]);;

let MOD_5_ADD_LEFT = prove
 (`!x a. (x MOD 5 + a) MOD 5 = (x + a) MOD 5`,
  REPEAT GEN_TAC THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let KECCAK_BYTELIST_BOUND = prove
 (`!l. num_of_bytelist l < 2 EXP (8 * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[num_of_bytelist; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES; EXP_ADD] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let KECCAK_BYTELIST_EL = prove
 (`!l k. k < LENGTH l
         ==> (num_of_bytelist l DIV 2 EXP (8 * k)) MOD 2 EXP 8 =
             val(EL k l:byte)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; num_of_bytelist; LT_SUC] THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    DISCH_TAC THEN FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
      [GSYM(MATCH_MP th (ASSUME `k < LENGTH(t:byte list)`))]) THEN
    REWRITE_TAC[ARITH_RULE `8 * SUC k = 8 + 8 * k`; EXP_ADD;
                GSYM DIV_DIV] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[DIV_MULT_ADD; DIV_LT; ARITH_EQ; ADD_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* theta: the map of the column parities, and its iterates.                  *)
(* ------------------------------------------------------------------------- *)

let keccak_theta_parity = new_definition
 `keccak_theta_parity a b r (c:num->int64) =
    \x. word_xor (c x)
         (word_xor (c((x + a) MOD 5)) (word_rol (c((x + b) MOD 5)) r))`;;

let KECCAK_THETA_PARITY_SQUARE = prove
 (`!a b r c.
        keccak_theta_parity a b r (keccak_theta_parity a b r c) =
        keccak_theta_parity (2 * a) (2 * b) (2 * r) c`,
  REWRITE_TAC[keccak_theta_parity; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_ROL_XOR; WORD_ROL_COMPOSE; MOD_5_ADD_LEFT] THEN
  REWRITE_TAC[MULT_2] THEN REWRITE_TAC[ADD_AC] THEN WORD_BITWISE_TAC);;

let KECCAK_THETA_PARITY_LOCAL = prove
 (`!a b r c d.
        (!x. x < 5 ==> c x = d x)
        ==> !x. x < 5 ==> keccak_theta_parity a b r c x =
                          keccak_theta_parity a b r d x`,
  REWRITE_TAC[keccak_theta_parity] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOD_LT_EQ; ARITH_EQ]);;

let KECCAK_THETA_PARITY_INJ_STEP = prove
 (`!a b r.
        (!c d. (!x. x < 5
                    ==> keccak_theta_parity (2 * a) (2 * b) (2 * r) c x =
                        keccak_theta_parity (2 * a) (2 * b) (2 * r) d x)
               ==> (!x. x < 5 ==> c x = d x))
        ==> (!c d. (!x. x < 5 ==> keccak_theta_parity a b r c x =
                                  keccak_theta_parity a b r d x)
                   ==> (!x. x < 5 ==> c x = d x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (SPECL [`a:num`; `b:num`; `r:num`] KECCAK_THETA_PARITY_LOCAL)) THEN
  REWRITE_TAC[ETA_AX; KECCAK_THETA_PARITY_SQUARE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let KECCAK_THETA_PARITY_INJ_64 = prove
 (`!c d. (!x. x < 5 ==> keccak_theta_parity 256 64 64 c x =
                        keccak_theta_parity 256 64 64 d x)
         ==> (!x. x < 5 ==> c x = d x)`,
  SUBGOAL_THEN `keccak_theta_parity 256 64 64 = keccak_theta_parity 1 4 0`
  SUBST1_TAC THENL
   [REWRITE_TAC[keccak_theta_parity; FUN_EQ_THM; WORD_ROL_ZERO] THEN
    REPEAT GEN_TAC THEN
    SIMP_TAC[WORD_ROL_EQ_SELF; DIMINDEX_64;
             NUMBER_RULE `!n:num. n divides n`] THEN
    REWRITE_TAC[ARITH_RULE `x + 256 = (x + 1) + 5 * 51 /\
                            x + 64 = (x + 4) + 5 * 12`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. keccak_theta_parity 1 4 0 (keccak_theta_parity 2 8 0 c) = c`
  ASSUME_TAC THENL
   [REWRITE_TAC[keccak_theta_parity; FUN_EQ_THM; WORD_ROL_ZERO] THEN
    REWRITE_TAC[MOD_5_ADD_LEFT] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE
     `x + 9 = (x + 4) + 5 * 1 /\ x + 8 = (x + 3) + 5 * 1 /\
      x + 6 = (x + 1) + 5 * 1 /\ x + 12 = (x + 2) + 5 * 2`] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN WORD_BITWISE_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (SPECL [`1`; `4`; `0`] KECCAK_THETA_PARITY_LOCAL)) THEN
  REWRITE_TAC[ETA_AX; KECCAK_THETA_PARITY_SQUARE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (SPECL [`1`; `4`; `0`] KECCAK_THETA_PARITY_LOCAL)) THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let KECCAK_THETA_PARITY_INJ = prove
 (`!c d. (!x. x < 5 ==> keccak_theta_parity 4 1 1 c x =
                        keccak_theta_parity 4 1 1 d x)
         ==> (!x. x < 5 ==> c x = d x)`,
  let step a b r =
    MATCH_MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [a; b; r] KECCAK_THETA_PARITY_INJ_STEP)) in
  step `4` `1` `1` THEN step `8` `2` `2` THEN step `16` `4` `4` THEN
  step `32` `8` `8` THEN step `64` `16` `16` THEN step `128` `32` `32` THEN
  ACCEPT_TAC KECCAK_THETA_PARITY_INJ_64);;

let KECCAK_THETA_PARITY_THETA = prove
 (`!a. (\x. word_xor (keccak_theta a x 0)
             (word_xor (keccak_theta a x 1)
               (word_xor (keccak_theta a x 2)
                 (word_xor (keccak_theta a x 3) (keccak_theta a x 4))))) =
       keccak_theta_parity 4 1 1
        (\x. word_xor (a x 0)
              (word_xor (a x 1)
                (word_xor (a x 2) (word_xor (a x 3) (a x 4)))))`,
  REWRITE_TAC[keccak_theta; keccak_theta_parity; FUN_EQ_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN WORD_BITWISE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The step mappings, the rounds and the permutation are injective.          *)
(* ------------------------------------------------------------------------- *)

let KECCAK_THETA_INJ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> keccak_theta a x y = keccak_theta b x y)
         ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `ca = \x. word_xor ((a:num->num->int64) x 0)
                        (word_xor (a x 1)
                          (word_xor (a x 2) (word_xor (a x 3) (a x 4))))` THEN
  ABBREV_TAC `cb = \x. word_xor ((b:num->num->int64) x 0)
                        (word_xor (b x 1)
                          (word_xor (b x 2) (word_xor (b x 3) (b x 4))))` THEN
  SUBGOAL_THEN `!x. x < 5 ==> (ca:num->int64) x = cb x` ASSUME_TAC THENL
   [MATCH_MP_TAC KECCAK_THETA_PARITY_INJ THEN
    MAP_EVERY EXPAND_TAC ["ca"; "cb"] THEN
    REWRITE_TAC[GSYM KECCAK_THETA_PARITY_THETA] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < 5 /\ 1 < 5 /\ 2 < 5 /\ 3 < 5 /\ 4 < 5`];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`]) THEN
  ASM_REWRITE_TAC[keccak_theta] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC WORD_XOR_EQ_CANCEL_IMP THEN
  BINOP_TAC THENL [ALL_TAC; AP_THM_TAC THEN AP_TERM_TAC] THEN
  FIRST_X_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  MAP_EVERY EXPAND_TAC ["ca"; "cb"] THEN
  SIMP_TAC[MOD_LT_EQ; ARITH_EQ]);;

let KECCAK_RHO_INJ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> keccak_rho a x y = keccak_rho b x y)
         ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REWRITE_TAC[keccak_rho; WORD_ROL_INJ]);;

let KECCAK_PI_INDEX = prove
 (`!x y. x < 5 ==> (y + 3 * ((2 * x + 3 * y) MOD 5)) MOD 5 = x`,
  REPEAT STRIP_TAC THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[ARITH_RULE
   `y + 3 * (2 * x + 3 * y) = x + 5 * (x + 2 * y)`] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let KECCAK_PI_INJ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> keccak_pi a x y = keccak_pi b x y)
         ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REWRITE_TAC[keccak_pi] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:num`; `(2 * x + 3 * y) MOD 5`]) THEN
  ASM_SIMP_TAC[MOD_LT_EQ; ARITH_EQ; KECCAK_PI_INDEX]);;

let KECCAK_CHI_ROW_INJ = prove
 (`!p0 p1 p2 p3 p4 q0 q1 q2 q3 q4:int64.
        word_xor p0 (word_and (word_not p1) p2) =
        word_xor q0 (word_and (word_not q1) q2) /\
        word_xor p1 (word_and (word_not p2) p3) =
        word_xor q1 (word_and (word_not q2) q3) /\
        word_xor p2 (word_and (word_not p3) p4) =
        word_xor q2 (word_and (word_not q3) q4) /\
        word_xor p3 (word_and (word_not p4) p0) =
        word_xor q3 (word_and (word_not q4) q0) /\
        word_xor p4 (word_and (word_not p0) p1) =
        word_xor q4 (word_and (word_not q0) q1)
        ==> p0 = q0 /\ p1 = q1 /\ p2 = q2 /\ p3 = q3 /\ p4 = q4`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR; BIT_WORD_AND; BIT_WORD_NOT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_IMP_FORALL_THM; GSYM FORALL_AND_THM] THEN
  REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
  REWRITE_TAC[GSYM IMP_CONJ; GSYM FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT);;

let KECCAK_CHI_INJ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> keccak_chi a x y = keccak_chi b x y)
         ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REWRITE_TAC[keccak_chi] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[TAUT `p /\ q ==> r <=> q ==> p ==> r`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; GSYM FORALL_AND_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:num` THEN
  ASM_CASES_TAC `y < 5` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_ACCEPT_TAC KECCAK_CHI_ROW_INJ);;

let KECCAK_IOTA_INJ = prove
 (`!i a b.
        (!x y. x < 5 /\ y < 5 ==> keccak_iota i a x y = keccak_iota i b x y)
        ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REWRITE_TAC[keccak_iota] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`]) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[WORD_XOR_RCANCEL]);;

let KECCAK_RND_INJ = prove
 (`!i a b.
        (!x y. x < 5 /\ y < 5 ==> keccak_rnd i a x y = keccak_rnd i b x y)
        ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  REWRITE_TAC[keccak_rnd] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP KECCAK_IOTA_INJ) THEN
  DISCH_THEN(MP_TAC o MATCH_MP KECCAK_CHI_INJ) THEN
  DISCH_THEN(MP_TAC o MATCH_MP KECCAK_PI_INJ) THEN
  DISCH_THEN(MP_TAC o MATCH_MP KECCAK_RHO_INJ) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP KECCAK_THETA_INJ));;

let KECCAK_ROUNDS_INJ = prove
 (`!n a b.
        (!x y. x < 5 /\ y < 5
               ==> keccak_rounds n a x y = keccak_rounds n b x y)
        ==> (!x y. x < 5 /\ y < 5 ==> a x y = b x y)`,
  INDUCT_TAC THEN REWRITE_TAC[keccak_rounds] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP KECCAK_RND_INJ) THEN ASM_REWRITE_TAC[]);;

let KECCAK_F1600_INJ = prove
 (`!s t. keccak_f1600 s = keccak_f1600 t <=> s = t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[keccak_f1600] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM KECCAK_STATE_LANES] THEN
  MATCH_MP_TAC KECCAK_STATE_EQ THEN
  MATCH_MP_TAC KECCAK_ROUNDS_INJ THEN EXISTS_TAC `24` THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\s. keccak_lanes s x y`) THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[KECCAK_LANES_STATE]);;

(* ------------------------------------------------------------------------- *)
(* Squeezing is periodic.                                                    *)
(* ------------------------------------------------------------------------- *)

let KECCAK_SQUEEZE_ONE = prove
 (`!s. keccak_squeeze 1 s = keccak_f1600 s`,
  REWRITE_TAC[num_CONV `1`; keccak_squeeze]);;

let KECCAK_SQUEEZE_SPLIT = prove
 (`!m n s. keccak_squeeze (m + n) s = keccak_squeeze m (keccak_squeeze n s)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze; ADD_CLAUSES]);;

let KECCAK_SQUEEZE_INJ = prove
 (`!n s t. keccak_squeeze n s = keccak_squeeze n t <=> s = t`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze; KECCAK_F1600_INJ]);;

let KECCAK_SQUEEZE_PERIODIC = prove
 (`!s. ?q. 0 < q /\ !k. keccak_squeeze (k * q) s = s`,
  GEN_TAC THEN
  SUBGOAL_THEN `?m n. m < n /\ keccak_squeeze m s = keccak_squeeze n s`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\n. keccak_squeeze n (s:1600 word)`; `(:num)`]
                  INFINITE_IMAGE) THEN
    REWRITE_TAC[num_INFINITE; IN_UNIV; INFINITE; NOT_IMP] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
      REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `~(m < n) /\ ~(n < m) ==> m:num = n`) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(:1600 word)` THEN
      REWRITE_TAC[FINITE_WORD; SUBSET_UNIV]];
    ALL_TAC] THEN
  EXISTS_TAC `n - m:num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n - m <=> m < n`] THEN
  SUBGOAL_THEN `keccak_squeeze (n - m) s = s` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM(SPEC `m:num` KECCAK_SQUEEZE_INJ)] THEN
    REWRITE_TAC[GSYM KECCAK_SQUEEZE_SPLIT] THEN
    ASM_SIMP_TAC[ARITH_RULE `m < n ==> m + n - m = n`];
    INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; keccak_squeeze] THEN
    ASM_REWRITE_TAC[KECCAK_SQUEEZE_SPLIT]]);;

let KECCAK_SQUEEZE_PERIODIC_ALT = prove
 (`!s. ?q. 0 < q /\
           !k. keccak_squeeze ((k + 1) * q - 1) (keccak_f1600 s) = s`,
  GEN_TAC THEN MP_TAC(SPEC `s:1600 word` KECCAK_SQUEEZE_PERIODIC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[GSYM KECCAK_SQUEEZE_ONE; GSYM KECCAK_SQUEEZE_SPLIT] THEN
  SUBGOAL_THEN `(k + 1) * q - 1 + 1 = (k + 1) * q` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(k + 1) * q = k * q + q`] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The padding, and the sponge for a message that fits in one block.         *)
(* ------------------------------------------------------------------------- *)

let KECCAK_PAD_LENGTH = prove
 (`!r d len. 0 < r ==> LENGTH(keccak_pad r d len) = r - len MOD r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_pad] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_REPLICATE] THENL
   [ASM_ARITH_TAC;
    MP_TAC(SPECL [`len:num`; `r:num`] MOD_LT_EQ) THEN ASM_ARITH_TAC]);;

let KECCAK_PADDED_LENGTH = prove
 (`!r d m. LENGTH m < r
           ==> LENGTH(APPEND m (keccak_pad r d (LENGTH m))) = r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_APPEND; KECCAK_PAD_LENGTH; MOD_LT] THEN
  ASM_ARITH_TAC);;

let KECCAK_PAD_LAST = prove
 (`!r d len. len < r
             ==> EL (r - 1 - len) (keccak_pad r d len) =
                 if len = r - 1 then word(d + 128) else word 128`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[keccak_pad; MOD_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SUB_REFL; EL; HD]; ALL_TAC] THEN
  SUBGOAL_THEN `r - 1 - len = SUC(r - len - 2)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]] THEN
  SIMP_TAC[EL_APPEND; LENGTH_REPLICATE; LT_REFL; SUB_REFL; EL; HD]);;

let KECCAK_PADDED_LAST = prove
 (`!r d m. LENGTH m < r
           ==> EL (r - 1) (APPEND m (keccak_pad r d (LENGTH m))) =
               if LENGTH m = r - 1 then word(d + 128) else word 128`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `m < r ==> ~(r - 1 < m)`] THEN
  ASM_SIMP_TAC[KECCAK_PAD_LAST]);;

let KECCAK_ABSORB_1 = prove
 (`!r p. keccak_absorb r p 1 = keccak_f1600 (word(p MOD 2 EXP (8 * r)))`,
  REWRITE_TAC[num_CONV `1`; keccak_absorb] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1; WORD_XOR_0]);;

let KECCAK_SPONGE_PERIODIC = prove
 (`!c d m.
        LENGTH m < (1600 - c) DIV 8
        ==> ?q. 0 < q /\
                !k i. i < (1600 - c) DIV 8
                      ==> keccak_sponge c d m
                            ((1600 - c) DIV 8 * ((k + 1) * q - 1) + i) =
                          EL i (APPEND m (keccak_pad ((1600 - c) DIV 8) d
                                                     (LENGTH m)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[keccak_sponge] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `r = (1600 - c) DIV 8` THEN DISCH_TAC THEN
  ABBREV_TAC `p = APPEND m (keccak_pad r d (LENGTH(m:byte list)))` THEN
  SUBGOAL_THEN `LENGTH(p:byte list) = r` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC KECCAK_PADDED_LENGTH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < r /\ 8 * r <= 1600` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_REFL; ARITH_RULE `0 < r ==> ~(r = 0)`; KECCAK_ABSORB_1] THEN
  MP_TAC(ISPEC `word(num_of_bytelist p MOD 2 EXP (8 * r)):1600 word`
         KECCAK_SQUEEZE_PERIODIC_ALT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ADD_CLAUSES;
               ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`] THEN
  MP_TAC(SPEC `p:byte list` KECCAK_BYTELIST_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `num_of_bytelist p < 2 EXP 1600` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (8 * r)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]] THEN
  MATCH_MP_TAC KECCAK_BYTELIST_EL THEN ASM_REWRITE_TAC[]);;

(* The last byte of output block (k + 1) * q - 1 of SHAKE128 and SHAKE256    *)
(* of a message of one block is the last byte of the padding.                *)

let SHAKE128_PERIODIC_LAST = prove
 (`!m. LENGTH m < 168
       ==> ?q. 0 < q /\
               !k. shake128 m (168 * ((k + 1) * q - 1) + 167) =
                   if LENGTH m = 167 then word 159 else word 128`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`256`; `0x1F`; `m:byte list`] KECCAK_SPONGE_PERIODIC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[shake128] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `167`]) THEN
  MP_TAC(SPECL [`168`; `31`; `m:byte list`] KECCAK_PADDED_LAST) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SHAKE256_PERIODIC_LAST = prove
 (`!m. LENGTH m < 136
       ==> ?q. 0 < q /\
               !k. shake256 m (136 * ((k + 1) * q - 1) + 135) =
                   if LENGTH m = 135 then word 159 else word 128`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`512`; `0x1F`; `m:byte list`] KECCAK_SPONGE_PERIODIC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[shake256] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `135`]) THEN
  MP_TAC(SPECL [`136`; `31`; `m:byte list`] KECCAK_PADDED_LAST) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Counting: if candidate f k is accepted for every k and f is increasing,   *)
(* at least n of the candidates before f n are accepted.                     *)
(* ------------------------------------------------------------------------- *)

let CARD_RESTRICT_INCREASING = prove
 (`!P (f:num->num) n.
        (!k. P(f k)) /\ (!k. f k < f(SUC k))
        ==> n <= CARD {j | j < f n /\ P j}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m k. m < k ==> (f:num->num) m < f k` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN
    STRIP_TAC THEN ASM_MESON_TAC[LT_TRANS];
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS `CARD(IMAGE (f:num->num) {k | k < n})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x = n ==> n <= x`) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    REWRITE_TAC[CARD_NUMSEG_LT; FINITE_NUMSEG_LT] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `~(x < y) /\ ~(y < x) ==> x:num = y`) THEN
    ASM_MESON_TAC[LT_REFL];
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < f(n:num)}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]]]);;

let KECCAK_PERIOD_INCREASING = prove
 (`!a b q k. 0 < a /\ 0 < q
             ==> a * ((k + 1) * q - 1) + b < a * ((SUC k + 1) * q - 1) + b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LT_ADD_RCANCEL; LT_MULT_LCANCEL] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(a = 0) <=> 0 < a`] THEN
  REWRITE_TAC[ADD1; ARITH_RULE `((k + 1) + 1) * q = (k + 1) * q + q`] THEN
  SUBGOAL_THEN `~((k + 1) * q = 0)` MP_TAC THENL
   [REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
