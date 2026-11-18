(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The arithmetic of mldsa-native's portable C code in the NTT domain and    *)
(* its relation to FIPS 204 (common/fips204/fips204.ml): from the            *)
(* congruences of mldsa_native_ntt_cong.ml, for inputs within the            *)
(* bounds of the C contracts, the NTT as mldsa_ntt, the inverse NTT of the   *)
(* Montgomery dot product of a row of the matrix with a vector as the dot    *)
(* product in R_q, and the inverse NTT of a pointwise Montgomery product as  *)
(* the product in R_q.                                                       *)
(* ========================================================================= *)

needs "common/fips204/properties/mldsa_native_ntt_cong.ml";;
needs "common/fips204/properties/fips204_properties.ml";;

(* ------------------------------------------------------------------------- *)
(* The explicit forms of the NTT and of its inverse (with its Montgomery     *)
(* factor 2^32) as mldsa_ntt and mldsa_ntt_inv of FIPS 204.                  *)
(* ------------------------------------------------------------------------- *)

let ARM_MLDSA_FORWARD_NTT_MLDSA_NTT = prove
 (`!a k. arm_mldsa_forward_ntt a k = mldsa_ntt (mldsa_poly a) k`,
  REWRITE_TAC[arm_mldsa_forward_ntt; MLDSA_NTT_MLDSA_POLY]);;

let ARM_MLDSA_INVERSE_NTT_MLDSA_NTT_INV = prove
 (`!a k. k < 256
         ==> arm_mldsa_inverse_ntt a k =
             (&2 pow 32 * coeff k (mldsa_ntt_inv (\i. a i rem &8380417)))
             rem &8380417`,
  SIMP_TAC[arm_mldsa_inverse_ntt; MLDSA_NTT_INV_TOMONT]);;

(* ------------------------------------------------------------------------- *)
(* Two facts about R_q in the NTT domain: the inverse NTT is linear for      *)
(* scalars, and the dot product of the inverse NTTs of the rows of a matrix  *)
(* with a vector is the inverse NTT of the sums of the pointwise products.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NTT_INV_CMUL = prove
 (`!c a k.
        (!i. i < 256 ==> &0 <= a i /\ a i < &8380417) /\ k < 256
        ==> coeff k (mldsa_ntt_inv (\i. (c * a i) rem &8380417)) =
            (c * coeff k (mldsa_ntt_inv a)) rem &8380417`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_NTT_INV_COEFF o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[MLDSA_NTT_INV_COEFF] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!C x y c n:int. (x == c * y) (mod n)
                    ==> (C * x == c * (C * y)) (mod n)`) THEN
  REWRITE_TAC[GSYM ISUM_LMUL] THEN MATCH_MP_TAC INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[INT_MUL_ASSOC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!x y w n:int. (x == y) (mod n) ==> (x * w == y * w) (mod n)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let MLDSA_DOT_NTT_INV_ISUM = prove
 (`!n a v.
        (!j k. j < n /\ k < 256 ==> &0 <= a j k /\ a j k < &8380417) /\
        (!j. j < n ==> v j IN ring_carrier mldsa_rq)
        ==> mldsa_ntt_inv
             (\k. isum {j | j < n} (\j. a j k * mldsa_ntt (v j) k)
                  rem &8380417) =
            mldsa_dot n (\j. mldsa_ntt_inv (a j)) v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_DOT_NTT_INV] THEN
  REWRITE_TAC[MLDSA_ZQ] THEN
  SIMP_TAC[MLDSA_ZQ_RING_SUM; FINITE_NUMSEG_LT]);;

(* ------------------------------------------------------------------------- *)
(* The inverse NTT of an array congruent to 2^-32 * S is the inverse NTT of  *)
(* S (the Montgomery factors cancel); the C NTT represents mldsa_ntt of its  *)
(* input; the dot products of the C code; and the pointwise products.        *)
(* ------------------------------------------------------------------------- *)

let MLD_MONT_CANCEL = prove
 (`(&2 pow 32 * &(inverse_mod 8380417 4294967296) == &1:int) (mod &8380417)`,
  REWRITE_TAC[MLD_MONT_INVERSE; GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let MLD_FIPS204_INVNTT_MONT = prove
 (`!(P:num->int32) S.
        (!k. k < 256
             ==> abs(ival(P k)) < &8380417 /\
                 (ival(P k) == &(inverse_mod 8380417 4294967296) * S k)
                 (mod &8380417))
        ==> !n. n < 256
                ==> (ival(mld_poly_invntt_tomont P n) ==
                     coeff n (mldsa_ntt_inv (\k. S k rem &8380417)))
                    (mod &8380417) /\
                    abs(ival(mld_poly_invntt_tomont P n)) < &8380417`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `P:num->int32` MLD_POLY_INVNTT_TOMONT_CONG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n < 256` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARM_MLDSA_INVERSE_NTT_MLDSA_NTT_INV] THEN
  SUBGOAL_THEN
   `mldsa_ntt_inv (\i. (ival o (P:num->int32)) i rem &8380417) =
    mldsa_ntt_inv
     (\i. (&(inverse_mod 8380417 4294967296) * (S i rem &8380417))
          rem &8380417)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[INT_REM_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `i < 256`)) THEN
    MP_TAC(SPECL [`(S:num->int) i`; `&8380417:int`] INT_REM_MOD_SELF) THEN
    SPEC_TAC(`&8380417:int`,`q:int`) THEN
    SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
    CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`&(inverse_mod 8380417 4294967296):int`;
    `\i. (S:num->int) i rem &8380417`; `n:num`] MLDSA_NTT_INV_CMUL)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC MLD_MONT_CANCEL THEN
  SPEC_TAC(`coeff n (mldsa_ntt_inv (\k. (S:num->int) k rem &8380417))`,
           `x:int`) THEN
  SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
  SPEC_TAC(`(&2 pow 32):int`,`t:int`) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`c * x:int`; `q:int`] INT_REM_MOD_SELF) THEN
  MP_TAC(SPECL [`t * (c * x) rem q:int`; `q:int`] INT_REM_MOD_SELF) THEN
  CONV_TAC INTEGER_RULE);;

let MLD_FIPS204_POLY_NTT = prove
 (`!x:num->int32.
        (!i. i < 256 ==> abs(ival(x i)) < &8380417)
        ==> !k. k < 256
                ==> (ival(mld_poly_ntt x k) ==
                     mldsa_ntt (mldsa_poly (\i. ival(x i))) k)
                    (mod &8380417) /\
                    abs(ival(mld_poly_ntt x k)) < &94279689`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MLD_POLY_NTT_CONG) THEN
  REWRITE_TAC[ARM_MLDSA_FORWARD_NTT_MLDSA_NTT; o_DEF]);;

let MLD_FIPS204_POLYVEC_NTT = prove
 (`!l (x:num->int32).
        (!j. j < 256 * l ==> abs(ival(x j)) < &8380417)
        ==> !j m. j < l /\ m < 256
                  ==> (ival(mld_polyvec_map mld_poly_ntt x (256 * j + m)) ==
                       mldsa_ntt (mldsa_poly (\i. ival(x(256 * j + i)))) m)
                      (mod &8380417) /\
                      abs(ival(mld_polyvec_map mld_poly_ntt x (256 * j + m)))
                      < &94279689`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `m:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
  MP_TAC(SPEC `mld_poly_of (x:num->int32) j` MLD_FIPS204_POLY_NTT) THEN
  REWRITE_TAC[mld_poly_of] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[]]);;

(* The inverse NTT of the Montgomery dot product of a row u of the matrix    *)
(* in the NTT domain (values in [0,q), row j being the array of A_j^) with   *)
(* a vector v that represents the NTTs of polynomials Y_j (within the NTT    *)
(* bound) is congruent to the dot product sum_j A_j * Y_j in R_q.            *)

let MLD_FIPS204_INVNTT_ACC_TAC acccong l =
  let lt = mk_small_numeral l and nt = mk_small_numeral (256 * l) in
  let sub t = subst [lt,`l:num`; nt,`n:num`] t in
  let ubnd = sub
   `!j m. j < l /\ m < 256
          ==> &0 <= ival((u:num->int32)(256 * j + m)) /\
              ival(u(256 * j + m)) < &8380417`
  and vrep = sub
   `!j m. j < l /\ m < 256
          ==> (ival((v:num->int32)(256 * j + m)) ==
               mldsa_ntt ((Y:num->(1->num)->int) j) m) (mod &8380417) /\
              abs(ival(v(256 * j + m))) < &94279689`
  and sumc = sub `(isum {j | j < l}
      (\j. ival((u:num->int32)(k + 256 * j)) *
           ival((v:num->int32)(k + 256 * j))) ==
     isum {j | j < l}
      (\j. ival(u(256 * j + k)) * mldsa_ntt ((Y:num->(1->num)->int) j) k))
    (mod &8380417)`
  and atm = sub `isum {j | j < l}
      (\j. ival((u:num->int32)(k + 256 * j)) *
           ival((v:num->int32)(k + 256 * j)))`
  and btm = sub `isum {j | j < l}
      (\j. ival((u:num->int32)(256 * j + k)) *
           mldsa_ntt ((Y:num->(1->num)->int) j) k)`
  and ptm = sub `ival(mld_polyvec_pointwise_acc_montgomery l (u:num->int32)
                       (v:num->int32) k)` in
  let idx = ARITH_RULE(sub `i < n ==> i = 256 * (i DIV 256) + i MOD 256 /\
                                     i DIV 256 < l /\ i MOD 256 < 256`) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [lt; `\j k. ival((u:num->int32)(256 * j + k))`;
     `Y:num->(1->num)->int`] MLDSA_DOT_NTT_INV_ISUM)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MLD_FIPS204_INVNTT_MONT THEN BETA_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`u:num->int32`; `v:num->int32`; `k:num`] acccong) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    DISCH_THEN(MP_TAC o MATCH_MP idx) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC ubnd THEN
      DISCH_THEN(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      UNDISCH_TAC vrep THEN
      DISCH_THEN(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[MLDSA_POINTWISE_ACC_ISUM; o_THM] THEN
  SUBGOAL_THEN sumc MP_TAC THENL
   [MATCH_MP_TAC INT_CONG_ISUM THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `k + 256 * j = 256 * j + k`] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!a b c n:int. (b == c) (mod n) ==> (a * b == a * c) (mod n)`) THEN
    UNDISCH_TAC vrep THEN DISCH_THEN(MP_TAC o SPECL [`j:num`; `k:num`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [mk_binop `( * ):int->int->int` atm
                 `&(inverse_mod 8380417 4294967296):int`; `&8380417:int`]
               INT_REM_MOD_SELF) THEN
  W(fun (asl,w) ->
    let r = find_term (fun t -> is_comb t && is_comb(rator t) &&
                                rator(rator t) = `(rem):int->int->int`) w in
    SPEC_TAC(r,`r:int`)) THEN
  SPEC_TAC(atm,`a:int`) THEN SPEC_TAC(btm,`b:int`) THEN
  SPEC_TAC(ptm,`p:int`) THEN
  SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE;;

let MLD_FIPS204_INVNTT_ACC_STMT l =
  subst [mk_small_numeral l,`l:num`]
  `!(u:num->int32) (v:num->int32) (Y:num->(1->num)->int).
        (!j m. j < l /\ m < 256
               ==> &0 <= ival(u(256 * j + m)) /\
                   ival(u(256 * j + m)) < &8380417) /\
        (!j. j < l ==> Y j IN ring_carrier mldsa_rq) /\
        (!j m. j < l /\ m < 256
               ==> (ival(v(256 * j + m)) == mldsa_ntt (Y j) m)
                   (mod &8380417) /\
                   abs(ival(v(256 * j + m))) < &94279689)
        ==> !k. k < 256
                ==> (ival(mld_poly_invntt_tomont
                       (mld_polyvec_pointwise_acc_montgomery l u v) k) ==
                     coeff k (mldsa_dot l
                       (\j. mldsa_ntt_inv (\m. ival(u(256 * j + m)))) Y))
                    (mod &8380417) /\
                    abs(ival(mld_poly_invntt_tomont
                       (mld_polyvec_pointwise_acc_montgomery l u v) k))
                    < &8380417`;;

let MLD_FIPS204_INVNTT_ACC_L4 = prove
 (MLD_FIPS204_INVNTT_ACC_STMT 4,
  MLD_FIPS204_INVNTT_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L4_CONG 4);;

let MLD_FIPS204_INVNTT_ACC_L5 = prove
 (MLD_FIPS204_INVNTT_ACC_STMT 5,
  MLD_FIPS204_INVNTT_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L5_CONG 5);;

let MLD_FIPS204_INVNTT_ACC_L7 = prove
 (MLD_FIPS204_INVNTT_ACC_STMT 7,
  MLD_FIPS204_INVNTT_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L7_CONG 7);;

(* The inverse NTT of the pointwise Montgomery product of a and b, which     *)
(* represent the NTTs of f and g within the NTT bound, is congruent to the   *)
(* product f * g in R_q.                                                     *)

let MLD_FIPS204_INVNTT_POINTWISE = prove
 (`!(a:num->int32) (b:num->int32) f g.
        f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq /\
        (!k. k < 256 ==> (ival(a k) == mldsa_ntt f k) (mod &8380417) /\
                         abs(ival(a k)) < &94279689) /\
        (!k. k < 256 ==> (ival(b k) == mldsa_ntt g k) (mod &8380417) /\
                         abs(ival(b k)) < &94279689)
        ==> !k. k < 256
                ==> (ival(mld_poly_invntt_tomont
                       (mld_poly_pointwise_montgomery a b) k) ==
                     coeff k (ring_mul mldsa_rq f g)) (mod &8380417) /\
                    abs(ival(mld_poly_invntt_tomont
                       (mld_poly_pointwise_montgomery a b) k)) < &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM MLDSA_NTT_INV_MUL] THEN REWRITE_TAC[MLDSA_ZQ] THEN
  MATCH_MP_TAC MLD_FIPS204_INVNTT_MONT THEN BETA_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:num->int32`; `b:num->int32`; `k:num`]
               MLD_POLY_POINTWISE_MONTGOMERY_CONG) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[mldsa_pointwise; o_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(MP_TAC o CONJUNCT1)) THEN
  MP_TAC(SPECL [`ival((a:num->int32) k) * ival((b:num->int32) k) *
                 &(inverse_mod 8380417 4294967296)`; `&8380417:int`]
               INT_REM_MOD_SELF) THEN
  W(fun (asl,w) ->
    let r = find_term (fun t -> is_comb t && is_comb(rator t) &&
                                rator(rator t) = `(rem):int->int->int`) w in
    SPEC_TAC(r,`r:int`)) THEN
  SPEC_TAC(`ival((a:num->int32) k)`,`x:int`) THEN
  SPEC_TAC(`ival((b:num->int32) k)`,`y:int`) THEN
  SPEC_TAC(`mldsa_ntt (f:(1->num)->int) k`,`x':int`) THEN
  SPEC_TAC(`mldsa_ntt (g:(1->num)->int) k`,`y':int`) THEN
  SPEC_TAC(`ival(mld_poly_pointwise_montgomery (a:num->int32)
                  (b:num->int32) k)`,`p:int`) THEN
  SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;
