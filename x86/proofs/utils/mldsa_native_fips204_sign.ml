(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing of mldsa-native and FIPS 204: for each parameter set, the         *)
(* signature that the specification of mldsa-native's signing                *)
(* (mld_sign_ok_44, mld_sign_sig_44 etc. of common/mldsa_native_sign.ml)     *)
(* gives for a secret key, the message representative mu and the 32 random   *)
(* bytes rnd is the one of mldsa_sign_mu of common/fips204.ml, and when the  *)
(* C code gives up after its maximal number of attempts, none of these       *)
(* attempts of FIPS 204 succeeds. This assumes that the rejection samplers   *)
(* of the C code terminate and that the s2 part of the secret key has fields *)
(* at most 2 * eta, as every key that key generation makes has: the C code   *)
(* checks the low bits and computes the hints the alternative way of Section *)
(* 5.1 of the Round 3 Dilithium specification (mldsa_sign_attempt_alt of     *)
(* common/fips204_theory.ml), which is the same as FIPS 204 for such keys.   *)
(* The hashes mu = H(tr || pre || m, 64) and rho'' = H(key || rnd || mu, 64) *)
(* of the C code are those of FIPS 204 too.                                  *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_fips204_keypair.ml";;

(* ------------------------------------------------------------------------- *)
(* The hashes: mu = H(tr || pre || m, 64) (mld_sign_mu), rho'' = H(key ||    *)
(* rnd || mu, 64) (mld_sign_rhoprime) and the stream of c~ = H(mu || w1      *)
(* packed) (mld_sign_ctilde) with the byte strings as numbers, as SHAKE256   *)
(* of the concatenated byte strings.                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_BYTELIST_NUM = prove
 (`!(f:num->byte) n.
        bytelist_of_num n (num_of_bytelist(list_of_seq f n)) = list_of_seq f n`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) n` BYTELIST_OF_NUM_OF_BYTELIST) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ]);;

let MLD_FIPS204_SIGN_NUM_BOUND = prove
 (`!(f:num->byte) n. num_of_bytelist(list_of_seq f n) < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) n` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let MLD_FIPS204_SIGN_SPLIT_BOUND = prove
 (`!m n e a b.
        e = 8 * m /\ a < 2 EXP e /\ b < 2 EXP (8 * n)
        ==> a + 2 EXP e * b < 2 EXP (8 * (m + n))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * m) * (b + 1)` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let MLD_FIPS204_SIGN_BYTELIST_SPLIT = prove
 (`!t m n e a b.
        t = m + n /\ e = 8 * m /\ a < 2 EXP e
        ==> bytelist_of_num t (a + 2 EXP e * b) =
            APPEND (bytelist_of_num m a) (bytelist_of_num n b)`,
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MLD_FIPS204_SAMPLE_BYTELIST_OF_NUM_SPLIT THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let MLD_FIPS204_SIGN_SHAKE256_APPEND = prove
 (`!t m n e a b.
        t = m + n /\ e = 8 * m /\ a < 2 EXP e /\ b < 2 EXP (8 * n)
        ==> mld_shake256_byte t (a + 2 EXP e * b) =
            shake256 (APPEND (bytelist_of_num m a) (bytelist_of_num n b))`,
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_SHAKE256_BYTE o
    lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLD_FIPS204_SIGN_SPLIT_BOUND THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MLD_FIPS204_SIGN_BYTELIST_SPLIT THEN ASM_REWRITE_TAC[]]);;

let MLD_FIPS204_SIGN_MU = prove
 (`!(tr:num->byte) prelen pre mlen m.
        pre < 2 EXP (8 * prelen) /\ m < 2 EXP (8 * mlen)
        ==> bytelist_of_num 64 (mld_sign_mu tr prelen pre mlen m) =
            mldsa_h (APPEND (list_of_seq tr 64)
                            (APPEND (bytelist_of_num prelen pre)
                                    (bytelist_of_num mlen m))) 64`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_sign_mu; mldsa_h; MLD_FIPS204_SIGN_BYTELIST_NUM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`64 + prelen + mlen`; `64`; `prelen + mlen`; `512`;
                `num_of_bytelist(list_of_seq (tr:num->byte) 64)`;
                `pre + 2 EXP (8 * prelen) * m`]
               MLD_FIPS204_SIGN_SHAKE256_APPEND) THEN
  REWRITE_TAC[MLD_FIPS204_SIGN_BYTELIST_NUM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      MP_TAC(ISPECL [`tr:num->byte`; `64`] MLD_FIPS204_SIGN_NUM_BOUND) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      MATCH_MP_TAC MLD_FIPS204_SIGN_SPLIT_BOUND THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MLD_FIPS204_SIGN_BYTELIST_SPLIT THEN ASM_REWRITE_TAC[]]);;

let MLD_FIPS204_SIGN_RHOPRIME = prove
 (`!(key:num->byte) rnd mu.
        rnd < 2 EXP 256 /\ mu < 2 EXP 512
        ==> bytelist_of_num 64 (mld_sign_rhoprime key rnd mu) =
            mldsa_h (APPEND (list_of_seq key 32)
                            (APPEND (bytelist_of_num 32 rnd)
                                    (bytelist_of_num 64 mu))) 64`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_sign_rhoprime; mldsa_h; MLD_FIPS204_SIGN_BYTELIST_NUM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`128`; `32`; `96`; `256`;
                `num_of_bytelist(list_of_seq (key:num->byte) 32)`;
                `rnd + 2 EXP 256 * mu`]
               MLD_FIPS204_SIGN_SHAKE256_APPEND) THEN
  REWRITE_TAC[MLD_FIPS204_SIGN_BYTELIST_NUM] THEN
  MP_TAC(SPECL [`96`; `32`; `64`; `256`; `rnd:num`; `mu:num`]
               MLD_FIPS204_SIGN_BYTELIST_SPLIT) THEN
  MP_TAC(SPECL [`32`; `64`; `256`; `rnd:num`; `mu:num`]
               MLD_FIPS204_SIGN_SPLIT_BOUND) THEN
  MP_TAC(ISPECL [`key:num->byte`; `32`] MLD_FIPS204_SIGN_NUM_BOUND) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN ASM_MESON_TAC[]);;

let MLD_FIPS204_SIGN_CTILDE = prove
 (`!k w1p mu (w1:num->byte).
        mu < 2 EXP 512
        ==> mld_sign_ctilde k w1p mu w1 =
            shake256 (APPEND (bytelist_of_num 64 mu)
                             (list_of_seq w1 (k * w1p)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_sign_ctilde] THEN
  MP_TAC(SPECL [`64 + k * w1p`; `64`; `k * w1p`; `512`; `mu:num`;
                `num_of_bytelist(list_of_seq (w1:num->byte) (k * w1p))`]
               MLD_FIPS204_SIGN_SHAKE256_APPEND) THEN
  ASM_REWRITE_TAC[MLD_FIPS204_SIGN_NUM_BOUND;
                  MLD_FIPS204_SIGN_BYTELIST_NUM] THEN
  ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* FIPS 204 signing from mu is the first attempt n (counter kappa = l * n)   *)
(* that is not rejected: mld_fips204_sign_attempt is attempt n of            *)
(* mldsa_sign_mu, with the secret key decoded as there.                      *)
(* ------------------------------------------------------------------------- *)

let mld_fips204_sign_attempt = new_definition
 `mld_fips204_sign_attempt
    ((k,l,eta,tau,lam,gamma1,gamma2,omega):mldsa_params)
    (sk:byte list) (mu:byte list) (rnd:byte list) n =
    let c = mldsa_bitlen(2 * eta) in
    let rho = mldsa_slice 0 32 sk and key = mldsa_slice 32 32 sk in
    let s1b = mldsa_slice 128 (32 * c * l) sk
    and s2b = mldsa_slice (128 + 32 * c * l) (32 * c * k) sk
    and t0b = mldsa_slice (128 + 32 * c * (l + k)) (416 * k) sk in
    let s1 = \i. mldsa_poly(\j. &eta - mldsa_field c s1b (256 * i + j)) in
    let s2 = \i. mldsa_poly(\j. &eta - mldsa_field c s2b (256 * i + j)) in
    let t0 = \i. mldsa_poly(\j. &4096 - mldsa_field 13 t0b (256 * i + j)) in
    let rho'' = mldsa_h (APPEND key (APPEND rnd mu)) 64 in
    mldsa_sign_attempt (k,l,eta,tau,lam,gamma1,gamma2,omega)
     (mldsa_expand_a rho) s1 s2 t0 mu rho'' (l * n)`;;

let MLD_FIPS204_SIGN_MU_ATTEMPT = prove
 (`!p sk mu rnd.
        mldsa_sign_mu p sk mu rnd =
        if ?n. ~(mld_fips204_sign_attempt p sk mu rnd n = NONE)
        then mld_fips204_sign_attempt p sk mu rnd
              (minimal n. ~(mld_fips204_sign_attempt p sk mu rnd n = NONE))
        else NONE`,
  REWRITE_TAC[FORALL_PAIR_THM; mldsa_sign_mu; mld_fips204_sign_attempt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One coefficient of w = A y as mld_sign_w computes it: the inverse NTT     *)
(* only reads the 256 coefficients of its argument, so polynomial i of the   *)
(* product of the matrix with y^ is the pointwise product of row i, whose    *)
(* inverse NTT the lemmas MLD_FIPS204_INVNTT_ACC_L4, _L5 and _L7 give for    *)
(* l = 4, 5 and 7 (the hypothesis below, a statement about l); mld_caddq     *)
(* then makes it the coefficient of the element of R_q.                      *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_INVNTT_LOCAL = prove
 (`!x y:num->int32 i.
        (!j. j < 256 ==> x j = y j) /\ i < 256
        ==> mld_poly_invntt_tomont x i = mld_poly_invntt_tomont y i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_poly_invntt_tomont] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!n. n <= 8
        ==> !i. i < 256 ==> mld_invntt_layers n x i = mld_invntt_layers n y i`
   (fun th -> ASM_SIMP_TAC[th; LE_REFL]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[mld_invntt_layers] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[MLD_INVNTT_BLOCKS_LOCAL] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `8 - (8 - n) = n` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mld_invntt_block] THEN
  ABBREV_TAC `L = 2 EXP n` THEN
  SUBGOAL_THEN `256 = 2 * L * 2 EXP (7 - n)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP); GSYM EXP_ADD] THEN
    SUBGOAL_THEN `SUC(n + 7 - n) = 8` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `j < 2 * L * j DIV (2 * L) + L ==> j + L < 256`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `2 * L * (j DIV (2 * L) + 1) <= 256` MP_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
      SUBGOAL_THEN `~(2 * L = 0)` ASSUME_TAC THENL
       [EXPAND_TAC "L" THEN REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
        ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_SIMP_TAC[ARITH_RULE `j < 256 ==> j - L < 256`]);;

let MLD_FIPS204_SIGN_W = prove
 (`!l. (!(u:num->int32) (v:num->int32) (Y:num->(1->num)->int).
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
                      < &8380417)
       ==> !k rho (y:num->int32) (Y:num->(1->num)->int) i m.
             mld_matrix_terminates k l rho /\ rho < 2 EXP 256 /\
             k <= 256 /\ l <= 256 /\ i < k /\ m < 256 /\
             (!j. j < l ==> Y j IN ring_carrier mldsa_rq) /\
             (!j n. j < l /\ n < 256
                    ==> (ival(y(256 * j + n)) == coeff n (Y j))
                        (mod &8380417) /\
                        abs(ival(y(256 * j + n))) < &8380417)
             ==> ival(mld_sign_w l (mld_polyvec_matrix_expand l rho) y
                       (256 * i + m)) =
                 coeff m (mldsa_dot l
                           (mldsa_expand_a (bytelist_of_num 32 rho) i) Y)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "acc") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u = \j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j)` THEN
  SUBGOAL_THEN
   `!j n. j < l /\ n < 256
          ==> ival((u:num->int32)(256 * j + n)) =
              &(val(mld_polyvec_matrix_expand l rho
                     (256 * (l * i + j) + n))) /\
              &0 <= ival(u(256 * j + n)) /\ ival(u(256 * j + n)) < &8380417`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    EXPAND_TAC "u" THEN BETA_TAC THEN
    REWRITE_TAC[ARITH_RULE
     `(256 * l) * i + 256 * j + n = 256 * (l * i + j) + n`] THEN
    MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `i:num`; `j:num`; `n:num`]
                 MLD_FIPS204_MATRIX_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MLDSA_REJ_NTT_POLY_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j n. j < l /\ n < 256
          ==> (ival(mld_polyvec_map mld_poly_ntt (y:num->int32)
                     (256 * j + n)) ==
               mldsa_ntt ((Y:num->(1->num)->int) j) n) (mod &8380417) /\
              abs(ival(mld_polyvec_map mld_poly_ntt y (256 * j + n)))
              < &94279689`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`l:num`; `y:num->int32`] MLD_FIPS204_POLYVEC_NTT) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t DIV 256`; `t MOD 256`] o
        check (fun th -> is_forall(concl th) &&
                         free_in `y:num->int32` (concl th))) THEN
      REWRITE_TAC[ARITH_RULE `256 * t DIV 256 + t MOD 256 = t`] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `mldsa_poly (\i. ival((y:num->int32)(256 * j + i))) =
      (Y:num->(1->num)->int) j`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[MLDSA_POLY_EQ];
    ALL_TAC] THEN
  USE_THEN "acc" (MP_TAC o SPECL
   [`u:num->int32`; `mld_polyvec_map mld_poly_ntt (y:num->int32)`;
    `Y:num->(1->num)->int`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `m:num`)] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mld_sign_w l (mld_polyvec_matrix_expand l rho) y (256 * i + m) =
    mld_caddq (mld_poly_invntt_tomont
     (mld_polyvec_pointwise_acc_montgomery l u
       (mld_polyvec_map mld_poly_ntt y)) m)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[mld_sign_w; MLD_POLYVEC_MAP_COEFF] THEN
    REWRITE_TAC[mld_poly_caddq] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP] THEN
    MATCH_MP_TAC MLD_FIPS204_SIGN_INVNTT_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:num` THEN DISCH_TAC THEN EXPAND_TAC "u" THEN
    ASM_SIMP_TAC[mld_poly_of; MLD_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_COEFF];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MLD_CADDQ_REM] THEN
  SUBGOAL_THEN
   `mldsa_dot l (\j. mldsa_ntt_inv (\m. ival((u:num->int32)(256 * j + m))))
     Y = mldsa_dot l (mldsa_expand_a (bytelist_of_num 32 rho) i) Y`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC MLDSA_DOT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `i:num`; `j:num`]
                 MLD_FIPS204_EXPAND_A) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INT_REM_UNIQUE] THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_SIMP_TAC[MLDSA_RQ_COEFF; MLDSA_DOT_IN_RQ]);;

(* ------------------------------------------------------------------------- *)
(* The challenge in the NTT domain (mld_sign_cphat): when its sampling       *)
(* terminates, it represents SampleInBall of c~, with coefficients in        *)
(* [-1,1] and so within the bound of the NTT.                                *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_CPHAT = prove
 (`!tau ctlen (ct:num->byte) k.
        mld_poly_challenge_terminates tau ctlen
         (num_of_bytelist(list_of_seq ct ctlen)) /\ k < 256
        ==> (ival(mld_sign_cphat tau ctlen ct k) ==
             mldsa_ntt (mldsa_sample_in_ball tau (list_of_seq ct ctlen)) k)
            (mod &8380417) /\
            abs(ival(mld_sign_cphat tau ctlen ct k)) < &94279689`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_sign_cphat] THEN
  ABBREV_TAC `C = num_of_bytelist(list_of_seq (ct:num->byte) ctlen)` THEN
  SUBGOAL_THEN `C < 2 EXP (8 * ctlen)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[MLD_FIPS204_SIGN_NUM_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `list_of_seq (ct:num->byte) ctlen = bytelist_of_num ctlen C`
  SUBST1_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[MLD_FIPS204_SIGN_BYTELIST_NUM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tau:num`; `ctlen:num`; `C:num`]
               MLD_FIPS204_POLY_CHALLENGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPEC `mld_poly_challenge tau ctlen C` MLD_FIPS204_POLY_NTT) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`tau:num`; `ctlen:num`; `C:num`]
                 MLD_FIPS204_POLY_CHALLENGE_COEFFS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(INT_ARITH `abs(x:int) <= &1 ==> abs x < &8380417`) THEN
    REWRITE_TAC[MLDSA_BALL_COEFFS_BOUND];
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* One coefficient of z = y + c s1 (mld_sign_z), of w0 - c s2 (mld_sign_r0,  *)
(* with dlo giving LowBits of the coefficients of w in [0,q)) and of c t0    *)
(* (mld_sign_ct0): congruent to that of the element of R_q and in the range  *)
(* of mld_reduce32, given that s1hat, s2hat, t0hat and cphat represent the   *)
(* NTTs of s1, s2, t0 and c within the NTT bound.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_Z = prove
 (`!(s1hat:num->int32) (cphat:num->int32) (y:num->int32) S1 c Y i m.
        S1 IN ring_carrier mldsa_rq /\ c IN ring_carrier mldsa_rq /\
        Y IN ring_carrier mldsa_rq /\ m < 256 /\
        (!k. k < 256
             ==> (ival(s1hat(256 * i + k)) == mldsa_ntt S1 k) (mod &8380417) /\
                 abs(ival(s1hat(256 * i + k))) < &94279689) /\
        (!k. k < 256
             ==> (ival(cphat k) == mldsa_ntt c k) (mod &8380417) /\
                 abs(ival(cphat k)) < &94279689) /\
        (!k. k < 256
             ==> (ival(y(256 * i + k)) == coeff k Y) (mod &8380417) /\
                 abs(ival(y(256 * i + k))) <= &524288)
        ==> (ival(mld_sign_z s1hat cphat y i m) ==
             coeff m (ring_add mldsa_rq Y (ring_mul mldsa_rq c S1)))
            (mod &8380417) /\
            --(&6283009) <= ival(mld_sign_z s1hat cphat y i m) /\
            ival(mld_sign_z s1hat cphat y i m) < &6283009`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mld_poly_of (s1hat:num->int32) i`; `cphat:num->int32`;
                `S1:(1->num)->int`; `c:(1->num)->int`]
               MLD_FIPS204_INVNTT_POINTWISE) THEN
  ASM_REWRITE_TAC[mld_poly_of] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
  ASM_REWRITE_TAC[mld_sign_z; mld_poly_reduce; mld_poly_add; mld_poly_of] THEN
  ABBREV_TAC
   `X = mld_poly_invntt_tomont
         (mld_poly_pointwise_montgomery (\i'. s1hat(256 * i + i')) cphat)
         m` THEN
  ABBREV_TAC `Z = (y:num->int32)(256 * i + m)` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o
    check (fun th -> is_forall(concl th) &&
                     free_in `y:num->int32` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word_add X Z:int32) = ival X + ival Z` ASSUME_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_IVAL_WORD_ADD THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `word_add X Z:int32` MLD_FIPS204_REDUCE32) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MLDSA_RQ_COEFF_ADD; RING_MUL] THEN
  SUBGOAL_THEN `ring_mul mldsa_rq c S1 = ring_mul mldsa_rq S1 c`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[INT_CONG_RREM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `(x:int == y) (mod n)`) (concl th)))) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN CONV_TAC INTEGER_RULE);;

let MLD_FIPS204_SIGN_R0 = prove
 (`!(dlo:(num->int32)->num->int32) (w:num->int32) (s2hat:num->int32)
    (cphat:num->int32) W S2 c gamma2 j m.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        W IN ring_carrier mldsa_rq /\ S2 IN ring_carrier mldsa_rq /\
        c IN ring_carrier mldsa_rq /\ m < 256 /\
        (!a i. &0 <= ival(a i) /\ ival(a i) < &8380417
               ==> ival(dlo a i) = mldsa_lowbits gamma2 (ival(a i))) /\
        (!k. k < 256 ==> ival(w(256 * j + k)) = coeff k W) /\
        (!k. k < 256
             ==> (ival(s2hat(256 * j + k)) == mldsa_ntt S2 k) (mod &8380417) /\
                 abs(ival(s2hat(256 * j + k))) < &94279689) /\
        (!k. k < 256
             ==> (ival(cphat k) == mldsa_ntt c k) (mod &8380417) /\
                 abs(ival(cphat k)) < &94279689)
        ==> (ival(mld_sign_r0 dlo w s2hat cphat j m) ==
             coeff m (ring_sub mldsa_rq
                       (mldsa_poly(\i. mldsa_lowbits gamma2 (coeff i W)))
                       (ring_mul mldsa_rq c S2)))
            (mod &8380417) /\
            --(&6283009) <= ival(mld_sign_r0 dlo w s2hat cphat j m) /\
            ival(mld_sign_r0 dlo w s2hat cphat j m) < &6283009`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mld_poly_of (s2hat:num->int32) j`; `cphat:num->int32`;
                `S2:(1->num)->int`; `c:(1->num)->int`]
               MLD_FIPS204_INVNTT_POINTWISE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[mld_poly_of]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `X = mld_poly_invntt_tomont
         (mld_poly_pointwise_montgomery (mld_poly_of s2hat j) cphat) m` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `ival((dlo:(num->int32)->num->int32) (mld_poly_of w j) m) =
    mldsa_lowbits gamma2 (coeff m W)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`mld_poly_of (w:num->int32) j`; `m:num`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `dlo:(num->int32)->num->int32` (concl th))) THEN
    ASM_SIMP_TAC[mld_poly_of; MLDSA_RQ_COEFF];
    ALL_TAC] THEN
  ABBREV_TAC `D = (dlo:(num->int32)->num->int32) (mld_poly_of w j) m` THEN
  SUBGOAL_THEN `abs(ival(D:int32)) <= &4190208` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN TRANS_TAC INT_LE_TRANS `&gamma2:int` THEN
    ASM_SIMP_TAC[MLDSA_LOWBITS_BOUND; INT_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mld_sign_r0; mld_poly_reduce; mld_poly_sub] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ival(word_sub D X:int32) = ival D - ival X` ASSUME_TAC THENL
   [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `word_sub D X:int32` MLD_FIPS204_REDUCE32) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MLDSA_RQ_COEFF_SUB; MLDSA_POLY_IN_RQ; RING_MUL;
               COEFF_MLDSA_POLY] THEN
  SUBGOAL_THEN `ring_mul mldsa_rq c S2 = ring_mul mldsa_rq S2 c`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[INT_CONG_RREM] THEN
  MP_TAC(ISPECL [`mldsa_lowbits gamma2 (coeff m (W:(1->num)->int))`;
                 `&8380417:int`] INT_REM_MOD_SELF) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `(x:int == y) (mod n)`) (concl th)))) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN CONV_TAC INTEGER_RULE);;

let MLD_FIPS204_SIGN_CT0 = prove
 (`!(t0hat:num->int32) (cphat:num->int32) T0 c j m.
        T0 IN ring_carrier mldsa_rq /\ c IN ring_carrier mldsa_rq /\
        m < 256 /\
        (!k. k < 256
             ==> (ival(t0hat(256 * j + k)) == mldsa_ntt T0 k) (mod &8380417) /\
                 abs(ival(t0hat(256 * j + k))) < &94279689) /\
        (!k. k < 256
             ==> (ival(cphat k) == mldsa_ntt c k) (mod &8380417) /\
                 abs(ival(cphat k)) < &94279689)
        ==> (ival(mld_sign_ct0 t0hat cphat j m) ==
             coeff m (ring_mul mldsa_rq c T0)) (mod &8380417) /\
            --(&6283009) <= ival(mld_sign_ct0 t0hat cphat j m) /\
            ival(mld_sign_ct0 t0hat cphat j m) < &6283009`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mld_poly_of (t0hat:num->int32) j`; `cphat:num->int32`;
                `T0:(1->num)->int`; `c:(1->num)->int`]
               MLD_FIPS204_INVNTT_POINTWISE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[mld_poly_of]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `X = mld_poly_invntt_tomont
         (mld_poly_pointwise_montgomery (mld_poly_of t0hat j) cphat) m` THEN
  STRIP_TAC THEN
  REWRITE_TAC[mld_sign_ct0; mld_poly_reduce] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `X:int32` MLD_FIPS204_REDUCE32) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `ring_mul mldsa_rq c T0 = ring_mul mldsa_rq T0 c`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `(x:int == y) (mod n)`) (concl th)))) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* The checks of an attempt: mld_sign_rej gives l + 2 * k + 1 exactly when   *)
(* all of them pass, and for coefficients that represent elements of R_q in  *)
(* the range of mld_reduce32 the norm checks of the polynomials of a vector  *)
(* are the bound on its infinity norm.                                       *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_REJ = prove
 (`!k l bndz bndw bndh omega (mkhint:(num->int32)->(num->byte)->num->bool)
    (z:num->num->int32) (r0:num->num->int32) (ct0:num->num->int32)
    (x:num->int32) (w1:num->byte).
        mld_sign_rej k l bndz bndw bndh omega mkhint z r0 ct0 x w1 =
        l + 2 * k + 1 <=>
        (!i. i < l ==> mld_poly_chknorm (z i) (word bndz) = word 0) /\
        (!j. j < k ==> mld_poly_chknorm (r0 j) (word bndw) = word 0) /\
        (!j. j < k ==> mld_poly_chknorm (ct0 j) (word bndh) = word 0) /\
        mld_hint_count (mkhint x w1) (256 * k) <= omega`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_sign_rej] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o BETA_RULE o
                  GEN_REWRITE_RULE I [MINIMAL]) THEN ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o BETA_RULE o
                  GEN_REWRITE_RULE I [MINIMAL]) THEN ARITH_TAC;
      SUBGOAL_THEN `!j. j < 2 * k ==> j DIV 2 < k` ASSUME_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` MP_TAC o
                    check (is_exists o concl)) THEN
      ASM_CASES_TAC `EVEN j` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(l + 2 * k = l + 2 * k + 1)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2 * j` o
                  check (free_in `bndw:num` o concl)) THEN
    REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * j) DIV 2 = j`] THEN
    MATCH_MP_TAC(TAUT `p ==> (~p \/ q ==> q)`) THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2 * j + 1` o
                  check (free_in `bndw:num` o concl)) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_DOUBLE; ARITH_EVEN;
                ARITH_RULE `(2 * j + 1) DIV 2 = j`] THEN
    MATCH_MP_TAC(TAUT `p ==> (~p \/ q ==> q)`) THEN ASM_ARITH_TAC]);;

let MLD_FIPS204_SIGN_CHKNORM = prove
 (`!n B (a:num->num->int32) (f:num->(1->num)->int).
        B <= 2097408 /\
        (!i. i < n ==> f i IN ring_carrier mldsa_rq) /\
        (!i m. i < n /\ m < 256
               ==> (ival(a i m) == coeff m (f i)) (mod &8380417) /\
                   --(&6283009) <= ival(a i m) /\ ival(a i m) < &6283009)
        ==> ((!i. i < n ==> mld_poly_chknorm (a i) (word B) = word 0) <=>
             mldsa_vec_norm_lt n B f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_vec_norm_lt] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `i < n` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(a:num->num->int32) i`; `B:num`]
                MLD_FIPS204_POLY_CHKNORM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[MLDSA_POLY_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The C functions of the parameter sets, in the forms that the attempt      *)
(* theorems below assume: the bound of the coefficients of y, the packing of *)
(* z for gamma1 = 2^17 and 2^19, and the packing of w1, the low part and the *)
(* hints for gamma2 = (q - 1) / 88 and (q - 1) / 32, the high parts that the *)
(* hints use being unpacked from w1 packed.                                  *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_FIELD_TAC c =
  W(fun (asl,w) ->
    let t = find_term (can (term_match [] (subst [c,`c:num`]
                         `mldsa_field c b i`))) w in
    MP_TAC(ISPECL [rand(rator t); rand t] (SPEC c MLDSA_FIELD_BOUND))) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC;;

let MLD_FIPS204_SIGN_GAMMA1_17_BOUND = prove
 (`!seed (nonce:int16) i.
        i < 256
        ==> abs(ival(mld_poly_uniform_gamma1_17 seed nonce i)) <= &131072`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mld_poly_uniform_gamma1_17;
               MLD_FIPS204_SAMPLE_POLYZ_UNPACK_17] THEN
  MLD_FIPS204_SIGN_FIELD_TAC `18`);;

let MLD_FIPS204_SIGN_GAMMA1_19_BOUND = prove
 (`!seed (nonce:int16) i.
        i < 256
        ==> abs(ival(mld_poly_uniform_gamma1_19 seed nonce i)) <= &524288`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mld_poly_uniform_gamma1_19;
               MLD_FIPS204_SAMPLE_POLYZ_UNPACK_19] THEN
  MLD_FIPS204_SIGN_FIELD_TAC `20`);;

let MLD_FIPS204_SIGN_ZPACK_17 = prove
 (`!m (x:num->int32).
        (!i. i < 256 * m
             ==> --(&131072) < ival(x i) /\ ival(x i) <= &131072)
        ==> list_of_seq (mld_polyvec_pack 576 mld_polyz_pack_17 x) (m * 576) =
            mldsa_encode (1 + mldsa_bitlen(131072 - 1)) (256 * m)
             (\i. &131072 - ival(x i))`,
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[ARITH_RULE `m * 576 = 576 * m`] THEN
  MATCH_MP_TAC MLD_FIPS204_POLYVEC_Z_PACK_17 THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let MLD_FIPS204_SIGN_ZPACK_19 = prove
 (`!m (x:num->int32).
        (!i. i < 256 * m
             ==> --(&524288) < ival(x i) /\ ival(x i) <= &524288)
        ==> list_of_seq (mld_polyvec_pack 640 mld_polyz_pack_19 x) (m * 640) =
            mldsa_encode (1 + mldsa_bitlen(524288 - 1)) (256 * m)
             (\i. &524288 - ival(x i))`,
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[ARITH_RULE `m * 640 = 640 * m`] THEN
  MATCH_MP_TAC MLD_FIPS204_POLYVEC_Z_PACK_19 THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let MLD_FIPS204_SIGN_W1_88 = prove
 (`!m (w:num->int32).
        (!n. n < 256 * m ==> &0 <= ival(w n) /\ ival(w n) < &8380417)
        ==> list_of_seq
             (mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192 w)
             (m * 192) =
            mldsa_encode (mldsa_bitlen(8380416 DIV (2 * 95232) - 1)) (256 * m)
             (\n. mldsa_highbits 95232 (ival(w n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_sign_w1] THEN
  SUBGOAL_THEN
   `mld_polyvec_pack 192 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) w =
    mld_polyvec_pack 192 mld_polyw1_pack_88
     (\n. mld_decompose_hi_88 ((w:num->int32) n))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_POLYVEC_PACK_O THEN
    REWRITE_TAC[mld_poly_decompose_hi_88];
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `m * 192 = 192 * m`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_POLYVEC_W1_PACK_88 o
    lhand o snd) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPEC `(w:num->int32) i` MLD_FIPS204_DECOMPOSE_88_BOUNDS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MLDSA_ENCODE_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_DECOMPOSE_88]);;

let MLD_FIPS204_SIGN_W1_32 = prove
 (`!m (w:num->int32).
        (!n. n < 256 * m ==> &0 <= ival(w n) /\ ival(w n) < &8380417)
        ==> list_of_seq
             (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128 w)
             (m * 128) =
            mldsa_encode (mldsa_bitlen(8380416 DIV (2 * 261888) - 1)) (256 * m)
             (\n. mldsa_highbits 261888 (ival(w n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_sign_w1] THEN
  SUBGOAL_THEN
   `mld_polyvec_pack 128 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) w =
    mld_polyvec_pack 128 mld_polyw1_pack_32
     (\n. mld_decompose_hi_32 ((w:num->int32) n))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_POLYVEC_PACK_O THEN
    REWRITE_TAC[mld_poly_decompose_hi_32];
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `m * 128 = 128 * m`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_POLYVEC_W1_PACK_32 o
    lhand o snd) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPEC `(w:num->int32) i` MLD_FIPS204_DECOMPOSE_32_BOUNDS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MLDSA_ENCODE_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_DECOMPOSE_32]);;

let MLD_FIPS204_SIGN_DLO_88 = prove
 (`!(a:num->int32) i.
        &0 <= ival(a i) /\ ival(a i) < &8380417
        ==> ival(mld_poly_decompose_lo_88 a i) =
            mldsa_lowbits 95232 (ival(a i))`,
  SIMP_TAC[MLD_FIPS204_POLY_DECOMPOSE_88]);;

let MLD_FIPS204_SIGN_DLO_32 = prove
 (`!(a:num->int32) i.
        &0 <= ival(a i) /\ ival(a i) < &8380417
        ==> ival(mld_poly_decompose_lo_32 a i) =
            mldsa_lowbits 261888 (ival(a i))`,
  SIMP_TAC[MLD_FIPS204_POLY_DECOMPOSE_32]);;

let MLD_FIPS204_SIGN_MAKE_HINT_88 = prove
 (`!m (lo:(num->int32)->num->int32) (w:num->int32) (s2h:num->int32)
    (t0h:num->int32) (cp:num->int32)
    (r0:num->(1->num)->int) (ct0:num->(1->num)->int).
        (!p. p < 256 * m ==> &0 <= ival(w p) /\ ival(w p) < &8380417) /\
        (!j. j < m ==> r0 j IN ring_carrier mldsa_rq /\
                       ct0 j IN ring_carrier mldsa_rq) /\
        (!j i. j < m /\ i < 256
               ==> (ival(mld_sign_r0 lo w s2h cp j i) == coeff i (r0 j))
                   (mod &8380417) /\
                   (ival(mld_sign_ct0 t0h cp j i) == coeff i (ct0 j))
                   (mod &8380417) /\
                   abs(ival(mld_sign_r0 lo w s2h cp j i)) < &95232 /\
                   abs(ival(mld_sign_ct0 t0h cp j i)) < &95232)
        ==> mld_polyvec_make_hint_88 (mld_sign_hint_x m lo w s2h t0h cp)
             (mld_sign_hint_w1 m 192
               (mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
                            192 w)) =
            \p. p < 256 * m /\
                let v = mldsa_modpm
                         (coeff (p MOD 256)
                           (ring_add mldsa_rq (r0(p DIV 256)) (ct0(p DIV 256))))
                         8380417 in
                ~(--(&95232) < v /\ v <= &95232 \/
                  mldsa_highbits 95232 (ival(w p)) = &0 /\ v = --(&95232))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`m:num`; `lo:(num->int32)->num->int32`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cp:num->int32`;
    `mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192 w`;
    `r0:num->(1->num)->int`; `ct0:num->(1->num)->int`;
    `\p. mldsa_highbits 95232 (ival((w:num->int32) p))`]
   MLD_FIPS204_SIGN_HINT_88) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN(ACCEPT_TAC o BETA_RULE)] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[mld_sign_w1] THEN
  SUBGOAL_THEN
   `mld_polyvec_pack 192 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) w =
    mld_polyvec_pack 192 mld_polyw1_pack_88
     (\n. mld_decompose_hi_88 ((w:num->int32) n))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_POLYVEC_PACK_O THEN
    REWRITE_TAC[mld_poly_decompose_hi_88];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`m:num`; `\n. mld_decompose_hi_88 ((w:num->int32) n)`;
    `mld_polyvec_pack 192 mld_polyw1_pack_88
      (\n. mld_decompose_hi_88 ((w:num->int32) n))`; `p:num`]
   MLD_FIPS204_POLYVEC_W1_UNPACK_PACK_88) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPEC `(w:num->int32) i` MLD_FIPS204_DECOMPOSE_88_BOUNDS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_DECOMPOSE_88]]);;

let MLD_FIPS204_SIGN_MAKE_HINT_32 = prove
 (`!m (lo:(num->int32)->num->int32) (w:num->int32) (s2h:num->int32)
    (t0h:num->int32) (cp:num->int32)
    (r0:num->(1->num)->int) (ct0:num->(1->num)->int).
        (!p. p < 256 * m ==> &0 <= ival(w p) /\ ival(w p) < &8380417) /\
        (!j. j < m ==> r0 j IN ring_carrier mldsa_rq /\
                       ct0 j IN ring_carrier mldsa_rq) /\
        (!j i. j < m /\ i < 256
               ==> (ival(mld_sign_r0 lo w s2h cp j i) == coeff i (r0 j))
                   (mod &8380417) /\
                   (ival(mld_sign_ct0 t0h cp j i) == coeff i (ct0 j))
                   (mod &8380417) /\
                   abs(ival(mld_sign_r0 lo w s2h cp j i)) < &261888 /\
                   abs(ival(mld_sign_ct0 t0h cp j i)) < &261888)
        ==> mld_polyvec_make_hint_32 (mld_sign_hint_x m lo w s2h t0h cp)
             (mld_sign_hint_w1 m 128
               (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                            128 w)) =
            \p. p < 256 * m /\
                let v = mldsa_modpm
                         (coeff (p MOD 256)
                           (ring_add mldsa_rq (r0(p DIV 256)) (ct0(p DIV 256))))
                         8380417 in
                ~(--(&261888) < v /\ v <= &261888 \/
                  mldsa_highbits 261888 (ival(w p)) = &0 /\
                  v = --(&261888))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`m:num`; `lo:(num->int32)->num->int32`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cp:num->int32`;
    `mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128 w`;
    `r0:num->(1->num)->int`; `ct0:num->(1->num)->int`;
    `\p. mldsa_highbits 261888 (ival((w:num->int32) p))`]
   MLD_FIPS204_SIGN_HINT_32) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN(ACCEPT_TAC o BETA_RULE)] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[mld_sign_w1] THEN
  SUBGOAL_THEN
   `mld_polyvec_pack 128 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) w =
    mld_polyvec_pack 128 mld_polyw1_pack_32
     (\n. mld_decompose_hi_32 ((w:num->int32) n))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_POLYVEC_PACK_O THEN
    REWRITE_TAC[mld_poly_decompose_hi_32];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`m:num`; `\n. mld_decompose_hi_32 ((w:num->int32) n)`;
    `mld_polyvec_pack 128 mld_polyw1_pack_32
      (\n. mld_decompose_hi_32 ((w:num->int32) n))`; `p:num`]
   MLD_FIPS204_POLYVEC_W1_UNPACK_PACK_32) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPEC `(w:num->int32) i` MLD_FIPS204_DECOMPOSE_32_BOUNDS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_DECOMPOSE_32]]);;

(* ------------------------------------------------------------------------- *)
(* The signature c~ || z packed || hints as a list of three parts.           *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_LIST_OF_SEQ3 = prove
 (`!(a:num->A) b c m n p.
        list_of_seq (\t. if t < m then a t
                         else if t < m + n then b(t - m)
                         else c(t - (m + n))) (m + n + p) =
        APPEND (list_of_seq a m) (APPEND (list_of_seq b n) (list_of_seq c p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLD_LIST_OF_SEQ_ADD] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[];
    BINOP_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    SIMP_TAC[ARITH_RULE `~(m + i < m) /\ (i < n ==> m + i < m + n) /\
                         ~(m + n + i < m + n) /\ (m + i) - m = i /\
                         (m + n + i) - (m + n) = i`] THEN
    REWRITE_TAC[ADD_ASSOC; ARITH_RULE `~(m + n + i < m)`]]);;

(* ------------------------------------------------------------------------- *)
(* One whole attempt (mld_sign_attempt_rej and mld_sign_attempt_sig) as the  *)
(* attempt of Section 5.1 (mldsa_sign_attempt_alt), for the matrix expanded  *)
(* from rho, any s1, s2 and t0 in R_q represented by s1hat, s2hat and t0hat  *)
(* in the NTT domain, and the C functions g1 (y), zpack (z), w1enc (w1),     *)
(* dlo (w0) and mkhint (the hints) of a parameter set, given by their        *)
(* properties as hypotheses: the C attempt passes its checks exactly when    *)
(* the alternative one is not rejected, and then its signature is the        *)
(* alternative one.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_ATTEMPT_ALT = prove
 (`!k l eta tau lam gamma1 gamma2 omega ctlen (g1:num->int16->num->int32)
    (zpack:(num->int32)->num->byte) zp bndz bndw bndh
    (w1enc:(num->int32)->num->byte) w1p (dlo:(num->int32)->num->int32)
    (mkhint:(num->int32)->(num->byte)->num->bool)
    rho (s1hat:num->int32) (s2hat:num->int32) (t0hat:num->int32)
    (S1:num->(1->num)->int) (S2:num->(1->num)->int) (T0:num->(1->num)->int)
    mu rhoprime kappa.
        (!(u:num->int32) (v:num->int32) (Y:num->(1->num)->int).
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
                        < &8380417) /\
        (!seed nonce kappa r.
            seed < 2 EXP 512 /\ val nonce = (kappa + r) MOD 65536
            ==> mldsa_poly (\i. ival(g1 seed nonce i)) =
                mldsa_expand_mask gamma1 (bytelist_of_num 64 seed) kappa r) /\
        (!seed nonce i.
            i < 256 ==> abs(ival(g1 seed nonce i)) <= &gamma1) /\
        (!m (x:num->int32).
            (!i. i < 256 * m
                 ==> --(&gamma1) < ival(x i) /\ ival(x i) <= &gamma1)
            ==> list_of_seq (mld_polyvec_pack zp zpack x) (m * zp) =
                mldsa_encode (1 + mldsa_bitlen(gamma1 - 1)) (256 * m)
                 (\i. &gamma1 - ival(x i))) /\
        (!m (w:num->int32).
            (!n. n < 256 * m ==> &0 <= ival(w n) /\ ival(w n) < &8380417)
            ==> list_of_seq (mld_sign_w1 w1enc w1p w) (m * w1p) =
                mldsa_encode (mldsa_bitlen(8380416 DIV (2 * gamma2) - 1))
                 (256 * m) (\n. mldsa_highbits gamma2 (ival(w n)))) /\
        (!(a:num->int32) i.
            &0 <= ival(a i) /\ ival(a i) < &8380417
            ==> ival(dlo a i) = mldsa_lowbits gamma2 (ival(a i))) /\
        (!m (lo:(num->int32)->num->int32) (w:num->int32) (s2h:num->int32)
          (t0h:num->int32) (cp:num->int32)
          (r0:num->(1->num)->int) (ct0:num->(1->num)->int).
            (!p. p < 256 * m ==> &0 <= ival(w p) /\ ival(w p) < &8380417) /\
            (!j. j < m ==> r0 j IN ring_carrier mldsa_rq /\
                           ct0 j IN ring_carrier mldsa_rq) /\
            (!j i. j < m /\ i < 256
                   ==> (ival(mld_sign_r0 lo w s2h cp j i) == coeff i (r0 j))
                       (mod &8380417) /\
                       (ival(mld_sign_ct0 t0h cp j i) == coeff i (ct0 j))
                       (mod &8380417) /\
                       abs(ival(mld_sign_r0 lo w s2h cp j i)) < &gamma2 /\
                       abs(ival(mld_sign_ct0 t0h cp j i)) < &gamma2)
            ==> mkhint (mld_sign_hint_x m lo w s2h t0h cp)
                       (mld_sign_hint_w1 m w1p (mld_sign_w1 w1enc w1p w)) =
                \p. p < 256 * m /\
                    let v = mldsa_modpm
                             (coeff (p MOD 256)
                               (ring_add mldsa_rq (r0(p DIV 256))
                                                  (ct0(p DIV 256))))
                             8380417 in
                    ~(--(&gamma2) < v /\ v <= &gamma2 \/
                      mldsa_highbits gamma2 (ival(w p)) = &0 /\
                      v = --(&gamma2))) /\
        k <= 256 /\ l <= 256 /\ gamma1 <= 524288 /\
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\ ctlen = lam DIV 4 /\
        bndz = gamma1 - tau * eta /\ bndw = gamma2 - tau * eta /\
        bndh = gamma2 /\
        mld_matrix_terminates k l rho /\ rho < 2 EXP 256 /\
        (!j. j < l ==> S1 j IN ring_carrier mldsa_rq) /\
        (!j. j < k ==> S2 j IN ring_carrier mldsa_rq /\
                       T0 j IN ring_carrier mldsa_rq) /\
        (!j m. j < l /\ m < 256
               ==> (ival(s1hat(256 * j + m)) == mldsa_ntt (S1 j) m)
                   (mod &8380417) /\
                   abs(ival(s1hat(256 * j + m))) < &94279689) /\
        (!j m. j < k /\ m < 256
               ==> (ival(s2hat(256 * j + m)) == mldsa_ntt (S2 j) m)
                   (mod &8380417) /\
                   abs(ival(s2hat(256 * j + m))) < &94279689 /\
                   (ival(t0hat(256 * j + m)) == mldsa_ntt (T0 j) m)
                   (mod &8380417) /\
                   abs(ival(t0hat(256 * j + m))) < &94279689) /\
        mu < 2 EXP 512 /\ rhoprime < 2 EXP 512 /\
        mld_poly_challenge_terminates tau ctlen
         (num_of_bytelist(list_of_seq
           (mld_sign_ctilde k w1p mu
             (mld_sign_w1 w1enc w1p
               (mld_sign_w l (mld_polyvec_matrix_expand l rho)
                 (mld_sign_y g1 rhoprime kappa))))
           ctlen))
        ==> mldsa_sign_attempt_alt (k,l,eta,tau,lam,gamma1,gamma2,omega)
             (mldsa_expand_a (bytelist_of_num 32 rho)) S1 S2 T0
             (bytelist_of_num 64 mu) (bytelist_of_num 64 rhoprime) kappa =
            if mld_sign_attempt_rej k l ctlen tau g1 bndz bndw bndh w1enc w1p
                dlo mkhint omega (mld_polyvec_matrix_expand l rho)
                s1hat s2hat t0hat mu rhoprime kappa = l + 2 * k + 1
            then SOME(list_of_seq
                   (mld_sign_attempt_sig k l ctlen tau g1 zpack zp w1enc w1p
                     dlo mkhint omega (mld_polyvec_matrix_expand l rho)
                     s1hat s2hat t0hat mu rhoprime kappa)
                   (ctlen + l * zp + omega + k))
            else NONE`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "acc") (CONJUNCTS_THEN2
   (LABEL_TAC "g1") (CONJUNCTS_THEN2 (LABEL_TAC "g1b") (CONJUNCTS_THEN2
   (LABEL_TAC "zpack") (CONJUNCTS_THEN2 (LABEL_TAC "w1") (CONJUNCTS_THEN2
   (LABEL_TAC "dlo") (CONJUNCTS_THEN2 (LABEL_TAC "hint")
   STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `bndz <= gamma1 /\ bndw <= gamma2 /\ gamma2 <= 2095104`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mldsa_sign_attempt_alt; mld_sign_attempt_rej;
              mld_sign_attempt_sig] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN

  (*** Abbreviations for the C values and the FIPS 204 values ***)

  ABBREV_TAC `yC = mld_sign_y g1 rhoprime kappa` THEN
  ABBREV_TAC `wC = mld_sign_w l (mld_polyvec_matrix_expand l rho) yC` THEN
  ABBREV_TAC `w1C = mld_sign_w1 w1enc w1p wC` THEN
  ABBREV_TAC `ctC = mld_sign_ctilde k w1p mu w1C` THEN
  ABBREV_TAC `cphat = mld_sign_cphat tau ctlen ctC` THEN
  ABBREV_TAC `fy = \i:num. mldsa_expand_mask gamma1
                            (bytelist_of_num 64 rhoprime) kappa i` THEN
  ABBREV_TAC `fw = \i:num. mldsa_dot l (mldsa_expand_a
                                         (bytelist_of_num 32 rho) i) fy` THEN
  ABBREV_TAC `fw1 = \n. mldsa_highbits gamma2
                         (coeff (n MOD 256)
                           ((fw:num->(1->num)->int)(n DIV 256)))` THEN
  ABBREV_TAC `fw0 = \i:num. mldsa_poly(\j. mldsa_lowbits gamma2
                              (coeff j ((fw:num->(1->num)->int) i)))` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> lhs(concl th) = `ctlen:num`)) THEN
  ABBREV_TAC `fct = mldsa_h (APPEND (bytelist_of_num 64 mu)
                    (mldsa_encode (mldsa_bitlen(8380416 DIV (2 * gamma2) - 1))
                                  (256 * k) fw1)) ctlen` THEN
  ABBREV_TAC `fc = mldsa_sample_in_ball tau fct` THEN
  ABBREV_TAC `fz = \i:num. ring_add mldsa_rq ((fy:num->(1->num)->int) i)
                    (ring_mul mldsa_rq fc ((S1:num->(1->num)->int) i))` THEN
  ABBREV_TAC `fr0 = \i:num. ring_sub mldsa_rq ((fw0:num->(1->num)->int) i)
                     (ring_mul mldsa_rq fc ((S2:num->(1->num)->int) i))` THEN
  ABBREV_TAC `fct0 = \i:num. ring_mul mldsa_rq fc
                              ((T0:num->(1->num)->int) i)` THEN
  W(fun (asl,w) ->
     let t = find_term (can (term_match [] `mldsa_hint_count h (256 * k)`))
                       w in
     ABBREV_TAC (mk_eq(`fh:num->bool`,rand(rator t)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> lhs(concl th) = `bndz:num`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> lhs(concl th) = `bndw:num`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
   (fun th -> lhs(concl th) = `bndh:num`)) THEN
  REWRITE_TAC[MLD_FIPS204_SIGN_REJ] THEN

  (*** y, w, c~ and the challenge ***)

  SUBGOAL_THEN
   `!j m. m < 256
          ==> (ival((yC:num->int32)(256 * j + m)) == coeff m (fy j))
              (mod &8380417) /\
              abs(ival(yC(256 * j + m))) <= &gamma1`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["yC"; "fy"] THEN
    SIMP_TAC[mld_sign_y; MLD_POLYVEC_COEFF; ASSUME `m < 256`] THEN
    USE_THEN "g1" (MP_TAC o SPECL
     [`rhoprime:num`; `word(kappa + j):int16`; `kappa:num`; `j:num`]) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_16; ASSUME `rhoprime < 2 EXP 512`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[COEFF_MLDSA_POLY; INT_CONG_RREM; INT_CONG_REFL] THEN
    USE_THEN "g1b" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i m. i < k /\ m < 256
          ==> ival((wC:num->int32)(256 * i + m)) = coeff m (fw i)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["wC"; "fw"] THEN BETA_TAC THEN
    USE_THEN "acc" (MP_TAC o MATCH_MP MLD_FIPS204_SIGN_W) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "fy" THEN REWRITE_TAC[MLDSA_EXPAND_MASK_IN_RQ];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      TRANS_TAC INT_LET_TRANS `&gamma1:int` THEN
      ASM_SIMP_TAC[INT_OF_NUM_LT] THEN
      UNDISCH_TAC `gamma1 <= 524288` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n < 256 * k
        ==> ival((wC:num->int32) n) = coeff (n MOD 256) (fw(n DIV 256)) /\
            &0 <= ival(wC n) /\ ival(wC n) < &8380417`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n DIV 256`; `n MOD 256`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `wC:num->int32` (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `256 * n DIV 256 + n MOD 256 = n`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `n < 256 * k` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MLDSA_RQ_COEFF THEN EXPAND_TAC "fw" THEN
    REWRITE_TAC[MLDSA_DOT_IN_RQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `fct = list_of_seq (ctC:num->byte) ctlen` SUBST_ALL_TAC THENL
   [EXPAND_TAC "fct" THEN REWRITE_TAC[mldsa_h] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "ctC" THEN
    SIMP_TAC[MLD_FIPS204_SIGN_CTILDE; ASSUME `mu < 2 EXP 512`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "w1C" THEN
    USE_THEN "w1" (MP_TAC o SPECL [`k:num`; `wC:num->int32`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC MLDSA_ENCODE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    EXPAND_TAC "fw1" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `fc IN ring_carrier mldsa_rq` ASSUME_TAC THENL
   [EXPAND_TAC "fc" THEN REWRITE_TAC[MLDSA_SAMPLE_IN_BALL_IN_RQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m < 256
        ==> (ival((cphat:num->int32) m) == mldsa_ntt fc m) (mod &8380417) /\
            abs(ival(cphat m)) < &94279689`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["cphat"; "fc"] THEN
    MATCH_MP_TAC MLD_FIPS204_SIGN_CPHAT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** z, w0 - c s2 and c t0, and their checks ***)

  SUBGOAL_THEN
   `!i m. i < l /\ m < 256
          ==> (ival(mld_sign_z s1hat cphat yC i m) == coeff m (fz i))
              (mod &8380417) /\
              --(&6283009) <= ival(mld_sign_z s1hat cphat yC i m) /\
              ival(mld_sign_z s1hat cphat yC i m) < &6283009`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "fz" THEN BETA_TAC THEN
    MATCH_MP_TAC MLD_FIPS204_SIGN_Z THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "fy" THEN REWRITE_TAC[MLDSA_EXPAND_MASK_IN_RQ];
      X_GEN_TAC `t:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      TRANS_TAC INT_LE_TRANS `&gamma1:int` THEN
      ASM_SIMP_TAC[INT_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j m. j < k /\ m < 256
          ==> (ival(mld_sign_r0 dlo wC s2hat cphat j m) == coeff m (fr0 j))
              (mod &8380417) /\
              --(&6283009) <= ival(mld_sign_r0 dlo wC s2hat cphat j m) /\
              ival(mld_sign_r0 dlo wC s2hat cphat j m) < &6283009`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["fr0"; "fw0"] THEN
    BETA_TAC THEN MATCH_MP_TAC MLD_FIPS204_SIGN_R0 THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "fw" THEN REWRITE_TAC[MLDSA_DOT_IN_RQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j m. j < k /\ m < 256
          ==> (ival(mld_sign_ct0 t0hat cphat j m) == coeff m (fct0 j))
              (mod &8380417) /\
              --(&6283009) <= ival(mld_sign_ct0 t0hat cphat j m) /\
              ival(mld_sign_ct0 t0hat cphat j m) < &6283009`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "fct0" THEN
    BETA_TAC THEN MATCH_MP_TAC MLD_FIPS204_SIGN_CT0 THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun (t,v) ->
    SUBGOAL_THEN t (fun th -> REWRITE_TAC[GSYM th]) THENL
     [MATCH_MP_TAC MLD_FIPS204_SIGN_CHKNORM THEN
      ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`bndz <= gamma1`; `bndw <= gamma2`; `gamma1 <= 524288`;
          `gamma2 <= 2095104`] THEN ARITH_TAC;
        GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC v THEN
        EXPAND_TAC "fy" THEN EXPAND_TAC "fw0" THEN
        ASM_SIMP_TAC[RING_ADD; RING_SUB; RING_MUL; MLDSA_POLY_IN_RQ;
                     MLDSA_EXPAND_MASK_IN_RQ]];
      ALL_TAC])
   [`(!i. i < l ==> mld_poly_chknorm (mld_sign_z s1hat cphat yC i)
                                     (word bndz) = word 0) <=>
     mldsa_vec_norm_lt l bndz fz`,"fz";
    `(!j. j < k ==> mld_poly_chknorm (mld_sign_r0 dlo wC s2hat cphat j)
                                     (word bndw) = word 0) <=>
     mldsa_vec_norm_lt k bndw fr0`,"fr0";
    `(!j. j < k ==> mld_poly_chknorm (mld_sign_ct0 t0hat cphat j)
                                     (word gamma2) = word 0) <=>
     mldsa_vec_norm_lt k gamma2 fct0`,"fct0"] THEN
  ASM_CASES_TAC
   `!j. j < k ==> mld_poly_chknorm (mld_sign_r0 dlo wC s2hat cphat j)
                                   (word bndw) = word 0` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC
   `!j. j < k ==> mld_poly_chknorm (mld_sign_ct0 t0hat cphat j)
                                   (word gamma2) = word 0` THEN
  ASM_REWRITE_TAC[] THEN

  (*** The hints, once w0 - c s2 and c t0 have passed their checks ***)

  SUBGOAL_THEN
   `!j i. j < k /\ i < 256
          ==> abs(ival(mld_sign_r0 dlo wC s2hat cphat j i)) < &bndw /\
              abs(ival(mld_sign_ct0 t0hat cphat j i)) < &gamma2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`mld_sign_r0 dlo wC s2hat cphat j`; `bndw:num`]
                    MLD_FIPS204_POLY_CHKNORM_ABS);
      MP_TAC(ISPECL [`mld_sign_ct0 t0hat cphat j`; `gamma2:num`]
                    MLD_FIPS204_POLY_CHKNORM_ABS)] THEN
    (ANTS_TAC THENL
      [ASM_SIMP_TAC[] THEN
       MAP_EVERY UNDISCH_TAC [`bndw <= gamma2`; `gamma2 <= 2095104`] THEN
       ARITH_TAC;
       ALL_TAC]) THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mkhint (mld_sign_hint_x k dlo wC s2hat t0hat cphat)
           (mld_sign_hint_w1 k w1p w1C) = (fh:num->bool)`
  SUBST1_TAC THENL
   [USE_THEN "hint" (MP_TAC o SPECL
     [`k:num`; `dlo:(num->int32)->num->int32`; `wC:num->int32`;
      `s2hat:num->int32`; `t0hat:num->int32`; `cphat:num->int32`;
      `fr0:num->(1->num)->int`; `fct0:num->(1->num)->int`]) THEN
    REWRITE_TAC[ASSUME `mld_sign_w1 w1enc w1p wC = w1C`] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        GEN_TAC THEN DISCH_TAC THEN
        MAP_EVERY EXPAND_TAC ["fr0"; "fct0"; "fw0"] THEN
        ASM_SIMP_TAC[RING_SUB; RING_MUL; MLDSA_POLY_IN_RQ];
        REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC(INT_ARITH `!b:int. x < b /\ b <= g ==> x < g`) THEN
        EXISTS_TAC `&bndw:int` THEN ASM_SIMP_TAC[INT_OF_NUM_LE]];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "fh" THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BETA_TAC THEN
    ASM_CASES_TAC `p < 256 * k` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "fw1" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN

  (*** The signature ***)

  REWRITE_TAC[MLD_FIPS204_HINT_COUNT] THEN
  ASM_CASES_TAC
   `!i. i < l ==> mld_poly_chknorm (mld_sign_z s1hat cphat yC i)
                                   (word bndz) = word 0` THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[MLD_FIPS204_SIGN_LIST_OF_SEQ3; ETA_AX] THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [ALL_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLD_FIPS204_PACK_HINTS THEN
    REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!i m. i < l /\ m < 256
          ==> abs(ival(mld_sign_z s1hat cphat yC i m)) < &bndz`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`mld_sign_z s1hat cphat yC i`; `bndz:num`]
                  MLD_FIPS204_POLY_CHKNORM_ABS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`bndz <= gamma1`; `gamma1 <= 524288`] THEN
      ARITH_TAC;
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "zpack" (MP_TAC o SPECL
   [`l:num`; `mld_polyvec (mld_sign_z s1hat cphat yC)`]) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_polyvec] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n DIV 256`; `n MOD 256`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `&bndz:int` (concl th))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `n < 256 * l` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `bndz <= gamma1` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MLDSA_ENCODE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_polyvec] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLD_FIPS204_MODPM_IVAL THEN
  SUBGOAL_THEN `n DIV 256 < l /\ n MOD 256 < 256` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n < 256 * l` THEN ARITH_TAC; ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC(INT_ARITH
   `!b:int. x < b /\ b <= &4190208 ==> x <= &4190208`) THEN
  EXISTS_TAC `&bndz:int` THEN ASM_SIMP_TAC[INT_OF_NUM_LE] THEN
  MAP_EVERY UNDISCH_TAC [`bndz <= gamma1`; `gamma1 <= 524288`] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The secret key: the NTTs of the polynomials of s1, s2 and t0 that the C   *)
(* code unpacks represent those that skDecode gives.                         *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_POLYVEC_NTT = prove
 (`!n (x:num->int32) (a:num->int).
        (!i. i < 256 * n ==> ival(x i) = a i /\ abs(a i) < &8380417)
        ==> !j m. j < n /\ m < 256
                  ==> (ival(mld_polyvec_map mld_poly_ntt x (256 * j + m)) ==
                       mldsa_ntt (mldsa_poly(\i. a(256 * j + i))) m)
                      (mod &8380417) /\
                      abs(ival(mld_polyvec_map mld_poly_ntt x (256 * j + m)))
                      < &94279689`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->int32`] MLD_FIPS204_POLYVEC_NTT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mldsa_poly(\i. ival((x:num->int32)(256 * j + i))) =
    mldsa_poly(\i. a(256 * j + i))`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MLDSA_POLY_EXT THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  BETA_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `256 * j + i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let MLD_FIPS204_SIGN_FIELD_SUB_BOUND = prove
 (`!K c b i. K <= 4096 /\ c <= 13
             ==> abs(&K - mldsa_field c b i) < &8380417`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:num`; `b:byte list`; `i:num`] MLDSA_FIELD_BOUND) THEN
  MP_TAC(ISPECL [`c:num`; `13`; `&2:int`] INT_POW_MONO) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  UNDISCH_TAC `K <= 4096` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Attempt n of FIPS 204 signing from mu (mld_fips204_sign_attempt) for the  *)
(* secret key as a byte array, from the C attempt with kappa = l * n: when   *)
(* the challenge sampling of the attempt terminates, it is not rejected      *)
(* exactly when the C checks pass (mld_sign_rejn gives l + 2 * k + 1), and   *)
(* the signature is then that of the C code. The hypotheses on the C         *)
(* functions are those of MLD_FIPS204_SIGN_ATTEMPT_ALT and the unpacking of  *)
(* s1 and s2 (unpack, p bytes per polynomial of c-bit fields); the fields of *)
(* s2 must be at most 2 * eta for the attempt to be the one of Section 5.1.  *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_ATTEMPT = prove
 (`!k l eta tau lam gamma1 gamma2 omega c (unpack:(num->byte)->num->int32) p
    ctlen (g1:num->int16->num->int32) (zpack:(num->int32)->num->byte) zp
    bndz bndw bndh (w1enc:(num->int32)->num->byte) w1p
    (dlo:(num->int32)->num->int32)
    (mkhint:(num->int32)->(num->byte)->num->bool).
        (!(u:num->int32) (v:num->int32) (Y:num->(1->num)->int).
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
                        < &8380417) /\
        (!m b n. n < 256 * m
                 ==> ival(mld_polyvec_unpack p unpack b n) =
                     &eta - mldsa_field c (list_of_seq b (p * m)) n) /\
        (!seed nonce kappa r.
            seed < 2 EXP 512 /\ val nonce = (kappa + r) MOD 65536
            ==> mldsa_poly (\i. ival(g1 seed nonce i)) =
                mldsa_expand_mask gamma1 (bytelist_of_num 64 seed) kappa r) /\
        (!seed nonce i.
            i < 256 ==> abs(ival(g1 seed nonce i)) <= &gamma1) /\
        (!m (x:num->int32).
            (!i. i < 256 * m
                 ==> --(&gamma1) < ival(x i) /\ ival(x i) <= &gamma1)
            ==> list_of_seq (mld_polyvec_pack zp zpack x) (m * zp) =
                mldsa_encode (1 + mldsa_bitlen(gamma1 - 1)) (256 * m)
                 (\i. &gamma1 - ival(x i))) /\
        (!m (w:num->int32).
            (!n. n < 256 * m ==> &0 <= ival(w n) /\ ival(w n) < &8380417)
            ==> list_of_seq (mld_sign_w1 w1enc w1p w) (m * w1p) =
                mldsa_encode (mldsa_bitlen(8380416 DIV (2 * gamma2) - 1))
                 (256 * m) (\n. mldsa_highbits gamma2 (ival(w n)))) /\
        (!(a:num->int32) i.
            &0 <= ival(a i) /\ ival(a i) < &8380417
            ==> ival(dlo a i) = mldsa_lowbits gamma2 (ival(a i))) /\
        (!m (lo:(num->int32)->num->int32) (w:num->int32) (s2h:num->int32)
          (t0h:num->int32) (cp:num->int32)
          (r0:num->(1->num)->int) (ct0:num->(1->num)->int).
            (!p. p < 256 * m ==> &0 <= ival(w p) /\ ival(w p) < &8380417) /\
            (!j. j < m ==> r0 j IN ring_carrier mldsa_rq /\
                           ct0 j IN ring_carrier mldsa_rq) /\
            (!j i. j < m /\ i < 256
                   ==> (ival(mld_sign_r0 lo w s2h cp j i) == coeff i (r0 j))
                       (mod &8380417) /\
                       (ival(mld_sign_ct0 t0h cp j i) == coeff i (ct0 j))
                       (mod &8380417) /\
                       abs(ival(mld_sign_r0 lo w s2h cp j i)) < &gamma2 /\
                       abs(ival(mld_sign_ct0 t0h cp j i)) < &gamma2)
            ==> mkhint (mld_sign_hint_x m lo w s2h t0h cp)
                       (mld_sign_hint_w1 m w1p (mld_sign_w1 w1enc w1p w)) =
                \p. p < 256 * m /\
                    let v = mldsa_modpm
                             (coeff (p MOD 256)
                               (ring_add mldsa_rq (r0(p DIV 256))
                                                  (ct0(p DIV 256))))
                             8380417 in
                    ~(--(&gamma2) < v /\ v <= &gamma2 \/
                      mldsa_highbits gamma2 (ival(w p)) = &0 /\
                      v = --(&gamma2))) /\
        k <= 256 /\ l <= 256 /\ eta <= 4 /\ c <= 4 /\ gamma1 <= 524288 /\
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\
        c = mldsa_bitlen(2 * eta) /\ p = 32 * c /\ ctlen = lam DIV 4 /\
        bndz = gamma1 - tau * eta /\ bndw = gamma2 - tau * eta /\
        bndh = gamma2
        ==> !(sk:num->byte) skl mu rnd n.
              128 + p * (l + k) + 416 * k <= skl /\
              mu < 2 EXP 512 /\ rnd < 2 EXP 256 /\
              (!n. n < 256 * k
                   ==> mldsa_field c
                        (mldsa_slice (128 + 32 * c * l) (32 * c * k)
                                     (list_of_seq sk skl)) n
                       <= &(2 * eta)) /\
              mld_matrix_terminates k l (mld_sk_rho sk) /\
              mld_poly_challenge_terminates tau ctlen
               (num_of_bytelist(list_of_seq
                 (mld_sign_ctilde k w1p mu
                   (mld_sign_w1 w1enc w1p
                     (mld_sign_w l (mld_polyvec_matrix_expand l (mld_sk_rho sk))
                       (mld_sign_y g1
                         (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu)
                         (l * n)))))
                 ctlen))
              ==> mld_fips204_sign_attempt
                   (k,l,eta,tau,lam,gamma1,gamma2,omega)
                   (list_of_seq sk skl) (bytelist_of_num 64 mu)
                   (bytelist_of_num 32 rnd) n =
                  if mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh
                      w1enc w1p dlo mkhint omega sk mu rnd n = l + 2 * k + 1
                  then SOME(list_of_seq
                         (mld_sign_attempt_sig k l ctlen tau g1 zpack zp
                           w1enc w1p dlo mkhint omega
                           (mld_polyvec_matrix_expand l (mld_sk_rho sk))
                           (mld_polyvec_map mld_poly_ntt
                             (mld_sk_s1 unpack p sk))
                           (mld_polyvec_map mld_poly_ntt
                             (mld_sk_s2 l unpack p sk))
                           (mld_polyvec_map mld_poly_ntt (mld_sk_t0 k l p sk))
                           mu (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu)
                           (l * n))
                         (ctlen + l * zp + omega + k))
                  else NONE`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "acc") (CONJUNCTS_THEN2
   (LABEL_TAC "unpack") (CONJUNCTS_THEN2 (LABEL_TAC "g1") (CONJUNCTS_THEN2
   (LABEL_TAC "g1b") (CONJUNCTS_THEN2 (LABEL_TAC "zpack") (CONJUNCTS_THEN2
   (LABEL_TAC "w1") (CONJUNCTS_THEN2 (LABEL_TAC "dlo") (CONJUNCTS_THEN2
   (LABEL_TAC "hint") STRIP_ASSUME_TAC)))))))) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check
                        (fun th -> lhs(concl th) = v)))
   [`p:num`; `ctlen:num`; `bndz:num`; `bndw:num`; `bndh:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mld_fips204_sign_attempt; mld_sign_rejn] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> lhs(concl th) = `c:num`)) THEN

  (*** The secret key as skDecode reads it, and rho'' ***)

  SUBGOAL_THEN
   `0 + 32 <= skl /\ 32 + 32 <= skl /\ 128 + 32 * c * l <= skl /\
    (128 + 32 * c * l) + 32 * c * k <= skl /\
    (128 + 32 * c * (l + k)) + 416 * k <= skl`
  MP_TAC THENL
   [UNDISCH_TAC `128 + (32 * c) * (l + k) + 416 * k <= skl` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
   FIRST_X_ASSUM(MP_TAC o check (free_in `mldsa_slice` o concl)) THEN
   SIMP_TAC[MLD_FIPS204_SLICE_LIST_OF_SEQ; th]) THEN
  DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
  SUBGOAL_THEN
   `list_of_seq (sk:num->byte) 32 = bytelist_of_num 32 (mld_sk_rho sk)`
  SUBST1_TAC THENL
   [REWRITE_TAC[mld_sk_rho; MLD_FIPS204_SIGN_BYTELIST_NUM]; ALL_TAC] THEN
  MP_TAC(SPECL [`\j. (sk:num->byte)(32 + j)`; `rnd:num`; `mu:num`]
               MLD_FIPS204_SIGN_RHOPRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN

  (*** The attempt of Section 5.1, then the C attempt ***)

  W(MP_TAC o PART_MATCH (rand o rand) MLDSA_SIGN_ATTEMPT_ALT o lhs o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MLDSA_POLY_IN_RQ] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC MLDSA_SKDECODE_NORM THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `i < k` THEN UNDISCH_TAC `j < 256` THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC MLD_FIPS204_SIGN_ATTEMPT_ALT THEN
  ASM_REWRITE_TAC[MLDSA_POLY_IN_RQ] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mld_sk_rho] THEN
    MP_TAC(ISPECL [`sk:num->byte`; `32`] MLD_FIPS204_SIGN_NUM_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MP_TAC(BETA_RULE(ISPECL
     [`l:num`; `mld_sk_s1 unpack (32 * c) (sk:num->byte)`;
      `\i. &eta - mldsa_field c
                   (list_of_seq (\i. (sk:num->byte)(128 + i)) (32 * c * l)) i`]
     MLD_FIPS204_SIGN_POLYVEC_NTT)) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[mld_sk_s1] THEN
      USE_THEN "unpack" (fun th -> REWRITE_TAC[MP (SPECL
       [`l:num`; `\j. (sk:num->byte)(128 + j)`; `i:num`] th)
       (ASSUME `i < 256 * l`)]) THEN
      REWRITE_TAC[ARITH_RULE `(32 * c) * l = 32 * c * l`];
      MATCH_MP_TAC MLD_FIPS204_SIGN_FIELD_SUB_BOUND THEN
      MAP_EVERY UNDISCH_TAC [`eta <= 4`; `c <= 4`] THEN ARITH_TAC];
    MP_TAC(BETA_RULE(ISPECL
     [`k:num`; `mld_sk_s2 l unpack (32 * c) (sk:num->byte)`;
      `\i. &eta - mldsa_field c
                   (list_of_seq (\i. (sk:num->byte)((128 + 32 * c * l) + i))
                                (32 * c * k)) i`]
     MLD_FIPS204_SIGN_POLYVEC_NTT)) THEN
    MP_TAC(BETA_RULE(ISPECL
     [`k:num`; `mld_sk_t0 k l (32 * c) (sk:num->byte)`;
      `\i. &4096 - mldsa_field 13
                    (list_of_seq (\i. (sk:num->byte)
                                       ((128 + 32 * c * (l + k)) + i))
                                 (416 * k)) i`]
     MLD_FIPS204_SIGN_POLYVEC_NTT)) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[mld_sk_t0] THEN
        ASM_SIMP_TAC[MLD_FIPS204_POLYVEC_T0_UNPACK] THEN
        REWRITE_TAC[ARITH_RULE
         `128 + (l + k) * 32 * c + j = (128 + 32 * c * (l + k)) + j`];
        MATCH_MP_TAC MLD_FIPS204_SIGN_FIELD_SUB_BOUND THEN ARITH_TAC];
      DISCH_TAC] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[mld_sk_s2; ARITH_RULE
         `128 + l * 32 * c + j = (128 + 32 * c * l) + j`] THEN
        USE_THEN "unpack" (fun th -> REWRITE_TAC[MP (SPECL
         [`k:num`; `\j. (sk:num->byte)((128 + 32 * c * l) + j)`; `i:num`] th)
         (ASSUME `i < 256 * k`)]) THEN
        REWRITE_TAC[ARITH_RULE `(32 * c) * k = 32 * c * k`];
        MATCH_MP_TAC MLD_FIPS204_SIGN_FIELD_SUB_BOUND THEN
        MAP_EVERY UNDISCH_TAC [`eta <= 4`; `c <= 4`] THEN ARITH_TAC];
      DISCH_TAC] THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[mld_sign_rhoprime] THEN
    W(MP_TAC o PART_MATCH lhand MLD_FIPS204_SIGN_NUM_BOUND o lhand o snd) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The first accepted attempt: if attempt n of FIPS 204 is that of the C     *)
(* code for every attempt that the C code makes, the signature of the first  *)
(* attempt that the C code accepts is that of FIPS 204, and if the C code    *)
(* accepts none of its maxatt attempts, FIPS 204 rejects these attempts too. *)
(* The challenge sampling terminates in each attempt that the C code makes   *)
(* if mld_sign_terminates holds.                                             *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_FIRST_CORE = prove
 (`!(att:num->(A)option) (r:num->bool) (s:num->A) maxatt.
        (!n. n < (if ?n. n < maxatt /\ r n
                  then (minimal n. n < maxatt /\ r n) + 1 else maxatt)
             ==> att n = if r n then SOME(s n) else NONE)
        ==> ((?n. n < maxatt /\ r n)
             ==> (if ?n. ~(att n = NONE)
                  then att(minimal n. ~(att n = NONE)) else NONE) =
                 SOME(s(minimal n. n < maxatt /\ r n))) /\
            (~(?n. n < maxatt /\ r n)
             ==> !n. n < maxatt ==> att n = NONE)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `?n. n < maxatt /\ (r:num->bool) n` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC; RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o BETA_RULE o GEN_REWRITE_RULE I [MINIMAL]) THEN
  ABBREV_TAC `N = minimal n. n < maxatt /\ (r:num->bool) n` THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. n <= N ==> (att:num->(A)option) n =
                                if n = N then SOME(s N) else NONE`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_CASES_TAC `n:num = N` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `n < maxatt` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(minimal n. ~((att:num->(A)option) n = NONE)) = N`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MINIMAL_UNIQUE THEN
    ASM_SIMP_TAC[LE_REFL; option_DISTINCT] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[LE_REFL]; ASM_MESON_TAC[LE_REFL; option_DISTINCT]]);;

let MLD_FIPS204_SIGN_FIRST = prove
 (`!k l (unpack:(num->byte)->num->int32) p ctlen tau
    (g1:num->int16->num->int32) (zpack:(num->int32)->num->byte) zp
    bndz bndw bndh (w1enc:(num->int32)->num->byte) w1p
    (dlo:(num->int32)->num->int32)
    (mkhint:(num->int32)->(num->byte)->num->bool) omega maxatt
    (sk:num->byte) mu rnd (att:num->(byte list)option) siglen.
        (!n. n < mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
                  w1enc w1p dlo mkhint omega maxatt sk mu rnd
             ==> att n =
                 if mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh
                     w1enc w1p dlo mkhint omega sk mu rnd n = l + 2 * k + 1
                 then SOME(list_of_seq
                       (mld_sign_attempt_sig k l ctlen tau g1 zpack zp
                         w1enc w1p dlo mkhint omega
                         (mld_polyvec_matrix_expand l (mld_sk_rho sk))
                         (mld_polyvec_map mld_poly_ntt (mld_sk_s1 unpack p sk))
                         (mld_polyvec_map mld_poly_ntt
                           (mld_sk_s2 l unpack p sk))
                         (mld_polyvec_map mld_poly_ntt (mld_sk_t0 k l p sk))
                         mu (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu)
                         (l * n))
                       siglen)
                 else NONE)
        ==> (mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p
              dlo mkhint omega maxatt sk mu rnd
             ==> (if ?n. ~(att n = NONE)
                  then att(minimal n. ~(att n = NONE)) else NONE) =
                 SOME(list_of_seq
                       (mld_sign_sig k l unpack p ctlen tau g1 zpack zp
                         bndz bndw bndh w1enc w1p dlo mkhint omega maxatt
                         sk mu rnd)
                       siglen)) /\
            (~mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p
               dlo mkhint omega maxatt sk mu rnd
             ==> !n. n < maxatt ==> att n = NONE)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_nattempts; mld_sign_sig; mld_sign_ok] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MLD_FIPS204_SIGN_FIRST_CORE) THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[ADD_SUB]);;

let MLD_FIPS204_SIGN_TERMINATES = prove
 (`!k l (unpack:(num->byte)->num->int32) p ctlen tau
    (g1:num->int16->num->int32) bndz bndw bndh
    (w1enc:(num->int32)->num->byte) w1p (dlo:(num->int32)->num->int32)
    (mkhint:(num->int32)->(num->byte)->num->bool) omega maxatt
    (sk:num->byte) mu rnd n.
        mld_sign_terminates k l unpack p ctlen tau g1 bndz bndw bndh
         w1enc w1p dlo mkhint omega maxatt sk mu rnd /\
        n < mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
             w1enc w1p dlo mkhint omega maxatt sk mu rnd
        ==> mld_poly_challenge_terminates tau ctlen
             (num_of_bytelist(list_of_seq
               (mld_sign_ctilde k w1p mu
                 (mld_sign_w1 w1enc w1p
                   (mld_sign_w l (mld_polyvec_matrix_expand l (mld_sk_rho sk))
                     (mld_sign_y g1 (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu)
                       (l * n)))))
               ctlen))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_terminates; mld_sign_declass;
              mld_sign_attempt_declass] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `n:num`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The three parameter sets. The proof is the same for each, given by the    *)
(* definitions of the parameter set and of the C functions (from which       *)
(* MLD_FIPS204_SIGN_INST takes the parameters) and the lemmas for the C      *)
(* functions that MLD_FIPS204_SIGN_ATTEMPT assumes: if the C code accepts an *)
(* attempt, mldsa_sign_mu gives the signature of the first one, and if it    *)
(* gives up, none of the attempts that it made succeeds in FIPS 204 either.  *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_INST (params_def,ok_def,sig_def,term_def) fmts =
  match snd(strip_comb(rhs(concl ok_def))),
        snd(strip_comb(rhs(concl sig_def))),
        striplist dest_pair (rhs(concl params_def)) with
    [k;l;unpack;p;ctlen;tau;g1;bndz;bndw;bndh;w1enc;w1p;dlo;mkhint;
     omega;maxatt],
    [_;_;_;_;_;_;_;zpack;zp;_;_;_;_;_;_;_;_;_],
    [_;_;eta;_;lam;gamma1;gamma2;_] ->
      let pn = dest_small_numeral p and kn = dest_small_numeral k
      and ln = dest_small_numeral l in
      let c = mk_small_numeral(pn / 32)
      and skl = mk_small_numeral(128 + pn * (ln + kn) + 416 * kn) in
      let th = SPECL [k;l;eta;tau;lam;gamma1;gamma2;omega;c;unpack;p;ctlen;
                      g1;zpack;zp;bndz;bndw;bndh;w1enc;w1p;dlo;mkhint]
                     MLD_FIPS204_SIGN_ATTEMPT in
      let hyps = prove
       (lhand(concl th),
        REPEAT CONJ_TAC THEN
        (FIRST(map MATCH_ACCEPT_TAC fmts) ORELSE
         (REWRITE_TAC[MLDSA_GAMMA2_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC[MLDSA_BITLEN_CLAUSES]))) in
      MP th hyps,skl,
      SPECL [k;l;unpack;p;ctlen;tau;g1;bndz;bndw;bndh;w1enc;w1p;dlo;mkhint;
             omega;maxatt] MLD_FIPS204_SIGN_TERMINATES
  | _ -> failwith "MLD_FIPS204_SIGN_INST";;

let MLD_FIPS204_SIGN_TAC defs fmts =
  let params_def,ok_def,sig_def,term_def = defs in
  let att_th,skl,term_th = MLD_FIPS204_SIGN_INST defs fmts in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[term_def]) THEN
  REWRITE_TAC[ok_def; sig_def; params_def; MLD_FIPS204_SIGN_MU_ATTEMPT] THEN
  MATCH_MP_TAC MLD_FIPS204_SIGN_FIRST THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`sk:num->byte`; skl; `mu:num`; `rnd:num`; `n:num`] att_th) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(CONV_TAC NUM_REDUCE_CONV THEN FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC term_th THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];;

let MLD_FIPS204_SIGN_44 = prove
 (`!(sk:num->byte) mu rnd.
     mu < 2 EXP 512 /\ rnd < 2 EXP 256 /\
     (!n. n < 1024
          ==> mldsa_field 3 (mldsa_slice 512 384 (list_of_seq sk 2560)) n
              <= &4) /\
     mld_matrix_terminates 4 4 (mld_sk_rho sk) /\
     mld_sign_terminates_44 sk mu rnd
     ==> (mld_sign_ok_44 sk mu rnd
          ==> mldsa_sign_mu mldsa44 (list_of_seq sk 2560)
               (bytelist_of_num 64 mu) (bytelist_of_num 32 rnd) =
              SOME(list_of_seq (mld_sign_sig_44 sk mu rnd) 2420)) /\
         (~mld_sign_ok_44 sk mu rnd
          ==> !n. n < 16382
                  ==> mld_fips204_sign_attempt mldsa44
                       (list_of_seq sk 2560) (bytelist_of_num 64 mu)
                       (bytelist_of_num 32 rnd) n = NONE)`,
  MLD_FIPS204_SIGN_TAC
   (mldsa44,mld_sign_ok_44,mld_sign_sig_44,mld_sign_terminates_44)
   [MLD_FIPS204_INVNTT_ACC_L4; MLD_FIPS204_POLYVEC_ETA_UNPACK_2;
    MLD_FIPS204_POLY_UNIFORM_GAMMA1_17; MLD_FIPS204_SIGN_GAMMA1_17_BOUND;
    MLD_FIPS204_SIGN_ZPACK_17; MLD_FIPS204_SIGN_W1_88;
    MLD_FIPS204_SIGN_DLO_88; MLD_FIPS204_SIGN_MAKE_HINT_88]);;

let MLD_FIPS204_SIGN_65 = prove
 (`!(sk:num->byte) mu rnd.
     mu < 2 EXP 512 /\ rnd < 2 EXP 256 /\
     (!n. n < 1536
          ==> mldsa_field 4 (mldsa_slice 768 768 (list_of_seq sk 4032)) n
              <= &8) /\
     mld_matrix_terminates 6 5 (mld_sk_rho sk) /\
     mld_sign_terminates_65 sk mu rnd
     ==> (mld_sign_ok_65 sk mu rnd
          ==> mldsa_sign_mu mldsa65 (list_of_seq sk 4032)
               (bytelist_of_num 64 mu) (bytelist_of_num 32 rnd) =
              SOME(list_of_seq (mld_sign_sig_65 sk mu rnd) 3309)) /\
         (~mld_sign_ok_65 sk mu rnd
          ==> !n. n < 13106
                  ==> mld_fips204_sign_attempt mldsa65
                       (list_of_seq sk 4032) (bytelist_of_num 64 mu)
                       (bytelist_of_num 32 rnd) n = NONE)`,
  MLD_FIPS204_SIGN_TAC
   (mldsa65,mld_sign_ok_65,mld_sign_sig_65,mld_sign_terminates_65)
   [MLD_FIPS204_INVNTT_ACC_L5; MLD_FIPS204_POLYVEC_ETA_UNPACK_4;
    MLD_FIPS204_POLY_UNIFORM_GAMMA1_19; MLD_FIPS204_SIGN_GAMMA1_19_BOUND;
    MLD_FIPS204_SIGN_ZPACK_19; MLD_FIPS204_SIGN_W1_32;
    MLD_FIPS204_SIGN_DLO_32; MLD_FIPS204_SIGN_MAKE_HINT_32]);;

let MLD_FIPS204_SIGN_87 = prove
 (`!(sk:num->byte) mu rnd.
     mu < 2 EXP 512 /\ rnd < 2 EXP 256 /\
     (!n. n < 2048
          ==> mldsa_field 3 (mldsa_slice 800 768 (list_of_seq sk 4896)) n
              <= &4) /\
     mld_matrix_terminates 8 7 (mld_sk_rho sk) /\
     mld_sign_terminates_87 sk mu rnd
     ==> (mld_sign_ok_87 sk mu rnd
          ==> mldsa_sign_mu mldsa87 (list_of_seq sk 4896)
               (bytelist_of_num 64 mu) (bytelist_of_num 32 rnd) =
              SOME(list_of_seq (mld_sign_sig_87 sk mu rnd) 4627)) /\
         (~mld_sign_ok_87 sk mu rnd
          ==> !n. n < 9361
                  ==> mld_fips204_sign_attempt mldsa87
                       (list_of_seq sk 4896) (bytelist_of_num 64 mu)
                       (bytelist_of_num 32 rnd) n = NONE)`,
  MLD_FIPS204_SIGN_TAC
   (mldsa87,mld_sign_ok_87,mld_sign_sig_87,mld_sign_terminates_87)
   [MLD_FIPS204_INVNTT_ACC_L7; MLD_FIPS204_POLYVEC_ETA_UNPACK_2;
    MLD_FIPS204_POLY_UNIFORM_GAMMA1_19; MLD_FIPS204_SIGN_GAMMA1_19_BOUND;
    MLD_FIPS204_SIGN_ZPACK_19; MLD_FIPS204_SIGN_W1_32;
    MLD_FIPS204_SIGN_DLO_32; MLD_FIPS204_SIGN_MAKE_HINT_32]);;
