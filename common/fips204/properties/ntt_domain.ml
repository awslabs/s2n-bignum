(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Part 4: the NTT-domain forms of FIPS 204 Algorithms 6, 7 and 8 (KeyGen,   *)
(* Sign and Verify): A^ is the matrix of RejNTTPoly samples and the          *)
(* products are pointwise products of NTTs followed by NTT^-1.               *)
(* ========================================================================= *)

needs "common/fips204/properties/encoding.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The ML-DSA algorithms in the NTT-domain form of the pseudocode of FIPS    *)
(* 204 Algorithms 6 (key generation), 7 (one attempt of the signing loop)    *)
(* and 8 (verification): A^ is the matrix of RejNTTPoly samples, and the     *)
(* products are pointwise products of NTTs followed by NTT^-1. They need the *)
(* assumption that the RejNTTPoly values used are < q, which holds whenever  *)
(* RejNTTPoly is well defined, i.e. whenever the loop of FIPS 204 Algorithm  *)
(* 30 terminates.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REJ_NTT_POLY_POS = prove
 (`!rho i. &0 <= mldsa_rej_ntt_poly rho i`,
  REWRITE_TAC[mldsa_rej_ntt_poly] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_POS]);;

let MLDSA_REJ_BOUNDED_POLY_IN_RQ = prove
 (`!eta rho. mldsa_rej_bounded_poly eta rho IN ring_carrier mldsa_rq`,
  REWRITE_TAC[mldsa_rej_bounded_poly] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]);;

let MLDSA_EXPAND_MASK_IN_RQ = prove
 (`!gamma1 rho kappa r.
        mldsa_expand_mask gamma1 rho kappa r IN ring_carrier mldsa_rq`,
  REWRITE_TAC[mldsa_expand_mask] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]);;

let MLDSA_SAMPLE_IN_BALL_IN_RQ = prove
 (`!tau rho. mldsa_sample_in_ball tau rho IN ring_carrier mldsa_rq`,
  REWRITE_TAC[mldsa_sample_in_ball; MLDSA_POLY_IN_RQ]);;

let MLDSA_EXPAND_A = prove
 (`!rho i. mldsa_expand_a rho i =
           \j. mldsa_ntt_inv
                (mldsa_rej_ntt_poly (APPEND rho [word j; word i]))`,
  REWRITE_TAC[FUN_EQ_THM; mldsa_expand_a]);;

let MLDSA_DOT_EXPAND_A = prove
 (`!rho k l.
        (!i j n. i < k /\ j < l /\ n < 256
                 ==> mldsa_rej_ntt_poly (APPEND rho [word j; word i]) n
                     < &8380417)
        ==> !s i. (!j. j < l ==> s j IN ring_carrier mldsa_rq) /\ i < k
                  ==> mldsa_dot l (mldsa_expand_a rho i) s =
                      mldsa_ntt_inv
                       (\n. ring_sum mldsa_zq {j | j < l}
                             (\j. ring_mul mldsa_zq
                                   (mldsa_rej_ntt_poly
                                     (APPEND rho [word j; word i]) n)
                                   (mldsa_ntt (s j) n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLDSA_EXPAND_A] THEN
  MP_TAC(ISPECL [`l:num`;
                 `\j. mldsa_rej_ntt_poly (APPEND rho [word j; word i])`;
                 `s:num->(1->num)->int`] MLDSA_DOT_NTT_INV) THEN
  ASM_SIMP_TAC[MLDSA_REJ_NTT_POLY_POS]);;

let DIV256_LT = ARITH_RULE `!n k. n DIV 256 < k <=> n < 256 * k`;;

(* ASM_SIMP_TAC with p in the context when simplifying q in p /\ q, as in    *)
(* the hints h = \p. p < 256 * k /\ ... of mldsa_sign_attempt.               *)

let MLDSA_CONJ_SIMP_TAC =
  let CONJ_CONG = TAUT
   `(p <=> p') ==> (p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')` in
  fun thl ->
    let Simpset(net,prover,provers,rewmaker) = basic_ss [] in
    let ss = Simpset(net_of_cong CONJ_CONG net,prover,provers,rewmaker) in
    ASM(fun thl' -> CONV_TAC(SIMPLIFY_CONV ss thl')) thl;;

let MLDSA_KEYGEN_INTERNAL_FIPS = prove
 (`!k l eta tau lam gamma1 gamma2 omega xi.
        (!i j n. i < k /\ j < l /\ n < 256
                 ==> mldsa_rej_ntt_poly
                      (APPEND (mldsa_slice 0 32
                                (mldsa_h (APPEND xi [word k; word l]) 128))
                              [word j; word i]) n < &8380417)
        ==> mldsa_keygen_internal (k,l,eta,tau,lam,gamma1,gamma2,omega) xi =
            let seeds = mldsa_h (APPEND xi [word k; word l]) 128 in
            let rho = mldsa_slice 0 32 seeds
            and rho' = mldsa_slice 32 64 seeds
            and key = mldsa_slice 96 32 seeds in
            let Ahat = \i j. mldsa_rej_ntt_poly (APPEND rho [word j; word i]) in
            let s1 = \i. mldsa_rej_bounded_poly eta
                          (APPEND rho' (bytelist_of_num 2 i)) in
            let s2 = \i. mldsa_rej_bounded_poly eta
                          (APPEND rho' (bytelist_of_num 2 (l + i))) in
            let s1hat = \i. mldsa_ntt (s1 i) in
            let t = \i. ring_add mldsa_rq
                         (mldsa_ntt_inv
                           (\n. ring_sum mldsa_zq {j | j < l}
                                 (\j. ring_mul mldsa_zq (Ahat i j n)
                                                        (s1hat j n))))
                         (s2 i) in
            let t1 = \n. FST(mldsa_power2round
                              (coeff (n MOD 256) (t(n DIV 256)))) in
            let t0 = \n. SND(mldsa_power2round
                              (coeff (n MOD 256) (t(n DIV 256)))) in
            let pk = APPEND rho (mldsa_encode 10 (256 * k) t1) in
            let c = mldsa_bitlen(2 * eta) in
            let s1b = mldsa_encode c (256 * l)
                       (\n. &eta - mldsa_modpm (coeff (n MOD 256)
                                                (s1(n DIV 256))) 8380417)
            and s2b = mldsa_encode c (256 * k)
                       (\n. &eta - mldsa_modpm (coeff (n MOD 256)
                                                (s2(n DIV 256))) 8380417)
            and t0b = mldsa_encode 13 (256 * k) (\n. &4096 - t0 n) in
            pk,APPEND rho (APPEND key (APPEND (mldsa_h pk 64)
                                              (APPEND s1b (APPEND s2b t0b))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_keygen_internal] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC
   `rho = mldsa_slice 0 32 (mldsa_h (APPEND xi [word k; word l]) 128)` THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MLDSA_DOT_EXPAND_A) THEN
  REWRITE_TAC[mldsa_encode] THEN
  ASM_SIMP_TAC[DIV256_LT; MLDSA_REJ_BOUNDED_POLY_IN_RQ]);;

let MLDSA_SIGN_ATTEMPT_FIPS = prove
 (`!k l eta tau lam gamma1 gamma2 omega rho s1 s2 t0 mu rho'' kappa.
        (!i j n. i < k /\ j < l /\ n < 256
                 ==> mldsa_rej_ntt_poly (APPEND rho [word j; word i]) n
                     < &8380417) /\
        (!i. i < l ==> s1 i IN ring_carrier mldsa_rq) /\
        (!i. i < k ==> s2 i IN ring_carrier mldsa_rq /\
                       t0 i IN ring_carrier mldsa_rq)
        ==> mldsa_sign_attempt (k,l,eta,tau,lam,gamma1,gamma2,omega)
             (mldsa_expand_a rho) s1 s2 t0 mu rho'' kappa =
            let Ahat = \i j. mldsa_rej_ntt_poly (APPEND rho [word j; word i]) in
            let s1hat = \i. mldsa_ntt (s1 i)
            and s2hat = \i. mldsa_ntt (s2 i)
            and t0hat = \i. mldsa_ntt (t0 i) in
            let y = \i. mldsa_expand_mask gamma1 rho'' kappa i in
            let yhat = \i. mldsa_ntt (y i) in
            let w = \i. mldsa_ntt_inv
                         (\n. ring_sum mldsa_zq {j | j < l}
                               (\j. ring_mul mldsa_zq (Ahat i j n)
                                                      (yhat j n))) in
            let w1 = \n. mldsa_highbits gamma2
                          (coeff (n MOD 256) (w(n DIV 256))) in
            let ct = mldsa_h (APPEND mu (mldsa_encode
                                (mldsa_bitlen(8380416 DIV (2 * gamma2) - 1))
                                (256 * k) w1))
                             (lam DIV 4) in
            let c = mldsa_sample_in_ball tau ct in
            let chat = mldsa_ntt c in
            let cs1 = \i. mldsa_ntt_inv
                           (\n. ring_mul mldsa_zq (chat n) (s1hat i n))
            and cs2 = \i. mldsa_ntt_inv
                           (\n. ring_mul mldsa_zq (chat n) (s2hat i n)) in
            let z = \i. ring_add mldsa_rq (y i) (cs1 i) in
            let r = \i. ring_sub mldsa_rq (w i) (cs2 i) in
            let ct0 = \i. mldsa_ntt_inv
                           (\n. ring_mul mldsa_zq (chat n) (t0hat i n)) in
            let h = \p. p < 256 * k /\
                        mldsa_makehint gamma2
                         (--(coeff (p MOD 256) (ct0(p DIV 256))))
                         (coeff (p MOD 256)
                           (ring_add mldsa_rq (r(p DIV 256))
                                              (ct0(p DIV 256)))) in
            let beta = tau * eta in
            if mldsa_vec_norm_lt l (gamma1 - beta) z /\
               (!i j. i < k /\ j < 256
                      ==> abs(mldsa_lowbits gamma2 (coeff j (r i)))
                          < &(gamma2 - beta)) /\
               mldsa_vec_norm_lt k gamma2 ct0 /\
               mldsa_hint_count h (256 * k) <= omega
            then SOME(APPEND ct
                       (APPEND (mldsa_encode (1 + mldsa_bitlen(gamma1 - 1))
                                             (256 * l)
                                 (\n. &gamma1 -
                                      mldsa_modpm (coeff (n MOD 256)
                                                    (z(n DIV 256)))
                                                  8380417))
                               (mldsa_hintbitpack k omega h)))
            else NONE`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   (ASSUME_TAC o MATCH_MP MLDSA_DOT_EXPAND_A) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[mldsa_sign_attempt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[mldsa_encode; mldsa_vec_norm_lt] THEN
  MLDSA_CONJ_SIMP_TAC[DIV256_LT; MLDSA_EXPAND_MASK_IN_RQ;
                      MLDSA_SAMPLE_IN_BALL_IN_RQ; GSYM MLDSA_NTT_INV_MUL]);;

let MLDSA_VERIFY_MU_FIPS = prove
 (`!k l eta tau lam gamma1 gamma2 omega pk mu sg.
        (!i j n. i < k /\ j < l /\ n < 256
                 ==> mldsa_rej_ntt_poly
                      (APPEND (mldsa_slice 0 32 pk) [word j; word i]) n
                     < &8380417)
        ==> (mldsa_verify_mu_accepts (k,l,eta,tau,lam,gamma1,gamma2,omega)
              pk mu sg <=>
             let c = 1 + mldsa_bitlen(gamma1 - 1) in
             let rho = mldsa_slice 0 32 pk
             and t1b = mldsa_slice 32 (320 * k) pk in
             let t1 = \i. mldsa_poly
                           (\j. &8192 * mldsa_field 10 t1b (256 * i + j)) in
             let ct = mldsa_slice 0 (lam DIV 4) sg
             and zb = mldsa_slice (lam DIV 4) (32 * c * l) sg
             and hb = mldsa_slice (lam DIV 4 + 32 * c * l) (omega + k) sg in
             let z = \i. mldsa_poly
                          (\j. &gamma1 - mldsa_field c zb (256 * i + j)) in
             LENGTH pk = 32 + 320 * k /\
             LENGTH sg = lam DIV 4 + 32 * c * l + omega + k /\
             match mldsa_hintbitunpack k omega hb with
               NONE -> F
             | SOME h ->
                let Ahat = \i j. mldsa_rej_ntt_poly
                                  (APPEND rho [word j; word i]) in
                let cc = mldsa_sample_in_ball tau ct in
                let zhat = \j. mldsa_ntt (z j)
                and chat = mldsa_ntt cc
                and t1hat = \i. mldsa_ntt (t1 i) in
                let w = \i. mldsa_ntt_inv
                             (\n. ring_sub mldsa_zq
                                   (ring_sum mldsa_zq {j | j < l}
                                     (\j. ring_mul mldsa_zq (Ahat i j n)
                                                            (zhat j n)))
                                   (ring_mul mldsa_zq (chat n)
                                                      (t1hat i n))) in
                let w1 = \n. mldsa_usehint gamma2 (h n)
                              (coeff (n MOD 256) (w(n DIV 256))) in
                mldsa_vec_norm_lt l (gamma1 - tau * eta) z /\
                mldsa_h (APPEND mu (mldsa_encode
                                     (mldsa_bitlen
                                       (8380416 DIV (2 * gamma2) - 1))
                                     (256 * k) w1))
                        (lam DIV 4) = ct)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_verify_mu_accepts] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MLDSA_DOT_EXPAND_A) THEN
  REWRITE_TAC[mldsa_encode] THEN
  ASM_SIMP_TAC[DIV256_LT; MLDSA_POLY_IN_RQ; MLDSA_SAMPLE_IN_BALL_IN_RQ;
               GSYM MLDSA_NTT_INV_MUL; MLDSA_NTT_INV_SUB; RING_SUM; RING_MUL;
               MLDSA_NTT_IN_ZQ]);;

type_invention_error := false;;
