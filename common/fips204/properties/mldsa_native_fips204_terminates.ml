(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The rejection samplers of mldsa-native terminate, for every input that    *)
(* the C code gives them.                                                    *)
(*                                                                           *)
(* common/fips204/properties/terminates.ml shows that SHAKE128 and SHAKE256  *)
(* of a message of one block have enough acceptable candidates, using that   *)
(* Keccak-f1600 is a permutation. Here the C-level predicates                *)
(*                                                                           *)
(*   mld_rej_uniform_terminates, mld_matrix_terminates,                      *)
(*   mld_rej_eta_terminates, mld_keypair_terminates,                         *)
(*   mld_poly_challenge_terminates, mld_sign_terminates                      *)
(*                                                                           *)
(* are derived from those facts, so that the theorems about the C code do    *)
(* not need them as hypotheses. What remains of them are bounds on the seeds *)
(* (rho < 2^256 and the like), which hold for byte strings of the right      *)
(* length.                                                                   *)
(* ========================================================================= *)

needs "common/fips204/properties/mldsa_native_fips204_ntt.ml";;
needs "common/fips204/properties/mldsa_native_fips204_sample.ml";;
needs "common/fips204/properties/terminates.ml";;
needs "common/mldsa_native_sign.ml";;

(* ------------------------------------------------------------------------- *)
(* mld_rej_uniform_c and the matrix: seeds of 34 bytes.                      *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_REJ_UNIFORM_TERMINATES = prove
 (`!rho. LENGTH rho < 168 ==> mld_rej_uniform_terminates (shake128 rho)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mld_rej_uniform_terminates] THEN
  MP_TAC(SPECL [`rho:byte list`; `256`] MLDSA_REJ_NTT_POLY_TERMINATES) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `J:num` THEN
  REWRITE_TAC[mld_rej_uniform_list; MLD_FIPS204_SAMPLE_LENGTH_FILTER;
              MLD_FIPS204_SAMPLE_REJ_UNIFORM_CAND] THEN
  SIMP_TAC[]);;

let MLD_FIPS204_MATRIX_TERMINATES = prove
 (`!k l rho.
        rho < 2 EXP 256 /\ k <= 256 /\ l <= 256
        ==> mld_matrix_terminates k l rho`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_matrix_terminates] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rho:num`; `i:num`; `j:num`] MLD_FIPS204_MATRIX_SEED) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[MLD_FIPS204_SHAKE128_STREAM] THEN
  MATCH_MP_TAC MLD_FIPS204_REJ_UNIFORM_TERMINATES THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* mld_rej_eta_c and key generation: seeds of 66 bytes.                      *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_REJ_ETA_TERMINATES = prove
 (`!eta rho.
        LENGTH rho < 135 ==> mld_rej_eta_terminates eta (shake256 rho)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mld_rej_eta_terminates] THEN
  MP_TAC(SPECL [`eta:num`; `rho:byte list`; `256`]
    MLDSA_REJ_BOUNDED_POLY_TERMINATES) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `TT:num` THEN
  REWRITE_TAC[mld_rej_eta_list; LENGTH_MAP; MLD_FIPS204_SAMPLE_LENGTH_FILTER;
              mld_rej_eta_valid; MLD_FIPS204_SAMPLE_REJ_ETA_NIBBLE] THEN
  ASM_CASES_TAC `eta = 2` THEN ASM_REWRITE_TAC[]);;

let MLD_FIPS204_KEYPAIR_TERMINATES = prove
 (`!eta k l (used:num->bool) seed.
        (!n. used n ==> n < 65536)
        ==> mld_keypair_terminates eta k l used seed`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keypair_terminates] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `mld_keypair_rhoprime k l seed < 2 EXP 512` ASSUME_TAC THENL
   [REWRITE_TAC[mld_keypair_rhoprime] THEN
    MP_TAC(ISPEC `list_of_seq (\j. mld_keypair_seedbuf k l seed (32 + j)) 64`
      NUM_OF_BYTELIST_BOUND) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`mld_keypair_rhoprime k l seed`; `n:num`]
    MLD_FIPS204_SEED_NONCE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ASM_SIMP_TAC[MLD_FIPS204_SHAKE256_STREAM] THEN
  MATCH_MP_TAC MLD_FIPS204_REJ_ETA_TERMINATES THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_challenge_c (SampleInBall): the bytes of c~ of at most 64 bytes. *)
(* If the stream has, after every position, a later byte of at most          *)
(* 256 - tau, then the number k of coefficients set reaches tau: it never    *)
(* exceeds tau, never decreases, and increases at each such byte.            *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_CHALLENGE_STEP_BOUND = prove
 (`!tau (s:num->byte) n. FST(mld_poly_challenge_step tau s n) <= tau`,
  REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[mld_poly_challenge_step] THEN ARITH_TAC;
    REWRITE_TAC[MLD_FIPS204_SAMPLE_CHALLENGE_STEP_FST;
                mld_poly_challenge_accept] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let MLD_FIPS204_CHALLENGE_STEP_MONO = prove
 (`!tau (s:num->byte) m n.
        m <= n
        ==> FST(mld_poly_challenge_step tau s m) <=
            FST(mld_poly_challenge_step tau s n)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[LE] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    STRIP_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[MLD_FIPS204_SAMPLE_CHALLENGE_STEP_FST] THEN
    SUBGOAL_THEN
     `FST(mld_poly_challenge_step tau (s:num->byte) m) <=
      FST(mld_poly_challenge_step tau s n)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ARITH_TAC]);;

let MLD_FIPS204_CHALLENGE_STREAM_TERMINATES = prove
 (`!tau (s:num->byte).
        (!N. ?p. N < p /\ val(s p) <= 256 - tau)
        ==> ?n. FST(mld_poly_challenge_step tau s n) = tau`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. m <= tau ==> ?n. m <= FST(mld_poly_challenge_step tau (s:num->byte) n)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `n0:num`)] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o SPEC `8 + n0` o
                  check (is_forall o concl)) THEN
    EXISTS_TAC `SUC(p - 8)` THEN
    MP_TAC(SPECL [`tau:num`; `s:num->byte`; `n0:num`; `p - 8`]
      MLD_FIPS204_CHALLENGE_STEP_MONO) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`tau:num`; `s:num->byte`; `p - 8`]
      MLD_FIPS204_CHALLENGE_STEP_BOUND) THEN
    DISCH_TAC THEN
    REWRITE_TAC[MLD_FIPS204_SAMPLE_CHALLENGE_STEP_FST;
                mld_poly_challenge_accept] THEN
    SUBGOAL_THEN `8 + (p - 8) = p` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:num`) THEN REWRITE_TAC[LE_REFL] THEN
  MESON_TAC[MLD_FIPS204_CHALLENGE_STEP_BOUND; LE_ANTISYM]);;

let MLD_FIPS204_POLY_CHALLENGE_TERMINATES = prove
 (`!tau ctlen c.
        c < 2 EXP (8 * ctlen) /\ ctlen < 135 /\ tau <= 128
        ==> mld_poly_challenge_terminates tau ctlen c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_poly_challenge_terminates] THEN
  ASM_SIMP_TAC[MLD_FIPS204_SHAKE256_BYTE] THEN
  MATCH_MP_TAC MLD_FIPS204_CHALLENGE_STREAM_TERMINATES THEN
  X_GEN_TAC `N:num` THEN
  MP_TAC(SPECL [`tau:num`; `bytelist_of_num ctlen c`; `N:num`]
    MLDSA_SAMPLE_IN_BALL_TERMINATES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN ASM_ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Signing: c~ is a byte string of ctlen <= 64 bytes in every attempt.       *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_BYTELIST_NUM_BOUND = prove
 (`!(f:num->byte) n. num_of_bytelist(list_of_seq f n) < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) n` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; EXP_MULT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MLD_FIPS204_SIGN_TERMINATES_ALL = prove
 (`!k l (unpack:(num->byte)->num->int32) p ctlen tau
    (g1:num->int16->num->int32) bndz bndw bndh
    (w1enc:(num->int32)->num->byte) w1p (dlo:(num->int32)->num->int32)
    (mkhint:(num->int32)->(num->byte)->num->bool) omega maxatt
    (sk:num->byte) mu rnd.
        ctlen < 135 /\ tau <= 128
        ==> mld_sign_terminates k l unpack p ctlen tau g1 bndz bndw bndh
             w1enc w1p dlo mkhint omega maxatt sk mu rnd`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_sign_terminates; mld_sign_declass;
              mld_sign_attempt_declass] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MLD_FIPS204_POLY_CHALLENGE_TERMINATES THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC MLD_FIPS204_BYTELIST_NUM_BOUND);;

(* ------------------------------------------------------------------------- *)
(* The instances that the theorems about the C code assume: seeds rho and    *)
(* c~ are read from byte strings, so they are below 2^(8 n) whatever the     *)
(* bytes, and the nonces of key generation are below 2^16.                   *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SLICE_NUM_BOUND = prove
 (`!a n l. num_of_bytelist(mldsa_slice a n l) < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `mldsa_slice a n (l:byte list)` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_MLDSA_SLICE; EXP_MULT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MLD_FIPS204_MATRIX_TERMINATES_SK = prove
 (`!k l sk. k <= 256 /\ l <= 256 ==> mld_matrix_terminates k l (mld_sk_rho sk)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_FIPS204_MATRIX_TERMINATES THEN
  ASM_REWRITE_TAC[mld_sk_rho] THEN
  MP_TAC(SPECL [`sk:num->byte`; `32`] MLD_FIPS204_BYTELIST_NUM_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MLD_FIPS204_MATRIX_TERMINATES_KEYPAIR = prove
 (`!k l seed.
        k <= 256 /\ l <= 256
        ==> mld_matrix_terminates k l (mld_keypair_rho k l seed)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_FIPS204_MATRIX_TERMINATES THEN
  ASM_REWRITE_TAC[mld_keypair_rho] THEN
  MP_TAC(SPECL [`mld_keypair_seedbuf k l seed`; `32`]
    MLD_FIPS204_BYTELIST_NUM_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MLD_FIPS204_MATRIX_TERMINATES_SLICE = prove
 (`!k l a (b:byte list).
        k <= 256 /\ l <= 256
        ==> mld_matrix_terminates k l (num_of_bytelist(mldsa_slice a 32 b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_FIPS204_MATRIX_TERMINATES THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a:num`; `32`; `b:byte list`] MLD_FIPS204_SLICE_NUM_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MLD_FIPS204_POLY_CHALLENGE_TERMINATES_SLICE = prove
 (`!tau ctlen a (b:byte list).
        ctlen < 135 /\ tau <= 128
        ==> mld_poly_challenge_terminates tau ctlen
             (num_of_bytelist(mldsa_slice a ctlen b))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MLD_FIPS204_POLY_CHALLENGE_TERMINATES THEN
  ASM_REWRITE_TAC[MLD_FIPS204_SLICE_NUM_BOUND]);;

let MLD_FIPS204_KEYPAIR_TERMINATES_44 = prove
 (`!seed. mld_keypair_terminates_44 seed`,
  GEN_TAC THEN REWRITE_TAC[mld_keypair_terminates_44] THEN
  MATCH_MP_TAC MLD_FIPS204_KEYPAIR_TERMINATES THEN
  SIMP_TAC[] THEN ARITH_TAC);;

let MLD_FIPS204_KEYPAIR_TERMINATES_65 = prove
 (`!seed. mld_keypair_terminates_65 seed`,
  GEN_TAC THEN REWRITE_TAC[mld_keypair_terminates_65] THEN
  MATCH_MP_TAC MLD_FIPS204_KEYPAIR_TERMINATES THEN
  SIMP_TAC[] THEN ARITH_TAC);;

let MLD_FIPS204_KEYPAIR_TERMINATES_87 = prove
 (`!seed. mld_keypair_terminates_87 seed`,
  GEN_TAC THEN REWRITE_TAC[mld_keypair_terminates_87] THEN
  MATCH_MP_TAC MLD_FIPS204_KEYPAIR_TERMINATES THEN
  SIMP_TAC[] THEN ARITH_TAC);;

let MLD_FIPS204_SIGN_TERMINATES_44 = prove
 (`!sk mu rnd. mld_sign_terminates_44 sk mu rnd`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_sign_terminates_44] THEN
  MATCH_MP_TAC MLD_FIPS204_SIGN_TERMINATES_ALL THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_FIPS204_SIGN_TERMINATES_65 = prove
 (`!sk mu rnd. mld_sign_terminates_65 sk mu rnd`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_sign_terminates_65] THEN
  MATCH_MP_TAC MLD_FIPS204_SIGN_TERMINATES_ALL THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_FIPS204_SIGN_TERMINATES_87 = prove
 (`!sk mu rnd. mld_sign_terminates_87 sk mu rnd`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_sign_terminates_87] THEN
  MATCH_MP_TAC MLD_FIPS204_SIGN_TERMINATES_ALL THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_FIPS204_MATRIX_TERMINATES_LIST = prove
 (`!k l (f:num->byte).
        k <= 256 /\ l <= 256
        ==> mld_matrix_terminates k l (num_of_bytelist(list_of_seq f 32))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_FIPS204_MATRIX_TERMINATES THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`f:num->byte`; `32`] MLD_FIPS204_BYTELIST_NUM_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MLD_FIPS204_POLY_CHALLENGE_TERMINATES_LIST = prove
 (`!tau ctlen (f:num->byte).
        ctlen < 135 /\ tau <= 128
        ==> mld_poly_challenge_terminates tau ctlen
             (num_of_bytelist(list_of_seq f ctlen))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MLD_FIPS204_POLY_CHALLENGE_TERMINATES THEN
  ASM_REWRITE_TAC[MLD_FIPS204_BYTELIST_NUM_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* All the termination predicates of the three parameter sets, as rewrite    *)
(* rules !x. P x = T for rewriting the CORRECT theorems of the C functions,  *)
(* and MLD_FIPS204_DISCHARGE, which removes them from the hypotheses of such *)
(* a theorem.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_TERMINATES_RULES =
  let disch th = MP th (prove(lhand(concl th),CONV_TAC NUM_REDUCE_CONV)) in
  let eqt th = map (fun th -> EQT_INTRO th)
                [th] |> hd in
  let inst (k,l,tau,ct,kp,sg) =
    let kn = mk_small_numeral k and ln = mk_small_numeral l
    and taun = mk_small_numeral tau and ctn = mk_small_numeral ct in
    [GEN_ALL(disch(SPECL [kn; ln; `seed:num`]
                    MLD_FIPS204_MATRIX_TERMINATES_KEYPAIR));
     GEN_ALL(disch(SPECL [kn; ln; `sk:num->byte`]
                    MLD_FIPS204_MATRIX_TERMINATES_SK));
     GEN_ALL(disch(SPECL [kn; ln; `a:num`; `b:byte list`]
                    MLD_FIPS204_MATRIX_TERMINATES_SLICE));
     GEN_ALL(disch(SPECL [kn; ln; `f:num->byte`]
                    MLD_FIPS204_MATRIX_TERMINATES_LIST));
     GEN_ALL(disch(SPECL [taun; ctn; `a:num`; `b:byte list`]
                    MLD_FIPS204_POLY_CHALLENGE_TERMINATES_SLICE));
     GEN_ALL(disch(SPECL [taun; ctn; `f:num->byte`]
                    MLD_FIPS204_POLY_CHALLENGE_TERMINATES_LIST));
     kp; sg] in
  ignore eqt;
  end_itlist (@)
   [inst (4,4,39,32,MLD_FIPS204_KEYPAIR_TERMINATES_44,
                    MLD_FIPS204_SIGN_TERMINATES_44);
    inst (6,5,49,48,MLD_FIPS204_KEYPAIR_TERMINATES_65,
                    MLD_FIPS204_SIGN_TERMINATES_65);
    inst (8,7,60,64,MLD_FIPS204_KEYPAIR_TERMINATES_87,
                    MLD_FIPS204_SIGN_TERMINATES_87)];;

let MLD_FIPS204_DISCHARGE =
  PURE_REWRITE_RULE
   (MLD_FIPS204_TERMINATES_RULES @
    [AND_CLAUSES; IMP_CLAUSES; FORALL_SIMP; EXISTS_SIMP]);;
