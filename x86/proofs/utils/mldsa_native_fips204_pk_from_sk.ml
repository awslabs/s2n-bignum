(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key in mldsa-native and FIPS 204: for each     *)
(* parameter set, the public key that the specification of mldsa-native's    *)
(* mld_sign_pk_from_sk (mld_pk_from_sk_pk of common/mldsa_native_sign.ml)    *)
(* computes from a secret key sk is pkEncode(rho, t1), where rho, s1 and s2  *)
(* are decoded from sk as by skDecode and (t1, t0) = Power2Round(A s1 + s2)  *)
(* as in key generation, and the check of the key (mld_pk_from_sk_valid)     *)
(* passes iff s1 and s2 are within [-eta, eta], t0 is the one in sk and tr   *)
(* is H(pk, 64).                                                             *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_fips204_keypair.ml";;

(* ------------------------------------------------------------------------- *)
(* The results of the checks: the norm checks give 0 or all ones, so the OR  *)
(* of two is 0 iff both are; the constant-time comparison is 0 iff the byte  *)
(* strings are equal; and the norm check with bound eta + 1 of polynomials   *)
(* unpacked as eta minus a field of c <= 4 bits passes iff every field is at *)
(* most 2 * eta.                                                             *)
(* ------------------------------------------------------------------------- *)

let MLD_POLYVEC_CHKNORM_CASES = prove
 (`!n (x:num->int32) B.
        mld_polyvec_chknorm n x B = word 0 \/
        mld_polyvec_chknorm n x B = word 4294967295`,
  INDUCT_TAC THEN REWRITE_TAC[mld_polyvec_chknorm] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_poly_chknorm] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o SPECL [`x:num->int32`; `B:int32`]) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let MLD_POLYVEC_CHKNORM_OR = prove
 (`!m n (x:num->int32) y B C.
        word_zx(word_or (mld_polyvec_chknorm m x B)
                        (mld_polyvec_chknorm n y C)):byte = word 0 <=>
        mld_polyvec_chknorm m x B = word 0 /\
        mld_polyvec_chknorm n y C = word 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`m:num`; `x:num->int32`; `B:int32`]
               MLD_POLYVEC_CHKNORM_CASES) THEN
  MP_TAC(SPECL [`n:num`; `y:num->int32`; `C:int32`]
               MLD_POLYVEC_CHKNORM_CASES) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let MLD_LIST_OF_SEQ_EQ_ALT = prove
 (`!(f:num->A) g n.
        list_of_seq f n = list_of_seq g n <=> !i. i < n ==> f i = g i`,
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let MLD_CT_MEMCMP_EQ = prove
 (`!(a:num->byte) b len.
        mld_ct_memcmp a b len = word 0 <=>
        list_of_seq a len = list_of_seq b len`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_ct_memcmp; MLD_LIST_OF_SEQ_EQ_ALT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;
let MLD_FORALL_POLYVEC_INDEX = prove
 (`!n P. (!i. i < n ==> !j. j < 256 ==> P(256 * i + j)) <=>
         (!m. m < 256 * n ==> P m)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `m DIV 256`) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `m MOD 256`) THEN
    REWRITE_TAC[ARITH_RULE `256 * m DIV 256 + m MOD 256 = m`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC]);;

let MLD_FIPS204_CHKNORM_ETA = prove
 (`!n (x:num->int32) eta c b.
        eta <= 4 /\ c <= 4 /\
        (!m. m < 256 * n ==> ival(x m) = &eta - mldsa_field c b m)
        ==> (mld_polyvec_chknorm n x (word(eta + 1)) = word 0 <=>
             !m. m < 256 * n ==> mldsa_field c b m <= &(2 * eta))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m. &0 <= mldsa_field c b m /\ mldsa_field c b m < &16`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP c <= 16` MP_TAC THENL
     [TRANS_TAC LE_TRANS `2 EXP 4` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_POW] THEN
    MESON_TAC[MLDSA_FIELD_BOUND; INT_LTE_TRANS];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_POLYVEC_CHKNORM o
    lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; SIMPLE_ARITH_TAC] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl)) THEN
    UNDISCH_TAC `eta <= 4` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[mldsa_vec_norm_lt; mldsa_norm_lt] THEN
  SIMP_TAC[COEFF_MLDSA_POLY; MLDSA_MODPM_REM] THEN
  SUBGOAL_THEN
   `!m. m < 256 * n
        ==> (abs(mldsa_modpm (ival((x:num->int32) m)) 8380417) < &(eta + 1) <=>
             mldsa_field c b m <= &(2 * eta))`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o
      check (fun th -> free_in `&16:int` (concl th))) THEN
    UNDISCH_TAC `eta <= 4` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    SPEC_TAC(`mldsa_field c b m`,`f:int`) THEN REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_MODPM_SMALL o
      rand o lhand o lhand o snd) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`;
    `\m. abs(mldsa_modpm (ival((x:num->int32) m)) 8380417) < &(eta + 1)`]
    MLD_FORALL_POLYVEC_INDEX) THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let MLD_FIPS204_EQ_RHS_TAC =
  MATCH_MP_TAC(MESON[] `!a b c:A. b = c ==> (a = b <=> a = c)`);;

(* ------------------------------------------------------------------------- *)
(* The public key and the check, for the three parameter sets. The proof,    *)
(* the same for the three, follows that of key generation; the parameters    *)
(* of the set come from the goal, and the lemmas for unpacking s1 and s2 and *)
(* for compute_t are arguments.                                              *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_PK_FROM_SK_TAC (unpack_th,computet_th) =
  W(fun (asl,w) ->
    let vtm = find_term (fun t -> try fst(strip_comb t) =
                                      `mld_pk_from_sk_valid`
                                  with Failure _ -> false) w in
    match snd(strip_comb vtm) with
      [k_tm; l_tm; eta_tm; unpack_tm; p_tm; _] ->
    let k = dest_small_numeral k_tm and l = dest_small_numeral l_tm
    and eta = dest_small_numeral eta_tm and p = dest_small_numeral p_tm in
    let tab =
      map (fun (s,n) -> s,mk_small_numeral n)
       ["k",k; "l",l; "eta",eta; "p",p; "c",(if eta = 2 then 3 else 4);
        "nl",256 * l; "nk",256 * k; "pl",p * l; "pk",p * k;
        "s2off",128 + p * l; "t0off",128 + p * (l + k); "t0len",416 * k;
        "t1len",320 * k; "pklen",32 + 320 * k] @
      ["unpack",unpack_tm] in
    let kp = MLD_FIPS204_KEYPAIR_INST tab in
    GEN_TAC THEN DISCH_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SIMP_TAC[MLD_FIPS204_SLICE_LIST_OF_SEQ; ARITH] THEN
    REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN

    (*** s1 and s2 as the C code unpacks them ***)

    SUBGOAL_THEN(kp
     `!n. n < nl
          ==> ival(mld_sk_s1 unpack p skb n) =
              &eta - mldsa_field c (list_of_seq (\i. skb(128 + i)) pl) n`)
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[mld_sk_s1] THEN
      MP_TAC(ISPECL [l_tm; `\j. (skb:num->byte)(128 + j)`; `n:num`]
                    unpack_th) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN(kp
     `!n. n < nk
          ==> ival(mld_sk_s2 l unpack p skb n) =
              &eta - mldsa_field c (list_of_seq (\i. skb(s2off + i)) pk) n`)
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[mld_sk_s2] THEN
      REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC(ISPECL [k_tm; kp `\j. (skb:num->byte)(s2off + j)`; `n:num`]
                    unpack_th) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    (*** The coefficients of t ***)

    SUBGOAL_THEN(kp
     `!n. n < nk
          ==> ival(mld_pk_from_sk_t l unpack p skb n) =
              coeff (n MOD 256)
               (ring_add mldsa_rq
                 (mldsa_dot l
                   (mldsa_expand_a (list_of_seq skb 32) (n DIV 256))
                   (\i. mldsa_poly
                         (\j. &eta - mldsa_field c
                                      (list_of_seq (\i. skb(128 + i)) pl)
                                      (256 * i + j))))
                 (mldsa_poly
                   (\j. &eta - mldsa_field c
                                (list_of_seq (\i. skb(s2off + i)) pk)
                                (256 * n DIV 256 + j))))`)
    ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MP_TAC(ARITH_RULE(kp
       `n < nk ==> n = 256 * n DIV 256 + n MOD 256 /\
                   n DIV 256 < k /\ n MOD 256 < 256`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC
        (LAND_CONV o RAND_CONV o RAND_CONV) [th]) STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[mld_pk_from_sk_t] THEN
      MP_TAC(BETA_RULE(ISPECL
       [k_tm; unpack_tm; p_tm; `mld_sk_rho skb`;
        kp `mld_polyvec_map mld_poly_ntt (mld_sk_s1 unpack p skb)`;
        kp `\j. (skb:num->byte)(128 + l * p + j)`;
        kp `\i. mldsa_poly
                 (\j. &eta - mldsa_field c
                              (list_of_seq (\i. skb(128 + i)) pl)
                              (256 * i + j))`;
        `n DIV 256`; `n MOD 256`] computet_th)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MLDSA_POLY_IN_RQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[mld_sk_rho] THEN
          MP_TAC(ISPEC `list_of_seq (skb:num->byte) 32`
                       NUM_OF_BYTELIST_BOUND) THEN
          REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[];
          MP_TAC(ISPECL [l_tm; kp `mld_sk_s1 unpack p skb`]
                        MLD_FIPS204_POLYVEC_NTT) THEN
          ANTS_TAC THENL
           [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
            FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
              check (free_in `mld_sk_s1` o concl)) THEN
            ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
            MP_TAC(ISPECL [kp `c:num`;
                           kp `list_of_seq (\i. (skb:num->byte)(128 + i)) pl`;
                           `j:num`] MLDSA_FIELD_BOUND) THEN
            CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC;
            ALL_TAC] THEN
          MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
          MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
          DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(TAUT `(a <=> b) ==> a /\ c ==> b /\ c`) THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          MATCH_MP_TAC MLDSA_POLY_EXT THEN X_GEN_TAC `i:num` THEN
          DISCH_TAC THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          SIMPLE_ARITH_TAC;
          X_GEN_TAC `m:num` THEN DISCH_TAC THEN
          MP_TAC(ISPECL [p_tm; unpack_tm;
                         kp `\j. (skb:num->byte)(128 + l * p + j)`;
                         `n DIV 256`; `m:num`] MLD_POLYVEC_UNPACK_COEFF) THEN
          ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `256 * n DIV 256 + m` o
            check (free_in `mld_sk_s2` o concl)) THEN
          REWRITE_TAC[mld_sk_s2] THEN CONV_TAC NUM_REDUCE_CONV THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
          MP_TAC(ISPECL [kp `c:num`;
                         kp `list_of_seq (\i. (skb:num->byte)(s2off + i)) pk`;
                         `256 * n DIV 256 + m`] MLDSA_FIELD_BOUND) THEN
          CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
       [AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[mld_sk_rho] THEN
        MP_TAC(ISPEC `list_of_seq (skb:num->byte) 32`
                     BYTELIST_OF_NUM_OF_BYTELIST) THEN
        REWRITE_TAC[LENGTH_LIST_OF_SEQ];
        MATCH_MP_TAC MLDSA_POLY_EXT THEN X_GEN_TAC `m:num` THEN
        DISCH_TAC THEN BETA_TAC THEN
        MP_TAC(ISPECL [p_tm; unpack_tm;
                       kp `\j. (skb:num->byte)(128 + l * p + j)`;
                       `n DIV 256`; `m:num`] MLD_POLYVEC_UNPACK_COEFF) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `256 * n DIV 256 + m` o
          check (free_in `mld_sk_s2` o concl)) THEN
        REWRITE_TAC[mld_sk_s2] THEN
        ANTS_TAC THENL [SIMPLE_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN

    (*** Their ranges and Power2Round ***)

    ABBREV_TAC(kp `TT = mld_pk_from_sk_t l unpack p skb`) THEN
    SUBGOAL_THEN(kp
     `!n. n < nk
          ==> ival((TT:num->int32) n) =
              coeff (n MOD 256)
               (ring_add mldsa_rq
                 (mldsa_dot l
                   (mldsa_expand_a (list_of_seq skb 32) (n DIV 256))
                   (\i. mldsa_poly
                         (\j. &eta - mldsa_field c
                                      (list_of_seq (\i. skb(128 + i)) pl)
                                      (256 * i + j))))
                 (mldsa_poly
                   (\j. &eta - mldsa_field c
                                (list_of_seq (\i. skb(s2off + i)) pk)
                                (256 * n DIV 256 + j)))) /\
              &0 <= ival(TT n) /\ ival(TT n) < &8380417 /\
              (ival(mld_power2round_hi(TT n)),
               ival(mld_power2round_lo(TT n))) =
              mldsa_power2round(ival(TT n))`)
    ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `TT:num->int32` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
      MATCH_MP_TAC(TAUT `(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MLDSA_RQ_COEFF THEN
        SIMP_TAC[RING_ADD; MLDSA_DOT_IN_RQ; MLDSA_POLY_IN_RQ];
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN STRIP_TAC THEN
        MATCH_MP_TAC MLD_FIPS204_POWER2ROUND THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN

    (*** The public key ***)

    SUBGOAL_THEN(kp
     `list_of_seq (mld_pk_from_sk_pk l unpack p skb) pklen =
      APPEND (list_of_seq skb 32)
       (mldsa_encode 10 nk
         (\n. ival(mld_power2round_hi((TT:num->int32) n))))`)
    ASSUME_TAC THENL
     [REWRITE_TAC[mld_pk_from_sk_pk] THEN
      ASM_REWRITE_TAC[ARITH_RULE(kp `pklen = 32 + t1len`);
                      MLD_LIST_OF_SEQ_ADD] THEN
      BINOP_TAC THENL
       [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `~(32 + k < 32) /\ (32 + k) - 32 = k`] THEN
      REWRITE_TAC[ETA_AX] THEN
      MP_TAC(ISPECL [k_tm;
       `mld_polyvec_map mld_poly_power2round_hi (TT:num->int32)`]
       MLD_FIPS204_POLYVEC_T1_PACK) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN(kp
       `!i. i < nk
            ==> ival(mld_polyvec_map mld_poly_power2round_hi
                      (TT:num->int32) i) =
                ival(mld_power2round_hi(TT i))`)
      ASSUME_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
        MP_TAC(ISPECL [`mld_poly_power2round_hi`; `TT:num->int32`;
                       `i DIV 256`; `i MOD 256`] MLD_POLYVEC_MAP_COEFF) THEN
        REWRITE_TAC[MOD_LT_EQ; ARITH_EQ;
                    ARITH_RULE `256 * i DIV 256 + i MOD 256 = i`] THEN
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[mld_poly_power2round_hi; mld_poly_of] THEN
        REWRITE_TAC[ARITH_RULE `256 * i DIV 256 + i MOD 256 = i`];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
          check (fun th -> is_forall(concl th) &&
                           free_in `mldsa_power2round` (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `ival((TT:num->int32) i)` MLDSA_POWER2ROUND_BOUNDS) THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FST; SND] THEN
        SIMP_TAC[];
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MLDSA_ENCODE_EQ THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MLD_FIPS204_ENCODE_SUBST_TAC
     (kp `mldsa_encode 10 nk f`)
     (kp `mldsa_encode 10 nk
           (\n. ival(mld_power2round_hi((TT:num->int32) n)))`)
     (MLD_FIPS204_TFACT_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        free_in `mldsa_power2round` (concl th) && is_eq(concl th) &&
        not(is_forall(concl th)))) THEN
      REWRITE_TAC[FST]) THEN
    MLD_FIPS204_ENCODE_SUBST_TAC
     (kp `mldsa_encode 13 nk f`)
     (kp `mldsa_encode 13 nk
           (\n. &4096 - ival(mld_power2round_lo((TT:num->int32) n)))`)
     (MLD_FIPS204_TFACT_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        free_in `mldsa_power2round` (concl th) && is_eq(concl th) &&
        not(is_forall(concl th)))) THEN
      REWRITE_TAC[SND]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `mld_pk_from_sk_pk` (concl th))) THEN

    (*** The checks ***)

    REWRITE_TAC[mld_pk_from_sk_valid; MLD_POLYVEC_CHKNORM_OR;
                MLD_CT_MEMCMP_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_THEN(kp `mld_pk_from_sk_t l unpack p skb = TT`)
     (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC(TAUT `(a <=> a') /\ (b <=> b') /\ (c <=> c') /\ (d <=> d')
                       ==> (a /\ b /\ c /\ d <=> a' /\ b' /\ c' /\ d')`) THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [l_tm; kp `mld_sk_s1 unpack p skb`; eta_tm; kp `c:num`;
                     kp `list_of_seq (\i. (skb:num->byte)(128 + i)) pl`]
                    MLD_FIPS204_CHKNORM_ETA) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [k_tm; kp `mld_sk_s2 l unpack p skb`; eta_tm; kp `c:num`;
                     kp `list_of_seq (\i. (skb:num->byte)(s2off + i)) pk`]
                    MLD_FIPS204_CHKNORM_ETA) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[];
      REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN MLD_FIPS204_EQ_RHS_TAC THEN
      MP_TAC(ISPECL [k_tm;
                     `mld_polyvec_map mld_poly_power2round_lo (TT:num->int32)`]
                    MLD_FIPS204_POLYVEC_T0_PACK) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN(kp
       `!i. i < nk
            ==> ival(mld_polyvec_map mld_poly_power2round_lo
                      (TT:num->int32) i) =
                ival(mld_power2round_lo(TT i))`)
      ASSUME_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
        MP_TAC(ISPECL [`mld_poly_power2round_lo`; `TT:num->int32`;
                       `i DIV 256`; `i MOD 256`] MLD_POLYVEC_MAP_COEFF) THEN
        REWRITE_TAC[MOD_LT_EQ; ARITH_EQ;
                    ARITH_RULE `256 * i DIV 256 + i MOD 256 = i`] THEN
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[mld_poly_power2round_lo; mld_poly_of] THEN
        REWRITE_TAC[ARITH_RULE `256 * i DIV 256 + i MOD 256 = i`];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
          check (fun th -> is_forall(concl th) &&
                           free_in `mldsa_power2round` (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(SPEC `ival((TT:num->int32) i)` MLDSA_POWER2ROUND_BOUNDS) THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          free_in `mldsa_power2round` (concl th) && is_eq(concl th) &&
          not(is_forall(concl th)))) THEN
        REWRITE_TAC[FST; SND] THEN INT_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MLDSA_ENCODE_EQ THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[mldsa_h] THEN MLD_FIPS204_EQ_RHS_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_SHAKE256_BYTE o
        lhand o snd) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPEC (kp `list_of_seq (mld_pk_from_sk_pk l unpack p skb)
                                      pklen`)
                     NUM_OF_BYTELIST_BOUND) THEN
        REWRITE_TAC[LENGTH_LIST_OF_SEQ; EXP_MULT] THEN
        CONV_TAC NUM_REDUCE_CONV;
        DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN
      MP_TAC(ISPEC (kp `list_of_seq (mld_pk_from_sk_pk l unpack p skb) pklen`)
                   BYTELIST_OF_NUM_OF_BYTELIST) THEN
      REWRITE_TAC[LENGTH_LIST_OF_SEQ]]
    | _ -> failwith "MLD_FIPS204_PK_FROM_SK_TAC");;

let MLD_FIPS204_PK_FROM_SK_44 = prove
 (`!skb:num->byte.
     mld_matrix_terminates 4 4 (mld_sk_rho skb)
     ==> let sk = list_of_seq skb 2560 in
         let rho = mldsa_slice 0 32 sk
         and s1b = mldsa_slice 128 384 sk
         and s2b = mldsa_slice 512 384 sk
         and t0b = mldsa_slice 896 1664 sk in
         let s1 = \i. mldsa_poly(\j. &2 - mldsa_field 3 s1b (256 * i + j))
         and s2 = \i. mldsa_poly(\j. &2 - mldsa_field 3 s2b (256 * i + j)) in
         let t = \i. ring_add mldsa_rq
                      (mldsa_dot 4 (mldsa_expand_a rho i) s1) (s2 i) in
         let pk = APPEND rho
                   (mldsa_encode 10 1024
                     (\n. FST(mldsa_power2round
                               (coeff (n MOD 256) (t(n DIV 256)))))) in
         list_of_seq (mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 skb) 1312 =
         pk /\
         (mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96 skb <=>
          (!n. n < 1024 ==> mldsa_field 3 s1b n <= &4) /\
          (!n. n < 1024 ==> mldsa_field 3 s2b n <= &4) /\
          t0b = mldsa_encode 13 1024
                 (\n. &4096 - SND(mldsa_power2round
                                   (coeff (n MOD 256) (t(n DIV 256))))) /\
          mldsa_slice 64 64 sk = mldsa_h pk 64)`,
  MLD_FIPS204_PK_FROM_SK_TAC
   (MLD_FIPS204_POLYVEC_ETA_UNPACK_2,MLD_FIPS204_COMPUTE_T_L4));;

let MLD_FIPS204_PK_FROM_SK_65 = prove
 (`!skb:num->byte.
     mld_matrix_terminates 6 5 (mld_sk_rho skb)
     ==> let sk = list_of_seq skb 4032 in
         let rho = mldsa_slice 0 32 sk
         and s1b = mldsa_slice 128 640 sk
         and s2b = mldsa_slice 768 768 sk
         and t0b = mldsa_slice 1536 2496 sk in
         let s1 = \i. mldsa_poly(\j. &4 - mldsa_field 4 s1b (256 * i + j))
         and s2 = \i. mldsa_poly(\j. &4 - mldsa_field 4 s2b (256 * i + j)) in
         let t = \i. ring_add mldsa_rq
                      (mldsa_dot 5 (mldsa_expand_a rho i) s1) (s2 i) in
         let pk = APPEND rho
                   (mldsa_encode 10 1536
                     (\n. FST(mldsa_power2round
                               (coeff (n MOD 256) (t(n DIV 256)))))) in
         list_of_seq (mld_pk_from_sk_pk 5 mld_polyeta_unpack_4 128 skb) 1952 =
         pk /\
         (mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4 128 skb <=>
          (!n. n < 1280 ==> mldsa_field 4 s1b n <= &8) /\
          (!n. n < 1536 ==> mldsa_field 4 s2b n <= &8) /\
          t0b = mldsa_encode 13 1536
                 (\n. &4096 - SND(mldsa_power2round
                                   (coeff (n MOD 256) (t(n DIV 256))))) /\
          mldsa_slice 64 64 sk = mldsa_h pk 64)`,
  MLD_FIPS204_PK_FROM_SK_TAC
   (MLD_FIPS204_POLYVEC_ETA_UNPACK_4,MLD_FIPS204_COMPUTE_T_L5));;

let MLD_FIPS204_PK_FROM_SK_87 = prove
 (`!skb:num->byte.
     mld_matrix_terminates 8 7 (mld_sk_rho skb)
     ==> let sk = list_of_seq skb 4896 in
         let rho = mldsa_slice 0 32 sk
         and s1b = mldsa_slice 128 672 sk
         and s2b = mldsa_slice 800 768 sk
         and t0b = mldsa_slice 1568 3328 sk in
         let s1 = \i. mldsa_poly(\j. &2 - mldsa_field 3 s1b (256 * i + j))
         and s2 = \i. mldsa_poly(\j. &2 - mldsa_field 3 s2b (256 * i + j)) in
         let t = \i. ring_add mldsa_rq
                      (mldsa_dot 7 (mldsa_expand_a rho i) s1) (s2 i) in
         let pk = APPEND rho
                   (mldsa_encode 10 2048
                     (\n. FST(mldsa_power2round
                               (coeff (n MOD 256) (t(n DIV 256)))))) in
         list_of_seq (mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96 skb) 2592 =
         pk /\
         (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96 skb <=>
          (!n. n < 1792 ==> mldsa_field 3 s1b n <= &4) /\
          (!n. n < 2048 ==> mldsa_field 3 s2b n <= &4) /\
          t0b = mldsa_encode 13 2048
                 (\n. &4096 - SND(mldsa_power2round
                                   (coeff (n MOD 256) (t(n DIV 256))))) /\
          mldsa_slice 64 64 sk = mldsa_h pk 64)`,
  MLD_FIPS204_PK_FROM_SK_TAC
   (MLD_FIPS204_POLYVEC_ETA_UNPACK_2,MLD_FIPS204_COMPUTE_T_L7));;

(* ------------------------------------------------------------------------- *)
(* The secret key of key generation decodes to its parts: for the three      *)
(* parameter sets, assuming that the samplings of key generation terminate,  *)
(* the code accepts the secret key that FIPS 204 key generation gives for a  *)
(* seed and computes from it the public key of that key generation.          *)
(* MLDSA_KEYGEN_INTERNAL_SK gives the parts of the secret key of             *)
(* mldsa_keygen_internal, and MLDSA_KEYGEN_INTERNAL_SKDECODE, when the       *)
(* coefficients of s1 and s2 are within [-eta,eta], the conditions of        *)
(* MLD_FIPS204_PK_FROM_SK_44 etc. for it.                                    *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_REJ_BOUNDED_POLY_SMALL = prove
 (`!eta rho i.
        (eta = 2 \/ eta = 4) /\ rho < 2 EXP 512 /\ i < 256 /\
        mld_rej_eta_terminates eta
         (mld_shake256_stream 66 (rho + 2 EXP 512 * i))
        ==> !m. abs(mldsa_modpm
                     (coeff m (mldsa_rej_bounded_poly eta
                                (APPEND (bytelist_of_num 64 rho)
                                        (bytelist_of_num 2 i))))
                     8380417) <= &eta`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word i:byte) = i` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(if eta = 2 then 2 else 4) = eta` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`eta:num`; `rho:num`; `word i:byte`]
               MLD_FIPS204_POLY_UNIFORM_ETA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[COEFF_MLDSA_POLY] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`eta:num`; `rho:num`; `word i:byte`; `m:num`]
                 MLD_FIPS204_POLY_UNIFORM_ETA_BOUND) THEN
    ASM_REWRITE_TAC[MLDSA_MODPM_REM] THEN
    SPEC_TAC(`ival(mld_poly_uniform_eta eta rho (word i) m)`,`x:int`) THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_MODPM_SMALL o
      rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `abs(x:int) <= &eta` THEN
      UNDISCH_TAC `eta = 2 \/ eta = 4` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`&0:int`; `8380417`] MLDSA_MODPM_SMALL) THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC]);;

let LENGTH_MLDSA_ENCODE = prove
 (`!c n f. LENGTH(mldsa_encode c n f) = (c * n) DIV 8`,
  REWRITE_TAC[mldsa_encode; LENGTH_BYTELIST_OF_NUM]);;

let MLDSA_SLICE_ALL = prove
 (`!n (l:byte list). LENGTH l = n ==> mldsa_slice 0 n l = l`,
  MESON_TAC[MLDSA_SLICE_LENGTH]);;

let MLDSA_POLY_MODPM_COEFF = prove
 (`!f. f IN ring_carrier mldsa_rq
       ==> mldsa_poly(\j. mldsa_modpm (coeff j f) 8380417) = f`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_POLY_EQ] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`coeff i (f:(1->num)->int)`; `8380417`] MLDSA_MODPM) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MLD_FIPS204_SLICE_STEP_TAC =
  let c1 = CONJUNCT1(SPEC_ALL MLDSA_SLICE_APPEND)
  and c2 = CONJUNCT2(SPEC_ALL MLDSA_SLICE_APPEND)
  and nrm = ARITH_RULE `y <= x ==> (x + a) - y = (x - y) + a` in
  W(fun (asl,w) ->
    let t = lhand w in
    (MP_TAC(PART_MATCH (lhand o rand) c1 t) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_THEN SUBST1_TAC])
    ORELSE
    (MP_TAC(PART_MATCH (lhand o rand) c2 t) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[nrm; ARITH; ADD_CLAUSES; ADD_SUB; ADD_SUB2; SUB_REFL] THEN
     CONV_TAC NUM_REDUCE_CONV));;

let MLD_FIPS204_SK_SLICES = prove
 (`!(rho:byte list) key tr s1b s2b t0b a b c.
        LENGTH rho = 32 /\ LENGTH key = 32 /\ LENGTH tr = 64 /\
        LENGTH s1b = a /\ LENGTH s2b = b /\ LENGTH t0b = c
        ==> LENGTH(APPEND rho (APPEND key (APPEND tr
                    (APPEND s1b (APPEND s2b t0b))))) = 128 + a + b + c /\
            mldsa_slice 0 32 (APPEND rho (APPEND key (APPEND tr
                    (APPEND s1b (APPEND s2b t0b))))) = rho /\
            mldsa_slice 64 64 (APPEND rho (APPEND key (APPEND tr
                    (APPEND s1b (APPEND s2b t0b))))) = tr /\
            mldsa_slice 128 a (APPEND rho (APPEND key (APPEND tr
                    (APPEND s1b (APPEND s2b t0b))))) = s1b /\
            mldsa_slice (128 + a) b (APPEND rho (APPEND key (APPEND tr
                    (APPEND s1b (APPEND s2b t0b))))) = s2b /\
            mldsa_slice (128 + a + b) c (APPEND rho (APPEND key (APPEND tr
                    (APPEND s1b (APPEND s2b t0b))))) = t0b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT MLD_FIPS204_SLICE_STEP_TAC THEN
  MATCH_MP_TAC MLDSA_SLICE_ALL THEN ASM_REWRITE_TAC[]);;

let MLDSA_KEYGEN_INTERNAL_SK = prove
 (`!k l eta tau lam gamma1 gamma2 omega xi.
    let c = mldsa_bitlen(2 * eta) in
    let seeds = mldsa_h (APPEND xi [word k; word l]) 128 in
    let rho = mldsa_slice 0 32 seeds and rho' = mldsa_slice 32 64 seeds in
    let s1 = \i. mldsa_rej_bounded_poly eta
                  (APPEND rho' (bytelist_of_num 2 i))
    and s2 = \i. mldsa_rej_bounded_poly eta
                  (APPEND rho' (bytelist_of_num 2 (l + i))) in
    let t = \i. ring_add mldsa_rq (mldsa_dot l (mldsa_expand_a rho i) s1)
                                  (s2 i) in
    let pk = FST(mldsa_keygen_internal
                  (k,l,eta,tau,lam,gamma1,gamma2,omega) xi)
    and sk = SND(mldsa_keygen_internal
                  (k,l,eta,tau,lam,gamma1,gamma2,omega) xi) in
    LENGTH sk = 128 + 32 * c * l + 32 * c * k + 416 * k /\
    mldsa_slice 0 32 sk = rho /\
    mldsa_slice 64 64 sk = mldsa_h pk 64 /\
    mldsa_slice 128 (32 * c * l) sk =
    mldsa_encode c (256 * l)
     (\n. &eta - mldsa_modpm (coeff (n MOD 256) (s1(n DIV 256))) 8380417) /\
    mldsa_slice (128 + 32 * c * l) (32 * c * k) sk =
    mldsa_encode c (256 * k)
     (\n. &eta - mldsa_modpm (coeff (n MOD 256) (s2(n DIV 256))) 8380417) /\
    mldsa_slice (128 + 32 * c * l + 32 * c * k) (416 * k) sk =
    mldsa_encode 13 (256 * k)
     (\n. &4096 - SND(mldsa_power2round(coeff (n MOD 256) (t(n DIV 256))))) /\
    pk = APPEND rho
          (mldsa_encode 10 (256 * k)
            (\n. FST(mldsa_power2round(coeff (n MOD 256) (t(n DIV 256))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_keygen_internal] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC MLD_FIPS204_SK_SLICES THEN
  REWRITE_TAC[LENGTH_MLDSA_SLICE; LENGTH_MLDSA_ENCODE; mldsa_h;
              LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[ARITH_RULE `c * 256 * l = 8 * (32 * c * l)`;
              ARITH_RULE `13 * 256 * k = 8 * (416 * k)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let MLD_FIPS204_DECODE_TAC eth =
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(fun (asl,w) -> GEN_REWRITE_TAC RAND_CONV
    [GSYM(MATCH_MP MLDSA_POLY_MODPM_COEFF
      (ISPECL [`eta:num`; rand(rand w)] MLDSA_REJ_BOUNDED_POLY_IN_RQ))]) THEN
  MATCH_MP_TAC MLDSA_POLY_EXT THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * i + j` o check (fun th ->
    is_forall(concl th) && free_in eth (concl th) &&
    free_in `mldsa_field` (concl th) &&
    not(free_in `mldsa_poly` (concl th)))) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(256 * i + j) DIV 256 = i /\ (256 * i + j) MOD 256 = j`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ADD_CLAUSES;
                 ARITH_EQ];
    INT_ARITH_TAC];;
let MLDSA_KEYGEN_INTERNAL_SKDECODE = prove
 (`!k l eta tau lam gamma1 gamma2 omega xi.
    (eta = 2 \/ eta = 4) /\
    (!i m. i < l + k
           ==> abs(mldsa_modpm
                    (coeff m (mldsa_rej_bounded_poly eta
                      (APPEND (mldsa_slice 32 64
                                (mldsa_h (APPEND xi [word k; word l]) 128))
                              (bytelist_of_num 2 i))))
                    8380417) <= &eta)
    ==> let pk = FST(mldsa_keygen_internal
                      (k,l,eta,tau,lam,gamma1,gamma2,omega) xi)
        and sk = SND(mldsa_keygen_internal
                      (k,l,eta,tau,lam,gamma1,gamma2,omega) xi) in
        let c = mldsa_bitlen(2 * eta) in
        let rho = mldsa_slice 0 32 sk
        and s1b = mldsa_slice 128 (32 * c * l) sk
        and s2b = mldsa_slice (128 + 32 * c * l) (32 * c * k) sk
        and t0b = mldsa_slice (128 + 32 * c * l + 32 * c * k) (416 * k) sk in
        let s1 = \i. mldsa_poly(\j. &eta - mldsa_field c s1b (256 * i + j))
        and s2 = \i. mldsa_poly(\j. &eta - mldsa_field c s2b (256 * i + j)) in
        let t = \i. ring_add mldsa_rq
                     (mldsa_dot l (mldsa_expand_a rho i) s1) (s2 i) in
        let pk' = APPEND rho
                   (mldsa_encode 10 (256 * k)
                     (\n. FST(mldsa_power2round
                               (coeff (n MOD 256) (t(n DIV 256)))))) in
        pk' = pk /\
        (!n. n < 256 * l ==> mldsa_field c s1b n <= &(2 * eta)) /\
        (!n. n < 256 * k ==> mldsa_field c s2b n <= &(2 * eta)) /\
        t0b = mldsa_encode 13 (256 * k)
               (\n. &4096 - SND(mldsa_power2round
                                 (coeff (n MOD 256) (t(n DIV 256))))) /\
        mldsa_slice 64 64 sk = mldsa_h pk' 64`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(SPECL [`k:num`; `l:num`; `eta:num`; `tau:num`; `lam:num`;
                `gamma1:num`; `gamma2:num`; `omega:num`; `xi:byte list`]
               MLDSA_KEYGEN_INTERNAL_SK) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `SK = SND(mldsa_keygen_internal
                        (k,l,eta,tau,lam,gamma1,gamma2,omega) xi)` THEN
  ABBREV_TAC `PK = FST(mldsa_keygen_internal
                        (k,l,eta,tau,lam,gamma1,gamma2,omega) xi)` THEN
  ABBREV_TAC `c = mldsa_bitlen(2 * eta)` THEN
  ABBREV_TAC `RP = mldsa_slice 32 64
                    (mldsa_h (APPEND xi [word k; word l]) 128)` THEN
  ABBREV_TAC `RHO = mldsa_slice 0 32
                    (mldsa_h (APPEND xi [word k; word l]) 128)` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
RULE_ASSUM_TAC BETA_RULE THEN
  ABBREV_TAC `E1 = mldsa_encode c (256 * l)
     (\n. &eta - mldsa_modpm (coeff (n MOD 256)
            (mldsa_rej_bounded_poly eta
              (APPEND RP (bytelist_of_num 2 (n DIV 256))))) 8380417)` THEN
  ABBREV_TAC `E2 = mldsa_encode c (256 * k)
     (\n. &eta - mldsa_modpm (coeff (n MOD 256)
            (mldsa_rej_bounded_poly eta
              (APPEND RP (bytelist_of_num 2 (l + n DIV 256))))) 8380417)` THEN
  SUBGOAL_THEN `&2 * &eta < (&2:int) pow c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n < 256 * l
        ==> mldsa_field c E1 n =
            &eta - mldsa_modpm (coeff (n MOD 256)
             (mldsa_rej_bounded_poly eta
               (APPEND RP (bytelist_of_num 2 (n DIV 256))))) 8380417`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXPAND_TAC "E1" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_FIELD_ENCODE_SMALL o
      lhand o snd) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `c * 256 * l = 8 * 32 * c * l`] THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n DIV 256`; `n MOD 256`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `mldsa_modpm` (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `n < 256 * l` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&2 * &eta < (&2:int) pow c` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
SUBGOAL_THEN
   `!n. n < 256 * k
        ==> mldsa_field c E2 n =
            &eta - mldsa_modpm (coeff (n MOD 256)
             (mldsa_rej_bounded_poly eta
               (APPEND RP (bytelist_of_num 2 (l + n DIV 256))))) 8380417`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXPAND_TAC "E2" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_FIELD_ENCODE_SMALL o
      lhand o snd) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `c * 256 * k = 8 * 32 * c * k`] THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l + n DIV 256`; `n MOD 256`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `abs:int->int` (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `n < 256 * k` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&2 * &eta < (&2:int) pow c` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
SUBGOAL_THEN
   `!i. i < l
        ==> mldsa_poly (\j. &eta - mldsa_field c E1 (256 * i + j)) =
            mldsa_rej_bounded_poly eta (APPEND RP (bytelist_of_num 2 i))`
  ASSUME_TAC THENL [MLD_FIPS204_DECODE_TAC `E1:byte list`; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> mldsa_poly (\j. &eta - mldsa_field c E2 (256 * i + j)) =
            mldsa_rej_bounded_poly eta
             (APPEND RP (bytelist_of_num 2 (l + i)))`
  ASSUME_TAC THENL [MLD_FIPS204_DECODE_TAC `E2:byte list`; ALL_TAC] THEN
SUBGOAL_THEN
   `!n. n < 256 * k
        ==> ring_add mldsa_rq
             (mldsa_dot l (mldsa_expand_a RHO (n DIV 256))
               (\i. mldsa_poly(\j. &eta - mldsa_field c E1 (256 * i + j))))
             (mldsa_poly(\j. &eta - mldsa_field c E2 (256 * n DIV 256 + j))) =
            ring_add mldsa_rq
             (mldsa_dot l (mldsa_expand_a RHO (n DIV 256))
               (\i. mldsa_rej_bounded_poly eta
                     (APPEND RP (bytelist_of_num 2 i))))
             (mldsa_rej_bounded_poly eta
               (APPEND RP (bytelist_of_num 2 (l + n DIV 256))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN BINOP_TAC THENL
     [MATCH_MP_TAC MLDSA_DOT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `E2:byte list` (concl th) &&
        free_in `mldsa_poly` (concl th))) THEN
      UNDISCH_TAC `n < 256 * k` THEN ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC MLDSA_ENCODE_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n DIV 256`; `n MOD 256`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `abs:int->int` (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `n < 256 * l` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l + n DIV 256`; `n MOD 256`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `abs:int->int` (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `n < 256 * k` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
    MATCH_MP_TAC MLDSA_ENCODE_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MLDSA_ENCODE_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]]);;

let MLD_FIPS204_PK_FROM_SK_KEYGEN_TAC (params_def,kpterm_def,pfs_th) =
  let tuple = rhs(concl params_def) in
  let comps = striplist dest_pair tuple in
  let k_tm = el 0 comps and l_tm = el 1 comps in
  let kg = mk_comb(mk_comb(`mldsa_keygen_internal`,lhs(concl params_def)),
                   `xi:byte list`) in
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `xi = bytelist_of_num 32 seed` THEN
  SUBGOAL_THEN `LENGTH(xi:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "xi" THEN REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[GSYM params_def]
    (CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (ISPECL (comps @ [`xi:byte list`]) MLDSA_KEYGEN_INTERNAL_SK))) THEN
  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   (subst [kg,`kg:byte list#byte list`; k_tm,`k:num`; l_tm,`l:num`]
     `mld_sk_rho (\j. EL j (SND(kg:byte list#byte list))) =
      mld_keypair_rho k l seed`)
  ASSUME_TAC THENL
   [REWRITE_TAC[mld_sk_rho; mld_keypair_rho] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [k_tm; l_tm; `seed:num`] MLD_FIPS204_KEYPAIR_SEEDBUF) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[params_def; mldsa_keygen_internal; mldsa_h] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[SND] THEN
    ASM_SIMP_TAC[EL_APPEND; LENGTH_MLDSA_SLICE; EL_MLDSA_SLICE;
                 EL_LIST_OF_SEQ; ADD_CLAUSES] THEN
    MATCH_MP_TAC EL_LIST_OF_SEQ THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[GSYM params_def]
    (CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (ISPECL (comps @ [`xi:byte list`]) MLDSA_KEYGEN_INTERNAL_SKDECODE))) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MP_TAC(SPECL [k_tm; l_tm; `seed:num`] MLD_FIPS204_KEYPAIR_SEEDBUF) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    MP_TAC(SPECL [k_tm; l_tm; `seed:num`] MLD_FIPS204_KEYPAIR_RHO) THEN
    ASM_REWRITE_TAC[mldsa_h] THEN
    SIMP_TAC[MLD_FIPS204_SLICE_LIST_OF_SEQ; ARITH] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2 th)]) THEN
    MATCH_MP_TAC MLD_FIPS204_REJ_BOUNDED_POLY_SMALL THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[mld_keypair_rhoprime] THEN
      W(MP_TAC o PART_MATCH lhand NUM_OF_BYTELIST_BOUND o lhand o snd) THEN
      REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[];
      SIMPLE_ARITH_TAC;
      UNDISCH_TAC (mk_comb(lhs(concl kpterm_def),`seed:num`)) THEN
      REWRITE_TAC[kpterm_def; mld_keypair_terminates] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN
  MP_TAC(SPEC (mk_abs(`j:num`,mk_comb(mk_comb(`EL:num->byte list->byte`,
                 `j:num`),mk_comb(`SND:byte list#byte list->byte list`,kg))))
              pfs_th) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       fst(dest_comb(lhs(concl th))) = `LENGTH:byte list->num`
    then REWRITE_TAC[GSYM th; LIST_OF_SEQ_EQ_SELF] THEN ASSUME_TAC th
    else NO_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  ASM_REWRITE_TAC[];;

let MLD_FIPS204_PK_FROM_SK_KEYGEN_44 = prove
 (`!seed. seed < 2 EXP 256 /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 seed) /\
          mld_keypair_terminates_44 seed
          ==> mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96
               (\j. EL j (SND(mldsa_keygen_internal mldsa44
                               (bytelist_of_num 32 seed)))) /\
              list_of_seq
               (mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96
                 (\j. EL j (SND(mldsa_keygen_internal mldsa44
                                 (bytelist_of_num 32 seed)))))
               1312 =
              FST(mldsa_keygen_internal mldsa44 (bytelist_of_num 32 seed))`,
  MLD_FIPS204_PK_FROM_SK_KEYGEN_TAC
   (mldsa44,mld_keypair_terminates_44,MLD_FIPS204_PK_FROM_SK_44));;

let MLD_FIPS204_PK_FROM_SK_KEYGEN_65 = prove
 (`!seed. seed < 2 EXP 256 /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 seed) /\
          mld_keypair_terminates_65 seed
          ==> mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4 128
               (\j. EL j (SND(mldsa_keygen_internal mldsa65
                               (bytelist_of_num 32 seed)))) /\
              list_of_seq
               (mld_pk_from_sk_pk 5 mld_polyeta_unpack_4 128
                 (\j. EL j (SND(mldsa_keygen_internal mldsa65
                                 (bytelist_of_num 32 seed)))))
               1952 =
              FST(mldsa_keygen_internal mldsa65 (bytelist_of_num 32 seed))`,
  MLD_FIPS204_PK_FROM_SK_KEYGEN_TAC
   (mldsa65,mld_keypair_terminates_65,MLD_FIPS204_PK_FROM_SK_65));;

let MLD_FIPS204_PK_FROM_SK_KEYGEN_87 = prove
 (`!seed. seed < 2 EXP 256 /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 seed) /\
          mld_keypair_terminates_87 seed
          ==> mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
               (\j. EL j (SND(mldsa_keygen_internal mldsa87
                               (bytelist_of_num 32 seed)))) /\
              list_of_seq
               (mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                 (\j. EL j (SND(mldsa_keygen_internal mldsa87
                                 (bytelist_of_num 32 seed)))))
               2592 =
              FST(mldsa_keygen_internal mldsa87 (bytelist_of_num 32 seed))`,
  MLD_FIPS204_PK_FROM_SK_KEYGEN_TAC
   (mldsa87,mld_keypair_terminates_87,MLD_FIPS204_PK_FROM_SK_87));;
