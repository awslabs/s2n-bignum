(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of mldsa-native and FIPS 204: for each parameter set, the    *)
(* specification of mldsa-native's verification of a signature given mu      *)
(* (mld_verify_internal_ok of common/mldsa_native_sign.ml) holds exactly     *)
(* when mldsa_verify_mu of common/fips204.ml accepts the signature, assuming *)
(* that the expansion of the matrix and the sampling of the challenge of the *)
(* C code terminate; and mu as the C code computes it (mld_verify_mu) is     *)
(* H(H(pk, 64) || M', 64) for the formatted message M' = pre || m, so that   *)
(* the C verification of M' is mldsa_verify_internal.                        *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_fips204_keypair.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte strings as numbers: the bytes of a number below 2^(8 * m) followed   *)
(* by those of another, and the hash of mu || w1 packed that the C code      *)
(* compares with c~ (mu as a number below 2^512).                            *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_BYTES = prove
 (`!(s:num->byte) n.
        num_of_bytelist(list_of_seq s n) < 2 EXP (8 * n) /\
        bytelist_of_num n (num_of_bytelist(list_of_seq s n)) = list_of_seq s n`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `list_of_seq (s:num->byte) n` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `list_of_seq (s:num->byte) n` BYTELIST_OF_NUM_OF_BYTELIST) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

let MLD_FIPS204_VERIFY_SPLIT = prove
 (`!m n a b.
        a < 2 EXP (8 * m) /\ b < 2 EXP (8 * n)
        ==> a + 2 EXP (8 * m) * b < 2 EXP (8 * (m + n)) /\
            bytelist_of_num (m + n) (a + 2 EXP (8 * m) * b) =
            APPEND (bytelist_of_num m a) (bytelist_of_num n b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN
    TRANS_TAC LTE_TRANS `2 EXP (8 * m) + 2 EXP (8 * m) * b` THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `a + a * b = a * (b + 1)`; LE_MULT_LCANCEL] THEN
    ASM_ARITH_TAC;
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[EXP_MULT]) THEN
    REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MLD_FIPS204_SAMPLE_BYTELIST_OF_NUM_SPLIT THEN
    ASM_REWRITE_TAC[]]);;

let MLD_FIPS204_VERIFY_HASH = prove
 (`!mu n (w:num->byte) (sg:num->byte) ct.
        mu < 2 EXP 512
        ==> ((!j. j < ct
                  ==> sg j =
                      mld_shake256_byte (64 + n)
                       (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w n))
                       j) <=>
             mldsa_h (APPEND (bytelist_of_num 64 mu) (list_of_seq w n)) ct =
             list_of_seq sg ct)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`64`; `n:num`; `mu:num`;
                `num_of_bytelist(list_of_seq (w:num->byte) n)`]
               MLD_FIPS204_VERIFY_SPLIT) THEN
  REWRITE_TAC[MLD_FIPS204_VERIFY_BYTES; ARITH_RULE `8 * 64 = 512`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_FIPS204_SHAKE256_BYTE] THEN
  REWRITE_TAC[mldsa_h; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The message representative: mld_verify_mu, as the C code computes it from *)
(* the public key of pklen bytes, the prefix pre of prelen bytes and the     *)
(* message m of mlen bytes, is H(H(pk, 64) || pre || m, 64), and it is a     *)
(* number below 2^512, so that verification from it is mldsa_verify_internal *)
(* of the formatted message pre || m.                                        *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_MU_BOUND = prove
 (`!pklen (pkb:num->byte) prelen pre mlen m.
        mld_verify_mu pklen pkb prelen pre mlen m < 2 EXP 512`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_verify_mu] THEN
  MATCH_MP_TAC(ARITH_RULE `x < 2 EXP (8 * 64) ==> x < 2 EXP 512`) THEN
  REWRITE_TAC[MLD_FIPS204_VERIFY_BYTES]);;

let MLD_FIPS204_VERIFY_MU = prove
 (`!pklen (pkb:num->byte) prelen pre mlen m.
        pre < 2 EXP (8 * prelen) /\ m < 2 EXP (8 * mlen)
        ==> bytelist_of_num 64 (mld_verify_mu pklen pkb prelen pre mlen m) =
            mldsa_h (APPEND (mldsa_h (list_of_seq pkb pklen) 64)
                            (APPEND (bytelist_of_num prelen pre)
                                    (bytelist_of_num mlen m))) 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_verify_mu; mldsa_h] THEN
  REWRITE_TAC[MLD_FIPS204_VERIFY_BYTES] THEN
  SIMP_TAC[MLD_FIPS204_SHAKE256_BYTE; MLD_FIPS204_VERIFY_BYTES] THEN
  ABBREV_TAC
   `tr = num_of_bytelist
          (list_of_seq (shake256 (list_of_seq (pkb:num->byte) pklen)) 64)` THEN
  SUBGOAL_THEN
   `tr < 2 EXP 512 /\
    bytelist_of_num 64 tr =
    list_of_seq (shake256 (list_of_seq (pkb:num->byte) pklen)) 64`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tr" THEN REWRITE_TAC[ARITH_RULE `512 = 8 * 64`] THEN
    REWRITE_TAC[MLD_FIPS204_VERIFY_BYTES];
    ALL_TAC] THEN
  MP_TAC(SPECL [`prelen:num`; `mlen:num`; `pre:num`; `m:num`]
               MLD_FIPS204_VERIFY_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 * 64 = 512`]
   (SPECL [`64`; `prelen + mlen`; `tr:num`; `pre + 2 EXP (8 * prelen) * m`]
          MLD_FIPS204_VERIFY_SPLIT)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_FIPS204_SHAKE256_BYTE]);;

(* ------------------------------------------------------------------------- *)
(* The vector z of the signature (z_17 for gamma1 = 2^17, z_19 for gamma1 =  *)
(* 2^19): the norm check of the C code on the unpacked z is the bound on the *)
(* infinity norm of the z of FIPS 204 (gamma1 minus the fields of the bytes  *)
(* after c~), and the NTT of the unpacked z represents the NTT of that z.    *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_VEC_NORM_LT_EQ = prove
 (`!n b u v. (!i. i < n ==> u i = v i)
             ==> (mldsa_vec_norm_lt n b u <=> mldsa_vec_norm_lt n b v)`,
  SIMP_TAC[mldsa_vec_norm_lt]);;

let MLD_FIPS204_VERIFY_Z_STMT (p,f,g1,c) =
  subst [p,`P:num`; f,`f:(num->byte)->num->int32`; g1,`G:num`; c,`c:num`]
  `!l (sig:num->byte) ctlen.
        (!B. B <= 2097408
             ==> (mld_polyvec_chknorm l
                   (mld_polyvec_unpack P f (\j. sig(ctlen + j))) (word B) =
                  word 0 <=>
                  mldsa_vec_norm_lt l B
                   (\i. mldsa_poly (\j. &G - mldsa_field c
                          (list_of_seq (\j. sig(ctlen + j)) (P * l))
                          (256 * i + j))))) /\
        (!j m. j < l /\ m < 256
               ==> (ival(mld_polyvec_map mld_poly_ntt
                          (mld_polyvec_unpack P f (\j. sig(ctlen + j)))
                          (256 * j + m)) ==
                    mldsa_ntt (mldsa_poly (\i. &G - mldsa_field c
                          (list_of_seq (\j. sig(ctlen + j)) (P * l))
                          (256 * j + i))) m) (mod &8380417) /\
                   abs(ival(mld_polyvec_map mld_poly_ntt
                          (mld_polyvec_unpack P f (\j. sig(ctlen + j)))
                          (256 * j + m))) < &94279689)`;;

let MLD_FIPS204_VERIFY_Z_TAC (p,f,g1,c) unpackth =
  let sub = subst [p,`P:num`; f,`f:(num->byte)->num->int32`; g1,`G:num`;
                   c,`c:num`] in
  let ztm = sub `mld_polyvec_unpack P f (\j. (sig:num->byte)(ctlen + j))`
  and btm = sub `list_of_seq (\j. (sig:num->byte)(ctlen + j)) (P * l)` in
  let zfact = sub
   `!n. n < 256 * l
        ==> ival(mld_polyvec_unpack P f (\j. (sig:num->byte)(ctlen + j)) n) =
            &G - mldsa_field c (list_of_seq (\j. sig(ctlen + j)) (P * l)) n /\
            abs(ival(mld_polyvec_unpack P f (\j. sig(ctlen + j)) n)) <= &G`
  and zpoly = sub
   `mldsa_poly
     (\i. ival(mld_polyvec_unpack P f (\j. (sig:num->byte)(ctlen + j))
                (256 * j + i))) =
    mldsa_poly
     (\i. &G - mldsa_field c (list_of_seq (\j. sig(ctlen + j)) (P * l))
                (256 * j + i))` in
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN zfact ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`l:num`; `\j. (sig:num->byte)(ctlen + j)`; `n:num`]
                 unpackth) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [c; btm; `n:num`] MLDSA_FIELD_BOUND) THEN
    CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `B:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:num`; ztm; `B:num`] MLD_FIPS204_POLYVEC_CHKNORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC MLD_FIPS204_VERIFY_VEC_NORM_LT_EQ THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC MLDSA_POLY_EXT THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    BETA_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `256 * j + i`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num`; ztm] MLD_FIPS204_POLYVEC_NTT) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `j < l /\ m < 256` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN zpoly SUBST1_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  MATCH_MP_TAC MLDSA_POLY_EXT THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  BETA_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `256 * j + i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];;

let MLD_FIPS204_VERIFY_Z_17 = prove
 (MLD_FIPS204_VERIFY_Z_STMT
   (`576`,`mld_polyz_unpack_17`,`131072`,`18`),
  MLD_FIPS204_VERIFY_Z_TAC
   (`576`,`mld_polyz_unpack_17`,`131072`,`18`)
   MLD_FIPS204_POLYVEC_Z_UNPACK_17);;

let MLD_FIPS204_VERIFY_Z_19 = prove
 (MLD_FIPS204_VERIFY_Z_STMT
   (`640`,`mld_polyz_unpack_19`,`524288`,`20`),
  MLD_FIPS204_VERIFY_Z_TAC
   (`640`,`mld_polyz_unpack_19`,`524288`,`20`)
   MLD_FIPS204_POLYVEC_Z_UNPACK_19);;

(* ------------------------------------------------------------------------- *)
(* t1 and the challenge in the NTT domain: the NTT of t1 * 2^d, polynomial i *)
(* of t1 being unpacked from the 320 bytes at 32 + 320 * i of the public     *)
(* key, represents that of t1 * 2^d of FIPS 204 (the fields of 10 bits of    *)
(* the bytes after rho, times 2^13); and when the sampling terminates, the   *)
(* NTT of the challenge of the C code represents that of SampleInBall.       *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_T1 = prove
 (`!(pk:num->byte) k i.
        i < k
        ==> !m. m < 256
                ==> (ival(mld_poly_ntt (mld_poly_shiftl
                           (mld_polyt1_unpack (\j. pk(32 + 320 * i + j)))) m) ==
                     mldsa_ntt (mldsa_poly (\j. &8192 *
                       mldsa_field 10 (list_of_seq (\j. pk(32 + j)) (320 * k))
                                   (256 * i + j))) m)
                    (mod &8380417) /\
                    abs(ival(mld_poly_ntt (mld_poly_shiftl
                           (mld_polyt1_unpack (\j. pk(32 + 320 * i + j)))) m))
                    < &94279689`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!y:int32. &0 <= ival y /\ ival y < &1024
              ==> ival(word_mul y (word 8192)) = &8192 * ival y`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m < 256
        ==> ival(mld_poly_shiftl
                  (mld_polyt1_unpack (\j. (pk:num->byte)(32 + 320 * i + j)))
                  m) =
            &8192 * mldsa_field 10 (list_of_seq (\j. pk(32 + j)) (320 * k))
                                (256 * i + m)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`k:num`; `\j. (pk:num->byte)(32 + j)`; `256 * i + m`]
                 MLD_FIPS204_POLYVEC_T1_UNPACK) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MLD_POLYVEC_UNPACK_COEFF] THEN
    MP_TAC(SPECL [`10`; `list_of_seq (\j. (pk:num->byte)(32 + j)) (320 * k)`;
                  `256 * i + m`] MLDSA_FIELD_BOUND) THEN
    SPEC_TAC(`mldsa_field 10 (list_of_seq (\j. (pk:num->byte)(32 + j))
                                         (320 * k)) (256 * i + m)`,`f:int`) THEN
    GEN_TAC THEN CONV_TAC INT_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[mld_poly_shiftl] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `mld_poly_shiftl
                (mld_polyt1_unpack (\j. (pk:num->byte)(32 + 320 * i + j)))`
              MLD_FIPS204_POLY_NTT) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(SPECL [`10`; `list_of_seq (\j. (pk:num->byte)(32 + j)) (320 * k)`;
                  `256 * i + m`] MLDSA_FIELD_BOUND) THEN
    CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mldsa_poly (\t. ival(mld_poly_shiftl
       (mld_polyt1_unpack (\j. (pk:num->byte)(32 + 320 * i + j))) t)) =
    mldsa_poly (\j. &8192 *
       mldsa_field 10 (list_of_seq (\j. pk(32 + j)) (320 * k)) (256 * i + j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_POLY_EXT THEN ASM_SIMP_TAC[]; REWRITE_TAC[]]);;

let MLD_FIPS204_VERIFY_CHALLENGE = prove
 (`!tau ctlen c.
        c < 2 EXP (8 * ctlen) /\ mld_poly_challenge_terminates tau ctlen c
        ==> !k. k < 256
                ==> (ival(mld_poly_ntt (mld_poly_challenge tau ctlen c) k) ==
                     mldsa_ntt (mldsa_sample_in_ball tau
                                 (bytelist_of_num ctlen c)) k)
                    (mod &8380417) /\
                    abs(ival(mld_poly_ntt (mld_poly_challenge tau ctlen c) k))
                    < &94279689`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP MLD_FIPS204_POLY_CHALLENGE) THEN
  MATCH_MP_TAC MLD_FIPS204_POLY_NTT THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP MLD_FIPS204_POLY_CHALLENGE_COEFFS th]) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tau:num`; `shake256(bytelist_of_num ctlen c)`; `tau:num`;
                `i:num`] MLDSA_BALL_COEFFS_BOUND) THEN
  INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The NTT-domain computation of one polynomial of w' = A z - c t1 2^d. The  *)
(* Montgomery dot product of a row u of the matrix in the NTT domain (values *)
(* in [0,q)) with v representing the NTTs of polynomials Y_j is congruent    *)
(* to 2^-32 times the NTT of sum_j A_j * Y_j, A_j being the inverse NTT of   *)
(* polynomial j of u (MLD_FIPS204_VERIFY_ACC_L4, _L5 and _L7). If x is       *)
(* congruent to 2^-32 times the NTT of h, and a and b represent the NTTs of  *)
(* f and g, the C code computes coefficient n of h - f * g from x - a * b by *)
(* a reduction, the inverse NTT and caddq (MLD_FIPS204_VERIFY_W_GEN). So for *)
(* any row i, with the matrix expanded from rho, zhat representing the NTTs  *)
(* of Z, t1 unpacked from the public key and cphat representing the NTT of   *)
(* C, the C code computes coefficient n of polynomial i of A Z - C t1 2^d    *)
(* (MLD_FIPS204_VERIFY_W_L4, _L5 and _L7).                                   *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_ACC_STMT l =
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
                ==> (ival(mld_polyvec_pointwise_acc_montgomery l u v k) ==
                     &(inverse_mod 8380417 4294967296) *
                     mldsa_ntt (mldsa_dot l
                       (\j. mldsa_ntt_inv (\m. ival(u(256 * j + m)))) Y) k)
                    (mod &8380417) /\
                    abs(ival(mld_polyvec_pointwise_acc_montgomery l u v k))
                    < &8380417`;;

let MLD_FIPS204_VERIFY_ACC_TAC acccong l =
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
  and stm = sub
   `\k. isum {j | j < l}
         (\j. ival((u:num->int32)(256 * j + k)) *
              mldsa_ntt ((Y:num->(1->num)->int) j) k) rem &8380417`
  and sumc = sub
   `(isum {j | j < l}
      (\j. ival((u:num->int32)(k + 256 * j)) *
           ival((v:num->int32)(k + 256 * j))) ==
     isum {j | j < l}
      (\j. ival(u(256 * j + k)) * mldsa_ntt ((Y:num->(1->num)->int) j) k))
    (mod &8380417)`
  and atm = sub
   `isum {j | j < l}
      (\j. ival((u:num->int32)(k + 256 * j)) *
           ival((v:num->int32)(k + 256 * j)))`
  and btm = sub
   `isum {j | j < l}
      (\j. ival((u:num->int32)(256 * j + k)) *
           mldsa_ntt ((Y:num->(1->num)->int) j) k)`
  and ptm = sub
   `ival(mld_polyvec_pointwise_acc_montgomery l (u:num->int32)
          (v:num->int32) k)`
  and ctm = `&(inverse_mod 8380417 4294967296):int`
  and qtm = `&8380417:int`
  and mul = `( * ):int->int->int` and rem = `(rem):int->int->int` in
  let idx = ARITH_RULE(sub `i < n ==> i = 256 * (i DIV 256) + i MOD 256 /\
                                     i DIV 256 < l /\ i MOD 256 < 256`) in
  let r1 = mk_binop rem (mk_binop mul atm ctm) qtm
  and r2 = mk_binop rem btm qtm in
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [lt; `\j k. ival((u:num->int32)(256 * j + k))`;
     `Y:num->(1->num)->int`] MLDSA_DOT_NTT_INV_ISUM)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC stm MLDSA_NTT_INV) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    INT_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
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
  MP_TAC(SPECL [mk_binop mul atm ctm; qtm] INT_REM_MOD_SELF) THEN
  MP_TAC(SPECL [btm; qtm] INT_REM_MOD_SELF) THEN
  SPEC_TAC(r1,`r1:int`) THEN SPEC_TAC(r2,`r2:int`) THEN
  SPEC_TAC(atm,`a:int`) THEN SPEC_TAC(btm,`b:int`) THEN
  SPEC_TAC(ptm,`p:int`) THEN SPEC_TAC(ctm,`c:int`) THEN
  SPEC_TAC(qtm,`q:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE;;

let MLD_FIPS204_VERIFY_ACC_L4 = prove
 (MLD_FIPS204_VERIFY_ACC_STMT 4,
  MLD_FIPS204_VERIFY_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L4_CONG 4);;

let MLD_FIPS204_VERIFY_ACC_L5 = prove
 (MLD_FIPS204_VERIFY_ACC_STMT 5,
  MLD_FIPS204_VERIFY_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L5_CONG 5);;

let MLD_FIPS204_VERIFY_ACC_L7 = prove
 (MLD_FIPS204_VERIFY_ACC_STMT 7,
  MLD_FIPS204_VERIFY_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L7_CONG 7);;

let MLD_FIPS204_VERIFY_W_GEN = prove
 (`!(x:num->int32) (a:num->int32) (b:num->int32) f g h n.
        f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq /\
        h IN ring_carrier mldsa_rq /\
        (!k. k < 256
             ==> (ival(x k) ==
                  &(inverse_mod 8380417 4294967296) * mldsa_ntt h k)
                 (mod &8380417) /\
                 abs(ival(x k)) < &8380417) /\
        (!k. k < 256 ==> (ival(a k) == mldsa_ntt f k) (mod &8380417) /\
                         abs(ival(a k)) < &94279689) /\
        (!k. k < 256 ==> (ival(b k) == mldsa_ntt g k) (mod &8380417) /\
                         abs(ival(b k)) < &94279689) /\
        n < 256
        ==> ival(mld_poly_caddq
                  (mld_poly_invntt_tomont
                    (mld_poly_reduce
                      (mld_poly_sub x
                        (mld_poly_pointwise_montgomery a b)))) n) =
            coeff n (ring_sub mldsa_rq h (ring_mul mldsa_rq f g))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `P = mld_poly_reduce
         (mld_poly_sub x (mld_poly_pointwise_montgomery a b))` THEN
  SUBGOAL_THEN
   `!k. k < 256
        ==> abs(ival((P:num->int32) k)) < &8380417 /\
            (ival(P k) ==
             &(inverse_mod 8380417 4294967296) *
             (\k. mldsa_ntt h k - mldsa_ntt f k * mldsa_ntt g k) k)
            (mod &8380417)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[mld_poly_reduce; mld_poly_sub] THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP (ASSUME `k < 256`) o
                         SPEC `k:num` o check (is_forall o concl))) THEN
    MP_TAC(SPECL [`a:num->int32`; `b:num->int32`; `k:num`]
                 MLD_POLY_POINTWISE_MONTGOMERY_CONG) THEN
    ASM_REWRITE_TAC[mldsa_pointwise; o_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `ival(word_sub ((x:num->int32) k)
                    (mld_poly_pointwise_montgomery a b k)) =
      ival(x k) - ival(mld_poly_pointwise_montgomery a b k)`
    ASSUME_TAC THENL [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `word_sub ((x:num->int32) k)
                          (mld_poly_pointwise_montgomery a b k)`
                MLD_FIPS204_REDUCE32) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `(x:int == y) (mod n)`) (concl th)))) THEN
    MP_TAC(SPECL [`ival((a:num->int32) k) * ival((b:num->int32) k) *
                   &(inverse_mod 8380417 4294967296)`; `&8380417:int`]
                 INT_REM_MOD_SELF) THEN
    SPEC_TAC(`(ival((a:num->int32) k) * ival((b:num->int32) k) *
               &(inverse_mod 8380417 4294967296)) rem &8380417`,`r:int`) THEN
    SPEC_TAC(`ival(mld_reduce32 (word_sub ((x:num->int32) k)
                (mld_poly_pointwise_montgomery a b k)))`,`p:int`) THEN
    SPEC_TAC(`ival(mld_poly_pointwise_montgomery (a:num->int32) b k)`,
             `w:int`) THEN
    SPEC_TAC(`ival((x:num->int32) k)`,`xx:int`) THEN
    SPEC_TAC(`ival((a:num->int32) k)`,`aa:int`) THEN
    SPEC_TAC(`ival((b:num->int32) k)`,`bb:int`) THEN
    SPEC_TAC(`mldsa_ntt h k`,`hh:int`) THEN
    SPEC_TAC(`mldsa_ntt f k`,`ff:int`) THEN
    SPEC_TAC(`mldsa_ntt g k`,`gg:int`) THEN
    SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
    SPEC_TAC(`&8380417:int`,`q:int`) THEN
    REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP MLD_FIPS204_INVNTT_MONT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mldsa_ntt_inv
     (\k. (mldsa_ntt h k - mldsa_ntt f k * mldsa_ntt g k) rem &8380417) =
    ring_sub mldsa_rq h (ring_mul mldsa_rq f g)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_NTT_INV_UNIQUE THEN
    ASM_SIMP_TAC[RING_SUB; RING_MUL; MLDSA_NTT_SUB; MLDSA_NTT_MUL] THEN
    REWRITE_TAC[MLDSA_ZQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[];
    STRIP_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_POLY_CADDQ_REM o lhand o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INT_REM_UNIQUE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MLDSA_RQ_COEFF THEN ASM_SIMP_TAC[RING_SUB; RING_MUL]);;

let MLD_FIPS204_VERIFY_W_STMT l =
  subst [mk_small_numeral l,`l:num`]
  `!k rho (zhat:num->int32) (cphat:num->int32) (pk:num->byte)
     (Z:num->(1->num)->int) C i n.
        mld_matrix_terminates k l rho /\ rho < 2 EXP 256 /\ k <= 256 /\
        i < k /\ n < 256 /\
        (!j. j < l ==> Z j IN ring_carrier mldsa_rq) /\
        (!j m. j < l /\ m < 256
               ==> (ival(zhat(256 * j + m)) == mldsa_ntt (Z j) m)
                   (mod &8380417) /\
                   abs(ival(zhat(256 * j + m))) < &94279689) /\
        C IN ring_carrier mldsa_rq /\
        (!m. m < 256 ==> (ival(cphat m) == mldsa_ntt C m) (mod &8380417) /\
                         abs(ival(cphat m)) < &94279689)
        ==> ival(mld_poly_caddq
                  (mld_poly_invntt_tomont
                    (mld_poly_reduce
                      (mld_poly_sub
                        (mld_polyvec_pointwise_acc_montgomery l
                          (\j. mld_polyvec_matrix_expand l rho
                                 ((256 * l) * i + j)) zhat)
                        (mld_poly_pointwise_montgomery
                          (mld_poly_ntt (mld_poly_shiftl
                            (mld_polyt1_unpack (\j. pk(32 + 320 * i + j)))))
                          cphat)))) n) =
            coeff n (ring_sub mldsa_rq
                      (mldsa_dot l (mldsa_expand_a (bytelist_of_num 32 rho) i)
                                 Z)
                      (ring_mul mldsa_rq C
                        (mldsa_poly (\j. &8192 *
                          mldsa_field 10
                           (list_of_seq (\j. pk(32 + j)) (320 * k))
                           (256 * i + j)))))`;;

let MLD_FIPS204_VERIFY_W_TAC accth l =
  let lt = mk_small_numeral l in
  let sub t = subst [lt,`l:num`] t in
  let uabbr = sub
   `u = \j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j)`
  and uback = sub
   `(\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j)) =
    (u:num->int32)`
  and idx = ARITH_RULE(sub
     `(256 * l) * i + 256 * j + m = 256 * (l * i + j) + m`)
  and dotsub = sub
   `mldsa_dot l (mldsa_expand_a (bytelist_of_num 32 rho) i) Z =
    mldsa_dot l (\j. mldsa_ntt_inv (\m. ival((u:num->int32)(256 * j + m))))
              (Z:num->(1->num)->int)`
  and rowfacts = sub
   `!j m. j < l /\ m < 256
          ==> &0 <= ival((u:num->int32)(256 * j + m)) /\
              ival(u(256 * j + m)) < &8380417`
  and t1sym =
   `ring_mul mldsa_rq C
     (mldsa_poly (\j. &8192 *
        mldsa_field 10 (list_of_seq (\j. (pk:num->byte)(32 + j)) (320 * k))
                    (256 * i + j))) =
    ring_mul mldsa_rq
     (mldsa_poly (\j. &8192 *
        mldsa_field 10 (list_of_seq (\j. pk(32 + j)) (320 * k))
                    (256 * i + j))) C` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC uabbr THEN
  SUBGOAL_THEN rowfacts ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `m:num`] THEN STRIP_TAC THEN
    EXPAND_TAC "u" THEN BETA_TAC THEN REWRITE_TAC[idx] THEN
    MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `j:num`; `m:num`]
                 MLD_FIPS204_MATRIX_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[MLDSA_REJ_NTT_POLY_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN dotsub SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_DOT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN BETA_TAC THEN
    MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `j:num`]
                 MLD_FIPS204_EXPAND_A) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    BETA_TAC THEN UNDISCH_THEN uback (fun th -> REWRITE_TAC[GSYM th]) THEN
    BETA_TAC THEN REWRITE_TAC[idx] THEN
    MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `j:num`; `m:num`]
                 MLD_FIPS204_MATRIX_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN t1sym SUBST1_TAC THENL
   [MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC[MLDSA_POLY_IN_RQ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`pk:num->byte`; `k:num`; `i:num`] MLD_FIPS204_VERIFY_T1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`u:num->int32`; `zhat:num->int32`; `Z:num->(1->num)->int`]
               accth) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC MLD_FIPS204_VERIFY_W_GEN THEN
  ASM_REWRITE_TAC[MLDSA_POLY_IN_RQ; MLDSA_DOT_IN_RQ];;

let MLD_FIPS204_VERIFY_W_L4 = prove
 (MLD_FIPS204_VERIFY_W_STMT 4,
  MLD_FIPS204_VERIFY_W_TAC MLD_FIPS204_VERIFY_ACC_L4 4);;

let MLD_FIPS204_VERIFY_W_L5 = prove
 (MLD_FIPS204_VERIFY_W_STMT 5,
  MLD_FIPS204_VERIFY_W_TAC MLD_FIPS204_VERIFY_ACC_L5 5);;

let MLD_FIPS204_VERIFY_W_L7 = prove
 (MLD_FIPS204_VERIFY_W_STMT 7,
  MLD_FIPS204_VERIFY_W_TAC MLD_FIPS204_VERIFY_ACC_L7 7);;

(* ------------------------------------------------------------------------- *)
(* Verification. The proof is the same for the three parameter sets, given   *)
(* by the definition of the parameter set and the lemmas for z, UseHint, the *)
(* packing of w1 and w'. MLD_FIPS204_VERIFY_TABLE gives the numbers and      *)
(* functions of the set, from the parameters and the arguments of            *)
(* mld_verify_internal_ok in the goal, and MLD_FIPS204_KEYPAIR_INST          *)
(* instantiates the terms of the tactic with them. The C code accepts the    *)
(* signature iff z passes the norm check, the hints unpack and c~ is the     *)
(* hash of mu and w1 packed, as FIPS 204 does once the slices of the key and *)
(* the signature are those that the C code reads.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_TABLE params_def w =
  let rec bits n = if n = 0 then 0 else 1 + bits (n / 2) in
  let rec untuple t =
    try let a,b = dest_pair t in a::untuple b with Failure _ -> [t] in
  let vok = find_term (fun t ->
    try fst(dest_const(fst(strip_comb t))) = "mld_verify_internal_ok" &&
        length(snd(strip_comb t)) = 14
    with Failure _ -> false) w in
  match map dest_small_numeral (untuple(rhs(concl params_def))),
        snd(strip_comb vok) with
    [k;l;_;tau;_;g1;g2;omega],
    [_;_;ct_tm;zunpack;zp_tm;bnd_tm;usehint;_;_;_;_;_;_;_] ->
      let ct = dest_small_numeral ct_tm and zp = dest_small_numeral zp_tm
      and w1bits = bits(8380416 / (2 * g2) - 1) in
      map (fun (s,n) -> s,mk_small_numeral n)
       ["k",k; "l",l; "ct",ct; "zp",zp; "bnd",dest_small_numeral bnd_tm;
        "omega",omega; "tau",tau; "g1",g1; "g2",g2;
        "c",1 + bits(g1 - 1); "w1bits",w1bits; "w1max",1 lsl w1bits;
        "nk",256 * k; "zb",l * zp; "hboff",ct + l * zp; "t1b",320 * k] @
      ["zunpack",zunpack; "usehint",usehint]
  | _ -> failwith "MLD_FIPS204_VERIFY_TABLE";;

let MLD_FIPS204_VERIFY_TAC params_def (zth,uhdef,uhth,uhbnd,w1packth,wth) =
  W(fun (asl,w) ->
  let tab = MLD_FIPS204_VERIFY_TABLE params_def w in
  let kp = MLD_FIPS204_KEYPAIR_INST tab in
  let num s = assoc s tab in
  let uh1 = fst(strip_comb(body(rhs(concl(SPEC_ALL uhdef))))) in
  let zh = kp `mld_polyvec_map mld_poly_ntt
                (mld_polyvec_unpack zp zunpack (\j. (sigb:num->byte)(ct + j)))`
  and cph = kp `mld_poly_ntt (mld_poly_challenge tau ct CC)`
  and zf = kp `\i. mldsa_poly (\j. &g1 - mldsa_field c
                 (list_of_seq (\j. (sigb:num->byte)(ct + j)) zb)
                 (256 * i + j))`
  and cf = kp `mldsa_sample_in_ball tau (bytelist_of_num ct CC)` in
  let w1c = kp (subst [zh,`ZH:num->int32`; cph,`CPH:num->int32`]
   `mld_polyvec (mld_verify_w1 l usehint R ZH CPH (pkb:num->byte) omega HB)`)
  in
  let w1fact = kp (subst [w1c,`WV:num->int32`; zf,`Z:num->(1->num)->int`;
                          cf,`C:(1->num)->int`]
   `!i m. i < k /\ m < 256
          ==> ival((WV:num->int32)(256 * i + m)) =
              mldsa_usehint g2 (~(mld_unpack_hints omega HB i m = word 0))
               (coeff m (ring_sub mldsa_rq
                 (mldsa_dot l (mldsa_expand_a (bytelist_of_num 32 R) i) Z)
                 (ring_mul mldsa_rq C
                   (mldsa_poly (\j. &8192 * mldsa_field 10
                     (list_of_seq (\j. (pkb:num->byte)(32 + j)) t1b)
                     (256 * i + j)))))) /\
              &0 <= ival(WV(256 * i + m)) /\ ival(WV(256 * i + m)) < &w1max`)
  and nsplit = ARITH_RULE(kp
   `n < nk ==> n DIV 256 < k /\ n MOD 256 < 256 /\
               256 * n DIV 256 + n MOD 256 = n`)
  and isw1 th = is_forall(concl th) && free_in `mldsa_usehint` (concl th) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_verify_internal_ok] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `R = num_of_bytelist(list_of_seq (pkb:num->byte) 32)` THEN
  ABBREV_TAC (kp `CC = num_of_bytelist(list_of_seq (sigb:num->byte) ct)`) THEN
  STRIP_TAC THEN
  REWRITE_TAC[MATCH_MP MLD_FIPS204_VERIFY_HASH (ASSUME `mu < 2 EXP 512`)] THEN

  (*** The FIPS 204 side, with the slices as the C code reads them ***)

  REWRITE_TAC[params_def; mldsa_verify_mu] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[MLD_FIPS204_SLICE_LIST_OF_SEQ; ARITH] THEN
  REWRITE_TAC[ADD_CLAUSES; ETA_AX;
              ARITH_RULE(kp `ct + zb + t = hboff + t`)] THEN
  MP_TAC(REWRITE_RULE
   [ASSUME `num_of_bytelist(list_of_seq (pkb:num->byte) 32) = R`;
    ARITH_RULE `8 * 32 = 256`]
   (SPECL [`pkb:num->byte`; `32`] MLD_FIPS204_VERIFY_BYTES)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(REWRITE_RULE
   [ASSUME (kp `num_of_bytelist(list_of_seq (sigb:num->byte) ct) = CC`)]
   (SPECL [`sigb:num->byte`; num "ct"] MLD_FIPS204_VERIFY_BYTES)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN

  (*** The hints ***)

  MP_TAC(REWRITE_RULE[] (CONV_RULE NUM_REDUCE_CONV (SPECL
    [num "omega"; num "k"; kp `\t. (sigb:num->byte)(hboff + t)`]
    MLD_FIPS204_HINTBITUNPACK))) THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC (kp `HB = \t. (sigb:num->byte)(hboff + t)`) THEN
  ASM_CASES_TAC
   (kp `!i. i < k ==> mld_unpack_hints_ret omega k HB i = word 0`) THEN
  ASM_REWRITE_TAC[] THEN

  (*** z and its norm check ***)

  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [num "l"; `sigb:num->byte`; num "ct"] zth)) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> REWRITE_TAC[MP (SPEC (num "bnd") th)
                 (EQT_ELIM(NUM_REDUCE_CONV(kp `bnd <= 2097408`)))])
   ASSUME_TAC) THEN

  (*** The challenge, and the coefficients of w1' ***)

  MP_TAC(SPECL [num "tau"; num "ct"; `CC:num`]
               MLD_FIPS204_VERIFY_CHALLENGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN w1fact ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `m:num`] THEN STRIP_TAC THEN
    SIMP_TAC[MLD_POLYVEC_COEFF; ASSUME `m < 256`] THEN
    REWRITE_TAC[mld_verify_w1; uhdef] THEN
    MP_TAC(REWRITE_RULE[ARITH_RULE(kp `320 * k = t1b`)] (SPECL
      [num "k"; `R:num`; zh; cph; `pkb:num->byte`; zf; cf; `i:num`; `m:num`]
      wth)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MLDSA_SAMPLE_IN_BALL_IN_RQ; MLDSA_POLY_IN_RQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    DISCH_THEN(fun th ->
      ASSUME_TAC th THEN MP_TAC(ISPECL [rand(rhs(concl th)); `m:num`]
                                       MLDSA_RQ_COEFF)) THEN
    ANTS_TAC THENL
     [SIMP_TAC[RING_SUB; RING_MUL; MLDSA_DOT_IN_RQ;
               MLDSA_SAMPLE_IN_BALL_IN_RQ; MLDSA_POLY_IN_RQ];
      STRIP_TAC] THEN
    W(fun (asl,w) ->
      let t = find_term (fun t -> is_comb t && is_comb(rator t) &&
                                  rator(rator t) = uh1) w in
      MP_TAC(SPECL [rand(rator t); rand t] uhbnd) THEN
      MP_TAC(SPECL [rand(rator t); rand t] uhth)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN

  (*** w1' packed ***)

  MLD_FIPS204_ENCODE_SUBST_TAC (kp `mldsa_encode w1bits nk f`)
   (kp (subst [w1c,`WV:num->int32`]
     `mldsa_encode w1bits nk (\n. ival((WV:num->int32) n))`))
   (MP_TAC nsplit THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n DIV 256`; `n MOD 256`] o check isw1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REFL_TAC) THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [num "k"; w1c] w1packth)) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC nsplit THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n DIV 256`; `n MOD 256`] o check isw1) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let MLD_FIPS204_VERIFY_44 = prove
 (`!(sigb:num->byte) (pkb:num->byte) mu.
        mu < 2 EXP 512 /\
        mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 39 32
         (num_of_bytelist(list_of_seq sigb 32))
        ==> (mld_verify_internal_ok 4 4 32 mld_polyz_unpack_17 576 130994
              mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39 sigb pkb mu
             <=> mldsa_verify_mu mldsa44 (list_of_seq pkb 1312)
                  (bytelist_of_num 64 mu) (list_of_seq sigb 2420))`,
  MLD_FIPS204_VERIFY_TAC mldsa44
   (MLD_FIPS204_VERIFY_Z_17,mld_poly_use_hint_88,MLD_FIPS204_USE_HINT_88,
    MLD_FIPS204_USE_HINT_88_BOUNDS,MLD_FIPS204_POLYVEC_W1_PACK_88,
    MLD_FIPS204_VERIFY_W_L4));;

let MLD_FIPS204_VERIFY_65 = prove
 (`!(sigb:num->byte) (pkb:num->byte) mu.
        mu < 2 EXP 512 /\
        mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 49 48
         (num_of_bytelist(list_of_seq sigb 48))
        ==> (mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092
              mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 sigb pkb mu
             <=> mldsa_verify_mu mldsa65 (list_of_seq pkb 1952)
                  (bytelist_of_num 64 mu) (list_of_seq sigb 3309))`,
  MLD_FIPS204_VERIFY_TAC mldsa65
   (MLD_FIPS204_VERIFY_Z_19,mld_poly_use_hint_32,MLD_FIPS204_USE_HINT_32,
    MLD_FIPS204_USE_HINT_32_BOUNDS,MLD_FIPS204_POLYVEC_W1_PACK_32,
    MLD_FIPS204_VERIFY_W_L5));;

let MLD_FIPS204_VERIFY_87 = prove
 (`!(sigb:num->byte) (pkb:num->byte) mu.
        mu < 2 EXP 512 /\
        mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 60 64
         (num_of_bytelist(list_of_seq sigb 64))
        ==> (mld_verify_internal_ok 8 7 64 mld_polyz_unpack_19 640 524168
              mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60 sigb pkb mu
             <=> mldsa_verify_mu mldsa87 (list_of_seq pkb 2592)
                  (bytelist_of_num 64 mu) (list_of_seq sigb 4627))`,
  MLD_FIPS204_VERIFY_TAC mldsa87
   (MLD_FIPS204_VERIFY_Z_19,mld_poly_use_hint_32,MLD_FIPS204_USE_HINT_32,
    MLD_FIPS204_USE_HINT_32_BOUNDS,MLD_FIPS204_POLYVEC_W1_PACK_32,
    MLD_FIPS204_VERIFY_W_L7));;

(* ------------------------------------------------------------------------- *)
(* Verification of the formatted message M' = pre || m (internal mu): with   *)
(* mu computed by the C code, the C verification is mldsa_verify_internal.   *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_INTERNAL_44 = prove
 (`!(sigb:num->byte) (pkb:num->byte) prelen pre mlen m.
        pre < 2 EXP (8 * prelen) /\ m < 2 EXP (8 * mlen) /\
        mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 39 32
         (num_of_bytelist(list_of_seq sigb 32))
        ==> (mld_verify_internal_ok 4 4 32 mld_polyz_unpack_17 576 130994
              mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39 sigb pkb
              (mld_verify_mu 1312 pkb prelen pre mlen m)
             <=> mldsa_verify_internal mldsa44 (list_of_seq pkb 1312)
                  (APPEND (bytelist_of_num prelen pre)
                          (bytelist_of_num mlen m))
                  (list_of_seq sigb 2420))`,
  SIMP_TAC[MLD_FIPS204_VERIFY_44; MLD_FIPS204_VERIFY_MU_BOUND;
           MLD_FIPS204_VERIFY_MU; mldsa_verify_internal]);;

let MLD_FIPS204_VERIFY_INTERNAL_65 = prove
 (`!(sigb:num->byte) (pkb:num->byte) prelen pre mlen m.
        pre < 2 EXP (8 * prelen) /\ m < 2 EXP (8 * mlen) /\
        mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 49 48
         (num_of_bytelist(list_of_seq sigb 48))
        ==> (mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092
              mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 sigb pkb
              (mld_verify_mu 1952 pkb prelen pre mlen m)
             <=> mldsa_verify_internal mldsa65 (list_of_seq pkb 1952)
                  (APPEND (bytelist_of_num prelen pre)
                          (bytelist_of_num mlen m))
                  (list_of_seq sigb 3309))`,
  SIMP_TAC[MLD_FIPS204_VERIFY_65; MLD_FIPS204_VERIFY_MU_BOUND;
           MLD_FIPS204_VERIFY_MU; mldsa_verify_internal]);;

let MLD_FIPS204_VERIFY_INTERNAL_87 = prove
 (`!(sigb:num->byte) (pkb:num->byte) prelen pre mlen m.
        pre < 2 EXP (8 * prelen) /\ m < 2 EXP (8 * mlen) /\
        mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 60 64
         (num_of_bytelist(list_of_seq sigb 64))
        ==> (mld_verify_internal_ok 8 7 64 mld_polyz_unpack_19 640 524168
              mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60 sigb pkb
              (mld_verify_mu 2592 pkb prelen pre mlen m)
             <=> mldsa_verify_internal mldsa87 (list_of_seq pkb 2592)
                  (APPEND (bytelist_of_num prelen pre)
                          (bytelist_of_num mlen m))
                  (list_of_seq sigb 4627))`,
  SIMP_TAC[MLD_FIPS204_VERIFY_87; MLD_FIPS204_VERIFY_MU_BOUND;
           MLD_FIPS204_VERIFY_MU; mldsa_verify_internal]);;
