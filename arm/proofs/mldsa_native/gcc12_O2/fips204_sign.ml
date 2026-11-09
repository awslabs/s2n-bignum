(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The signing functions of mldsa-native in the gcc 12 -O2 image, stated     *)
(* with the FIPS 204 specification of ML-DSA in common/fips204.ml. For each  *)
(* parameter set, the theorem ..._FIPS204 of a function is its CORRECT       *)
(* theorem with the inputs and outputs as byte strings and the signature     *)
(* given by FIPS 204: ML-DSA.Sign_internal on M' = pre || m, or signing from *)
(* mu = the first 64 bytes of m when ext is not 0 (signature_internal),      *)
(* ML-DSA.Sign (signature), signing from mu (signature_extmu) and            *)
(* HashML-DSA.Sign (signature_pre_hash_internal, with the pre-hash ph and    *)
(* the hash function hashalg, and signature_pre_hash_shake256, with          *)
(* SHAKE256 pre-hashing). They follow from the CORRECT theorems and          *)
(* MLD_FIPS204_SIGN_44 etc. of utils/mldsa_native_fips204_sign.ml. When the  *)
(* code gives up (-4), the signature is zero and the first attempts of FIPS  *)
(* 204, as many as the code makes, are all rejected too. The secret key must *)
(* have s2 fields at most 2 * eta, as every key that key generation makes    *)
(* has, and the termination conditions are those of the CORRECT theorems.    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/fips204.ml";;
needs "arm/proofs/utils/mldsa_native_fips204_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_extmu_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_extmu_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_extmu_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_pre_hash_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_pre_hash_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_pre_hash_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_pre_hash_shake256_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_pre_hash_shake256_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_pre_hash_shake256_87_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte strings as numbers and as functions, and the 64 bytes of mu and      *)
(* the 32 random bytes as numbers.                                           *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_EL_LIST = prove
 (`!(l:byte list) n. LENGTH l = n ==> list_of_seq (\j. EL j l) n = l`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LIST_OF_SEQ_EQ_SELF]);;

let MLD_FIPS204_SIGN_BYTES_LENGTH = prove
 (`!(l:byte list) n.
        LENGTH l = n
        ==> num_of_bytelist l < 2 EXP (8 * n) /\
            bytelist_of_num n (num_of_bytelist l) = l`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BYTELIST_OF_NUM_OF_BYTELIST; EXP_MULT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[NUM_OF_BYTELIST_BOUND]);;

let MLD_FIPS204_SIGN_SK_RHO = prove
 (`!skl:byte list.
        mld_sk_rho (\j. EL j skl) = num_of_bytelist(mldsa_slice 0 32 skl)`,
  REWRITE_TAC[mld_sk_rho; mldsa_slice; ADD_CLAUSES]);;

let MLD_FIPS204_SIGN_MU64 = prove
 (`!l:byte list.
        LENGTH l = 64
        ==> num_of_bytelist l < 2 EXP 512 /\
            bytelist_of_num 64 (num_of_bytelist l) = l`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MLD_FIPS204_SIGN_BYTES_LENGTH) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MLD_FIPS204_SIGN_RND = prove
 (`!RND. RND < 2 EXP 256
         ==> LENGTH(bytelist_of_num 32 RND) = 32 /\
             num_of_bytelist(bytelist_of_num 32 RND) = RND`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN MATCH_MP_TAC MOD_LT THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MLD_FIPS204_SIGN_NUM_MOD = prove
 (`!(l:byte list) n.
        n <= LENGTH l
        ==> num_of_bytelist l MOD 2 EXP (8 * n) =
            num_of_bytelist(mldsa_slice 0 n l)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `n <= m ==> m = n + (m - n)`)) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD; mldsa_slice; ADD_CLAUSES] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[MLD_FIPS204_SIGN_NUM_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* The OIDs of the pre-hash functions of mldsa-native (hashalg = 1, ...,     *)
(* 12) as those of FIPS 204: mldsa_oid k for the FIPS 204 number k of the    *)
(* hash function.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_PREHASH_OID = prove
 (`mld_prehash_oid 1 = mldsa_oid 4 /\ mld_prehash_oid 2 = mldsa_oid 1 /\
   mld_prehash_oid 3 = mldsa_oid 2 /\ mld_prehash_oid 4 = mldsa_oid 3 /\
   mld_prehash_oid 5 = mldsa_oid 5 /\ mld_prehash_oid 6 = mldsa_oid 6 /\
   mld_prehash_oid 7 = mldsa_oid 7 /\ mld_prehash_oid 8 = mldsa_oid 8 /\
   mld_prehash_oid 9 = mldsa_oid 9 /\ mld_prehash_oid 10 = mldsa_oid 10 /\
   mld_prehash_oid 11 = mldsa_oid 11 /\ mld_prehash_oid 12 = mldsa_oid 12`,
  REWRITE_TAC[mld_prehash_oid; mldsa_oid] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The mu of the C code as that of FIPS 204, H(tr || M', 64), for M' =       *)
(* pre || m and for the HashML-DSA prefix 1 || |ctx| || ctx || OID || ph,    *)
(* with ph = H(m,64) for SHAKE256 pre-hashing.                               *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_MU_BYTES = prove
 (`!(skl:byte list) prel ml prelen mlen.
        LENGTH prel = prelen /\ LENGTH ml = mlen
        ==> mld_sign_mu (\j. EL (64 + j) skl) prelen (num_of_bytelist prel)
             mlen (num_of_bytelist ml) =
            num_of_bytelist
             (mldsa_h (APPEND (mldsa_slice 64 64 skl) (APPEND prel ml)) 64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\j. EL (64 + j) (skl:byte list)`; `prelen:num`;
                `num_of_bytelist(prel:byte list)`; `mlen:num`;
                `num_of_bytelist(ml:byte list)`] MLD_FIPS204_SIGN_MU) THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_BYTES_LENGTH] THEN
  REWRITE_TAC[mldsa_slice] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mld_sign_mu; MLD_FIPS204_SIGN_BYTELIST_NUM]);;

let MLD_FIPS204_SIGN_PREFIX_MU = prove
 (`!(skl:byte list) HA ctxl phl ctxlen phlen PLEN.
        LENGTH ctxl = ctxlen /\ LENGTH phl = phlen /\ ~(HA = 0) /\
        mld_domain_separation_prefix_length HA ctxlen phlen = PLEN /\
        ~(PLEN = 0)
        ==> mld_sign_mu (\j. EL (64 + j) skl) 0 0 PLEN
             (num_of_bytelist
               (mld_domain_separation_prefix HA
                 (bytelist_of_num ctxlen (num_of_bytelist ctxl))
                 (bytelist_of_num phlen (num_of_bytelist phl)))) =
            num_of_bytelist
             (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                        (APPEND (CONS (word 1) (CONS (word ctxlen) ctxl))
                                (APPEND (mld_prehash_oid HA) phl))) 64)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_BYTES_LENGTH] THEN
  MP_TAC(ISPECL [`skl:byte list`; `[]:byte list`;
                 `mld_domain_separation_prefix HA ctxl phl`; `0`; `PLEN:num`]
                MLD_FIPS204_SIGN_MU_BYTES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH] THEN
    MAP_EVERY (fun t -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                          check (fun th -> concl th = t)))
     [`LENGTH (ctxl:byte list) = ctxlen`; `LENGTH (phl:byte list) = phlen`;
      `mld_domain_separation_prefix_length HA (LENGTH (ctxl:byte list))
        (LENGTH (phl:byte list)) = PLEN`] THEN
    MATCH_MP_TAC LENGTH_MLD_DOMAIN_SEPARATION_PREFIX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[num_of_bytelist; APPEND] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[mld_domain_separation_prefix; APPEND]);;

let MLD_FIPS204_SIGN_SHAKE256_MU = prove
 (`!(skl:byte list) ctxl ml ctxlen.
        LENGTH ctxl = ctxlen /\ ctxlen <= 255
        ==> mld_sign_mu (\j. EL (64 + j) skl) 0 0
             (mld_domain_separation_prefix_length 12 ctxlen 64)
             (num_of_bytelist
               (mld_domain_separation_prefix 12
                 (bytelist_of_num ctxlen (num_of_bytelist ctxl))
                 (bytelist_of_num 64 (num_of_bytelist(mldsa_h ml 64))))) =
            num_of_bytelist
             (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                        (APPEND (CONS (word 1) (CONS (word ctxlen) ctxl))
                                (APPEND (mldsa_oid 12) (mldsa_h ml 64)))) 64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`skl:byte list`; `12`; `ctxl:byte list`;
                 `mldsa_h (ml:byte list) 64`; `ctxlen:num`; `64`;
                 `mld_domain_separation_prefix_length 12 ctxlen 64`]
                MLD_FIPS204_SIGN_PREFIX_MU) THEN
  REWRITE_TAC[MLD_FIPS204_PREHASH_OID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[mldsa_h; LENGTH_LIST_OF_SEQ; ARITH;
                  mld_domain_separation_prefix_length; mld_prehash_valid;
                  mld_prehash_length; GSYM NOT_LE] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MLD_FIPS204_SIGN_44 etc. for the secret key and the random bytes as byte  *)
(* strings: the signature of the first attempt that the C code accepts is    *)
(* that of signing from mu, and if it accepts none, its signature is zero    *)
(* and none of its attempts succeeds in FIPS 204.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_BYTES_TAC bridge_th ok_def sig_def =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `num_of_bytelist(rndl:byte list) < 2 EXP 256` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rndl:byte list`; `32`] MLD_FIPS204_SIGN_BYTES_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`\j. EL j (skl:byte list)`; `MU:num`;
                `num_of_bytelist(rndl:byte list)`] bridge_th) THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_EL_LIST; MLD_FIPS204_SIGN_SK_RHO;
               MLD_FIPS204_SIGN_BYTES_LENGTH] THEN
  REWRITE_TAC[ok_def; sig_def; mld_sign_sig] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_ZERO] THEN
  SIMP_TAC[];;

let MLD_FIPS204_SIGN_BYTES_44 = prove
 (`!skl MU rndl.
     LENGTH skl = 2560 /\ LENGTH rndl = 32 /\ MU < 2 EXP 512 /\
     (!n. n < 1024 ==> mldsa_field 3 (mldsa_slice 512 384 skl) n <= &4) /\
     mld_matrix_terminates 4 4 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
     mld_sign_terminates_44 (\j. EL j skl) MU (num_of_bytelist rndl)
     ==> (mld_sign_ok_44 (\j. EL j skl) MU (num_of_bytelist rndl)
          ==> mldsa_sign_mu mldsa44 skl (bytelist_of_num 64 MU) rndl =
              SOME(list_of_seq (mld_sign_sig_44 (\j. EL j skl) MU
                                 (num_of_bytelist rndl)) 2420)) /\
         (~mld_sign_ok_44 (\j. EL j skl) MU (num_of_bytelist rndl)
          ==> num_of_bytelist(list_of_seq (mld_sign_sig_44 (\j. EL j skl) MU
                                            (num_of_bytelist rndl)) 2420) =
              0 /\
              !n. n < 16382
                  ==> mld_fips204_sign_attempt mldsa44 skl
                       (bytelist_of_num 64 MU) rndl n = NONE)`,
  MLD_FIPS204_SIGN_BYTES_TAC MLD_FIPS204_SIGN_44
   mld_sign_ok_44 mld_sign_sig_44);;

let MLD_FIPS204_SIGN_BYTES_65 = prove
 (`!skl MU rndl.
     LENGTH skl = 4032 /\ LENGTH rndl = 32 /\ MU < 2 EXP 512 /\
     (!n. n < 1536 ==> mldsa_field 4 (mldsa_slice 768 768 skl) n <= &8) /\
     mld_matrix_terminates 6 5 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
     mld_sign_terminates_65 (\j. EL j skl) MU (num_of_bytelist rndl)
     ==> (mld_sign_ok_65 (\j. EL j skl) MU (num_of_bytelist rndl)
          ==> mldsa_sign_mu mldsa65 skl (bytelist_of_num 64 MU) rndl =
              SOME(list_of_seq (mld_sign_sig_65 (\j. EL j skl) MU
                                 (num_of_bytelist rndl)) 3309)) /\
         (~mld_sign_ok_65 (\j. EL j skl) MU (num_of_bytelist rndl)
          ==> num_of_bytelist(list_of_seq (mld_sign_sig_65 (\j. EL j skl) MU
                                            (num_of_bytelist rndl)) 3309) =
              0 /\
              !n. n < 13106
                  ==> mld_fips204_sign_attempt mldsa65 skl
                       (bytelist_of_num 64 MU) rndl n = NONE)`,
  MLD_FIPS204_SIGN_BYTES_TAC MLD_FIPS204_SIGN_65
   mld_sign_ok_65 mld_sign_sig_65);;

let MLD_FIPS204_SIGN_BYTES_87 = prove
 (`!skl MU rndl.
     LENGTH skl = 4896 /\ LENGTH rndl = 32 /\ MU < 2 EXP 512 /\
     (!n. n < 2048 ==> mldsa_field 3 (mldsa_slice 800 768 skl) n <= &4) /\
     mld_matrix_terminates 8 7 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
     mld_sign_terminates_87 (\j. EL j skl) MU (num_of_bytelist rndl)
     ==> (mld_sign_ok_87 (\j. EL j skl) MU (num_of_bytelist rndl)
          ==> mldsa_sign_mu mldsa87 skl (bytelist_of_num 64 MU) rndl =
              SOME(list_of_seq (mld_sign_sig_87 (\j. EL j skl) MU
                                 (num_of_bytelist rndl)) 4627)) /\
         (~mld_sign_ok_87 (\j. EL j skl) MU (num_of_bytelist rndl)
          ==> num_of_bytelist(list_of_seq (mld_sign_sig_87 (\j. EL j skl) MU
                                            (num_of_bytelist rndl)) 4627) =
              0 /\
              !n. n < 9361
                  ==> mld_fips204_sign_attempt mldsa87 skl
                       (bytelist_of_num 64 MU) rndl n = NONE)`,
  MLD_FIPS204_SIGN_BYTES_TAC MLD_FIPS204_SIGN_87
   mld_sign_ok_87 mld_sign_sig_87);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the API theorems. MLD_FIPS204_SIGN_MU_TAC turns the           *)
(* hypothesis num_of_bytelist e = MU into bytelist_of_num 64 MU = e and      *)
(* MU < 2 EXP 512; MLD_FIPS204_SIGN_CASES_TAC splits a goal                  *)
(* (ok ==> a) /\ (~ok ==> b) ==> g on ok; MLD_FIPS204_SIGN_SYM_TAC v flips   *)
(* the hypothesis v = t; MLD_FIPS204_SIGN_READ_TAC states the bytes of the   *)
(* signature as one number; MLD_FIPS204_SIGN_PRE_TAC reduces the ensures     *)
(* to the postcondition, given the CORRECT one; MLD_FIPS204_SIGN_TERM_TAC    *)
(* uses the termination hypothesis for the random bytes RND.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_MU_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if r = `MU:num` then
      let e = rand l in
      SUBGOAL_THEN (mk_conj(mk_eq(`bytelist_of_num 64 MU`,e),
                            `MU < 2 EXP 512`)) STRIP_ASSUME_TAC THENL
       [SUBST1_TAC(SYM th) THEN
        MATCH_MP_TAC(TAUT `p /\ q ==> q /\ p`) THEN
        MATCH_MP_TAC MLD_FIPS204_SIGN_MU64 THEN
        REPEAT COND_CASES_TAC THEN
        REWRITE_TAC[mldsa_h; LENGTH_LIST_OF_SEQ; LENGTH_MLDSA_SLICE];
        ALL_TAC]
    else failwith "MLD_FIPS204_SIGN_MU_TAC");;

let MLD_FIPS204_SIGN_CASES_TAC =
  MATCH_MP_TAC(TAUT `(p ==> a ==> g) /\ (~p ==> b ==> g)
                     ==> (p ==> a) /\ (~p ==> b) ==> g`) THEN
  CONJ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];;

let MLD_FIPS204_SIGN_SYM_TAC v =
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> lhs(concl th) = v));;

let MLD_FIPS204_SIGN_READ_TAC =
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP READ_BYTES_OF_BYTES8 o
    check (fun th -> is_forall(concl th) &&
                     free_in `sig:int64` (concl th)));;

let MLD_FIPS204_SIGN_PRE_TAC =
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BYTES8_OF_BYTES THEN ASM_SIMP_TAC[MLD_FIPS204_SIGN_EL_LIST];
    X_GEN_TAC `s:armstate`];;

let MLD_FIPS204_SIGN_TERM_TAC =
  FIRST_X_ASSUM(MP_TAC o SPEC `bytelist_of_num 32 RND` o check (fun th ->
    is_forall(concl th) &&
    type_of(fst(dest_forall(concl th))) = `:byte list`)) THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_RND];;

(* ------------------------------------------------------------------------- *)
(* signature_internal: Sign_internal on M' = pre || m (ext = 0) or signing   *)
(* from mu = the first 64 bytes of m.                                        *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_INTERNAL_API_TAC correct_th bridge_th =
  REPEAT GEN_TAC THEN DISCH_THEN(fun cth ->
    let th = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
      `rnd:int64`; `sk:int64`; `ext:int64`; `skl:byte list`;
      `ml:byte list`; `prel:byte list`; `rndl:byte list`; `MU:num`;
      `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] THEN
    STRIP_TAC THEN MLD_FIPS204_SIGN_SYM_TAC `MU:num` THEN
    MLD_FIPS204_SIGN_MU_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
      `rnd:int64`; `sk:int64`; `ext:int64`; `\j. EL j (skl:byte list)`;
      `num_of_bytelist(ml:byte list)`; `num_of_bytelist(prel:byte list)`;
      `num_of_bytelist(rndl:byte list)`; `MU:num`; `guard:int64`;
      `pc:num`; `stackpointer:int64`; `returnaddress:int64`] th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MLD_FIPS204_SIGN_SK_RHO] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rhs(concl th) = `MU:num`)) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLD_FIPS204_SIGN_MU_BYTES THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `2 EXP 512 = 2 EXP (8 * 64)`] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLD_FIPS204_SIGN_NUM_MOD THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MLD_FIPS204_SIGN_PRE_TAC THEN STRIP_TAC THEN MLD_FIPS204_SIGN_READ_TAC THEN
  MP_TAC(SPECL [`skl:byte list`; `MU:num`; `rndl:byte list`] bridge_th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN MLD_FIPS204_SIGN_CASES_TAC THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[mldsa_sign_internal] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ; UNWIND_THM1];;

(* ------------------------------------------------------------------------- *)
(* signature: ML-DSA.Sign with the context, the random bytes chosen by the   *)
(* code.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_API_TAC correct_th bridge_th =
  REPEAT GEN_TAC THEN DISCH_THEN(fun cth ->
    let th = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
      `sk:int64`; `skl:byte list`; `ml:byte list`; `ctxl:byte list`;
      `MU:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] THEN
    STRIP_TAC THEN MLD_FIPS204_SIGN_SYM_TAC `MU:num` THEN
    MLD_FIPS204_SIGN_MU_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
      `sk:int64`; `\j. EL j (skl:byte list)`;
      `num_of_bytelist(ml:byte list)`; `num_of_bytelist(ctxl:byte list)`;
      `MU:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MLD_FIPS204_SIGN_SK_RHO] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MLD_FIPS204_SIGN_BYTES_LENGTH] THEN
      REWRITE_TAC[mld_domain_separation_prefix] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        rhs(concl th) = `MU:num`)) THEN
      REWRITE_TAC[ASSUME `LENGTH (ctxl:byte list) = ctxlen`] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLD_FIPS204_SIGN_MU_BYTES THEN
      ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `ctxlen <= 255`)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `RND:num` THEN DISCH_TAC THEN MLD_FIPS204_SIGN_TERM_TAC];
    ALL_TAC] THEN
  MLD_FIPS204_SIGN_PRE_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `RND:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `bytelist_of_num 32 RND` THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_RND] THEN MLD_FIPS204_SIGN_READ_TAC THEN
  ASM_CASES_TAC `255 < ctxlen` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_imp(concl th) && lhand(concl th) = `255 < ctxlen`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[mldsa_sign] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_ZERO] THEN
    UNDISCH_TAC `255 < ctxlen` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [UNDISCH_TAC `~(255 < ctxlen)` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && lhand(concl th) = `ctxlen <= 255` &&
    free_in `s:armstate` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     lhand(concl th) = `ctxlen <= 255`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `bytelist_of_num 32 RND`)) THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_RND] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`skl:byte list`; `MU:num`; `bytelist_of_num 32 RND`]
               bridge_th) THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_RND] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    is_disj(concl th) && free_in `s:armstate` (concl th))) THEN
  MLD_FIPS204_SIGN_CASES_TAC THEN STRIP_TAC THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_ZERO; ETA_AX; option_INJ;
                  UNWIND_THM1; mldsa_sign; mldsa_sign_internal];;

(* ------------------------------------------------------------------------- *)
(* signature_extmu: signing from the given mu.                               *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_EXTMU_API_TAC correct_th bridge_th =
  REPEAT GEN_TAC THEN DISCH_THEN(fun cth ->
    let th = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `mu:int64`; `sk:int64`; `skl:byte list`;
      `mul:byte list`; `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `mu:int64`; `sk:int64`; `\j. EL j (skl:byte list)`;
      `num_of_bytelist(mul:byte list)`; `guard:int64`; `pc:num`;
      `stackpointer:int64`; `returnaddress:int64`] th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MLD_FIPS204_SIGN_SK_RHO] THEN
    X_GEN_TAC `RND:num` THEN DISCH_TAC THEN MLD_FIPS204_SIGN_TERM_TAC;
    ALL_TAC] THEN
  MLD_FIPS204_SIGN_PRE_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `RND:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `bytelist_of_num 32 RND` THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_RND] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MLD_FIPS204_SIGN_READ_TAC THEN MLD_FIPS204_SIGN_TERM_TAC THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`skl:byte list`; `num_of_bytelist(mul:byte list)`;
                `bytelist_of_num 32 RND`] bridge_th) THEN
  ASM_SIMP_TAC[MLD_FIPS204_SIGN_RND; MLD_FIPS204_SIGN_MU64] THEN
  MLD_FIPS204_SIGN_CASES_TAC THEN STRIP_TAC THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_ZERO; ETA_AX; option_INJ;
                  UNWIND_THM1];;

(* ------------------------------------------------------------------------- *)
(* signature_pre_hash_internal: HashML-DSA.Sign with the given pre-hash, the *)
(* hash function given by hashalg.                                           *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_PRE_HASH_INTERNAL_API_TAC correct_th bridge_th =
  REPEAT GEN_TAC THEN DISCH_THEN(fun cth ->
    let th = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
      `rnd:int64`; `sk:int64`; `hashalg:int64`; `skl:byte list`;
      `phl:byte list`; `ctxl:byte list`; `rndl:byte list`; `HA:num`;
      `PLEN:num`; `MU:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] THEN
    STRIP_TAC THEN
    MAP_EVERY MLD_FIPS204_SIGN_SYM_TAC [`HA:num`; `PLEN:num`; `MU:num`] THEN
    MLD_FIPS204_SIGN_MU_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
      `rnd:int64`; `sk:int64`; `hashalg:int64`; `\j. EL j (skl:byte list)`;
      `num_of_bytelist(phl:byte list)`; `num_of_bytelist(ctxl:byte list)`;
      `num_of_bytelist(rndl:byte list)`; `HA:num`; `PLEN:num`;
      `num_of_bytelist(mld_domain_separation_prefix HA
         (bytelist_of_num ctxlen (num_of_bytelist(ctxl:byte list)))
         (bytelist_of_num phlen (num_of_bytelist(phl:byte list))))`;
      `mld_sign_mu (\j. EL (64 + j) (skl:byte list)) 0 0 PLEN
        (num_of_bytelist(mld_domain_separation_prefix HA
          (bytelist_of_num ctxlen (num_of_bytelist(ctxl:byte list)))
          (bytelist_of_num phlen (num_of_bytelist(phl:byte list)))))`;
      `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MLD_FIPS204_SIGN_SK_RHO] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`skl:byte list`; `HA:num`; `ctxl:byte list`;
                  `phl:byte list`; `ctxlen:num`; `phlen:num`; `PLEN:num`]
                 MLD_FIPS204_SIGN_PREFIX_MU) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(concl th) = `~(HA = 0) /\ ~(PLEN = 0)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MLD_FIPS204_SIGN_PRE_TAC THEN STRIP_TAC THEN MLD_FIPS204_SIGN_READ_TAC THEN
  ASM_CASES_TAC `HA = 0 \/ PLEN = 0` THENL
   [SUBGOAL_THEN `~(~(HA = 0) /\ ~(PLEN = 0))` (fun th -> REWRITE_TAC[th])
    THENL [ASM_REWRITE_TAC[DE_MORGAN_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_ZERO];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM] o
    check (fun th -> concl th = `~(HA = 0 \/ PLEN = 0)`)) THEN
  SUBGOAL_THEN `~(255 < ctxlen)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(PLEN = 0)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rhs(concl th) = `PLEN:num`)) THEN
    REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`skl:byte list`; `HA:num`; `ctxl:byte list`;
                `phl:byte list`; `ctxlen:num`; `phlen:num`; `PLEN:num`]
               MLD_FIPS204_SIGN_PREFIX_MU) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `~(HA = 0) /\ ~(PLEN = 0)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`skl:byte list`; `MU:num`; `rndl:byte list`] bridge_th) THEN
  ASM_REWRITE_TAC[] THEN MLD_FIPS204_SIGN_CASES_TAC THEN STRIP_TAC THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_ZERO; ETA_AX; option_INJ;
                  UNWIND_THM1; hash_mldsa_sign; mldsa_sign_internal];;

(* ------------------------------------------------------------------------- *)
(* signature_pre_hash_shake256: HashML-DSA.Sign with SHAKE256 pre-hashing    *)
(* (OID 2.16.840.1.101.3.4.2.12, PH(M) = H(M,64)).                           *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SIGN_PRE_HASH_SHAKE256_API_TAC correct_th bridge_th =
  REPEAT GEN_TAC THEN DISCH_THEN(fun cth ->
    let th = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
      `rnd:int64`; `sk:int64`; `skl:byte list`; `ml:byte list`;
      `ctxl:byte list`; `rndl:byte list`; `MU:num`; `guard:int64`;
      `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
    STRIP_TAC THEN MLD_FIPS204_SIGN_SYM_TAC `MU:num` THEN
    MLD_FIPS204_SIGN_MU_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
      `rnd:int64`; `sk:int64`; `\j. EL j (skl:byte list)`;
      `num_of_bytelist(ml:byte list)`; `num_of_bytelist(ctxl:byte list)`;
      `num_of_bytelist(rndl:byte list)`;
      `num_of_bytelist(mldsa_h (ml:byte list) 64)`;
      `num_of_bytelist(mld_domain_separation_prefix 12
         (bytelist_of_num ctxlen (num_of_bytelist(ctxl:byte list)))
         (bytelist_of_num 64 (num_of_bytelist(mldsa_h (ml:byte list) 64))))`;
      `mld_sign_mu (\j. EL (64 + j) (skl:byte list)) 0 0
        (mld_domain_separation_prefix_length 12 ctxlen 64)
        (num_of_bytelist(mld_domain_separation_prefix 12
          (bytelist_of_num ctxlen (num_of_bytelist(ctxl:byte list)))
          (bytelist_of_num 64
            (num_of_bytelist(mldsa_h (ml:byte list) 64)))))`;
      `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MLD_FIPS204_SIGN_SK_RHO] THEN CONJ_TAC THENL
     [REWRITE_TAC[mldsa_h] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN
      ASM_SIMP_TAC[MLD_FIPS204_SHAKE256_BYTE; MLD_FIPS204_SIGN_BYTES_LENGTH];
      DISCH_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_SIGN_SHAKE256_MU] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `ctxlen <= 255`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MLD_FIPS204_SIGN_PRE_TAC THEN STRIP_TAC THEN MLD_FIPS204_SIGN_READ_TAC THEN
  ASM_CASES_TAC `255 < ctxlen` THENL
   [SUBGOAL_THEN `~(ctxlen <= 255)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `255 < ctxlen` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[hash_mldsa_sign] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [UNDISCH_TAC `~(255 < ctxlen)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`skl:byte list`; `ctxl:byte list`; `ml:byte list`;
                `ctxlen:num`] MLD_FIPS204_SIGN_SHAKE256_MU) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `ctxlen <= 255`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`skl:byte list`; `MU:num`; `rndl:byte list`] bridge_th) THEN
  ASM_REWRITE_TAC[] THEN MLD_FIPS204_SIGN_CASES_TAC THEN STRIP_TAC THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_ZERO; ETA_AX; option_INJ;
                  UNWIND_THM1; hash_mldsa_sign; mldsa_sign_internal];;

(* ------------------------------------------------------------------------- *)
(* The signing functions for ML-DSA-44.                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen pre prelen rnd sk ext skl ml prel rndl MU guard
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          LENGTH skl = 2560 /\ LENGTH ml = mlen /\ LENGTH prel = prelen /\
          LENGTH rndl = 32 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = num_of_bytelist
                (if word_zx ext = (word 0:int32)
                 then mldsa_h (APPEND (mldsa_slice 64 64 skl)
                                      (APPEND prel ml)) 64
                 else mldsa_slice 0 64 ml) /\
          (!n. n < 1024
               ==> mldsa_field 3 (mldsa_slice 512 384 skl) n <= &4) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          mld_sign_terminates_44 (\j. EL j skl) MU (num_of_bytelist rndl) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49536),49536)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49536),49536)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_signature_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd; sk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(pre,prelen)) s =
                    num_of_bytelist prel /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,2560)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. (if word_zx ext = (word 0:int32)
                               then mldsa_sign_internal mldsa44 skl
                                     (APPEND prel ml) rndl
                               else mldsa_sign_mu mldsa44 skl
                                     (mldsa_slice 0 64 ml) rndl) = SOME sg /\
                              read (memory :> bytes(sig,2420)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,2420)) s = 0 /\
                         !n. n < 16382
                             ==> mld_fips204_sign_attempt mldsa44 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49536),49536)])`,
  MLD_FIPS204_SIGN_INTERNAL_API_TAC
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_44);;

let MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig m mlen ctx ctxlen sk skl ml ctxl MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 2560 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 0) (CONS (word ctxlen) ctxl))
                                   ml)) 64) /\
          (!n. n < 1024
               ==> mldsa_field 3 (mldsa_slice 512 384 skl) n <= &4) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               !rndl. LENGTH rndl = 32
                      ==> mld_sign_terminates_44 (\j. EL j skl) MU
                           (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50032),50032)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50032),50032)]
           [(m,mlen); (ctx,ctxlen); (sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_signature) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(sk,2560)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    ?rndl.
                      LENGTH rndl = 32 /\
                      (255 < ctxlen
                       ==> C_RETURN s = word 4294967287 /\
                           mldsa_sign mldsa44 skl ml ctxl rndl = NONE) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 0 \/
                           C_RETURN s = word 4294967292 \/
                           C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> ?sg. mldsa_sign mldsa44 skl ml ctxl rndl = SOME sg /\
                                read (memory :> bytes(sig,2420)) s =
                                num_of_bytelist sg) /\
                      (~(C_RETURN s = word 0)
                       ==> read (memory :> bytes(sig,2420)) s = 0) /\
                      (C_RETURN s = word 4294967292
                       ==> !n. n < 16382
                               ==> mld_fips204_sign_attempt mldsa44 skl
                                    (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 50032),50032)])`,
  MLD_FIPS204_SIGN_API_TAC
   MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_44);;

let MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig mu sk skl mul guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          LENGTH skl = 2560 /\ LENGTH mul = 64 /\
          (!n. n < 1024
               ==> mldsa_field 3 (mldsa_slice 512 384 skl) n <= &4) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          (!rndl. LENGTH rndl = 32
                  ==> mld_sign_terminates_44 (\j. EL j skl)
                       (num_of_bytelist mul) (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49648),49648)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49648),49648)]
           [(mu,64); (sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_signature_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = num_of_bytelist mul /\
                    read (memory :> bytes(sk,2560)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    ?rndl.
                      LENGTH rndl = 32 /\
                      (C_RETURN s = word 0 \/ C_RETURN s = word 4294967292 \/
                       C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> ?sg. mldsa_sign_mu mldsa44 skl mul rndl = SOME sg /\
                                read (memory :> bytes(sig,2420)) s =
                                num_of_bytelist sg) /\
                      (C_RETURN s = word 4294967292
                       ==> read (memory :> bytes(sig,2420)) s = 0 /\
                           !n. n < 16382
                               ==> mld_fips204_sign_attempt mldsa44 skl mul
                                    rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49648),49648)])`,
  MLD_FIPS204_SIGN_EXTMU_API_TAC
   MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_44);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen rnd sk hashalg skl phl ctxl rndl HA PLEN MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 2560 /\ LENGTH phl = phlen /\ LENGTH ctxl = ctxlen /\
          LENGTH rndl = 32 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 1) (CONS (word ctxlen) ctxl))
                                   (APPEND (mld_prehash_oid HA) phl))) 64) /\
          (!n. n < 1024
               ==> mldsa_field 3 (mldsa_slice 512 384 skl) n <= &4) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               mld_sign_terminates_44 (\j. EL j skl) MU
                (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49952),49952)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49952),49952)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = num_of_bytelist phl /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,2560)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (HA = 0 \/ PLEN = 0
                     ==> C_RETURN s = word 4294967287 /\
                         read (memory :> bytes(sig,2420)) s = 0) /\
                    (~(HA = 0) /\ ~(PLEN = 0)
                     ==> C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. hash_mldsa_sign mldsa44 skl (mld_prehash_oid HA)
                               phl ctxl rndl = SOME sg /\
                              read (memory :> bytes(sig,2420)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,2420)) s = 0 /\
                         !n. n < 16382
                             ==> mld_fips204_sign_attempt mldsa44 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49952),49952)])`,
  MLD_FIPS204_SIGN_PRE_HASH_INTERNAL_API_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_44);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen rnd sk skl ml ctxl rndl MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 2560 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH rndl = 32 /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 1) (CONS (word ctxlen) ctxl))
                                   (APPEND (mldsa_oid 12) (mldsa_h ml 64))))
                         64) /\
          (!n. n < 1024
               ==> mldsa_field 3 (mldsa_slice 512 384 skl) n <= &4) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               mld_sign_terminates_44 (\j. EL j skl) MU
                (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50112),50112)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50112),50112)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd;
                                 sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,2560)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (255 < ctxlen
                     ==> C_RETURN s = word 4294967287 /\
                         hash_mldsa_sign mldsa44 skl (mldsa_oid 12)
                          (mldsa_h ml 64) ctxl rndl = NONE /\
                         read (memory :> bytes(sig,2420)) s = 0) /\
                    (ctxlen <= 255
                     ==> C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. hash_mldsa_sign mldsa44 skl (mldsa_oid 12)
                               (mldsa_h ml 64) ctxl rndl = SOME sg /\
                              read (memory :> bytes(sig,2420)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,2420)) s = 0 /\
                         !n. n < 16382
                             ==> mld_fips204_sign_attempt mldsa44 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 50112),50112)])`,
  MLD_FIPS204_SIGN_PRE_HASH_SHAKE256_API_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_44);;

(* ------------------------------------------------------------------------- *)
(* The signing functions for ML-DSA-65.                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen pre prelen rnd sk ext skl ml prel rndl MU guard
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          LENGTH skl = 4032 /\ LENGTH ml = mlen /\ LENGTH prel = prelen /\
          LENGTH rndl = 32 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = num_of_bytelist
                (if word_zx ext = (word 0:int32)
                 then mldsa_h (APPEND (mldsa_slice 64 64 skl)
                                      (APPEND prel ml)) 64
                 else mldsa_slice 0 64 ml) /\
          (!n. n < 1536
               ==> mldsa_field 4 (mldsa_slice 768 768 skl) n <= &8) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          mld_sign_terminates_65 (\j. EL j skl) MU (num_of_bytelist rndl) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73088),73088)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73088),73088)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd; sk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(pre,prelen)) s =
                    num_of_bytelist prel /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,4032)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. (if word_zx ext = (word 0:int32)
                               then mldsa_sign_internal mldsa65 skl
                                     (APPEND prel ml) rndl
                               else mldsa_sign_mu mldsa65 skl
                                     (mldsa_slice 0 64 ml) rndl) = SOME sg /\
                              read (memory :> bytes(sig,3309)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,3309)) s = 0 /\
                         !n. n < 13106
                             ==> mld_fips204_sign_attempt mldsa65 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73088),73088)])`,
  MLD_FIPS204_SIGN_INTERNAL_API_TAC
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_65);;

let MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig m mlen ctx ctxlen sk skl ml ctxl MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 4032 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 0) (CONS (word ctxlen) ctxl))
                                   ml)) 64) /\
          (!n. n < 1536
               ==> mldsa_field 4 (mldsa_slice 768 768 skl) n <= &8) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               !rndl. LENGTH rndl = 32
                      ==> mld_sign_terminates_65 (\j. EL j skl) MU
                           (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73584),73584)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73584),73584)]
           [(m,mlen); (ctx,ctxlen); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(sk,4032)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    ?rndl.
                      LENGTH rndl = 32 /\
                      (255 < ctxlen
                       ==> C_RETURN s = word 4294967287 /\
                           mldsa_sign mldsa65 skl ml ctxl rndl = NONE) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 0 \/
                           C_RETURN s = word 4294967292 \/
                           C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> ?sg. mldsa_sign mldsa65 skl ml ctxl rndl = SOME sg /\
                                read (memory :> bytes(sig,3309)) s =
                                num_of_bytelist sg) /\
                      (~(C_RETURN s = word 0)
                       ==> read (memory :> bytes(sig,3309)) s = 0) /\
                      (C_RETURN s = word 4294967292
                       ==> !n. n < 13106
                               ==> mld_fips204_sign_attempt mldsa65 skl
                                    (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73584),73584)])`,
  MLD_FIPS204_SIGN_API_TAC
   MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_65);;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig mu sk skl mul guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          LENGTH skl = 4032 /\ LENGTH mul = 64 /\
          (!n. n < 1536
               ==> mldsa_field 4 (mldsa_slice 768 768 skl) n <= &8) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          (!rndl. LENGTH rndl = 32
                  ==> mld_sign_terminates_65 (\j. EL j skl)
                       (num_of_bytelist mul) (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73200),73200)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73200),73200)]
           [(mu,64); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = num_of_bytelist mul /\
                    read (memory :> bytes(sk,4032)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    ?rndl.
                      LENGTH rndl = 32 /\
                      (C_RETURN s = word 0 \/ C_RETURN s = word 4294967292 \/
                       C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> ?sg. mldsa_sign_mu mldsa65 skl mul rndl = SOME sg /\
                                read (memory :> bytes(sig,3309)) s =
                                num_of_bytelist sg) /\
                      (C_RETURN s = word 4294967292
                       ==> read (memory :> bytes(sig,3309)) s = 0 /\
                           !n. n < 13106
                               ==> mld_fips204_sign_attempt mldsa65 skl mul
                                    rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73200),73200)])`,
  MLD_FIPS204_SIGN_EXTMU_API_TAC
   MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_65);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen rnd sk hashalg skl phl ctxl rndl HA PLEN MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 4032 /\ LENGTH phl = phlen /\ LENGTH ctxl = ctxlen /\
          LENGTH rndl = 32 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 1) (CONS (word ctxlen) ctxl))
                                   (APPEND (mld_prehash_oid HA) phl))) 64) /\
          (!n. n < 1536
               ==> mldsa_field 4 (mldsa_slice 768 768 skl) n <= &8) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               mld_sign_terminates_65 (\j. EL j skl) MU
                (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73504),73504)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73504),73504)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa65_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = num_of_bytelist phl /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,4032)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (HA = 0 \/ PLEN = 0
                     ==> C_RETURN s = word 4294967287 /\
                         read (memory :> bytes(sig,3309)) s = 0) /\
                    (~(HA = 0) /\ ~(PLEN = 0)
                     ==> C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. hash_mldsa_sign mldsa65 skl (mld_prehash_oid HA)
                               phl ctxl rndl = SOME sg /\
                              read (memory :> bytes(sig,3309)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,3309)) s = 0 /\
                         !n. n < 13106
                             ==> mld_fips204_sign_attempt mldsa65 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73504),73504)])`,
  MLD_FIPS204_SIGN_PRE_HASH_INTERNAL_API_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_65);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen rnd sk skl ml ctxl rndl MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 4032 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH rndl = 32 /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 1) (CONS (word ctxlen) ctxl))
                                   (APPEND (mldsa_oid 12) (mldsa_h ml 64))))
                         64) /\
          (!n. n < 1536
               ==> mldsa_field 4 (mldsa_slice 768 768 skl) n <= &8) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               mld_sign_terminates_65 (\j. EL j skl) MU
                (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73664),73664)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73664),73664)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa65_signature_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd;
                                 sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,4032)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (255 < ctxlen
                     ==> C_RETURN s = word 4294967287 /\
                         hash_mldsa_sign mldsa65 skl (mldsa_oid 12)
                          (mldsa_h ml 64) ctxl rndl = NONE /\
                         read (memory :> bytes(sig,3309)) s = 0) /\
                    (ctxlen <= 255
                     ==> C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. hash_mldsa_sign mldsa65 skl (mldsa_oid 12)
                               (mldsa_h ml 64) ctxl rndl = SOME sg /\
                              read (memory :> bytes(sig,3309)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,3309)) s = 0 /\
                         !n. n < 13106
                             ==> mld_fips204_sign_attempt mldsa65 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73664),73664)])`,
  MLD_FIPS204_SIGN_PRE_HASH_SHAKE256_API_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_65);;

(* ------------------------------------------------------------------------- *)
(* The signing functions for ML-DSA-87.                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen pre prelen rnd sk ext skl ml prel rndl MU guard
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          LENGTH skl = 4896 /\ LENGTH ml = mlen /\ LENGTH prel = prelen /\
          LENGTH rndl = 32 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = num_of_bytelist
                (if word_zx ext = (word 0:int32)
                 then mldsa_h (APPEND (mldsa_slice 64 64 skl)
                                      (APPEND prel ml)) 64
                 else mldsa_slice 0 64 ml) /\
          (!n. n < 2048
               ==> mldsa_field 3 (mldsa_slice 800 768 skl) n <= &4) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          mld_sign_terminates_87 (\j. EL j skl) MU (num_of_bytelist rndl) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112272),112272)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112272),112272)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd; sk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(pre,prelen)) s =
                    num_of_bytelist prel /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,4896)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. (if word_zx ext = (word 0:int32)
                               then mldsa_sign_internal mldsa87 skl
                                     (APPEND prel ml) rndl
                               else mldsa_sign_mu mldsa87 skl
                                     (mldsa_slice 0 64 ml) rndl) = SOME sg /\
                              read (memory :> bytes(sig,4627)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,4627)) s = 0 /\
                         !n. n < 9361
                             ==> mld_fips204_sign_attempt mldsa87 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112272),
                                  112272)])`,
  MLD_FIPS204_SIGN_INTERNAL_API_TAC
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_87);;

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig m mlen ctx ctxlen sk skl ml ctxl MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 4896 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 0) (CONS (word ctxlen) ctxl))
                                   ml)) 64) /\
          (!n. n < 2048
               ==> mldsa_field 3 (mldsa_slice 800 768 skl) n <= &4) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               !rndl. LENGTH rndl = 32
                      ==> mld_sign_terminates_87 (\j. EL j skl) MU
                           (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112768),112768)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112768),112768)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(sk,4896)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    ?rndl.
                      LENGTH rndl = 32 /\
                      (255 < ctxlen
                       ==> C_RETURN s = word 4294967287 /\
                           mldsa_sign mldsa87 skl ml ctxl rndl = NONE) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 0 \/
                           C_RETURN s = word 4294967292 \/
                           C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> ?sg. mldsa_sign mldsa87 skl ml ctxl rndl = SOME sg /\
                                read (memory :> bytes(sig,4627)) s =
                                num_of_bytelist sg) /\
                      (~(C_RETURN s = word 0)
                       ==> read (memory :> bytes(sig,4627)) s = 0) /\
                      (C_RETURN s = word 4294967292
                       ==> !n. n < 9361
                               ==> mld_fips204_sign_attempt mldsa87 skl
                                    (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112768),
                                  112768)])`,
  MLD_FIPS204_SIGN_API_TAC
   MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_87);;

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig mu sk skl mul guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          LENGTH skl = 4896 /\ LENGTH mul = 64 /\
          (!n. n < 2048
               ==> mldsa_field 3 (mldsa_slice 800 768 skl) n <= &4) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          (!rndl. LENGTH rndl = 32
                  ==> mld_sign_terminates_87 (\j. EL j skl)
                       (num_of_bytelist mul) (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112384),112384)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112384),112384)]
           [(mu,64); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = num_of_bytelist mul /\
                    read (memory :> bytes(sk,4896)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    ?rndl.
                      LENGTH rndl = 32 /\
                      (C_RETURN s = word 0 \/ C_RETURN s = word 4294967292 \/
                       C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> ?sg. mldsa_sign_mu mldsa87 skl mul rndl = SOME sg /\
                                read (memory :> bytes(sig,4627)) s =
                                num_of_bytelist sg) /\
                      (C_RETURN s = word 4294967292
                       ==> read (memory :> bytes(sig,4627)) s = 0 /\
                           !n. n < 9361
                               ==> mld_fips204_sign_attempt mldsa87 skl mul
                                    rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112384),
                                  112384)])`,
  MLD_FIPS204_SIGN_EXTMU_API_TAC
   MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_87);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen rnd sk hashalg skl phl ctxl rndl HA PLEN MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 4896 /\ LENGTH phl = phlen /\ LENGTH ctxl = ctxlen /\
          LENGTH rndl = 32 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 1) (CONS (word ctxlen) ctxl))
                                   (APPEND (mld_prehash_oid HA) phl))) 64) /\
          (!n. n < 2048
               ==> mldsa_field 3 (mldsa_slice 800 768 skl) n <= &4) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               mld_sign_terminates_87 (\j. EL j skl) MU
                (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112688),112688)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112688),112688)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa87_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = num_of_bytelist phl /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,4896)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (HA = 0 \/ PLEN = 0
                     ==> C_RETURN s = word 4294967287 /\
                         read (memory :> bytes(sig,4627)) s = 0) /\
                    (~(HA = 0) /\ ~(PLEN = 0)
                     ==> C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. hash_mldsa_sign mldsa87 skl (mld_prehash_oid HA)
                               phl ctxl rndl = SOME sg /\
                              read (memory :> bytes(sig,4627)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,4627)) s = 0 /\
                         !n. n < 9361
                             ==> mld_fips204_sign_attempt mldsa87 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112688),
                                  112688)])`,
  MLD_FIPS204_SIGN_PRE_HASH_INTERNAL_API_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_87);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen rnd sk skl ml ctxl rndl MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          LENGTH skl = 4896 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH rndl = 32 /\
          MU = num_of_bytelist
                (mldsa_h (APPEND (mldsa_slice 64 64 skl)
                           (APPEND (CONS (word 1) (CONS (word ctxlen) ctxl))
                                   (APPEND (mldsa_oid 12) (mldsa_h ml 64))))
                         64) /\
          (!n. n < 2048
               ==> mldsa_field 3 (mldsa_slice 800 768 skl) n <= &4) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(mldsa_slice 0 32 skl)) /\
               mld_sign_terminates_87 (\j. EL j skl) MU
                (num_of_bytelist rndl)) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112848),112848)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112848),112848)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa87_signature_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd;
                                 sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(rnd,32)) s = num_of_bytelist rndl /\
                    read (memory :> bytes(sk,4896)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    (255 < ctxlen
                     ==> C_RETURN s = word 4294967287 /\
                         hash_mldsa_sign mldsa87 skl (mldsa_oid 12)
                          (mldsa_h ml 64) ctxl rndl = NONE /\
                         read (memory :> bytes(sig,4627)) s = 0) /\
                    (ctxlen <= 255
                     ==> C_RETURN s = word 0 \/ C_RETURN s = word 4294967292) /\
                    (C_RETURN s = word 0
                     ==> ?sg. hash_mldsa_sign mldsa87 skl (mldsa_oid 12)
                               (mldsa_h ml 64) ctxl rndl = SOME sg /\
                              read (memory :> bytes(sig,4627)) s =
                              num_of_bytelist sg) /\
                    (C_RETURN s = word 4294967292
                     ==> read (memory :> bytes(sig,4627)) s = 0 /\
                         !n. n < 9361
                             ==> mld_fips204_sign_attempt mldsa87 skl
                                  (bytelist_of_num 64 MU) rndl n = NONE))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112848),
                                  112848)])`,
  MLD_FIPS204_SIGN_PRE_HASH_SHAKE256_API_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_SIGN_BYTES_87);;
