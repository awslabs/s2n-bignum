(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The verification API functions of mldsa-native in the gcc 12 -O2 image,   *)
(* stated with the FIPS 204 specification of ML-DSA in common/fips204.ml:    *)
(* for verify_internal, verify, verify_extmu, verify_pre_hash_internal and   *)
(* verify_pre_hash_shake256 and each parameter set, the theorem ..._FIPS204  *)
(* is the CORRECT theorem of the function with the signature, the public     *)
(* key, the message, the prefix, the context, mu and the pre-hash as byte    *)
(* strings, and the result that of ML-DSA.Verify_internal or of the          *)
(* verification from mu (mldsa_verify_internal, mldsa_verify_mu), of         *)
(* ML-DSA.Verify (mldsa_verify) or of HashML-DSA.Verify                      *)
(* (hash_mldsa_verify), with the error codes of the checks that the C code   *)
(* makes first. They are derived from the CORRECT theorems and the lemmas    *)
(* of utils/mldsa_native_fips204_verify.ml.                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_fips204_verify.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/fips204.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_extmu_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_extmu_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_extmu_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_shake256_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_shake256_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_shake256_87_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte strings: a list of n bytes as the number that memory holds, read     *)
(* byte by byte or as its first n' <= n bytes (the first 64 for external mu, *)
(* which the C code takes as the message MOD 2^512).                         *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_LIST_OF_SEQ_EL = prove
 (`!(l:A list) n. LENGTH l = n ==> list_of_seq (\j. EL j l) n = l`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LIST_OF_SEQ_EQ_SELF]);;

let MLD_FIPS204_VERIFY_BYTELIST_EQ = prove
 (`!(l:byte list) n.
        LENGTH l = n
        ==> bytelist_of_num n (num_of_bytelist l) = l /\
            num_of_bytelist l < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BYTELIST_OF_NUM_OF_BYTELIST] THEN
  MP_TAC(ISPEC `l:byte list` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_FIPS204_VERIFY_BYTELIST_PREFIX = prove
 (`!(l:byte list) n.
        n <= LENGTH l
        ==> bytelist_of_num n (num_of_bytelist l) = mldsa_slice 0 n l`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
  SUBGOAL_THEN `LENGTH(l:byte list) = n + (LENGTH l - n)` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MLD_FIPS204_SAMPLE_BYTELIST_OF_NUM_ADD] THEN
  SIMP_TAC[MLDSA_SLICE_APPEND; LENGTH_BYTELIST_OF_NUM; ADD_CLAUSES;
           LE_REFL] THEN
  MP_TAC(ISPEC `bytelist_of_num n (num_of_bytelist(l:byte list))`
               MLDSA_SLICE_LENGTH) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN SIMP_TAC[]);;

let MLD_FIPS204_VERIFY_EXTMU_BYTES = prove
 (`!l:byte list.
        64 <= LENGTH l
        ==> bytelist_of_num 64 (num_of_bytelist l MOD 2 EXP 512) =
            mldsa_slice 0 64 l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 512 = 256 EXP 64`; BYTELIST_OF_NUM_MOD] THEN
  MATCH_MP_TAC MLD_FIPS204_VERIFY_BYTELIST_PREFIX THEN ASM_REWRITE_TAC[]);;

let MLD_FIPS204_VERIFY_EL_BYTES8 = prove
 (`!a n (l:byte list) s.
        LENGTH l = n /\ read(memory :> bytes(a,n)) s = num_of_bytelist l
        ==> !j. j < n ==> read(memory :> bytes8(word_add a (word j))) s =
                          EL j l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC BYTES8_OF_BYTES THEN
  ASM_SIMP_TAC[MLD_FIPS204_VERIFY_LIST_OF_SEQ_EL]);;

let MLD_FIPS204_VERIFY_LENGTH_H = prove
 (`!m n. LENGTH(mldsa_h m n) = n`,
  REWRITE_TAC[mldsa_h; LENGTH_LIST_OF_SEQ]);;

(* ------------------------------------------------------------------------- *)
(* The domain separation prefix of the C code for HashML-DSA: it is rejected *)
(* (length 0) iff the hash algorithm is unknown or the pre-hash does not     *)
(* have its length, or the context is too long; otherwise it is the message  *)
(* 1 || |ctx| || ctx || OID || ph of HashML-DSA.Verify, of length |ctx| +    *)
(* |ph| + 13. The OID of SHAKE256 (hashalg 12) is mldsa_oid 12.              *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_PREHASH_CHECK = prove
 (`!h c p. (h = 0 \/ mld_domain_separation_prefix_length h c p = 0 <=>
            ~mld_prehash_valid h p \/ 255 < c) /\
           (~(h = 0) /\ ~(mld_domain_separation_prefix_length h c p = 0) <=>
            mld_prehash_valid h p /\ c <= 255)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_domain_separation_prefix_length] THEN
  ASM_CASES_TAC `255 < c` THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  ASM_CASES_TAC `h = 0` THEN ASM_REWRITE_TAC[mld_prehash_valid] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let MLD_FIPS204_VERIFY_PREHASH_PREFIX = prove
 (`!h (ctx:byte list) (ph:byte list).
        mld_prehash_valid h (LENGTH ph) /\ LENGTH ctx <= 255
        ==> mld_domain_separation_prefix_length h (LENGTH ctx) (LENGTH ph) =
            LENGTH(mld_domain_separation_prefix h ctx ph) /\
            LENGTH(mld_domain_separation_prefix h ctx ph) =
            LENGTH ctx + LENGTH ph + 13 /\
            !p pk sg.
              hash_mldsa_verify p pk (mld_prehash_oid h) ph sg ctx <=>
              mldsa_verify_internal p pk (mld_domain_separation_prefix h ctx ph)
               sg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(h = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `mld_prehash_valid h (LENGTH(ph:byte list))` THEN
    REWRITE_TAC[mld_prehash_valid] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mld_domain_separation_prefix_length;
                  mld_domain_separation_prefix; hash_mldsa_verify; APPEND;
                  GSYM NOT_LE] THEN
  REWRITE_TAC[LENGTH; LENGTH_APPEND; mld_prehash_oid] THEN ARITH_TAC);;

let MLD_FIPS204_VERIFY_PREHASH_VALID_SHAKE256 = prove
 (`mld_prehash_valid 12 64`,
  REWRITE_TAC[mld_prehash_valid; mld_prehash_length] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_FIPS204_VERIFY_PREHASH_OID_SHAKE256 = prove
 (`mld_prehash_oid 12 = mldsa_oid 12`,
  REWRITE_TAC[mld_prehash_oid; mldsa_oid] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The proofs. Each instantiates the CORRECT theorem with the byte strings   *)
(* (\j. EL j l for the signature and the public key, num_of_bytelist l for   *)
(* the others), weakens it with MLD_FIPS204_ENSURES_WEAKEN of fips204.ml,    *)
(* and turns the result of mld_verify_internal_ok into that of FIPS 204 with *)
(* MLD_FIPS204_VERIFY_INTERNAL_N (mu computed by the C code from the         *)
(* message, the prefix of ML-DSA or HashML-DSA being the message for the     *)
(* pre-hash functions) or MLD_FIPS204_VERIFY_N (external mu).                *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_VERIFY_PRE_TAC =
  REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `s:x86state` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THEN MATCH_MP_TAC MLD_FIPS204_VERIFY_EL_BYTES8 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

let MLD_FIPS204_VERIFY_TERMINATES_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && free_in `mld_matrix_terminates` (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC];;

let MLD_FIPS204_VERIFY_PREFIX_TAC htm phtm =
  MP_TAC(ISPECL [htm; `ctxl:byte list`; phtm]
                MLD_FIPS204_VERIFY_PREHASH_PREFIX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MLD_FIPS204_VERIFY_LENGTH_H;
                    MLD_FIPS204_VERIFY_PREHASH_VALID_SHAKE256] THEN
    SIMPLE_ARITH_TAC;
    ASM_REWRITE_TAC[MLD_FIPS204_VERIFY_LENGTH_H]] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2 th)] THEN
                       MP_TAC(CONJ (CONJUNCT1 th) (CONJUNCT1(CONJUNCT2 th))));;

let MLD_FIPS204_VERIFY_PREHASH_TAC int_th =
  W(fun (asl,w) ->
    let vtm = find_term (fun t ->
      try fst(dest_const(fst(strip_comb t))) = "mld_verify_mu" &&
          length(snd(strip_comb t)) = 6
      with Failure _ -> false) w in
    let ltm = el 4 (snd(strip_comb vtm)) and ptm = el 5 (snd(strip_comb vtm)) in
    MP_TAC(SPECL [`\j. EL j (sigl:byte list)`; `\j. EL j (pkl:byte list)`;
                  `0`; `0`; ltm; ptm] int_th)) THEN
  ASM_SIMP_TAC[MLD_FIPS204_VERIFY_BYTELIST_EQ; ARITH;
               MLD_FIPS204_VERIFY_LIST_OF_SEQ_EL; CONJUNCT1 bytelist_of_num;
               APPEND; BYTELIST_OF_NUM_OF_BYTELIST];;

let MLD_FIPS204_VERIFY_INTERNAL_API_TAC correct_th (int_th,mu_th) =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun cth ->
    let cth' = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
      `pk:int64`; `ext:int64`; `sigl:byte list`; `ml:byte list`;
      `prel:byte list`; `pkl:byte list`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
      `pk:int64`; `ext:int64`; `\j. EL j (sigl:byte list)`;
      `\j. EL j (pkl:byte list)`; `num_of_bytelist(ml:byte list)`;
      `num_of_bytelist(prel:byte list)`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] cth')) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_slice; ADD_CLAUSES]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  MLD_FIPS204_VERIFY_PRE_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `word_zx (ext:int64) = (word 0:int32)` THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`\j. EL j (sigl:byte list)`; `\j. EL j (pkl:byte list)`;
                  `prelen:num`; `num_of_bytelist(prel:byte list)`;
                  `mlen:num`; `num_of_bytelist(ml:byte list)`] int_th) THEN
    ASM_SIMP_TAC[MLD_FIPS204_VERIFY_BYTELIST_EQ;
                 MLD_FIPS204_VERIFY_LIST_OF_SEQ_EL];
    SUBGOAL_THEN `64 <= LENGTH(ml:byte list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`\j. EL j (sigl:byte list)`; `\j. EL j (pkl:byte list)`;
                  `num_of_bytelist(ml:byte list) MOD 2 EXP 512`] mu_th) THEN
    ASM_SIMP_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ;
                 MLD_FIPS204_VERIFY_EXTMU_BYTES;
                 MLD_FIPS204_VERIFY_LIST_OF_SEQ_EL]];;

let MLD_FIPS204_VERIFY_API_TAC correct_th int_th =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun cth ->
    let cth' = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
      `pk:int64`; `sigl:byte list`; `ml:byte list`; `ctxl:byte list`;
      `pkl:byte list`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
      `pk:int64`; `\j. EL j (sigl:byte list)`; `\j. EL j (pkl:byte list)`;
      `num_of_bytelist(ml:byte list)`; `num_of_bytelist(ctxl:byte list)`;
      `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
     cth')) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_slice; ADD_CLAUSES]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  MLD_FIPS204_VERIFY_PRE_TAC THEN
  REWRITE_TAC[mldsa_verify; mld_domain_separation_prefix;
              LENGTH_BYTELIST_OF_NUM] THEN
  ASM_SIMP_TAC[MLD_FIPS204_VERIFY_BYTELIST_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MLD_FIPS204_VERIFY_TERMINATES_TAC THEN
  MP_TAC(SPECL [`\j. EL j (sigl:byte list)`; `\j. EL j (pkl:byte list)`;
                `2 + ctxlen`;
                `num_of_bytelist(CONS (word 0) (CONS (word ctxlen)
                                  (ctxl:byte list)))`;
                `mlen:num`; `num_of_bytelist(ml:byte list)`] int_th) THEN
  ASM_SIMP_TAC[MLD_FIPS204_VERIFY_BYTELIST_EQ;
               MLD_FIPS204_VERIFY_LIST_OF_SEQ_EL; LENGTH;
               ARITH_RULE `SUC(SUC n) = 2 + n`];;

let MLD_FIPS204_VERIFY_EXTMU_API_TAC correct_th mu_th =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun cth ->
    let cth' = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `mu:int64`; `pk:int64`; `sigl:byte list`;
      `mul:byte list`; `pkl:byte list`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `mu:int64`; `pk:int64`; `\j. EL j (sigl:byte list)`;
      `\j. EL j (pkl:byte list)`; `num_of_bytelist(mul:byte list)`;
      `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
     cth')) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_slice; ADD_CLAUSES]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  MLD_FIPS204_VERIFY_PRE_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`\j. EL j (sigl:byte list)`; `\j. EL j (pkl:byte list)`;
                `num_of_bytelist(mul:byte list)`] mu_th) THEN
  MP_TAC(ISPECL [`mul:byte list`; `64`] MLD_FIPS204_VERIFY_BYTELIST_EQ) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 64 = 512`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_FIPS204_VERIFY_LIST_OF_SEQ_EL];;

let MLD_FIPS204_VERIFY_PRE_HASH_INTERNAL_API_TAC correct_th int_th =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun cth ->
    let cth' = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
      `pk:int64`; `hashalg:int64`; `sigl:byte list`; `phl:byte list`;
      `ctxl:byte list`; `pkl:byte list`; `HA:num`; `pc:num`;
      `stackpointer:int64`; `returnaddress:int64`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `HA:num`)) THEN
    MP_TAC(SPECL
     [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
      `pk:int64`; `hashalg:int64`; `\j. EL j (sigl:byte list)`;
      `\j. EL j (pkl:byte list)`; `num_of_bytelist(phl:byte list)`;
      `num_of_bytelist(ctxl:byte list)`; `val(word_zx(hashalg:int64):int32)`;
      `mld_domain_separation_prefix_length
        (val(word_zx(hashalg:int64):int32)) ctxlen phlen`;
      `num_of_bytelist(mld_domain_separation_prefix
        (val(word_zx(hashalg:int64):int32)) ctxl phl)`;
      `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
     cth')) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_slice; ADD_CLAUSES]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MLD_FIPS204_VERIFY_BYTELIST_EQ;
                 MLD_FIPS204_VERIFY_PREHASH_CHECK];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  MLD_FIPS204_VERIFY_PRE_TAC THEN
  REWRITE_TAC[MLD_FIPS204_VERIFY_PREHASH_CHECK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM; NOT_LT]) THEN
  MLD_FIPS204_VERIFY_TERMINATES_TAC THEN
  MLD_FIPS204_VERIFY_PREFIX_TAC
   `val(word_zx(hashalg:int64):int32)` `phl:byte list` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  MLD_FIPS204_VERIFY_PREHASH_TAC int_th;;

let MLD_FIPS204_VERIFY_PRE_HASH_SHAKE256_API_TAC correct_th int_th =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun cth ->
    let cth' = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
      `pk:int64`; `sigl:byte list`; `ml:byte list`; `ctxl:byte list`;
      `pkl:byte list`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL
     [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
      `pk:int64`; `\j. EL j (sigl:byte list)`; `\j. EL j (pkl:byte list)`;
      `num_of_bytelist(ml:byte list)`; `num_of_bytelist(ctxl:byte list)`;
      `num_of_bytelist(mldsa_h (ml:byte list) 64)`;
      `num_of_bytelist(mld_domain_separation_prefix 12 ctxl
                        (mldsa_h (ml:byte list) 64))`;
      `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
     cth')) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_slice; ADD_CLAUSES]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MLD_FIPS204_VERIFY_BYTELIST_EQ; MLD_FIPS204_SHAKE256_BYTE;
                 MLD_FIPS204_VERIFY_LENGTH_H] THEN
    ASM_SIMP_TAC[mldsa_h; MLD_FIPS204_VERIFY_BYTELIST_EQ;
                 MLD_FIPS204_SHAKE256_BYTE];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  MLD_FIPS204_VERIFY_PRE_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MLD_FIPS204_VERIFY_TERMINATES_TAC THEN
  REWRITE_TAC[GSYM MLD_FIPS204_VERIFY_PREHASH_OID_SHAKE256] THEN
  MLD_FIPS204_VERIFY_PREFIX_TAC `12` `mldsa_h (ml:byte list) 64` THEN
  DISCH_THEN(fun th ->
    REWRITE_TAC[GSYM(CONV_RULE NUM_REDUCE_CONV (CONJUNCT2 th))]) THEN
  MLD_FIPS204_VERIFY_PREHASH_TAC int_th;;

(* ------------------------------------------------------------------------- *)
(* ML-DSA-44: verification of the formatted message M' = pre || m or         *)
(* from external mu (verify_internal), of a message with a context           *)
(* (verify), from mu (verify_extmu), of a pre-hash with a context            *)
(* (verify_pre_hash_internal) and with the SHAKE256 pre-hash of a            *)
(* message (verify_pre_hash_shake256).                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig m mlen pre prelen pk ext sigl ml prel pkl pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 2420 /\ LENGTH ml = mlen /\ LENGTH prel = prelen /\
          LENGTH pkl = 1312 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(mldsa_slice 0 32 sigl)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 29997),29997))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,2420)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(pre,prelen)) s =
                    num_of_bytelist prel /\
                    read (memory :> bytes(pk,1312)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if (if word_zx ext = (word 0:int32)
                         then mldsa_verify_internal mldsa44 pkl
                               (APPEND prel ml) sigl
                         else mldsa_verify_mu mldsa44 pkl
                               (mldsa_slice 0 64 ml) sigl)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 29997),29997)])`,
  MLD_FIPS204_VERIFY_INTERNAL_API_TAC
   MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   (MLD_FIPS204_VERIFY_INTERNAL_44,MLD_FIPS204_VERIFY_44));;

let MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigl ml ctxl pkl pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 2420 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 1312 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(mldsa_slice 0 32 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 30468),30468))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,2420)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,1312)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (match mldsa_verify mldsa44 pkl ml sigl ctxl with
                       NONE -> word 4294967287
                     | SOME ok -> if ok then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30468),30468)])`,
  MLD_FIPS204_VERIFY_API_TAC
   MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_44);;

let MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig mu pk sigl mul pkl pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 2420 /\ LENGTH mul = 64 /\ LENGTH pkl = 1312 /\
          mld_matrix_terminates 4 4
           (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(mldsa_slice 0 32 sigl)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 30029),30029))
              [(sig,2420); (mu,64); (pk,1312); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,2420)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(mu,64)) s = num_of_bytelist mul /\
                    read (memory :> bytes(pk,1312)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mldsa_verify_mu mldsa44 pkl mul sigl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30029),30029)])`,
  MLD_FIPS204_VERIFY_EXTMU_API_TAC
   MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_44);;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen pk hashalg sigl phl ctxl pkl HA
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 2420 /\ LENGTH phl = phlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 1312 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          (mld_prehash_valid HA phlen /\ ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(mldsa_slice 0 32 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 30468),30468))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,2420)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(ph,phlen)) s = num_of_bytelist phl /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,1312)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if ~mld_prehash_valid HA phlen \/ 255 < ctxlen
                     then word 4294967287
                     else if hash_mldsa_verify mldsa44 pkl (mld_prehash_oid HA)
                              phl sigl ctxl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30468),30468)])`,
  MLD_FIPS204_VERIFY_PRE_HASH_INTERNAL_API_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_44);;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigl ml ctxl pkl pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 2420 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 1312 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(mldsa_slice 0 32 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 30651),30651))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,2420)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,1312)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if hash_mldsa_verify mldsa44 pkl (mldsa_oid 12)
                              (mldsa_h ml 64) sigl ctxl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30651),30651)])`,
  MLD_FIPS204_VERIFY_PRE_HASH_SHAKE256_API_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_44);;

(* ------------------------------------------------------------------------- *)
(* The same for ML-DSA-65.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig m mlen pre prelen pk ext sigl ml prel pkl pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 3309 /\ LENGTH ml = mlen /\ LENGTH prel = prelen /\
          LENGTH pkl = 1952 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(mldsa_slice 0 48 sigl)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45429),45429))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,3309)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(pre,prelen)) s =
                    num_of_bytelist prel /\
                    read (memory :> bytes(pk,1952)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if (if word_zx ext = (word 0:int32)
                         then mldsa_verify_internal mldsa65 pkl
                               (APPEND prel ml) sigl
                         else mldsa_verify_mu mldsa65 pkl
                               (mldsa_slice 0 64 ml) sigl)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45429),45429)])`,
  MLD_FIPS204_VERIFY_INTERNAL_API_TAC
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   (MLD_FIPS204_VERIFY_INTERNAL_65,MLD_FIPS204_VERIFY_65));;

let MLDSA_NATIVE_VERIFY_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigl ml ctxl pkl pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 3309 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 1952 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 49 48
                (num_of_bytelist(mldsa_slice 0 48 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45900),45900))
              [(sig,3309); (m,mlen); (ctx,ctxlen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_verify) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,3309)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,1952)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (match mldsa_verify mldsa65 pkl ml sigl ctxl with
                       NONE -> word 4294967287
                     | SOME ok -> if ok then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45900),45900)])`,
  MLD_FIPS204_VERIFY_API_TAC
   MLDSA_NATIVE_VERIFY_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_65);;

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig mu pk sigl mul pkl pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 3309 /\ LENGTH mul = 64 /\ LENGTH pkl = 1952 /\
          mld_matrix_terminates 6 5
           (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(mldsa_slice 0 48 sigl)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45461),45461))
              [(sig,3309); (mu,64); (pk,1952); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_verify_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,3309)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(mu,64)) s = num_of_bytelist mul /\
                    read (memory :> bytes(pk,1952)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mldsa_verify_mu mldsa65 pkl mul sigl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45461),45461)])`,
  MLD_FIPS204_VERIFY_EXTMU_API_TAC
   MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_65);;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen pk hashalg sigl phl ctxl pkl HA
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 3309 /\ LENGTH phl = phlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 1952 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          (mld_prehash_valid HA phlen /\ ctxlen <= 255
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 49 48
                (num_of_bytelist(mldsa_slice 0 48 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45900),45900))
              [(sig,3309); (ph,phlen); (ctx,ctxlen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_verify_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,3309)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(ph,phlen)) s = num_of_bytelist phl /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,1952)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if ~mld_prehash_valid HA phlen \/ 255 < ctxlen
                     then word 4294967287
                     else if hash_mldsa_verify mldsa65 pkl (mld_prehash_oid HA)
                              phl sigl ctxl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45900),45900)])`,
  MLD_FIPS204_VERIFY_PRE_HASH_INTERNAL_API_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_65);;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigl ml ctxl pkl pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 3309 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 1952 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 49 48
                (num_of_bytelist(mldsa_slice 0 48 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 46083),46083))
              [(sig,3309); (m,mlen); (ctx,ctxlen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,3309)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,1952)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if hash_mldsa_verify mldsa65 pkl (mldsa_oid 12)
                              (mldsa_h ml 64) sigl ctxl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 46083),46083)])`,
  MLD_FIPS204_VERIFY_PRE_HASH_SHAKE256_API_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_65);;

(* ------------------------------------------------------------------------- *)
(* The same for ML-DSA-87.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig m mlen pre prelen pk ext sigl ml prel pkl pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 4627 /\ LENGTH ml = mlen /\ LENGTH prel = prelen /\
          LENGTH pkl = 2592 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(mldsa_slice 0 64 sigl)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74349),74349))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,4627)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(pre,prelen)) s =
                    num_of_bytelist prel /\
                    read (memory :> bytes(pk,2592)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if (if word_zx ext = (word 0:int32)
                         then mldsa_verify_internal mldsa87 pkl
                               (APPEND prel ml) sigl
                         else mldsa_verify_mu mldsa87 pkl
                               (mldsa_slice 0 64 ml) sigl)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74349),74349)])`,
  MLD_FIPS204_VERIFY_INTERNAL_API_TAC
   MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   (MLD_FIPS204_VERIFY_INTERNAL_87,MLD_FIPS204_VERIFY_87));;

let MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigl ml ctxl pkl pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 4627 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 2592 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(mldsa_slice 0 64 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74820),74820))
              [(sig,4627); (m,mlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,4627)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,2592)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (match mldsa_verify mldsa87 pkl ml sigl ctxl with
                       NONE -> word 4294967287
                     | SOME ok -> if ok then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74820),74820)])`,
  MLD_FIPS204_VERIFY_API_TAC
   MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_87);;

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig mu pk sigl mul pkl pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 4627 /\ LENGTH mul = 64 /\ LENGTH pkl = 2592 /\
          mld_matrix_terminates 8 7
           (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(mldsa_slice 0 64 sigl)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74381),74381))
              [(sig,4627); (mu,64); (pk,2592); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,4627)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(mu,64)) s = num_of_bytelist mul /\
                    read (memory :> bytes(pk,2592)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mldsa_verify_mu mldsa87 pkl mul sigl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74381),74381)])`,
  MLD_FIPS204_VERIFY_EXTMU_API_TAC
   MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_87);;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen pk hashalg sigl phl ctxl pkl HA
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 4627 /\ LENGTH phl = phlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 2592 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          (mld_prehash_valid HA phlen /\ ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(mldsa_slice 0 64 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74820),74820))
              [(sig,4627); (ph,phlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,4627)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(ph,phlen)) s = num_of_bytelist phl /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,2592)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if ~mld_prehash_valid HA phlen \/ 255 < ctxlen
                     then word 4294967287
                     else if hash_mldsa_verify mldsa87 pkl (mld_prehash_oid HA)
                              phl sigl ctxl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74820),74820)])`,
  MLD_FIPS204_VERIFY_PRE_HASH_INTERNAL_API_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_87);;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 =
 prove
 (`!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigl ml ctxl pkl pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          LENGTH sigl = 4627 /\ LENGTH ml = mlen /\ LENGTH ctxl = ctxlen /\
          LENGTH pkl = 2592 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(mldsa_slice 0 32 pkl)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(mldsa_slice 0 64 sigl))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 75003),75003))
              [(sig,4627); (m,mlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sig,4627)) s = num_of_bytelist sigl /\
                    read (memory :> bytes(m,mlen)) s = num_of_bytelist ml /\
                    read (memory :> bytes(ctx,ctxlen)) s =
                    num_of_bytelist ctxl /\
                    read (memory :> bytes(pk,2592)) s = num_of_bytelist pkl)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if hash_mldsa_verify mldsa87 pkl (mldsa_oid 12)
                              (mldsa_h ml 64) sigl ctxl
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 75003),75003)])`,
  MLD_FIPS204_VERIFY_PRE_HASH_SHAKE256_API_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_VERIFY_INTERNAL_87);;
