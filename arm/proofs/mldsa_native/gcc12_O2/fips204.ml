(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The API functions of mldsa-native in the gcc 12 -O2 image, stated with    *)
(* the FIPS 204 specification of ML-DSA in common/fips204.ml: for each API   *)
(* function and parameter set, the theorem ..._FIPS204 is its CORRECT        *)
(* theorem with the inputs and outputs as byte strings and the results       *)
(* those of the FIPS 204 functions, derived from the CORRECT theorem and the *)
(* lemmas of utils/mldsa_native_fips204_*.ml relating the specification of   *)
(* the C code (common/mldsa_native_*.ml) to FIPS 204.                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_fips204_pk_from_sk.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keypair_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keypair_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keypair_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keypair_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keypair_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keypair_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pk_from_sk_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pk_from_sk_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pk_from_sk_87_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Weakening the pre- and postconditions of a CORRECT theorem, and           *)
(* byte strings of zeros.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_ENSURES_WEAKEN = prove
 (`!(step:A->A->bool) P Q C.
        ensures step P Q C
        ==> !P' Q'. (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s)
                    ==> ensures step P' Q' C`,
  MESON_TAC[ENSURES_PRECONDITION_THM; ENSURES_POSTCONDITION_THM]);;

let MLD_FIPS204_SEED_TAC xi =
  MP_TAC(ISPEC xi NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];;

let MLD_FIPS204_KEYPAIR_INTERNAL_TAC correct_th bridge_th =
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP correct_th) THEN
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `seed:int64`; `xi:byte list`; `guard:int64`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`pk:int64`; `sk:int64`; `seed:int64`; `num_of_bytelist(xi:byte list)`;
    `guard:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  REWRITE_TAC[] THEN X_GEN_TAC `s:armstate` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `num_of_bytelist(xi:byte list)` bridge_th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MLD_FIPS204_SEED_TAC `xi:byte list`; ALL_TAC] THEN
  MP_TAC(ISPEC `xi:byte list` BYTELIST_OF_NUM_OF_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN
  CONJ_TAC THEN MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN ASM_REWRITE_TAC[];;

let MLD_FIPS204_NUM_OF_BYTELIST_ZERO = prove
 (`!n. num_of_bytelist(list_of_seq (\j. word 0:byte) n) = 0`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; num_of_bytelist; NUM_OF_BYTELIST_APPEND;
                  VAL_WORD_0] THEN
  ARITH_TAC);;

let MLD_FIPS204_KEYPAIR_API_TAC correct_th bridge_th =
  REPEAT GEN_TAC THEN DISCH_THEN(fun cth ->
    let th = MATCH_MP correct_th cth in
    REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC(SPEC_ALL th)) THEN
  SUBGOAL_THEN
   `!SEED. SEED < 2 EXP 256 ==> num_of_bytelist(bytelist_of_num 32 SEED) = SEED`
  ASSUME_TAC THENL
   [REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOD_LT THEN POP_ASSUM MP_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `SEED:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `bytelist_of_num 32 SEED` o
      check (fun th -> is_forall(concl th) &&
                       free_in `mld_matrix_terminates` (concl th))) THEN
    ASM_SIMP_TAC[LENGTH_BYTELIST_OF_NUM];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  REWRITE_TAC[] THEN X_GEN_TAC `s:armstate` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `SEED:num` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `bytelist_of_num 32 SEED` THEN
  ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; mldsa_keygen] THEN
  MP_TAC(SPEC `SEED:num` bridge_th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `bytelist_of_num 32 SEED` o
      check (fun th -> is_forall(concl th) &&
                       free_in `mld_matrix_terminates` (concl th))) THEN
    ASM_SIMP_TAC[LENGTH_BYTELIST_OF_NUM];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN ASM_REWRITE_TAC[];;

let MLD_FIPS204_PK_FROM_SK_API_TAC correct_th bridge_th =
  REPEAT GEN_TAC THEN DISCH_THEN(fun cth ->
    let th = MATCH_MP correct_th cth in
    MAP_EVERY X_GEN_TAC
     [`pk:int64`; `sk:int64`; `skl:byte list`; `guard:int64`; `pc:num`;
      `stackpointer:int64`; `returnaddress:int64`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL
     [`pk:int64`; `sk:int64`; `\j. EL j (skl:byte list)`; `guard:int64`;
      `pc:num`; `stackpointer:int64`; `returnaddress:int64`] th)) THEN
  SUBGOAL_THEN `list_of_seq (\j. EL j (skl:byte list)) 32 =
                mldsa_slice 0 32 skl`
  ASSUME_TAC THENL [REWRITE_TAC[mldsa_slice; ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && lhand(concl th) = `LENGTH(skl:byte list)`
    then ASSUME_TAC(REWRITE_RULE[th] (ISPEC `skl:byte list`
                                      LIST_OF_SEQ_EQ_SELF))
    else NO_TAC) THEN
  ASM_REWRITE_TAC[mld_sk_rho] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP MLD_FIPS204_ENSURES_WEAKEN) THEN
  REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `s:armstate` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC BYTES8_OF_BYTES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `\j. EL j (skl:byte list)` bridge_th) THEN
  ASM_REWRITE_TAC[mld_sk_rho] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP READ_BYTES_OF_BYTES8 o
    check (fun th -> is_forall(concl th) &&
                     free_in `bytes8` (concl th))) THEN
  ASM_REWRITE_TAC[ETA_AX; MLD_FIPS204_NUM_OF_BYTELIST_ZERO];;

(* ------------------------------------------------------------------------- *)
(* Key generation from a seed (ML-DSA.KeyGen_internal) and with a random     *)
(* seed (ML-DSA.KeyGen), and the public key of a secret key.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed xi guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH xi = 32 /\
          mld_matrix_terminates 4 4
           (mld_keypair_rho 4 4 (num_of_bytelist xi)) /\
          mld_keypair_terminates_44 (num_of_bytelist xi) /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28096),28096)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28096),28096)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = num_of_bytelist xi)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    read (memory :> bytes(pk,1312)) s =
                    num_of_bytelist(FST(mldsa_keygen_internal mldsa44 xi)) /\
                    read (memory :> bytes(sk,2560)) s =
                    num_of_bytelist(SND(mldsa_keygen_internal mldsa44 xi)))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 28096),28096)])`,
  MLD_FIPS204_KEYPAIR_INTERNAL_TAC
   MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_KEYPAIR_44);;

let MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          (!xi. LENGTH xi = 32
                ==> mld_matrix_terminates 4 4
                     (mld_keypair_rho 4 4 (num_of_bytelist xi)) /\
                    mld_keypair_terminates_44 (num_of_bytelist xi)) /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560); (word_sub stackpointer (word 28192),28192)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560); (word_sub stackpointer (word 28192),28192)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev)
               (\s. read PC s = returnaddress /\
                    ?xi. LENGTH xi = 32 /\
                         (C_RETURN s = word 0 \/
                          C_RETURN s = word 4294967293) /\
                         (C_RETURN s = word 0
                          ==> read (memory :> bytes(pk,1312)) s =
                              num_of_bytelist(FST(mldsa_keygen mldsa44 xi)) /\
                              read (memory :> bytes(sk,2560)) s =
                              num_of_bytelist(SND(mldsa_keygen mldsa44 xi))))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 28192),28192)])`,
  MLD_FIPS204_KEYPAIR_API_TAC
   MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_KEYPAIR_44);;

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk skl guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH skl = 2560 /\
          mld_matrix_terminates 4 4
           (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          nonoverlapping (pk,1312) (word_sub stackpointer (word 30736),30736) /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (word_sub stackpointer (word 30736),30736)]
           [(sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sk,2560)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    let rho = mldsa_slice 0 32 skl
                    and s1b = mldsa_slice 128 384 skl
                    and s2b = mldsa_slice 512 384 skl
                    and t0b = mldsa_slice 896 1664 skl in
                    let s1 = \i. mldsa_poly(\j. &2 - mldsa_field 3 s1b
                                                     (256 * i + j))
                    and s2 = \i. mldsa_poly(\j. &2 - mldsa_field 3 s2b
                                                     (256 * i + j)) in
                    let t = \i. ring_add mldsa_rq
                                 (mldsa_dot 4 (mldsa_expand_a rho i) s1)
                                 (s2 i) in
                    let pk' = APPEND rho
                               (mldsa_encode 10 1024
                                 (\n. FST(mldsa_power2round
                                           (coeff (n MOD 256)
                                             (t(n DIV 256)))))) in
                    let ok =
                      ((!n. n < 1024 ==> mldsa_field 3 s1b n <= &4) /\
                       (!n. n < 1024 ==> mldsa_field 3 s2b n <= &4) /\
                       t0b = mldsa_encode 13 1024
                              (\n. &4096 - SND(mldsa_power2round
                                                (coeff (n MOD 256)
                                                  (t(n DIV 256))))) /\
                       mldsa_slice 64 64 skl = mldsa_h pk' 64) in
                    C_RETURN s = (if ok then word 0 else word 4294967289) /\
                    read (memory :> bytes(pk,1312)) s =
                    (if ok then num_of_bytelist pk' else 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312);
                  memory :> bytes(word_sub stackpointer (word 30736),30736)])`,
  MLD_FIPS204_PK_FROM_SK_API_TAC
   MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_PK_FROM_SK_44);;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed xi guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH xi = 32 /\
          mld_matrix_terminates 6 5
           (mld_keypair_rho 6 5 (num_of_bytelist xi)) /\
          mld_keypair_terminates_65 (num_of_bytelist xi) /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43440),43440)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43440),43440)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = num_of_bytelist xi)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    read (memory :> bytes(pk,1952)) s =
                    num_of_bytelist(FST(mldsa_keygen_internal mldsa65 xi)) /\
                    read (memory :> bytes(sk,4032)) s =
                    num_of_bytelist(SND(mldsa_keygen_internal mldsa65 xi)))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43440),43440)])`,
  MLD_FIPS204_KEYPAIR_INTERNAL_TAC
   MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_KEYPAIR_65);;

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          (!xi. LENGTH xi = 32
                ==> mld_matrix_terminates 6 5
                     (mld_keypair_rho 6 5 (num_of_bytelist xi)) /\
                    mld_keypair_terminates_65 (num_of_bytelist xi)) /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032); (word_sub stackpointer (word 43536),43536)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032); (word_sub stackpointer (word 43536),43536)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev)
               (\s. read PC s = returnaddress /\
                    ?xi. LENGTH xi = 32 /\
                         (C_RETURN s = word 0 \/
                          C_RETURN s = word 4294967293) /\
                         (C_RETURN s = word 0
                          ==> read (memory :> bytes(pk,1952)) s =
                              num_of_bytelist(FST(mldsa_keygen mldsa65 xi)) /\
                              read (memory :> bytes(sk,4032)) s =
                              num_of_bytelist(SND(mldsa_keygen mldsa65 xi))))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43536),43536)])`,
  MLD_FIPS204_KEYPAIR_API_TAC
   MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_KEYPAIR_65);;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk skl guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH skl = 4032 /\
          mld_matrix_terminates 6 5
           (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 46912),46912) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 46912),46912)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sk,4032)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    let rho = mldsa_slice 0 32 skl
                    and s1b = mldsa_slice 128 640 skl
                    and s2b = mldsa_slice 768 768 skl
                    and t0b = mldsa_slice 1536 2496 skl in
                    let s1 = \i. mldsa_poly(\j. &4 - mldsa_field 4 s1b
                                                     (256 * i + j))
                    and s2 = \i. mldsa_poly(\j. &4 - mldsa_field 4 s2b
                                                     (256 * i + j)) in
                    let t = \i. ring_add mldsa_rq
                                 (mldsa_dot 5 (mldsa_expand_a rho i) s1)
                                 (s2 i) in
                    let pk' = APPEND rho
                               (mldsa_encode 10 1536
                                 (\n. FST(mldsa_power2round
                                           (coeff (n MOD 256)
                                             (t(n DIV 256)))))) in
                    let ok =
                      ((!n. n < 1280 ==> mldsa_field 4 s1b n <= &8) /\
                       (!n. n < 1536 ==> mldsa_field 4 s2b n <= &8) /\
                       t0b = mldsa_encode 13 1536
                              (\n. &4096 - SND(mldsa_power2round
                                                (coeff (n MOD 256)
                                                  (t(n DIV 256))))) /\
                       mldsa_slice 64 64 skl = mldsa_h pk' 64) in
                    C_RETURN s = (if ok then word 0 else word 4294967289) /\
                    read (memory :> bytes(pk,1952)) s =
                    (if ok then num_of_bytelist pk' else 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 46912),46912)])`,
  MLD_FIPS204_PK_FROM_SK_API_TAC
   MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_PK_FROM_SK_65);;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed xi guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH xi = 32 /\
          mld_matrix_terminates 8 7
           (mld_keypair_rho 8 7 (num_of_bytelist xi)) /\
          mld_keypair_terminates_87 (num_of_bytelist xi) /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72144),72144)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72144),72144)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = num_of_bytelist xi)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    read (memory :> bytes(pk,2592)) s =
                    num_of_bytelist(FST(mldsa_keygen_internal mldsa87 xi)) /\
                    read (memory :> bytes(sk,4896)) s =
                    num_of_bytelist(SND(mldsa_keygen_internal mldsa87 xi)))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72144),72144)])`,
  MLD_FIPS204_KEYPAIR_INTERNAL_TAC
   MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_KEYPAIR_87);;

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          (!xi. LENGTH xi = 32
                ==> mld_matrix_terminates 8 7
                     (mld_keypair_rho 8 7 (num_of_bytelist xi)) /\
                    mld_keypair_terminates_87 (num_of_bytelist xi)) /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896); (word_sub stackpointer (word 72240),72240)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896); (word_sub stackpointer (word 72240),72240)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev)
               (\s. read PC s = returnaddress /\
                    ?xi. LENGTH xi = 32 /\
                         (C_RETURN s = word 0 \/
                          C_RETURN s = word 4294967293) /\
                         (C_RETURN s = word 0
                          ==> read (memory :> bytes(pk,2592)) s =
                              num_of_bytelist(FST(mldsa_keygen mldsa87 xi)) /\
                              read (memory :> bytes(sk,4896)) s =
                              num_of_bytelist(SND(mldsa_keygen mldsa87 xi))))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72240),72240)])`,
  MLD_FIPS204_KEYPAIR_API_TAC
   MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_KEYPAIR_87);;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FIPS204 = prove
 (`!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk skl guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH skl = 4896 /\
          mld_matrix_terminates 8 7
           (num_of_bytelist(mldsa_slice 0 32 skl)) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 76416),76416) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 76416),76416)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sk,4896)) s = num_of_bytelist skl)
               (\s. read PC s = returnaddress /\
                    let rho = mldsa_slice 0 32 skl
                    and s1b = mldsa_slice 128 672 skl
                    and s2b = mldsa_slice 800 768 skl
                    and t0b = mldsa_slice 1568 3328 skl in
                    let s1 = \i. mldsa_poly(\j. &2 - mldsa_field 3 s1b
                                                     (256 * i + j))
                    and s2 = \i. mldsa_poly(\j. &2 - mldsa_field 3 s2b
                                                     (256 * i + j)) in
                    let t = \i. ring_add mldsa_rq
                                 (mldsa_dot 7 (mldsa_expand_a rho i) s1)
                                 (s2 i) in
                    let pk' = APPEND rho
                               (mldsa_encode 10 2048
                                 (\n. FST(mldsa_power2round
                                           (coeff (n MOD 256)
                                             (t(n DIV 256)))))) in
                    let ok =
                      ((!n. n < 1792 ==> mldsa_field 3 s1b n <= &4) /\
                       (!n. n < 2048 ==> mldsa_field 3 s2b n <= &4) /\
                       t0b = mldsa_encode 13 2048
                              (\n. &4096 - SND(mldsa_power2round
                                                (coeff (n MOD 256)
                                                  (t(n DIV 256))))) /\
                       mldsa_slice 64 64 skl = mldsa_h pk' 64) in
                    C_RETURN s = (if ok then word 0 else word 4294967289) /\
                    read (memory :> bytes(pk,2592)) s =
                    (if ok then num_of_bytelist pk' else 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 76416),76416)])`,
  MLD_FIPS204_PK_FROM_SK_API_TAC
   MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   MLD_FIPS204_PK_FROM_SK_87);;
