(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with the secret key, all the attempts (ML-DSA-87): the proof (see *)
(* signature_internal_87_spec.ml).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/signature_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/unpack_sk_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/H_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_uniform_gamma1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_yvec_eager_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_caddq_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_decompose_pack_w1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_challenge_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_add_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pack_sig_z_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pack_sig_c_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pack_sig_h_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;

let SIGN87_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The proof is in parts, each a FULL lemma for a segment of the code (sp is *)
(* the stack pointer in the loop, sp0 = sp - 4528 the bottom of the frames   *)
(* of the callees, and B the base of the buffers, 32-byte aligned). The loop *)
(* over z up to an index m (ZPRE), the exit at a z whose norm check fails    *)
(* (ZFAIL), the loop over the rows of w0 up to a row m (RPRE), the exits at  *)
(* a row whose first or second check fails (RFAIL1, RFAIL2), the packing of  *)
(* c~ and the hints (TAIL), the cleanup and the decision (CLEAN), and the    *)
(* start of an attempt up to the NTT of the challenge (HEAD). The attempt    *)
(* (ATT) follows from them, with one path for each kind of result r of       *)
(* mld_sign_attempt_declass: r < 7 (z_r fails), 7 <= r < 23 (the check r - 7 *)
(* of the rows fails), 23 (too many hints) and 24 (success).                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check.                                                               *)
(* ------------------------------------------------------------------------- *)

let SIGN87_ZPRE_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_zpre.
        !e m sig B sp s1h cphat y pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ m <= 7 /\
          (!i. i < m
               ==> mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524168) =
                   word 0) /\
          PAIRWISE nonoverlapping [(sig,4627); (B,106816); (sp,160)] /\
          ALLPAIRS nonoverlapping [(sig,4627); (B,106816)]
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa87_signature_internal_loop2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 81920) /\
                    read X20 s = word_add B (word 103424) /\
                    read X23 s = word_add B (word 104448) /\
                    read X21 s = word 0 /\
                    read X24 s = word_add B (word 89088) /\
                    read X28 s = word_add B (word 96256) /\
                    read (memory :> bytes64 (word_add sp (word 96))) s = sig /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(104448 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1792
                         ==> read (memory :> bytes32
                                    (word_add B (word(89088 + 4 * j)))) s =
                             y j) /\
                    (!j. j < 1792
                         ==> read (memory :> bytes32
                                    (word_add B (word(96256 + 4 * j)))) s =
                             s1h j) /\
                    read events s = e)
               (\s. read PC s =
                    (if m < 7
                     then word(pc + mldsa87_signature_internal_loop2)
                     else word(pc + mldsa87_signature_internal_loop2_exit1)) /\
                    read X21 s = word m /\
                    read X24 s = word_add B (word(89088 + 1024 * m)) /\
                    read X28 s = word_add B (word(96256 + 1024 * m)) /\
                    (!t. t < 640 * m
                         ==> read (memory :> bytes8
                                    (word_add sig (word(64 + t)))) s =
                             mld_polyvec_pack 640 mld_polyz_pack_19
                              (mld_polyvec (mld_sign_z s1h cphat y)) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_zpre m sig B sp mc pc /\
                       memaccess_inbounds e2
                        [sig,4627; B,106816; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,4627; B,106816]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X21; X24; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 81920),1024);
                  memory :> bytes(word_add B (word 103424),1024);
                  memory :> bytes(word_add sig (word 64),4480)])`;;

let SIGN87_ZALLOWED =
  [`pc:num`; `sig:int64`; `B:int64`; `sp:int64`; `mc:int64`; `i:num`];;

let SIGN87_ZCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN87_EXEC name ilist
    SIGN87_ZALLOWED n;;

let SIGN87_COPY_TAC doff soff f n zs s =
  MP_TAC(SPECL [`B:int64`; doff; soff; `i:num`; n; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 7` THEN ARITH_TAC;
    DISCH_TAC];;

let SIGN87_ZPRE_INV =
 `\i s. read SP s = sp /\
        read X19 s = word_add B (word 81920) /\
        read X20 s = word_add B (word 103424) /\
        read X23 s = word_add B (word 104448) /\
        read X21 s = word i /\
        read X24 s = word_add B (word(89088 + 1024 * i)) /\
        read X28 s = word_add B (word(96256 + 1024 * i)) /\
        read (memory :> bytes64 (word_add sp (word 96))) s = sig /\
        read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
        mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add B (word(104448 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 1792
             ==> read (memory :> bytes32 (word_add B (word(89088 + 4 * j))))
                   s = y j) /\
        (!j. j < 1792
             ==> read (memory :> bytes32 (word_add B (word(96256 + 4 * j))))
                   s = s1h j) /\
        (!t. t < 640 * i
             ==> read (memory :> bytes8 (word_add sig (word(64 + t)))) s =
                 mld_polyvec_pack 640 mld_polyz_pack_19
                  (mld_polyvec (mld_sign_z s1h cphat y)) t)`;;

let SIGN87_ZBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(96256 + 1024 * i)),
                                         1024)) s4` THEN
  LIBC_PLT_TAC SIGN87_EXEC 4 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN87_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN87_ZALLOWED) 9 THEN
  SIGN87_COPY_TAC `103424` `96256` `s1h:num->int32` `1792` `zs:num`
    `s9:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (10--12) THEN
  SIGN87_ZCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s1h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC SIGN87_EXEC (14--15) THEN
  SIGN87_ZCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat`;
    `pc:num`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC SIGN87_EXEC (17--20) THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(89088 + 1024 * i)),
                                          1024)) s20` THEN
  LIBC_PLT_TAC SIGN87_EXEC 20 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN87_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN87_ZALLOWED) 25 THEN
  SIGN87_COPY_TAC `81920` `89088` `y:num->int32` `1792` `zs':num`
    `s25:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (26--28) THEN
  SIGN87_ZCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat)`;
    `mld_poly_of y i`; `pc:num`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC SIGN87_EXEC (30--31) THEN
  SIGN87_ZCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_add
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat))
      (mld_poly_of y i)`;
    `pc:num`; `read X30 s`] 32 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (33--36) THEN
  SIGN87_ZCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_z s1h cphat y i`; `read X1 s`;
    `pc:num`; `read X30 s`] 37 THEN
  SUBGOAL_THEN
   `mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524168) = word 0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524168) = word 0`]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (38--45) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i /\
    word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
    word(i + 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 7` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i < 7` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 7` THEN ARITH_TAC; ALL_TAC] THEN
  SIGN87_ZCALL_TAC "H_PZ"
   [`read X0 s`; `read X1 s`; `mld_sign_z s1h cphat y i`; `i:num`;
    `pc:num`; `read X30 s`] 46 THEN
  ARM_STEPS_TAC SIGN87_EXEC (47--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_19`; `640`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_19_LOCAL] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN87_ZPRE = prove
 (SIGN87_ZPRE_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CHK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PZ" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sig:int64) (B:int64) (sp:int64) (mc:int64) (pc:num).
     APPEND (f_ev_back m sig B sp mc pc)
      (APPEND (ENUMERATEL m (\i. f_ev_zit sig B sp mc pc i))
              (f_ev_front m sig B sp mc pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:num`; `sig:int64`; `B:int64`; `sp:int64`;
    `s1h:num->int32`; `cphat:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa87_signature_internal_loop2`
     `if m < 7 then pc + mldsa87_signature_internal_loop2
      else pc + mldsa87_signature_internal_loop2_exit1`
     SIGN87_ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN87_ZBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SIGN_BETA_ALL_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    SIGN_BETA_ALL_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT;
                    ENUMERATEL; APPEND] THEN
    SIGN_NIL_EVENTS_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exit from the loop over z at a polynomial whose norm check fails, to  *)
(* the cleanup (join2) with x21 = -1.                                        *)
(* ------------------------------------------------------------------------- *)

let SIGN87_ZFAIL_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_zfail.
        !e i sig B sp s1h cphat y pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ i < 7 /\
          ~(mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524168) =
            word 0) /\
          PAIRWISE nonoverlapping [(sig,4627); (B,106816); (sp,160)] /\
          ALLPAIRS nonoverlapping [(sig,4627); (B,106816)]
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa87_signature_internal_loop2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 81920) /\
                    read X20 s = word_add B (word 103424) /\
                    read X23 s = word_add B (word 104448) /\
                    read X21 s = word i /\
                    read X24 s = word_add B (word(89088 + 1024 * i)) /\
                    read X28 s = word_add B (word(96256 + 1024 * i)) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(104448 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1792
                         ==> read (memory :> bytes32
                                    (word_add B (word(89088 + 4 * j)))) s =
                             y j) /\
                    (!j. j < 1792
                         ==> read (memory :> bytes32
                                    (word_add B (word(96256 + 4 * j)))) s =
                             s1h j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa87_signature_internal_join2) /\
                    read X21 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_zfail i sig B sp mc pc /\
                       memaccess_inbounds e2
                        [sig,4627; B,106816; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,4627; B,106816]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X21; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 81920),1024);
                  memory :> bytes(word_add B (word 103424),1024)])`;;

let SIGN87_ZFAIL_ALLOWED =
  [`pc:num`; `sig:int64`; `B:int64`; `sp:int64`; `mc:int64`; `i:num`];;

let SIGN87_ZFCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN87_EXEC name ilist
    SIGN87_ZFAIL_ALLOWED n;;

let SIGN87_ZFCOPY_TAC doff soff f n zs s =
  MP_TAC(SPECL [`B:int64`; doff; soff; `i:num`; n; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 7` THEN ARITH_TAC; DISCH_TAC];;

let SIGN87_ZFAIL = prove
 (SIGN87_ZFAIL_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CHK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(i:num) (sig:int64) (B:int64) (sp:int64) (mc:int64) (pc:num).
     f_ev_zfail i sig B sp mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `i:num`; `sig:int64`; `B:int64`; `sp:int64`;
    `s1h:num->int32`; `cphat:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(96256 + 1024 * i)),
                                         1024)) s4` THEN
  LIBC_PLT_TAC SIGN87_EXEC 4 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN87_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN87_ZFAIL_ALLOWED) 9 THEN
  SIGN87_ZFCOPY_TAC `103424` `96256` `s1h:num->int32` `1792` `zs:num`
    `s9:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (10--12) THEN
  SIGN87_ZFCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s1h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC SIGN87_EXEC (14--15) THEN
  SIGN87_ZFCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat`;
    `pc:num`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC SIGN87_EXEC (17--20) THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(89088 + 1024 * i)),
                                          1024)) s20` THEN
  LIBC_PLT_TAC SIGN87_EXEC 20 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN87_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN87_ZFAIL_ALLOWED) 25 THEN
  SIGN87_ZFCOPY_TAC `81920` `89088` `y:num->int32` `1792` `zs':num`
    `s25:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (26--28) THEN
  SIGN87_ZFCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat)`;
    `mld_poly_of y i`; `pc:num`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC SIGN87_EXEC (30--31) THEN
  SIGN87_ZFCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_add
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat))
      (mld_poly_of y i)`;
    `pc:num`; `read X30 s`] 32 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (33--36) THEN
  SIGN87_ZFCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_z s1h cphat y i`; `read X1 s`;
    `pc:num`; `read X30 s`] 37 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  ARM_STEPS_TAC SIGN87_EXEC [38] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524168) =
      word 0)`]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (39--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass, leaving the rows of x of the hints.                                 *)
(* ------------------------------------------------------------------------- *)

let SIGN87_RPRE_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rpre.
        !e m B sp w s2h t0h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ m <= 8 /\
          (!j. j < m
               ==> mld_poly_chknorm
                    (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat j)
                    (word 261768) = word 0 /\
                   mld_poly_chknorm (mld_sign_ct0 t0h cphat j) (word 261888) =
                   word 0) /\
          nonoverlapping (B,106816) (sp,160) /\
          ALL (nonoverlapping (B,106816))
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa87_signature_internal_loop2_exit1) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 81920) /\
                    read X23 s = word_add B (word 104448) /\
                    read X26 s = word_add B (word 57344) /\
                    read (memory :> bytes64 (word_add sp (word 104))) s =
                    word_add B (word 73728) /\
                    read (memory :> bytes64 (word_add sp (word 152))) s =
                    word_add B (word 65536) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(104448 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(73728 + 4 * j)))) s =
                             t0h j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(57344 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                    read events s = e)
               (\s. read PC s =
                    (if m < 8
                     then word(pc + mldsa87_signature_internal_loop3)
                     else word(pc + mldsa87_signature_internal_loop3_exit1)) /\
                    read X21 s = word_add B (word(57344 + 1024 * m)) /\
                    read X24 s = word_add B (word(65536 + 1024 * m)) /\
                    read X28 s = word_add B (word(73728 + 1024 * m)) /\
                    (!j. j < 256 * m
                         ==> read (memory :> bytes32
                                    (word_add B (word(57344 + 4 * j)))) s =
                             mld_sign_hint_x 8 mld_poly_decompose_lo_32 w s2h
                              t0h cphat j) /\
                    (!j. 256 * m <= j /\ j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(57344 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rpre m B sp mc pc /\
                       memaccess_inbounds e2
                        [B,106816; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [B,106816]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X21; X24; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 81920),1024);
                  memory :> bytes(word_add B (word 57344),8192)])`;;

let SIGN87_RALLOWED =
  [`pc:num`; `B:int64`; `sp:int64`; `mc:int64`; `i:num`];;

let SIGN87_RCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN87_EXEC name ilist
    SIGN87_RALLOWED n;;

let SIGN87_RCOPY_TAC soff f zs s =
  MP_TAC(SPECL [`B:int64`; `81920`; soff; `i:num`; `2048`; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 8` THEN ARITH_TAC;
    DISCH_TAC];;

let SIGN87_RPRE_INV =
 `\i s. read SP s = sp /\
        read X19 s = word_add B (word 81920) /\
        read X23 s = word_add B (word 104448) /\
        read X21 s = word_add B (word(57344 + 1024 * i)) /\
        read X24 s = word_add B (word(65536 + 1024 * i)) /\
        read X28 s = word_add B (word(73728 + 1024 * i)) /\
        read (memory :> bytes64 (word_add sp (word 104))) s =
        word_add B (word 73728) /\
        read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
        mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add B (word(104448 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 2048
             ==> read (memory :> bytes32 (word_add B (word(65536 + 4 * j))))
                   s = s2h j) /\
        (!j. j < 2048
             ==> read (memory :> bytes32 (word_add B (word(73728 + 4 * j))))
                   s = t0h j) /\
        (!j. j < 256 * i
             ==> read (memory :> bytes32 (word_add B (word(57344 + 4 * j))))
                   s =
                 mld_sign_hint_x 8 mld_poly_decompose_lo_32 w s2h t0h cphat
                  j) /\
        (!j. 256 * i <= j /\ j < 2048
             ==> read (memory :> bytes32 (word_add B (word(57344 + 4 * j))))
                   s = mld_polyvec_map mld_poly_decompose_lo_32 w j)`;;

let SIGN87_RTEST = prove
 (`!j. (65536 + 1024 * j) + 1024 = 73728 <=> j + 1 = 8`,
  ARITH_TAC);;

let SIGN87_RFSLICE_TAC s =
  MP_TAC(SPECL [`B:int64`; `57344`; `2048`; `mld_poly_decompose_lo_32`;
                `w:num->int32`; `i:num`; s] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; s]
             `!j. 256 * i <= j /\ j < 2048
                  ==> read (memory :> bytes32
                             (word_add B (word (57344 + 4 * j))))
                        s = Q j`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 8` THEN ARITH_TAC; STRIP_TAC];;

let SIGN87_RFCOPY_TAC soff f zs s =
  MP_TAC(SPECL [`B:int64`; `81920`; soff; `i:num`; `2048`; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 8` THEN ARITH_TAC; DISCH_TAC];;

let SIGN87_RBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 8` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 8` THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(65536 + 1024 * i)),
                                         1024)) s4` THEN
  LIBC_PLT_TAC SIGN87_EXEC 4 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN87_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN87_RALLOWED) 9 THEN
  SIGN87_RFCOPY_TAC `65536` `s2h:num->int32` `zs:num` `s9:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (10--12) THEN
  SIGN87_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s2h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC SIGN87_EXEC (14--15) THEN
  SIGN87_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat`;
    `pc:num`; `read X30 s`] 16 THEN
  SIGN87_RFSLICE_TAC `s16:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (17--19) THEN
  SIGN87_RCALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`;
    `mld_poly_decompose_lo_32 (mld_poly_of w i)`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat)`;
    `pc:num`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC SIGN87_EXEC (21--22) THEN
  SIGN87_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_sub (mld_poly_decompose_lo_32 (mld_poly_of w i))
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat))`;
    `pc:num`; `read X30 s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (24--27) THEN
  SIGN87_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 28 THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
      (word 261768) = word 0`]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (29--33) THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(73728 + 1024 * i)),
                                          1024)) s33` THEN
  LIBC_PLT_TAC SIGN87_EXEC 33 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN87_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN87_RALLOWED) 38 THEN
  SIGN87_RFCOPY_TAC `73728` `t0h:num->int32` `zs':num` `s38:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (39--41) THEN
  SIGN87_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of t0h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC SIGN87_EXEC (43--44) THEN
  SIGN87_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat`;
    `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC SIGN87_EXEC (46--47) THEN
  SIGN87_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat)`;
    `pc:num`; `read X30 s`] 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (49--51) THEN
  SIGN87_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_ct0 t0h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 52 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) = word 0`]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (53--56) THEN
  SIGN87_RCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i`;
    `mld_sign_ct0 t0h cphat i`; `pc:num`; `read X30 s`] 57 THEN
  ARM_STEPS_TAC SIGN87_EXEC (58--63) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PTR_LOOP_TEST_TAC THEN REWRITE_TAC[SIGN87_RTEST] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN87_RPRE = prove
 (SIGN87_RPRE_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CHK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (B:int64) (sp:int64) (mc:int64) (pc:num).
     APPEND (f_ev_back m B sp mc pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit B sp mc pc i))
              (f_ev_front B sp mc pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:num`; `B:int64`; `sp:int64`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa87_signature_internal_loop3`
     `if m < 8 then pc + mldsa87_signature_internal_loop3
      else pc + mldsa87_signature_internal_loop3_exit1`
     SIGN87_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN87_RBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SIGN_BETA_ALL_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0;
                    WORD_ADD_0] THEN
    SIGN_CONCRETE_DISCHARGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exits from the loop over the rows at a row whose first check (w0 - c  *)
(* s2) or second check (c t0) fails.                                         *)
(* ------------------------------------------------------------------------- *)

let SIGN87_RFAIL1_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rfail1.
        !e i B sp w s2h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ i < 8 /\
          ~(mld_poly_chknorm
             (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
             (word 261768) = word 0) /\
          nonoverlapping (B,106816) (sp,160) /\
          ALL (nonoverlapping (B,106816))
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa87_signature_internal_loop3) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 81920) /\
                    read X23 s = word_add B (word 104448) /\
                    read X21 s = word_add B (word(57344 + 1024 * i)) /\
                    read X24 s = word_add B (word(65536 + 1024 * i)) /\
                    read X28 s = word_add B (word(73728 + 1024 * i)) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(104448 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             s2h j) /\
                    (!j. 256 * i <= j /\ j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(57344 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa87_signature_internal_join2) /\
                    read X21 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rfail1 i B sp mc pc /\
                       memaccess_inbounds e2
                        [B,106816; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [B,106816]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X21; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 81920),1024);
                  memory :> bytes(word_add B (word 57344),8192)])`;;

let SIGN87_RFAIL_SETUP_TAC tmpl vars =
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CHK" THEN
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC vars THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]);;

(*** The first part of a row, up to the norm check of w0 - c s2 ***)

let SIGN87_ROW_HEAD_TAC =
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(65536 + 1024 * i)),
                                         1024)) s4` THEN
  LIBC_PLT_TAC SIGN87_EXEC 4 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN87_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN87_RALLOWED) 9 THEN
  SIGN87_RFCOPY_TAC `65536` `s2h:num->int32` `zs:num` `s9:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (10--12) THEN
  SIGN87_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s2h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC SIGN87_EXEC (14--15) THEN
  SIGN87_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat`;
    `pc:num`; `read X30 s`] 16 THEN
  SIGN87_RFSLICE_TAC `s16:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (17--19) THEN
  SIGN87_RCALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`;
    `mld_poly_decompose_lo_32 (mld_poly_of w i)`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat)`;
    `pc:num`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC SIGN87_EXEC (21--22) THEN
  SIGN87_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_sub (mld_poly_decompose_lo_32 (mld_poly_of w i))
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat))`;
    `pc:num`; `read X30 s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (24--27) THEN
  SIGN87_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 28 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV)));;

let SIGN87_RFAIL1 = prove
 (SIGN87_RFAIL1_STMT,
  SIGN87_RFAIL_SETUP_TAC
   `\(i:num) (B:int64) (sp:int64) (mc:int64) (pc:num).
     f_ev_rfail1 i B sp mc pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `B:int64`; `sp:int64`; `w:num->int32`;
    `s2h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN87_ROW_HEAD_TAC THEN
  ARM_STEPS_TAC SIGN87_EXEC [29] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
       (word 261768) = word 0)`]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (30--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SIGN87_RFAIL2_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rfail2.
        !e i B sp w s2h t0h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ i < 8 /\
          mld_poly_chknorm
           (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
           (word 261768) = word 0 /\
          ~(mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) =
            word 0) /\
          nonoverlapping (B,106816) (sp,160) /\
          ALL (nonoverlapping (B,106816))
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa87_signature_internal_loop3) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 81920) /\
                    read X23 s = word_add B (word 104448) /\
                    read X21 s = word_add B (word(57344 + 1024 * i)) /\
                    read X24 s = word_add B (word(65536 + 1024 * i)) /\
                    read X28 s = word_add B (word(73728 + 1024 * i)) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(104448 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(73728 + 4 * j)))) s =
                             t0h j) /\
                    (!j. 256 * i <= j /\ j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(57344 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa87_signature_internal_join2) /\
                    read X21 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rfail2 i B sp mc pc /\
                       memaccess_inbounds e2
                        [B,106816; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [B,106816]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X21; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 81920),1024);
                  memory :> bytes(word_add B (word 57344),8192)])`;;

let SIGN87_RFAIL2 = prove
 (SIGN87_RFAIL2_STMT,
  SIGN87_RFAIL_SETUP_TAC
   `\(i:num) (B:int64) (sp:int64) (mc:int64) (pc:num).
     f_ev_rfail2 i B sp mc pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `B:int64`; `sp:int64`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN87_ROW_HEAD_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
      (word 261768) = word 0`]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (29--33) THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(73728 + 1024 * i)),
                                          1024)) s33` THEN
  LIBC_PLT_TAC SIGN87_EXEC 33 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN87_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN87_RALLOWED) 38 THEN
  SIGN87_RFCOPY_TAC `73728` `t0h:num->int32` `zs':num` `s38:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (39--41) THEN
  SIGN87_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of t0h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC SIGN87_EXEC (43--44) THEN
  SIGN87_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat`;
    `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC SIGN87_EXEC (46--47) THEN
  SIGN87_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat)`;
    `pc:num`; `read X30 s`] 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (49--51) THEN
  SIGN87_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_ct0 t0h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 52 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  ARM_STEPS_TAC SIGN87_EXEC [53] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) =
      word 0)`]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (54--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints, whose result is the value of x21 for  *)
(* the decision.                                                             *)
(* ------------------------------------------------------------------------- *)

let SIGN87_TAIL_STMT =
 `?f_tail.
    !e sig B sp0 ct (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 sp0 /\
      PAIRWISE nonoverlapping
       [(sig,4627); (B,106816); (word_add sp0 (word 4528),160); (sp0,4528)] /\
      ALL (nonoverlapping (word pc,libmldsa_size))
       [(sig,4627); (B,106816); (sp0,4528)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_mc /\
                read PC s = word(pc + mldsa87_signature_internal_loop3_exit1) /\
                read SP s = word_add sp0 (word 4528) /\
                read X19 s = word_add B (word 81920) /\
                read X25 s = word_add B (word 106752) /\
                read X26 s = word_add B (word 57344) /\
                read (memory :> bytes64 (word_add sp0 (word 4624))) s = sig /\
                read (memory :> bytes64 (word_add sp0 (word 4648))) s =
                word_add B (word 105472) /\
                (!j. j < 64
                     ==> read (memory :> bytes8
                                (word_add B (word(106752 + j)))) s = ct j) /\
                (!j. j < 2048
                     ==> read (memory :> bytes32
                                (word_add B (word(57344 + 4 * j)))) s = x j) /\
                (!j. j < 1024
                     ==> read (memory :> bytes8
                                (word_add B (word(105472 + j)))) s = b j) /\
                read events s = e)
           (\s. read PC s = word(pc + mldsa87_signature_internal_join2) /\
                read X21 s =
                word_zx(mld_pack_hints_ret 75 8
                         (mld_polyvec_make_hint_32 x b)) /\
                (!j. j < 64
                     ==> read (memory :> bytes8 (word_add sig (word j))) s =
                         ct j) /\
                (mld_pack_hints_ret 75 8 (mld_polyvec_make_hint_32 x b) =
                 word 0
                 ==> !t. t < 83
                         ==> read (memory :> bytes8
                                    (word_add sig (word(4544 + t)))) s =
                             mld_pack_hints 75 8
                              (mld_polyvec_make_hint_32 x b) t) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_tail sig B sp0 pc x b /\
                   memaccess_inbounds e2
                    [sig,4627; B,106816; word_add sp0 (word 4528),160; sp0,4528]
                    [sig,4627; B,106816; sp0,4528]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X21; X30] ,,
            MAYCHANGE
             [memory :> bytes(sig,64);
              memory :> bytes(word_add sig (word 4544),83);
              memory :> bytes(word_add B (word 81920),1024);
              memory :> bytes(sp0,4528)])`;;

let SIGN87_TAIL = prove
 (SIGN87_TAIL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_C_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PH" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (B:int64) (sp0:int64) (pc:num) (x:num->int32) (b:num->byte).
     f_ev_tail sig B sp0 pc x b:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `B:int64`; `sp0:int64`;
    `ct:num->byte`; `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; C_RETURN; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN87_EXEC "H_PC"
   [`read X0 s`; `read X1 s`; `ct:num->byte`; `pc:num`; `read X30 s`]
   [`pc:num`; `sig:int64`; `B:int64`; `sp0:int64`; `x:num->int32`;
    `b:num->byte`] 5 THEN
  ARM_STEPS_TAC SIGN87_EXEC (6--10) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN87_EXEC "H_PH"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `x:num->int32`;
    `b:num->byte`; `pc:num`; `read SP s`; `read X30 s`]
   [`pc:num`; `sig:int64`; `B:int64`; `sp0:int64`; `x:num->int32`;
    `b:num->byte`] 11 THEN
  ARM_STEPS_TAC SIGN87_EXEC [12] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt and the test of x21: to join4 on success, else  *)
(* to the update of kappa.                                                   *)
(* ------------------------------------------------------------------------- *)

let SIGN87_CLEAN_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_clean.
        !e ok B sp pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\
          nonoverlapping (B,106816) (sp,160) /\
          ALL (nonoverlapping (B,106816))
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa87_signature_internal_join2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 81920) /\
                    read X20 s = word_add B (word 103424) /\
                    read X21 s = (if ok then word 0 else word 4294967295) /\
                    read X23 s = word_add B (word 104448) /\
                    read X25 s = word_add B (word 106752) /\
                    read X26 s = word_add B (word 57344) /\
                    read X27 s = word_add B (word 89088) /\
                    read (memory :> bytes64 (word_add sp (word 120))) s =
                    word_add B (word 105472) /\
                    read (memory :> bytes64 (word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s =
                    (if ok then word(pc + mldsa87_signature_internal_join4)
                     else word(pc + mldsa87_signature_internal_loop1_next1)) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_clean ok B sp mf pc /\
                       memaccess_inbounds e2
                        [B,106816; sp,160; word(pc + got_memset),8; ea,el]
                        [B,106816]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X24; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 57344),8192);
                  memory :> bytes(word_add B (word 81920),7168);
                  memory :> bytes(word_add B (word 89088),7168);
                  memory :> bytes(word_add B (word 103424),1024);
                  memory :> bytes(word_add B (word 104448),1024);
                  memory :> bytes(word_add B (word 105472),1024);
                  memory :> bytes(word_add B (word 106752),64)])`;;

let SIGN87_CLEAN_MEMSET_TAC n =
  LIBC_PLT_TAC SIGN87_EXEC n THEN
  SIGN_LIBC_CALL_TAC "H_MEMSET" SIGN87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref [`pc:num`; `ok:bool`; `B:int64`; `sp:int64`; `mf:int64`]) (n + 5);;

let SIGN87_CLEAN = prove
 (SIGN87_CLEAN_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (B:int64) (sp:int64) (mf:int64) (pc:num).
     if ok then f_ev_clean_ok B sp mf pc else f_ev_clean_bad B sp mf pc
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `ok:bool`; `B:int64`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  BOOL_CASES_TAC `ok:bool` THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
  SIGN87_CLEAN_MEMSET_TAC 4 THEN
  ARM_STEPS_TAC SIGN87_EXEC (10--13) THEN SIGN87_CLEAN_MEMSET_TAC 13 THEN
  ARM_STEPS_TAC SIGN87_EXEC (19--22) THEN SIGN87_CLEAN_MEMSET_TAC 22 THEN
  ARM_STEPS_TAC SIGN87_EXEC (28--32) THEN SIGN87_CLEAN_MEMSET_TAC 32 THEN
  ARM_STEPS_TAC SIGN87_EXEC (38--41) THEN SIGN87_CLEAN_MEMSET_TAC 41 THEN
  ARM_STEPS_TAC SIGN87_EXEC (47--50) THEN SIGN87_CLEAN_MEMSET_TAC 50 THEN
  ARM_STEPS_TAC SIGN87_EXEC (56--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt: y, w, w1 and its packing, c~ with the inlined    *)
(* SHAKE256 calls, the challenge and its NTT.                                *)
(* ------------------------------------------------------------------------- *)

let SIGN87_HEAD_STMT =
 `!mf mc ea el ev.
    memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
    ==> ?f_head.
        !e B sp0 A mu rhop n C guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ n < 9361 /\
          num_of_bytelist(list_of_seq
           (mld_sign_ctilde 8 128 mu
             (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
               (mld_sign_w 7 A
                 (mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n)))))
           64) = C /\
          mld_poly_challenge_terminates 60 64 C /\
          PAIRWISE nonoverlapping
           [(B,106816); (word_add sp0 (word 4528),160);
            (word_add sp0 (word 111528),208);
            (sp0,4528)] /\
          ALLPAIRS nonoverlapping
           [(B,106816); (word_add sp0 (word 111528),208);
            (sp0,4528)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa87_signature_internal_loop1) /\
                    read SP s = word_add sp0 (word 4528) /\
                    read X19 s = word_add B (word 81920) /\
                    read X22 s = word_add sp0 (word 111528) /\
                    read X23 s = word_add B (word 104448) /\
                    read X25 s = word_add B (word 106752) /\
                    read X26 s = word_add B (word 57344) /\
                    read X27 s = word_add B (word 89088) /\
                    read (memory :> bytes16 (word_add sp0 (word 4644))) s =
                    word(7 * n) /\
                    read (memory :> bytes64 (word_add sp0 (word 4648))) s =
                    word_add B (word 105472) /\
                    read (memory :> bytes64 (word_add sp0 (word 4656))) s =
                    word_add B (word 106496) /\
                    read (memory :> bytes64 (word_add sp0 (word 4664))) s = B /\
                    read (memory :> bytes64 (word_add sp0 (word 4672))) s =
                    word_add B (word 96256) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 14336
                         ==> read (memory :> bytes32
                                    (word_add B (word(4 * j)))) s = A j) /\
                    read (memory :> bytes(word_add B (word 106624),64)) s =
                    mu /\
                    read (memory :> bytes(word_add B (word 106688),64)) s =
                    rhop /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa87_signature_internal_loop2) /\
                    read X21 s = word 0 /\
                    read X24 s = word_add B (word 89088) /\
                    read X28 s = word_add B (word 96256) /\
                    (!j. j < 1792
                         ==> read (memory :> bytes32
                                    (word_add B (word(89088 + 4 * j)))) s =
                             mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n)
                              j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(57344 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32
                              (mld_sign_w 7 A
                                (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                                  (7 * n))) j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes8
                                    (word_add B (word(105472 + j)))) s =
                             mld_sign_w1
                              (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                              128
                              (mld_sign_w 7 A
                                (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                                  (7 * n))) j) /\
                    read (memory :> bytes(word_add B (word 106752),64)) s = C /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(104448 + 4 * j)))) s =
                             mld_poly_ntt (mld_poly_challenge 60 64 C) j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_head B sp0 guard mf mc pc C /\
                       memaccess_inbounds e2
                        [B,106816; word_add sp0 (word 4528),160;
                         word_add sp0 (word 111528),208;
                         sp0,4528;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [B,106816; word_add sp0 (word 111528),208;
                         sp0,4528]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X21; X24; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 57344),8192);
                  memory :> bytes(word_add B (word 81920),7168);
                  memory :> bytes(word_add B (word 89088),7168);
                  memory :> bytes(word_add B (word 104448),1024);
                  memory :> bytes(word_add B (word 105472),1024);
                  memory :> bytes(word_add B (word 106752),64);
                  memory :> bytes(word_add sp0 (word 111528),208);
                  memory :> bytes(sp0,4528)])`;;

let SIGN87_W1 =
 `mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   (mld_sign_w 7 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n)))`;;

let SIGN87_W1NUM = mk_comb(`num_of_bytelist`,
  list_mk_comb(`list_of_seq:(num->byte)->num->(byte)list`,
      [SIGN87_W1; `1024`]));;

let SIGN87_ABSORBED =
  list_mk_comb(`mld_keccak_absorb`,
    [`136`; `word 0:1600 word`; `0`; `1088`;
     mk_binop `(+):num->num->num` `mu:num`
      (mk_binop `( * ):num->num->num` `2 EXP 512` SIGN87_W1NUM)]);;

let SIGN87_S2 = mk_comb(`FST:(1600 word#num)->1600 word`,SIGN87_ABSORBED);;

let SIGN87_S3 =
  list_mk_comb(`mld_keccak_finalize`,[`136`; `31`; SIGN87_S2; `0`]);;

let SIGN87_HCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN87_EXEC name ilist
   [`pc:num`; `B:int64`; `sp0:int64`; `guard:int64`; `mf:int64`; `mc:int64`;
    `C:num`] n;;

let SIGN87_HEAD = prove
 (SIGN87_HEAD_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th)
     "H_GAMMA" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_CHALLENGE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_CHAL"
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memcpy_full_contract mc ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th) "H_YVEC"
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_DEC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_FINALIZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_RELEASE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(B:int64) (sp0:int64) (guard:int64) (mf:int64) (mc:int64) (pc:num)
     (C:num). f_ev_head B sp0 guard mf mc pc C:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `B:int64`; `sp0:int64`; `A:num->int32`;
    `mu:num`; `rhop:num`; `n:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_WORD_ZX_16_32_64]) THEN
  SIGN87_HCALL_TAC "H_GAMMA"
   [`read X0 s`; `read X1 s`; `rhop:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_Y_KAPPA]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (7--11) THEN
  SIGN87_HCALL_TAC "H_YVEC"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `A:num->int32`;
    `mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n)`;
    `pc:num`; `read SP s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC SIGN87_EXEC (13--14) THEN
  SIGN87_HCALL_TAC "H_CADDQ"
   [`read X0 s`;
    `mld_polyvec_map mld_poly_invntt_tomont
      (mld_polyvec_matrix_pointwise_montgomery 7 A
        (mld_polyvec_map mld_poly_ntt
          (mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n))))`;
    `pc:num`; `read SP s`; `read X30 s`] 15 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (16--20) THEN
  SIGN87_HCALL_TAC "H_DEC"
   [`read X0 s`; `read X1 s`;
    `mld_sign_w 7 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n))`;
    `read X2 s`; `pc:num`; `read SP s`; `read X30 s`] 21 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w1]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (22--23) THEN
  SIGN87_HCALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 24 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (25--28) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 111528):int64` THEN
  SIGN87_HCALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `64`; `word 0:1600 word`; `0`; `mu:num`;
    `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 1024 ==> read (memory :> bytes8
         (word_add B (word (105472 + j)))) s = f j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  MLD_H_BOUND_TAC `word_add B (word 106624):int64` THEN
  ARM_STEPS_TAC SIGN87_EXEC (30--33) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 111528):int64` THEN
  SIGN87_HCALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `1024`;
    `FST(mld_keccak_absorb 136 (word 0) 0 64 mu)`; `64`; SIGN87_W1NUM;
    `pc:num`; `read SP s`; `read X30 s`] 34 THEN
  MP_TAC(SPECL [`64`; `1024`; `mu:num`; SIGN87_W1NUM]
               MLD_SHAKE256_ABSORB_APPEND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV SIGN_NUMERAL_CONV) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(CONV_RULE SIGN_NUMERAL_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (35--36) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 111528):int64` THEN
  MLD_H_GUARD_ADDR_TAC THEN
  SIGN87_HCALL_TAC "H_FINALIZE"
   [`read X0 s`; SIGN87_S2; `0`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 37 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN87_EXEC (38--41) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 111528):int64` THEN
  SIGN87_HCALL_TAC "H_SQUEEZE"
   [`read X0 s`; `64`; `read X2 s`; SIGN87_S3; `136`;
    `pc:num`; `read SP s`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC SIGN87_EXEC (43--44) THEN
  SIGN87_HCALL_TAC "H_RELEASE" [`read X0 s`; `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC SIGN87_EXEC (46--57) THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add B (word 106752),64)) s57 = C`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde; mld_shake256_byte; mld_shake256_state;
                MLD_KECCAK_ABSORB_SND] THEN
    CONV_TAC SIGN_NUMERAL_CONV THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
   `read (memory :> bytes (word_add B (word 106752),64)) s57 =
    num_of_bytelist l`) (concl th))) THEN
  SIGN87_HCALL_TAC "H_CHAL"
   [`read X0 s`; `read X1 s`; `C:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 58 THEN
  ARM_STEPS_TAC SIGN87_EXEC (59--62) THEN
  SIGN87_HCALL_TAC "H_NTT"
   [`read X0 s`; `mld_poly_challenge 60 64 C`; `pc:num`; `read X30 s`] 63 THEN
  ARM_STEPS_TAC SIGN87_EXEC [64] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt, from loop1 to join4 or loop1_next1, with the events a    *)
(* function of the declassified record (C,r,x,b).                            *)
(* ------------------------------------------------------------------------- *)

let SIGN87_ATT_STMT =
 `!mf mc ea el ev.
    memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
    ==> ?f_att.
        !e sig B sp0 A s1h s2h t0h mu rhop n C r x b guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ n < 9361 /\
          mld_sign_attempt_declass 8 7 64 60 mld_poly_uniform_gamma1_19
           524168 261768 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
           128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75
           A s1h s2h t0h mu rhop (7 * n) = (C,r,x,b) /\
          mld_poly_challenge_terminates 60 64 C /\
          PAIRWISE nonoverlapping
           [(sig,4627); (B,106816); (word_add sp0 (word 4528),160);
            (word_add sp0 (word 111528),208);
            (sp0,4528)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (B,106816); (word_add sp0 (word 111528),208);
            (sp0,4528)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa87_signature_internal_loop1) /\
                    read SP s = word_add sp0 (word 4528) /\
                    read X19 s = word_add B (word 81920) /\
                    read X20 s = word_add B (word 103424) /\
                    read X22 s = word_add sp0 (word 111528) /\
                    read X23 s = word_add B (word 104448) /\
                    read X25 s = word_add B (word 106752) /\
                    read X26 s = word_add B (word 57344) /\
                    read X27 s = word_add B (word 89088) /\
                    read (memory :> bytes64 (word_add sp0 (word 4624))) s =
                    sig /\
                    read (memory :> bytes64 (word_add sp0 (word 4632))) s =
                    word_add B (word 73728) /\
                    read (memory :> bytes16 (word_add sp0 (word 4644))) s =
                    word(7 * n) /\
                    read (memory :> bytes64 (word_add sp0 (word 4648))) s =
                    word_add B (word 105472) /\
                    read (memory :> bytes64 (word_add sp0 (word 4656))) s =
                    word_add B (word 106496) /\
                    read (memory :> bytes64 (word_add sp0 (word 4664))) s = B /\
                    read (memory :> bytes64 (word_add sp0 (word 4672))) s =
                    word_add B (word 96256) /\
                    read (memory :> bytes64 (word_add sp0 (word 4680))) s =
                    word_add B (word 65536) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 14336
                         ==> read (memory :> bytes32
                                    (word_add B (word(4 * j)))) s = A j) /\
                    (!j. j < 1792
                         ==> read (memory :> bytes32
                                    (word_add B (word(96256 + 4 * j)))) s =
                             s1h j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 2048
                         ==> read (memory :> bytes32
                                    (word_add B (word(73728 + 4 * j)))) s =
                             t0h j) /\
                    read (memory :> bytes(word_add B (word 106624),64)) s =
                    mu /\
                    read (memory :> bytes(word_add B (word 106688),64)) s =
                    rhop /\
                    read events s = e)
               (\s. read PC s =
                    (if r = 24
                     then word(pc + mldsa87_signature_internal_join4)
                     else word(pc + mldsa87_signature_internal_loop1_next1)) /\
                    read X21 s = (if r = 24 then word 0 else word 4294967295) /\
                    (r = 24
                     ==> !t. t < 4627
                             ==> read (memory :> bytes8
                                        (word_add sig (word t))) s =
                                 mld_sign_attempt_sig 8 7 64 60
                                  mld_poly_uniform_gamma1_19 mld_polyz_pack_19
                                  640
                                  (mld_polyw1_pack_32 o
                                   mld_poly_decompose_hi_32)
                                  128 mld_poly_decompose_lo_32
                                  mld_polyvec_make_hint_32 75
                                  A s1h s2h t0h mu rhop (7 * n) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_att sig B sp0 guard mf mc pc C r x b /\
                       memaccess_inbounds e2
                        [sig,4627; B,106816; word_add sp0 (word 4528),160;
                         word_add sp0 (word 111528),208;
                         sp0,4528;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,4627; B,106816; word_add sp0 (word 111528),208;
                         sp0,4528]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X21; X24; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_add B (word 57344),8192);
                  memory :> bytes(word_add B (word 81920),7168);
                  memory :> bytes(word_add B (word 89088),7168);
                  memory :> bytes(word_add B (word 103424),1024);
                  memory :> bytes(word_add B (word 104448),1024);
                  memory :> bytes(word_add B (word 105472),1024);
                  memory :> bytes(word_add B (word 106752),64);
                  memory :> bytes(word_add sp0 (word 111528),208);
                  memory :> bytes(sp0,4528)])`;;

let SIGN87_AALLOWED =
  [`sig:int64`; `B:int64`; `sp0:int64`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `C:num`; `r:num`; `x:num->int32`; `b:num->byte`];;

let SIGN87_ACALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN87_EXEC name ilist
    SIGN87_AALLOWED n;;

let SIGN87_CPH = `mld_poly_ntt (mld_poly_challenge 60 64 C)`;;
let SIGN87_Y = `mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n)`;;
let SIGN87_W =
  `mld_sign_w 7 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n))`;;
let SIGN87_R0 =
  list_mk_comb(`mld_sign_r0`,
    [`mld_poly_decompose_lo_32`; SIGN87_W; `s2h:num->int32`; SIGN87_CPH]);;
let SIGN87_CT0 =
  list_mk_comb(`mld_sign_ct0`,[`t0h:num->int32`; SIGN87_CPH]);;
let SIGN87_CT =
  `mld_sign_ctilde 8 128 mu
    (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
      (mld_sign_w 7 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n))))`;;
let SIGN87_SP = `word_add sp0 (word 4528):int64`;;

let SIGN87_SIGATT =
 `mld_sign_attempt_sig 8 7 64 60 mld_poly_uniform_gamma1_19 mld_polyz_pack_19
   640 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75
   A s1h s2h t0h mu rhop (7 * n)`;;

let SIGN87_ATT_MID = subst [SIGN87_SIGATT,`SIGATT:num->byte`]
 `\s. read SP s = word_add sp0 (word 4528) /\
      read X19 s = word_add B (word 81920) /\
      read X20 s = word_add B (word 103424) /\
      read X21 s = (if r = 24 then word 0 else word 4294967295) /\
      read X23 s = word_add B (word 104448) /\
      read X25 s = word_add B (word 106752) /\
      read X26 s = word_add B (word 57344) /\
      read X27 s = word_add B (word 89088) /\
      read (memory :> bytes64 (word_add sp0 (word 4648))) s =
      word_add B (word 105472) /\
      read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
      read (memory :> bytes(ea,el)) s = ev /\
      (r = 24
       ==> !t. t < 4627
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   SIGATT t)`;;

let SIGN87_ZCASE_TAC =
  SUBGOAL_THEN `r <= 7 /\ ~(r = 24)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 7` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 7 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SIGN87_ACALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `B:int64`; SIGN87_SP; `s1h:num->int32`;
    SIGN87_CPH; SIGN87_Y; `pc:num`] 2 THEN
  SIGN_PC_SIMP_TAC THEN
  SIGN87_ACALL_TAC "H_ZFAIL"
   [`r:num`; `sig:int64`; `B:int64`; SIGN87_SP; `s1h:num->int32`;
    SIGN87_CPH; SIGN87_Y; `pc:num`] 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_PATH_DISCHARGE_TAC;;

let SIGN87_WCASE_TAC =
  SUBGOAL_THEN `(r - 7) DIV 2 <= 8 /\ (r - 7) DIV 2 < 8 /\ ~(r = 24) /\
                2 * (r - 7) DIV 2 <= r - 7`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 23` THEN UNDISCH_TAC `7 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SIGN87_R0; SIGN87_CT0; `261768`; `261888`; `r - 7`;
                `(r - 7) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 7` THEN UNDISCH_TAC `r < 23` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SIGN87_ACALL_TAC "H_RPRE"
   [`(r - 7) DIV 2`; `B:int64`; SIGN87_SP; SIGN87_W; `s2h:num->int32`;
    `t0h:num->int32`; SIGN87_CPH; `pc:num`] 3 THEN
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `7 <= r /\ r < 23 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 7)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 7) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SIGN87_ACALL_TAC "H_RFAIL1"
     [`(r - 7) DIV 2`; `B:int64`; SIGN87_SP; SIGN87_W; `s2h:num->int32`;
      SIGN87_CPH; `pc:num`] 4;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 7) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (SPECL [`7`; `r:num`] SIGN_ODD_ROW)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r - 8` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `r < 23` THEN ARITH_TAC; DISCH_TAC] THEN
    SIGN87_ACALL_TAC "H_RFAIL2"
     [`(r - 7) DIV 2`; `B:int64`; SIGN87_SP; SIGN87_W; `s2h:num->int32`;
      `t0h:num->int32`; SIGN87_CPH; `pc:num`] 4] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_PATH_DISCHARGE_TAC;;

let SIGN87_TCASE_TAC =
  SUBGOAL_THEN `23 <= r /\ 8 <= 8` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 23)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SIGN87_R0; SIGN87_CT0; `261768`; `261888`; `16`; `8`]
               SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `23 <= r` THEN UNDISCH_TAC `j < 16` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SIGN87_ACALL_TAC "H_RPRE"
   [`8`; `B:int64`; SIGN87_SP; SIGN87_W; `s2h:num->int32`;
    `t0h:num->int32`; SIGN87_CPH; `pc:num`] 3 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read PC s = x`) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_LT_CONV) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 23 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 23 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 1024
        ==> read (memory :> bytes8 (word_add B (word (105472 + j)))) s3 =
            (b:num->byte) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "b"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_hint_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
      `read (memory :> bytes (word_add B (word 106752),64)) s = C`) (concl th)
    then FIRST_ASSUM(fun cth ->
           if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
           then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES_OFF
                            (TRANS th (SYM cth)))
           else NO_TAC)
    else NO_TAC) THEN
  SIGN87_ACALL_TAC "H_TAIL"
   [`sig:int64`; `B:int64`; `sp0:int64`; SIGN87_CT; `x:num->int32`;
    `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `23 <= r ==> (r = 24 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `word_zx (mld_pack_hints_ret 75 8 (mld_polyvec_make_hint_32 x b)):int64 =
    (if r = 24 then word 0 else word 4294967295)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC SIGN_PACK_HINTS_RET_ZX THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `mld_pack_hints_ret 75 8 (mld_polyvec_make_hint_32 x b) = word 0`
    ASSUME_TAC THENL
     [REWRITE_TAC[mld_pack_hints_ret] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      ASM_REWRITE_TAC[GSYM NOT_LT];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `mld_pack_hints_ret 75 8 h = word 0 ==> P`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[mld_sign_attempt_sig] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[mld_sign_cphat] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `4627 = (64 + 7 * 640) + 83` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SIGN_SIG_ASSEMBLE THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> can (term_match []
        `!t. t < 640 * 7
             ==> read (memory :> bytes8 (word_add sig (word (64 + t)))) s =
                 P t`) (concl th)));
    SIGN_PATH_DISCHARGE_TAC];;

let SIGN87_PATHS_TAC =
  ASM_CASES_TAC `r < 7` THENL
   [SIGN87_ZCASE_TAC;
    SUBGOAL_THEN `7 <= r /\ 7 <= 7` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 7)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `7 <= r ==> (!i. i < 7 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SIGN87_ACALL_TAC "H_ZPRE"
     [`7`; `sig:int64`; `B:int64`; SIGN87_SP; `s1h:num->int32`;
      SIGN87_CPH; SIGN87_Y; `pc:num`] 2 THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_CASES_TAC `r < 23` THENL [SIGN87_WCASE_TAC; SIGN87_TCASE_TAC]];;
let SIGN87_ACLEAN_TAC =
  FULL_INIT_TAC THEN
  SIGN87_ACALL_TAC "H_CLEAN"
   [`r = 24`; `B:int64`; SIGN87_SP; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;
let SIGN87_ATT = prove
 (SIGN87_ATT_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
   FIRST_X_ASSUM(fun th ->
     if is_conj(concl th) then
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN87_HEAD th) "H_HEAD"
     else NO_TAC) THEN
   FIRST_ASSUM(fun th ->
     if can (term_match [] `memcpy_full_contract mc ea el ev`) (concl th) then
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN87_ZPRE th) "H_ZPRE" THEN
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN87_ZFAIL th) "H_ZFAIL" THEN
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN87_RPRE th) "H_RPRE" THEN
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN87_RFAIL1 th) "H_RFAIL1" THEN
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN87_RFAIL2 th) "H_RFAIL2"
     else NO_TAC) THEN
   FIRST_ASSUM(fun th ->
     if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN87_CLEAN th) "H_CLEAN"
     else NO_TAC) THEN
   ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN87_TAIL "H_TAIL" THEN
   CONCRETIZE_F_EVENTS_TAC
    `\(sig:int64) (B:int64) (sp0:int64) (guard:int64) (mf:int64) (mc:int64)
      (pc:num) (C:num) (r:num) (x:num->int32) (b:num->byte).
      APPEND (f_ev_cl sig B sp0 guard mf mc pc C r x b)
       (APPEND
         (if r < 7 then f_ev_pz sig B sp0 guard mf mc pc C r x b
          else if r < 23
          then if EVEN (r - 7) then f_ev_pw1 sig B sp0 guard mf mc pc C r x b
               else f_ev_pw2 sig B sp0 guard mf mc pc C r x b
          else f_ev_pt sig B sp0 guard mf mc pc C r x b)
         (f_ev_hd sig B sp0 guard mf mc pc C r x b))
      :(uarch_event)list` THEN
   REPEAT META_EXISTS_TAC THEN
   MAP_EVERY X_GEN_TAC
    [`e:(uarch_event)list`; `sig:int64`; `B:int64`; `sp0:int64`;
     `A:num->int32`; `s1h:num->int32`; `s2h:num->int32`; `t0h:num->int32`;
     `mu:num`; `rhop:num`; `n:num`; `C:num`; `r:num`; `x:num->int32`;
     `b:num->byte`; `guard:int64`; `pc:num`] THEN
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
               C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
               fst SIGN87_EXEC] THEN
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `mld_sign_attempt_declass k l ctlen tau g1 bndz bndw bndh w1enc w1p dlo
      mkhint omega A s1hat s2hat t0hat mu rhoprime kappa = (C,r,x,b)`)
    (concl th))) THEN
   REWRITE_TAC[mld_sign_attempt_declass] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[mld_sign_cphat; th]) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
   CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
   STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP SIGN_REJ_CASES o check (fun th ->
     can (term_match []
      `mld_sign_rej k l bndz bndw bndh omega mkhint z r0 ct0 x w1 = r`)
      (concl th))) THEN
   CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
   STRIP_TAC THEN
   REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
               SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
               SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
   RULE_ASSUM_TAC(REWRITE_RULE
    [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
     SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
     SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
   ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa87_signature_internal_join2`
     SIGN87_ATT_MID THEN
   CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    SIGN87_ACALL_TAC "H_HEAD"
     [`B:int64`; `sp0:int64`; `A:num->int32`; `mu:num`; `rhop:num`; `n:num`;
      `C:num`; `guard:int64`; `pc:num`] 1 THEN
    SIGN87_PATHS_TAC;
    SIGN87_ACLEAN_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The facts about the attempts that the main proof needs, for D =           *)
(* mld_sign_declass_87 and its number of attempts.                           *)
(* ------------------------------------------------------------------------- *)

let SIGN87_ATT_ARGS =
 `mld_sign_attempt_declass 8 7 64 60 mld_poly_uniform_gamma1_19
   524168 261768 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
   128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75
   (mld_polyvec_matrix_expand 7 (mld_sk_rho skb))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. skb(128 + j))))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. skb(800 + j))))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. skb(1568 + j))))
   MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU)`;;

let SIGN87_DECLASS_FACTS = prove
 (`!skb MU RND.
        0 < mld_sign_natt 9361 24 (mld_sign_declass_87 skb MU RND) /\
        mld_sign_natt 9361 24 (mld_sign_declass_87 skb MU RND) <= 9361 /\
        (!i. i < mld_sign_natt 9361 24 (mld_sign_declass_87 skb MU RND)
             ==> mld_sign_declass_87 skb MU RND i =
                 mld_sign_attempt_declass 8 7 64 60 mld_poly_uniform_gamma1_19
                  524168 261768 261888
                  (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                  128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75
                  (mld_polyvec_matrix_expand 7 (mld_sk_rho skb))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(128 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(800 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 416 mld_polyt0_unpack
                      (\j. skb(1568 + j))))
                  MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU) (7 * i)) /\
        (!i. i + 1 < mld_sign_natt 9361 24 (mld_sign_declass_87 skb MU RND)
             ==> ~(FST(SND(mld_sign_declass_87 skb MU RND i)) = 24)) /\
        (mld_sign_ok_87 skb MU RND <=>
         FST(SND(mld_sign_declass_87 skb MU RND
                  (mld_sign_natt 9361 24 (mld_sign_declass_87 skb MU RND) -
                   1))) = 24) /\
        (~mld_sign_ok_87 skb MU RND
         ==> mld_sign_natt 9361 24 (mld_sign_declass_87 skb MU RND) =
             9361) /\
        mld_sign_sig_87 skb MU RND =
        (if mld_sign_ok_87 skb MU RND
         then mld_sign_attempt_sig 8 7 64 60 mld_poly_uniform_gamma1_19
               mld_polyz_pack_19 640
               (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
               mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75
               (mld_polyvec_matrix_expand 7 (mld_sk_rho skb))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                   (\j. skb(128 + j))))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                   (\j. skb(800 + j))))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 416 mld_polyt0_unpack
                   (\j. skb(1568 + j))))
               MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU)
               (7 * (mld_sign_natt 9361 24 (mld_sign_declass_87 skb MU RND) -
                     1))
         else \t. word 0) /\
        (mld_sign_terminates_87 skb MU RND
         ==> !i. i < mld_sign_natt 9361 24 (mld_sign_declass_87 skb MU RND)
                 ==> mld_poly_challenge_terminates 60 64
                      (FST(mld_sign_declass_87 skb MU RND i)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_declass_87; mld_sign_ok_87; mld_sign_sig_87;
              mld_sign_terminates_87] THEN
  MP_TAC(SPECL
   [`8`; `7`; `mld_polyeta_unpack_2`; `96`; `64`; `60`;
    `mld_poly_uniform_gamma1_19`; `524168`; `261768`; `261888`;
    `mld_polyw1_pack_32 o mld_poly_decompose_hi_32`; `128`;
    `mld_poly_decompose_lo_32`; `mld_polyvec_make_hint_32`; `75`; `9361`;
    `skb:num->byte`; `MU:num`; `RND:num`] SIGN_NATT_DECLASS) THEN
  CONV_TAC(LAND_CONV(LAND_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL
   [`8`; `7`; `mld_polyeta_unpack_2`; `96`; `64`; `60`;
    `mld_poly_uniform_gamma1_19`; `524168`; `261768`; `261888`;
    `mld_polyw1_pack_32 o mld_poly_decompose_hi_32`; `128`;
    `mld_poly_decompose_lo_32`; `mld_polyvec_make_hint_32`; `75`; `9361`;
    `skb:num->byte`; `MU:num`; `RND:num`] SIGN_NATTEMPTS_PROPS) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
  ABBREV_TAC
   `N = mld_sign_nattempts 8 7 mld_polyeta_unpack_2 96 64 60
         mld_poly_uniform_gamma1_19 524168 261768 261888
         (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
         mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75 9361
         skb MU RND` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_sign_declass; mld_sign_sig; mld_sign_terminates] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_sk_s1; mld_sk_s2; mld_sk_t0] THEN SIGN_NUMS_TAC THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < N` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `i + 1 < N` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SIGN_ATTEMPT_DECLASS_REJ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (term_match [] `!i. i + 1 < N ==> P i`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_sign_rejn; mld_sk_s1; mld_sk_s2; mld_sk_t0] THEN
    SIGN_NUMS_TAC THEN REWRITE_TAC[];
    SUBGOAL_THEN `N - 1 < N` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `0 < N` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SIGN_ATTEMPT_DECLASS_REJ] THEN
    REWRITE_TAC[mld_sign_rejn; mld_sk_s1; mld_sk_s2; mld_sk_t0] THEN
    SIGN_NUMS_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main proof. The events are those of the prologue (one function for    *)
(* each case of ext), then attempt i for each i < N, the number of attempts  *)
(* (mld_sign_natt 9361 24 D, with D what is declassified): an attempt that   *)
(* is followed by another (i + 1 < N), the successful last one, or the last  *)
(* one after which the signature is zeroed (9361 attempts, all rejected),    *)
(* then those of the epilogue; all of it twice, for the two positions of     *)
(* the buffers, at stackpointer + 5216 if stackpointer is a multiple of 32   *)
(* and at stackpointer + 5232 otherwise.                                     *)
(* ------------------------------------------------------------------------- *)

let SIGN87_TEMPLATE =
 `\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (rnd:int64)
   (sk:int64) (ext:int64) (rh:num)
   (D:num->num#num#(num->int32)#(num->byte)) (guard:int64) (mf:int64)
   (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
   if aligned 32 stackpointer then
     APPEND
      (f_ev_epila sig m mlen pre prelen rnd sk ext rh D guard mf mc pc
                  stackpointer returnaddress)
      (APPEND
        (ENUMERATEL (mld_sign_natt 9361 24 D)
          (\i. if i + 1 < mld_sign_natt 9361 24 D
               then f_ev_conta sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i
               else if FST(SND(D i)) = 24
               then f_ev_succa sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i
               else f_ev_exha sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i))
        (if word_zx ext = (word 0:int32)
         then f_ev_prolha sig m mlen pre prelen rnd sk ext rh D guard mf mc
                pc stackpointer returnaddress
         else f_ev_prolxa sig m mlen pre prelen rnd sk ext rh D guard mf mc
                pc stackpointer returnaddress))
   else
     APPEND
      (f_ev_epilu sig m mlen pre prelen rnd sk ext rh D guard mf mc pc
                  stackpointer returnaddress)
      (APPEND
        (ENUMERATEL (mld_sign_natt 9361 24 D)
          (\i. if i + 1 < mld_sign_natt 9361 24 D
               then f_ev_contu sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i
               else if FST(SND(D i)) = 24
               then f_ev_succu sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i
               else f_ev_exhu sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i))
        (if word_zx ext = (word 0:int32)
         then f_ev_prolhu sig m mlen pre prelen rnd sk ext rh D guard mf mc
                pc stackpointer returnaddress
         else f_ev_prolxu sig m mlen pre prelen rnd sk ext rh D guard mf mc
                pc stackpointer returnaddress))
   :(uarch_event)list`;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop over the attempts, for the buffers at           *)
(* stackpointer + b: the saved registers, the canary, the pointers in the    *)
(* frame, the matrix, s1, s2 and t0 (in NTT form), mu and rho'' do not       *)
(* change; before attempt i the registers of the loop hold the addresses of  *)
(* its buffers and kappa = 7 * i (the 32-bit word at sp + 116); after the    *)
(* last attempt x21 holds the result and sig the signature.                  *)
(* ------------------------------------------------------------------------- *)

let SIGN87_INV b =
  let nm n = mk_small_numeral n in
  subst
   [nm b,`oBB:num`; nm(b + 96256),`oS1:num`; nm(b + 65536),`oS2:num`;
    nm(b + 73728),`oT0:num`; nm(b + 105472),`oW1P:num`;
    nm(b + 106496),`oSEED:num`; nm(b + 106624),`oMUO:num`;
    nm(b + 106688),`oRHO:num`; nm(b + 81920),`oSCR:num`;
    nm(b + 103424),`oTT:num`; nm(b + 104448),`oCP:num`;
    nm(b + 106752),`oCT:num`;
    nm(b + 57344),`oW0:num`; nm(b + 89088),`oYY:num`]
  `\i s.
     read SP s = word_add stackpointer (word 5056) /\
     read (memory :> bytes64 (word_add stackpointer (word 5056))) s =
     x19_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5064))) s =
     x20_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5072))) s =
     x21_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5080))) s =
     x22_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5088))) s =
     x23_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5096))) s =
     x24_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5104))) s =
     x25_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5112))) s =
     x26_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5120))) s =
     x27_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5128))) s =
     x28_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5136))) s =
     returnaddress /\
     read (memory :> bytes64 (word_add stackpointer (word 112264))) s =
     canary /\
     read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
       s = guard /\
     read (memory :> bytes64 guard) s = canary /\
     read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
     read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\
     read (memory :> bytes(ea,el)) s = ev /\
     read (memory :> bytes64 (word_add stackpointer (word 5152))) s = sig /\
     read (memory :> bytes64 (word_add stackpointer (word 5160))) s =
     word_add stackpointer (word oT0) /\
     read (memory :> bytes64 (word_add stackpointer (word 5176))) s =
     word_add stackpointer (word oW1P) /\
     read (memory :> bytes64 (word_add stackpointer (word 5184))) s =
     word_add stackpointer (word oSEED) /\
     read (memory :> bytes64 (word_add stackpointer (word 5192))) s =
     word_add stackpointer (word oBB) /\
     read (memory :> bytes64 (word_add stackpointer (word 5200))) s =
     word_add stackpointer (word oS1) /\
     read (memory :> bytes64 (word_add stackpointer (word 5208))) s =
     word_add stackpointer (word oS2) /\
     (!j. j < 14336
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oBB + 4 * j)))) s =
              mld_polyvec_matrix_expand 7 rh j) /\
     (!j. j < 1792
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oS1 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                 (\j. skb(128 + j))) j) /\
     (!j. j < 2048
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oS2 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                 (\j. skb(800 + j))) j) /\
     (!j. j < 2048
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oT0 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 416 mld_polyt0_unpack
                 (\j. skb(1568 + j))) j) /\
     read (memory :> bytes(word_add stackpointer (word oMUO),64)) s = MU /\
     read (memory :> bytes(word_add stackpointer (word oRHO),64)) s =
     mld_sign_rhoprime (\j. skb(32 + j)) RND MU /\
     (i < mld_sign_natt 9361 24 D
      ==> read X19 s = word_add stackpointer (word oSCR) /\
          read X20 s = word_add stackpointer (word oTT) /\
          read X22 s = word_add stackpointer (word 112056) /\
          read X23 s = word_add stackpointer (word oCP) /\
          read X25 s = word_add stackpointer (word oCT) /\
          read X26 s = word_add stackpointer (word oW0) /\
          read X27 s = word_add stackpointer (word oYY) /\
          read (memory :> bytes32 (word_add stackpointer (word 5172))) s =
          word(7 * i)) /\
     (i = mld_sign_natt 9361 24 D
      ==> read X21 s =
          (if mld_sign_ok_87 skb MU RND then word 0 else word 4294967292) /\
          (!t. t < 4627
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   mld_sign_sig_87 skb MU RND t))`;;

let SIGN87_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 5247 5216 5232;;

let SIGN87_MALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `rnd:int64`; `sk:int64`; `ext:int64`; `rh:num`;
   `D:num->num#num#(num->int32)#(num->byte)`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let SIGN87_MCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN87_EXEC name ilist
    SIGN87_MALLOWED n;;

let SIGN87_NUMV s b k = subst [mk_small_numeral(b + k), mk_var(s,`:num`)];;

(* ------------------------------------------------------------------------- *)
(* The start: the callees as assumptions, the template, the frame (with the  *)
(* stack pointer at its bottom), the abbreviations rh and D (the arguments   *)
(* of the events), mu, the canary, the preserved registers and the facts     *)
(* about the attempts.                                                       *)
(* ------------------------------------------------------------------------- *)

let SIGN87_START_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if is_conj(concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN87_ATT th) "H_ATT"
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th) "H_MEXP"
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET"
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_H" THEN
  CONCRETIZE_F_EVENTS_TAC SIGN87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`;
    `pre:int64`; `prelen:num`; `rnd:int64`; `sk:int64`; `ext:int64`;
    `skb:num->byte`; `M:num`; mk_var("PRE",`:num`); `RND:num`; `MU:num`;
    `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 112272 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC `rh = mld_sk_rho skb` THEN
  ABBREV_TAC `D = mld_sign_declass_87 skb MU RND` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `MU = (if p then a else b)`) (concl th))) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 112272):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28) THEN
  MP_TAC(SPECL [`skb:num->byte`; `MU:num`; `RND:num`] SIGN87_DECLASS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The prologue, up to the start of the first attempt: unpack_sk, then on    *)
(* ext either mld_H87 for mu (from tr, the prefix and m) or the inlined copy *)
(* of 64 bytes from m (as four 128-bit words), then mld_H87 for rho'' (from  *)
(* the key, rnd and mu) and the matrix expansion. The offsets from b are     *)
(* those of rho, tr and the key in the seed buffer, mu and rho''.            *)
(* ------------------------------------------------------------------------- *)

let SIGN87_RHO_TAC b =
  let pat = SIGN87_NUMV "oRHO" b 106496
   `!j. j < 32 ==> read (memory :> bytes8
         (word_add stackpointer (word (oRHO + j)))) s = f j` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then FIRST_ASSUM(fun rth ->
           if is_eq(concl rth) && is_var(rhs(concl rth)) &&
              name_of(rhs(concl rth)) = "rh"
           then ASSUME_TAC(TRANS
                  (REWRITE_RULE[ETA_AX]
                    (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
                  (REWRITE_RULE[mld_sk_rho] rth))
           else NO_TAC)
    else NO_TAC);;

let SIGN87_PROL_TAIL_TAC b n0 =
  let sn k = mk_var("s"^string_of_int k,`:armstate`) in
  let nh = n0 + 19 and nm = n0 + 29 in
  let kpat = SIGN87_NUMV "oKEY" b 106592
   `!j. j < 32 ==> read (memory :> bytes8
         (word_add stackpointer (word (oKEY + j)))) s = f j`
  and rgoal = SIGN87_NUMV "oRHO" b 106688
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    mld_sign_rhoprime (\j. skb(32 + j)) RND MU`
  and rpat = SIGN87_NUMV "oRHO" b 106688
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    num_of_bytelist l` in
  ARM_STEPS_TAC SIGN87_EXEC (n0--(nh - 1)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] kpat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN87_MCALL_TAC "H_H"
   [`read X0 s`; `read X1 s`; `32`; `read X3 s`; `32`;
    `read X5 s`; `64`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(32 + j)) 32)`;
    `RND:num`; `MU:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] nh THEN
  SUBGOAL_THEN (subst [sn nh,`s:armstate`] rgoal) ASSUME_TAC THENL
   [REWRITE_TAC[mld_sign_rhoprime] THEN CONV_TAC SIGN_NUM_ARITH_CONV THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE SIGN_NUM_ARITH_CONV o
      check (fun th -> can (term_match [] rpat) (concl th)));
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] rpat) (concl th))) THEN
  ARM_STEPS_TAC SIGN87_EXEC ((nh + 1)--(nm - 1)) THEN
  SIGN87_RHO_TAC b THEN
  SIGN87_MCALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; `rh:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] nm THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `0 = n <=> n = 0`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  SIGN_SEL_DISCHARGE_TAC;;

let SIGN87_MU_TAC b n =
  let sv = mk_var("s"^string_of_int n,`:armstate`) in
  let mgoal = subst [sv,`s:armstate`] (SIGN87_NUMV "oMU" b 106624
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s = MU`)
  and mpat = subst [sv,`s:armstate`] (SIGN87_NUMV "oMU" b 106624
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s =
    num_of_bytelist l`) in
  SUBGOAL_THEN mgoal ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" &&
         not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_mu] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV));
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] mpat) (concl th)));;

let SIGN87_PROL_H_TAC b =
  let tpat = SIGN87_NUMV "oTR" b 106528
   `!j. j < 64 ==> read (memory :> bytes8
         (word_add stackpointer (word (oTR + j)))) s = f j` in
  ARM_STEPS_TAC SIGN87_EXEC [43] THEN
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  ARM_STEPS_TAC SIGN87_EXEC (44--51) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] tpat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN87_MCALL_TAC "H_H"
   [`read X0 s`; `read X1 s`; `64`; `read X3 s`; `prelen:num`;
    `read X5 s`; `mlen:num`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(64 + j)) 64)`;
    mk_var("PRE",`:num`); `M:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 52 THEN
  FIRST_ASSUM(fun th ->
    if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE
          [ASSUME `word_zx(ext:int64) = (word 0:int32)`] th)
    else NO_TAC) THEN
  SIGN87_MU_TAC b 52 THEN
  SIGN87_PROL_TAIL_TAC b 53;;

let SIGN87_M128_TAC s =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `~(word_zx (ext:int64) = (word 0:int32)) ==> 64 <= mlen`) (concl th)
    then ASSUME_TAC(MP th (ASSUME `~(word_zx(ext:int64) = (word 0:int32))`))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [`m:int64`] `read (memory :> bytes(m,mlen)) s = M`)
           (concl th)
    then MAP_EVERY (fun n ->
           MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral n;
                         s] SIGN_BYTES128_OF_BYTES) THEN
           ASM_REWRITE_TAC[] THEN
           ANTS_TAC THENL [UNDISCH_TAC `64 <= mlen` THEN ARITH_TAC;
                           CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                           REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC])
         [0;1;2;3]
    else NO_TAC);;

let SIGN87_PROL_X_TAC b =
  let mu = SIGN87_NUMV "oMU" b 106624
   `word_add stackpointer (word oMU):int64` in
  let mgoal = SIGN87_NUMV "oMU" b 106624
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s50 = MU`
  and mpat = SIGN87_NUMV "oMU" b 106624
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s50 =
    M MOD 2 EXP 512` in
  ARM_STEPS_TAC SIGN87_EXEC [43] THEN
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  SIGN87_M128_TAC `s43:armstate` THEN
  ARM_STEPS_TAC SIGN87_EXEC (44--50) THEN
  MP_TAC(SPECL [mu; `M:num`; `4`; `s50:armstate`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    CONV_TAC(LAND_CONV(DEPTH_CONV NUM_MULT_CONV)) THEN DISCH_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && is_var(rhs(concl th)) &&
       name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE
          [ASSUME `~(word_zx(ext:int64) = (word 0:int32))`] th)
    else NO_TAC) THEN
  SUBGOAL_THEN mgoal ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" &&
         not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] mpat) (concl th))) THEN
  SIGN87_PROL_TAIL_TAC b 51;;

let SIGN87_PROL_TAC b =
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN87_EXEC (1--4) THEN
  MEXP_BUFFER_TAC SIGN87_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC SIGN87_EXEC (5--10) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC SIGN87_EXEC (11--41) THEN
  SIGN87_MCALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `read X6 s`; `skb:num->byte`; `pc:num`; `read SP s`;
    `read X30 s`] 42 THEN
  ASM_CASES_TAC `word_zx(ext:int64) = (word 0:int32)` THENL
   [SIGN87_PROL_H_TAC b; SIGN87_PROL_X_TAC b];;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop over the attempts: the facts about attempt i     *)
(* (its record D i as mld_sign_attempt_declass gives it, the termination of  *)
(* its challenge, and the result and signature if it is the last), the       *)
(* attempt as one step (ATT, with B = stackpointer + b and sp0 =             *)
(* stackpointer + 528), then the three exits: on success to join4; on        *)
(* rejection kappa += 7, then back to loop1 or, after the last attempt, -4   *)
(* in x21 and the zeroing of the signature with memset, to join4. The        *)
(* equations for mld_sign_ok_87 and mld_sign_sig_87 are made conditional on  *)
(* ~(i + 1 < N) before any call, which would otherwise rewrite the           *)
(* postcondition with them.                                                  *)
(* ------------------------------------------------------------------------- *)

let SIGN87_BALLOWED = SIGN87_MALLOWED @ [`i:num`];;

let SIGN87_ATT_ILIST b =
  [`sig:int64`; mk_comb(`word_add stackpointer:int64->int64`,
                        mk_comb(`word:num->int64`,mk_small_numeral b));
   `word_add stackpointer (word 528):int64`;
   `mld_polyvec_matrix_expand 7 rh`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 96 mld_polyeta_unpack_2
       (\j. (skb:num->byte)(128 + j)))`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 96 mld_polyeta_unpack_2
       (\j. (skb:num->byte)(800 + j)))`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 416 mld_polyt0_unpack
       (\j. (skb:num->byte)(1568 + j)))`;
   `MU:num`; `mld_sign_rhoprime (\j. (skb:num->byte)(32 + j)) RND MU`;
   `i:num`; `FST((D:num->num#num#(num->int32)#(num->byte)) i)`;
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i))`;
   `FST(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `SND(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `guard:int64`; `pc:num`];;

let SIGN87_DANGER =
  [`mld_sign_ok_87 skb MU RND <=> P`;
   `mld_sign_sig_87 skb MU RND = x`];;

let SIGN87_BODY_INIT_TAC =
  let nth = UNDISCH(MP (ARITH_RULE
   `i < mld_sign_natt 9361 24 D
    ==> ~(i + 1 < mld_sign_natt 9361 24 D)
    ==> mld_sign_natt 9361 24 D - 1 = i`)
   (ASSUME `i < mld_sign_natt 9361 24 D`)) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ASSUME `i < mld_sign_natt 9361 24 D`;
              ASSUME `~(i = mld_sign_natt 9361 24 D)`] THEN
  SUBGOAL_THEN `i < 9361` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 9361 24 D`; `mld_sign_natt 9361 24 D <= 9361`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i < mld_sign_natt 9361 24 D
              ==> (D:num->num#num#(num->int32)#(num->byte)) i = x`)
         (concl th)
    then
      let th1 = MP (SPEC `i:num` th)
                   (ASSUME `i < mld_sign_natt 9361 24 D`) in
      let tup = `FST((D:num->num#num#(num->int32)#(num->byte)) i),
                 FST(SND(D i)),FST(SND(SND(D i))),SND(SND(SND(D i)))` in
      ASSUME_TAC(TRANS (SYM th1) (SYM(REWRITE_CONV[PAIR] tup)))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i < mld_sign_natt 9361 24 D
              ==> mld_poly_challenge_terminates 60 64
                   (FST((D:num->num#num#(num->int32)#(num->byte)) i))`)
         (concl th)
    then ASSUME_TAC(MP (SPEC `i:num` th)
                       (ASSUME `i < mld_sign_natt 9361 24 D`))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i + 1 < mld_sign_natt 9361 24 D
              ==> ~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) =
                    24)`)
         (concl th)
    then ASSUME_TAC(SPEC `i:num` th)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `mld_sign_ok_87 skb MU RND <=> P`) (concl th)
    then ASSUME_TAC(DISCH `~(i + 1 < mld_sign_natt 9361 24 D)`
                     (REWRITE_RULE[nth] th))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `mld_sign_sig_87 skb MU RND = x`) (concl th)
    then ASSUME_TAC(DISCH `~(i + 1 < mld_sign_natt 9361 24 D)`
                     (REWRITE_RULE[nth] th))
    else NO_TAC);;

let SIGN87_BODY_ATT_TAC b =
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes32
             (word_add stackpointer (word 5172))) s0 = word (7 * i)`)
           (concl th)
    then ASSUME_TAC(MATCH_MP SIGN_BYTES16_OF_BYTES32
          (CONJ th (MP (ARITH_RULE `i < 9361 ==> 7 * i < 65536`)
                       (ASSUME `i < 9361`))))
    else NO_TAC) THEN
  REMOVE_THEN "H_ATT" (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_O2_mc,SIGN87_EXEC,0x0,
       mldsa_native_libmldsa_gcc12_O2_mc,th)
      (`e:(uarch_event)list`::SIGN87_ATT_ILIST b) 1 THENL
     [REPEAT(CONJ_TAC THENL
        [SIGN_NUMS_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
      FULL_EXISTS_E2_TAC (ref SIGN87_BALLOWED);
      LABEL_TAC "H_ATT" th]);;

let SIGN87_BODY_DISCHARGE_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN87_CASE_TH = ASSUME
  `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 24`;;

let SIGN87_NCASE_TH = ASSUME
  `~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 24)`;;

let SIGN87_LAST_TAC cth =
  SUBGOAL_THEN `i + 1 = mld_sign_natt 9361 24 D` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 9361 24 D`; `~(i + 1 < mld_sign_natt 9361 24 D)`]
    THEN ARITH_TAC;
    DISCH_THEN(fun th -> ASSUME_TAC(EQT_INTRO th))] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `~(i + 1 < mld_sign_natt 9361 24 D)
          ==> (mld_sign_ok_87 skb MU RND <=> P)`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[cth]
          (MP th (ASSUME `~(i + 1 < mld_sign_natt 9361 24 D)`)))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `~(i + 1 < mld_sign_natt 9361 24 D)
          ==> mld_sign_sig_87 skb MU RND = x`) (concl th)
    then FIRST_ASSUM(fun oth ->
           let c = concl oth in
           if c = `mld_sign_ok_87 skb MU RND` ||
              c = `~mld_sign_ok_87 skb MU RND`
           then ASSUME_TAC(REWRITE_RULE[oth]
                 (MP th (ASSUME `~(i + 1 < mld_sign_natt 9361 24 D)`)))
           else NO_TAC)
    else NO_TAC);;

let SIGN87_SUCC_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read X21 s = (if b then x else y)`) (concl th))) THEN
  REWRITE_TAC[SIGN87_CASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 24 ==> P`)
    (concl th))) THEN
  REWRITE_TAC[SIGN87_CASE_TH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 9361 24 D)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> can (term_match []
     `i + 1 < mld_sign_natt 9361 24 D ==> P`) (concl th))) THEN
    REWRITE_TAC[SIGN87_CASE_TH];
    ALL_TAC] THEN
  SIGN87_LAST_TAC SIGN87_CASE_TH THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN87_BODY_DISCHARGE_TAC;;

let SIGN87_MEMSET_TAC allowed n =
  LIBC_PLT_TAC SIGN87_EXEC n THEN
  SIGN_LIBC_CALL_TAC "H_MEMSET" SIGN87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref allowed) (n + 5);;

let SIGN87_KAPPA_TAC =
  SUBGOAL_THEN `7 * i + 7 < 65536` ASSUME_TAC THENL
   [UNDISCH_TAC `i < 9361` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_KAPPA_ZX; SIGN_KAPPA_CMP]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`7 * i`; `7`; `65527`]
                                         SIGN_KAPPA_NEXT)
                               (CONJ (ASSUME `7 * i + 7 < 65536`)
                                     (ARITH_RULE `65527 < 65536`))]);;

let SIGN87_CONT_TAC =
  SUBGOAL_THEN `~(7 * i + 7 = 65527)` ASSUME_TAC THENL
   [UNDISCH_TAC `i + 1 < 9361` THEN ARITH_TAC; ALL_TAC] THEN
  SIGN_PC_SIMP_TAC THEN
  SUBGOAL_THEN `i + 1 < mld_sign_natt 9361 24 D` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match []
           `~(i + 1 < mld_sign_natt 9361 24 D)
            ==> (mld_sign_ok_87 skb MU RND <=> P)`) (concl th)
      then ASSUME_TAC(REWRITE_RULE[SIGN87_NCASE_TH]
            (MP th (ASSUME `~(i + 1 < mld_sign_natt 9361 24 D)`)))
      else NO_TAC) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `~mld_sign_ok_87 skb MU RND ==> P`) (concl th)
      then MP_TAC(MP th (ASSUME `~mld_sign_ok_87 skb MU RND`))
      else NO_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 9361 24 D`; `~(i + 1 < mld_sign_natt 9361 24 D)`;
      `i + 1 < 9361`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i + 1 = mld_sign_natt 9361 24 D)` ASSUME_TAC THENL
   [UNDISCH_TAC `i + 1 < mld_sign_natt 9361 24 D` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `7 * (i + 1) = 7 * i + 7`] THEN
  SIGN87_BODY_DISCHARGE_TAC;;

let SIGN87_EXH_TAC =
  SUBGOAL_THEN `7 * i + 7 = 65527` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(i + 1 < 9361)`; `i < 9361`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIGN_PC_SIMP_TAC THEN
  ARM_STEPS_TAC SIGN87_EXEC (11--16) THEN
  SIGN87_MEMSET_TAC SIGN87_BALLOWED 16 THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 9361 24 D)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mld_sign_natt 9361 24 D <= 9361`; `~(i + 1 < 9361)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SIGN87_LAST_TAC SIGN87_NCASE_TH THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `!i. i < 4627 ==> read (memory :> bytes8 (word_add sig (word i))) s =
                      word_zx(word 0:int64)`) (concl th))) THEN
  REWRITE_TAC[WORD_ZX_0] THEN DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN87_BODY_DISCHARGE_TAC;;

let SIGN87_FAIL_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read X21 s = (if b then x else y)`) (concl th))) THEN
  REWRITE_TAC[SIGN87_NCASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 24 ==> P`)
    (concl th))) THEN
  ARM_STEPS_TAC SIGN87_EXEC (2--10) THEN
  SIGN87_KAPPA_TAC THEN
  ASM_CASES_TAC `i + 1 < 9361` THENL [SIGN87_CONT_TAC; SIGN87_EXH_TAC];;

let SIGN87_BODY_TAC b =
  SIGN87_BODY_INIT_TAC THEN SIGN87_BODY_ATT_TAC b THEN
  ASM_CASES_TAC
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 24` THENL
   [SIGN87_SUCC_TAC; SIGN87_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The epilogue, from join4: the memsets of s2, t0, s1 and the matrix, the   *)
(* inlined zeroing of the 256 bytes of the seed buffer and the check of the  *)
(* canary.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SIGN87_EPIL_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN87_EPIL_TAC =
  SIGN_DROP_TAC SIGN87_DANGER THEN
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC SIGN87_EXEC (1--5) THEN
  SIGN87_MEMSET_TAC SIGN87_MALLOWED 5 THEN
  ARM_STEPS_TAC SIGN87_EXEC (11--15) THEN
  SIGN87_MEMSET_TAC SIGN87_MALLOWED 15 THEN
  ARM_STEPS_TAC SIGN87_EXEC (21--25) THEN
  SIGN87_MEMSET_TAC SIGN87_MALLOWED 25 THEN
  ARM_STEPS_TAC SIGN87_EXEC (31--35) THEN
  SIGN87_MEMSET_TAC SIGN87_MALLOWED 35 THEN
  ARM_STEPS_TAC SIGN87_EXEC (41--51) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC SIGN87_EXEC (52--69) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SIGN_RET_ZX] THEN
  SIGN87_EPIL_DISCHARGE_TAC;;

let SIGN87_MAIN_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `mld_sign_natt 9361 24 D`
   `pc + mldsa87_signature_internal_loop1`
   `pc + mldsa87_signature_internal_join4` (SIGN87_INV b) THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC; SIGN87_PROL_TAC b; SIGN87_BODY_TAC b; SIGN87_EPIL_TAC];;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  SIGN87_START_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    SIGN87_MAIN_TAC 5216;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    SIGN87_MAIN_TAC 5232]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
