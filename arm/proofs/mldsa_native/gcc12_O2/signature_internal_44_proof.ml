(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with the secret key, all the attempts (ML-DSA-44): the proof (see *)
(* signature_internal_44_spec.ml).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/signature_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/unpack_sk_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/H_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_uniform_gamma1_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_yvec_eager_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_caddq_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_decompose_pack_w1_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_challenge_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_add_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pack_sig_z_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pack_sig_c_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pack_sig_h_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;

let SIGN44_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The proof is in parts, each a FULL lemma for a segment of the code (sp is *)
(* the stack pointer in the loop, sp0 = sp - 4496 the bottom of the frames   *)
(* of the callees, and B the base of the buffers, 32-byte aligned). The loop *)
(* over z up to an index m (ZPRE), the exit at a z whose norm check fails    *)
(* (ZFAIL), the loop over the rows of w0 up to a row m (RPRE), the exits at  *)
(* a row whose first or second check fails (RFAIL1, RFAIL2), the packing of  *)
(* c~ and the hints (TAIL), the cleanup and the decision (CLEAN), and the    *)
(* start of an attempt up to the NTT of the challenge (HEAD). The attempt    *)
(* (ATT) follows from them, with one path for each kind of result r of       *)
(* mld_sign_attempt_declass: r < 4 (z_r fails), 4 <= r < 12 (the check r - 4 *)
(* of the rows fails), 12 (too many hints) and 13 (success).                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check.                                                               *)
(* ------------------------------------------------------------------------- *)

let SIGN44_ZPRE_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_zpre.
        !e m sig B sp s1h cphat y pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ m <= 4 /\
          (!i. i < m
               ==> mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 130994) =
                   word 0) /\
          PAIRWISE nonoverlapping [(sig,2420); (B,44064); (sp,160)] /\
          ALLPAIRS nonoverlapping [(sig,2420); (B,44064)]
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa44_signature_internal_loop2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 20480) /\
                    read X20 s = word_add B (word 40960) /\
                    read X23 s = word_add B (word 41984) /\
                    read X22 s = word 0 /\
                    read X24 s = word_add B (word 24576) /\
                    read X28 s = word_add B (word 36864) /\
                    read (memory :> bytes64 (word_add sp (word 96))) s = sig /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(41984 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(24576 + 4 * j)))) s =
                             y j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(36864 + 4 * j)))) s =
                             s1h j) /\
                    read events s = e)
               (\s. read PC s =
                    (if m < 4
                     then word(pc + mldsa44_signature_internal_loop2)
                     else word(pc + mldsa44_signature_internal_loop2_exit1)) /\
                    read X22 s = word m /\
                    read X24 s = word_add B (word(24576 + 1024 * m)) /\
                    read X28 s = word_add B (word(36864 + 1024 * m)) /\
                    (!t. t < 576 * m
                         ==> read (memory :> bytes8
                                    (word_add sig (word(32 + t)))) s =
                             mld_polyvec_pack 576 mld_polyz_pack_17
                              (mld_polyvec (mld_sign_z s1h cphat y)) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_zpre m sig B sp mc pc /\
                       memaccess_inbounds e2
                        [sig,2420; B,44064; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,2420; B,44064]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X22; X24; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 20480),1024);
                  memory :> bytes(word_add B (word 40960),1024);
                  memory :> bytes(word_add sig (word 32),2304)])`;;

let SIGN44_ZALLOWED =
  [`pc:num`; `sig:int64`; `B:int64`; `sp:int64`; `mc:int64`; `i:num`];;

let SIGN44_ZCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN44_EXEC name ilist
    SIGN44_ZALLOWED n;;

let SIGN44_COPY_TAC doff soff f n zs s =
  MP_TAC(SPECL [`B:int64`; doff; soff; `i:num`; n; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 4` THEN ARITH_TAC;
    DISCH_TAC];;

let SIGN44_ZPRE_INV =
 `\i s. read SP s = sp /\
        read X19 s = word_add B (word 20480) /\
        read X20 s = word_add B (word 40960) /\
        read X23 s = word_add B (word 41984) /\
        read X22 s = word i /\
        read X24 s = word_add B (word(24576 + 1024 * i)) /\
        read X28 s = word_add B (word(36864 + 1024 * i)) /\
        read (memory :> bytes64 (word_add sp (word 96))) s = sig /\
        read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
        mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add B (word(41984 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 1024
             ==> read (memory :> bytes32 (word_add B (word(24576 + 4 * j))))
                   s = y j) /\
        (!j. j < 1024
             ==> read (memory :> bytes32 (word_add B (word(36864 + 4 * j))))
                   s = s1h j) /\
        (!t. t < 576 * i
             ==> read (memory :> bytes8 (word_add sig (word(32 + t)))) s =
                 mld_polyvec_pack 576 mld_polyz_pack_17
                  (mld_polyvec (mld_sign_z s1h cphat y)) t)`;;

let SIGN44_ZBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--4) THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(36864 + 1024 * i)),
                                         1024)) s4` THEN
  LIBC_PLT_TAC SIGN44_EXEC 4 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN44_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN44_ZALLOWED) 9 THEN
  SIGN44_COPY_TAC `40960` `36864` `s1h:num->int32` `1024` `zs:num`
    `s9:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (10--12) THEN
  SIGN44_ZCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s1h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC SIGN44_EXEC (14--15) THEN
  SIGN44_ZCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat`;
    `pc:num`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC SIGN44_EXEC (17--20) THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(24576 + 1024 * i)),
                                          1024)) s20` THEN
  LIBC_PLT_TAC SIGN44_EXEC 20 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN44_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN44_ZALLOWED) 25 THEN
  SIGN44_COPY_TAC `20480` `24576` `y:num->int32` `1024` `zs':num`
    `s25:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (26--28) THEN
  SIGN44_ZCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat)`;
    `mld_poly_of y i`; `pc:num`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC SIGN44_EXEC (30--31) THEN
  SIGN44_ZCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_add
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat))
      (mld_poly_of y i)`;
    `pc:num`; `read X30 s`] 32 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (33--36) THEN
  SIGN44_ZCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_z s1h cphat y i`; `read X1 s`;
    `pc:num`; `read X30 s`] 37 THEN
  SUBGOAL_THEN
   `mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 130994) = word 0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 130994) = word 0`]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (38--45) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i /\
    word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
    word(i + 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 4` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i < 4` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 4` THEN ARITH_TAC; ALL_TAC] THEN
  SIGN44_ZCALL_TAC "H_PZ"
   [`read X0 s`; `read X1 s`; `mld_sign_z s1h cphat y i`; `i:num`;
    `pc:num`; `read X30 s`] 46 THEN
  ARM_STEPS_TAC SIGN44_EXEC (47--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_17`; `576`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_17_LOCAL] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN44_ZPRE = prove
 (SIGN44_ZPRE_STMT,
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
    MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PZ" THEN
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
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa44_signature_internal_loop2`
     `if m < 4 then pc + mldsa44_signature_internal_loop2
      else pc + mldsa44_signature_internal_loop2_exit1`
     SIGN44_ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN44_ZBODY_TAC;
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
(* the cleanup (join2) with x22 = -1.                                        *)
(* ------------------------------------------------------------------------- *)

let SIGN44_ZFAIL_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_zfail.
        !e i sig B sp s1h cphat y pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ i < 4 /\
          ~(mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 130994) =
            word 0) /\
          PAIRWISE nonoverlapping [(sig,2420); (B,44064); (sp,160)] /\
          ALLPAIRS nonoverlapping [(sig,2420); (B,44064)]
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa44_signature_internal_loop2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 20480) /\
                    read X20 s = word_add B (word 40960) /\
                    read X23 s = word_add B (word 41984) /\
                    read X22 s = word i /\
                    read X24 s = word_add B (word(24576 + 1024 * i)) /\
                    read X28 s = word_add B (word(36864 + 1024 * i)) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(41984 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(24576 + 4 * j)))) s =
                             y j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(36864 + 4 * j)))) s =
                             s1h j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa44_signature_internal_join2) /\
                    read X22 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_zfail i sig B sp mc pc /\
                       memaccess_inbounds e2
                        [sig,2420; B,44064; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,2420; B,44064]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X22; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 20480),1024);
                  memory :> bytes(word_add B (word 40960),1024)])`;;

let SIGN44_ZFAIL_ALLOWED =
  [`pc:num`; `sig:int64`; `B:int64`; `sp:int64`; `mc:int64`; `i:num`];;

let SIGN44_ZFCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN44_EXEC name ilist
    SIGN44_ZFAIL_ALLOWED n;;

let SIGN44_ZFCOPY_TAC doff soff f n zs s =
  MP_TAC(SPECL [`B:int64`; doff; soff; `i:num`; n; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 4` THEN ARITH_TAC; DISCH_TAC];;

let SIGN44_ZFAIL = prove
 (SIGN44_ZFAIL_STMT,
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
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--4) THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(36864 + 1024 * i)),
                                         1024)) s4` THEN
  LIBC_PLT_TAC SIGN44_EXEC 4 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN44_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN44_ZFAIL_ALLOWED) 9 THEN
  SIGN44_ZFCOPY_TAC `40960` `36864` `s1h:num->int32` `1024` `zs:num`
    `s9:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (10--12) THEN
  SIGN44_ZFCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s1h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC SIGN44_EXEC (14--15) THEN
  SIGN44_ZFCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat`;
    `pc:num`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC SIGN44_EXEC (17--20) THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(24576 + 1024 * i)),
                                          1024)) s20` THEN
  LIBC_PLT_TAC SIGN44_EXEC 20 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN44_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN44_ZFAIL_ALLOWED) 25 THEN
  SIGN44_ZFCOPY_TAC `20480` `24576` `y:num->int32` `1024` `zs':num`
    `s25:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (26--28) THEN
  SIGN44_ZFCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat)`;
    `mld_poly_of y i`; `pc:num`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC SIGN44_EXEC (30--31) THEN
  SIGN44_ZFCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_add
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat))
      (mld_poly_of y i)`;
    `pc:num`; `read X30 s`] 32 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (33--36) THEN
  SIGN44_ZFCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_z s1h cphat y i`; `read X1 s`;
    `pc:num`; `read X30 s`] 37 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  ARM_STEPS_TAC SIGN44_EXEC [38] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 130994) =
      word 0)`]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (39--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass, leaving the rows of x of the hints.                                 *)
(* ------------------------------------------------------------------------- *)

let SIGN44_RPRE_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rpre.
        !e m B sp w s2h t0h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ m <= 4 /\
          (!j. j < m
               ==> mld_poly_chknorm
                    (mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat j)
                    (word 95154) = word 0 /\
                   mld_poly_chknorm (mld_sign_ct0 t0h cphat j) (word 95232) =
                   word 0) /\
          nonoverlapping (B,44064) (sp,160) /\
          ALL (nonoverlapping (B,44064))
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_internal_loop2_exit1) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 20480) /\
                    read X23 s = word_add B (word 41984) /\
                    read X25 s = word_add B (word 16384) /\
                    read (memory :> bytes64 (word_add sp (word 112))) s =
                    word_add B (word 32768) /\
                    read (memory :> bytes64 (word_add sp (word 152))) s =
                    word_add B (word 28672) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(41984 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(28672 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(32768 + 4 * j)))) s =
                             t0h j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(16384 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_88 w j) /\
                    read events s = e)
               (\s. read PC s =
                    (if m < 4
                     then word(pc + mldsa44_signature_internal_loop3)
                     else word(pc + mldsa44_signature_internal_loop3_exit1)) /\
                    read X22 s = word_add B (word(16384 + 1024 * m)) /\
                    read X24 s = word_add B (word(28672 + 1024 * m)) /\
                    read X28 s = word_add B (word(32768 + 1024 * m)) /\
                    (!j. j < 256 * m
                         ==> read (memory :> bytes32
                                    (word_add B (word(16384 + 4 * j)))) s =
                             mld_sign_hint_x 4 mld_poly_decompose_lo_88 w s2h
                              t0h cphat j) /\
                    (!j. 256 * m <= j /\ j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(16384 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_88 w j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rpre m B sp mc pc /\
                       memaccess_inbounds e2
                        [B,44064; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [B,44064]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X22; X24; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 20480),1024);
                  memory :> bytes(word_add B (word 16384),4096)])`;;

let SIGN44_RALLOWED =
  [`pc:num`; `B:int64`; `sp:int64`; `mc:int64`; `i:num`];;

let SIGN44_RCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN44_EXEC name ilist
    SIGN44_RALLOWED n;;

let SIGN44_RCOPY_TAC soff f zs s =
  MP_TAC(SPECL [`B:int64`; `20480`; soff; `i:num`; `1024`; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 4` THEN ARITH_TAC;
    DISCH_TAC];;

let SIGN44_RPRE_INV =
 `\i s. read SP s = sp /\
        read X19 s = word_add B (word 20480) /\
        read X23 s = word_add B (word 41984) /\
        read X22 s = word_add B (word(16384 + 1024 * i)) /\
        read X24 s = word_add B (word(28672 + 1024 * i)) /\
        read X28 s = word_add B (word(32768 + 1024 * i)) /\
        read (memory :> bytes64 (word_add sp (word 112))) s =
        word_add B (word 32768) /\
        read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
        mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add B (word(41984 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 1024
             ==> read (memory :> bytes32 (word_add B (word(28672 + 4 * j))))
                   s = s2h j) /\
        (!j. j < 1024
             ==> read (memory :> bytes32 (word_add B (word(32768 + 4 * j))))
                   s = t0h j) /\
        (!j. j < 256 * i
             ==> read (memory :> bytes32 (word_add B (word(16384 + 4 * j))))
                   s =
                 mld_sign_hint_x 4 mld_poly_decompose_lo_88 w s2h t0h cphat
                  j) /\
        (!j. 256 * i <= j /\ j < 1024
             ==> read (memory :> bytes32 (word_add B (word(16384 + 4 * j))))
                   s = mld_polyvec_map mld_poly_decompose_lo_88 w j)`;;

let SIGN44_RTEST = prove
 (`!j. (28672 + 1024 * j) + 1024 = 32768 <=> j + 1 = 4`,
  ARITH_TAC);;

let SIGN44_RFSLICE_TAC s =
  MP_TAC(SPECL [`B:int64`; `16384`; `1024`; `mld_poly_decompose_lo_88`;
                `w:num->int32`; `i:num`; s] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; s]
             `!j. 256 * i <= j /\ j < 1024
                  ==> read (memory :> bytes32
                             (word_add B (word (16384 + 4 * j))))
                        s = Q j`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 4` THEN ARITH_TAC; STRIP_TAC];;

let SIGN44_RFCOPY_TAC soff f zs s =
  MP_TAC(SPECL [`B:int64`; `20480`; soff; `i:num`; `1024`; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 4` THEN ARITH_TAC; DISCH_TAC];;

let SIGN44_RBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 4` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 4` THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--4) THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(28672 + 1024 * i)),
                                         1024)) s4` THEN
  LIBC_PLT_TAC SIGN44_EXEC 4 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN44_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN44_RALLOWED) 9 THEN
  SIGN44_RFCOPY_TAC `28672` `s2h:num->int32` `zs:num` `s9:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (10--12) THEN
  SIGN44_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s2h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC SIGN44_EXEC (14--15) THEN
  SIGN44_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat`;
    `pc:num`; `read X30 s`] 16 THEN
  SIGN44_RFSLICE_TAC `s16:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (17--19) THEN
  SIGN44_RCALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`;
    `mld_poly_decompose_lo_88 (mld_poly_of w i)`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat)`;
    `pc:num`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC SIGN44_EXEC (21--22) THEN
  SIGN44_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_sub (mld_poly_decompose_lo_88 (mld_poly_of w i))
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat))`;
    `pc:num`; `read X30 s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (24--27) THEN
  SIGN44_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 28 THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat i)
      (word 95154) = word 0`]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (29--33) THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(32768 + 1024 * i)),
                                          1024)) s33` THEN
  LIBC_PLT_TAC SIGN44_EXEC 33 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN44_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN44_RALLOWED) 38 THEN
  SIGN44_RFCOPY_TAC `32768` `t0h:num->int32` `zs':num` `s38:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (39--41) THEN
  SIGN44_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of t0h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC SIGN44_EXEC (43--44) THEN
  SIGN44_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat`;
    `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC SIGN44_EXEC (46--47) THEN
  SIGN44_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat)`;
    `pc:num`; `read X30 s`] 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (49--52) THEN
  SIGN44_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_ct0 t0h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 53 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 95232) = word 0`]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (54--57) THEN
  SIGN44_RCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat i`;
    `mld_sign_ct0 t0h cphat i`; `pc:num`; `read X30 s`] 58 THEN
  ARM_STEPS_TAC SIGN44_EXEC (59--64) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PTR_LOOP_TEST_TAC THEN REWRITE_TAC[SIGN44_RTEST] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN44_RPRE = prove
 (SIGN44_RPRE_STMT,
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
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa44_signature_internal_loop3`
     `if m < 4 then pc + mldsa44_signature_internal_loop3
      else pc + mldsa44_signature_internal_loop3_exit1`
     SIGN44_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN44_RBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SIGN_BETA_ALL_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0;
                    WORD_ADD_0] THEN
    SIGN_CONCRETE_DISCHARGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exits from the loop over the rows at a row whose first check (w0 - c  *)
(* s2) or second check (c t0) fails.                                         *)
(* ------------------------------------------------------------------------- *)

let SIGN44_RFAIL1_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rfail1.
        !e i B sp w s2h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ i < 4 /\
          ~(mld_poly_chknorm
             (mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat i)
             (word 95154) = word 0) /\
          nonoverlapping (B,44064) (sp,160) /\
          ALL (nonoverlapping (B,44064))
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa44_signature_internal_loop3) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 20480) /\
                    read X23 s = word_add B (word 41984) /\
                    read X22 s = word_add B (word(16384 + 1024 * i)) /\
                    read X24 s = word_add B (word(28672 + 1024 * i)) /\
                    read X28 s = word_add B (word(32768 + 1024 * i)) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(41984 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(28672 + 4 * j)))) s =
                             s2h j) /\
                    (!j. 256 * i <= j /\ j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(16384 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_88 w j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa44_signature_internal_join2) /\
                    read X22 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rfail1 i B sp mc pc /\
                       memaccess_inbounds e2
                        [B,44064; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [B,44064]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X22; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 20480),1024);
                  memory :> bytes(word_add B (word 16384),4096)])`;;

let SIGN44_RFAIL_SETUP_TAC tmpl vars =
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
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]);;

(*** The first part of a row, up to the norm check of w0 - c s2 ***)

let SIGN44_ROW_HEAD_TAC =
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--4) THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(28672 + 1024 * i)),
                                         1024)) s4` THEN
  LIBC_PLT_TAC SIGN44_EXEC 4 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN44_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN44_RALLOWED) 9 THEN
  SIGN44_RFCOPY_TAC `28672` `s2h:num->int32` `zs:num` `s9:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (10--12) THEN
  SIGN44_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s2h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC SIGN44_EXEC (14--15) THEN
  SIGN44_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat`;
    `pc:num`; `read X30 s`] 16 THEN
  SIGN44_RFSLICE_TAC `s16:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (17--19) THEN
  SIGN44_RCALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`;
    `mld_poly_decompose_lo_88 (mld_poly_of w i)`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat)`;
    `pc:num`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC SIGN44_EXEC (21--22) THEN
  SIGN44_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_sub (mld_poly_decompose_lo_88 (mld_poly_of w i))
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat))`;
    `pc:num`; `read X30 s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (24--27) THEN
  SIGN44_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 28 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV)));;

let SIGN44_RFAIL1 = prove
 (SIGN44_RFAIL1_STMT,
  SIGN44_RFAIL_SETUP_TAC
   `\(i:num) (B:int64) (sp:int64) (mc:int64) (pc:num).
     f_ev_rfail1 i B sp mc pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `B:int64`; `sp:int64`; `w:num->int32`;
    `s2h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN44_ROW_HEAD_TAC THEN
  ARM_STEPS_TAC SIGN44_EXEC [29] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat i)
       (word 95154) = word 0)`]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (30--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SIGN44_RFAIL2_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rfail2.
        !e i B sp w s2h t0h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ i < 4 /\
          mld_poly_chknorm
           (mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat i)
           (word 95154) = word 0 /\
          ~(mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 95232) =
            word 0) /\
          nonoverlapping (B,44064) (sp,160) /\
          ALL (nonoverlapping (B,44064))
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa44_signature_internal_loop3) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 20480) /\
                    read X23 s = word_add B (word 41984) /\
                    read X22 s = word_add B (word(16384 + 1024 * i)) /\
                    read X24 s = word_add B (word(28672 + 1024 * i)) /\
                    read X28 s = word_add B (word(32768 + 1024 * i)) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(41984 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(28672 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(32768 + 4 * j)))) s =
                             t0h j) /\
                    (!j. 256 * i <= j /\ j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(16384 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_88 w j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa44_signature_internal_join2) /\
                    read X22 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rfail2 i B sp mc pc /\
                       memaccess_inbounds e2
                        [B,44064; sp,160; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [B,44064]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X22; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 20480),1024);
                  memory :> bytes(word_add B (word 16384),4096)])`;;

let SIGN44_RFAIL2 = prove
 (SIGN44_RFAIL2_STMT,
  SIGN44_RFAIL_SETUP_TAC
   `\(i:num) (B:int64) (sp:int64) (mc:int64) (pc:num).
     f_ev_rfail2 i B sp mc pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `B:int64`; `sp:int64`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN44_ROW_HEAD_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_88 w s2h cphat i)
      (word 95154) = word 0`]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (29--33) THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(32768 + 1024 * i)),
                                          1024)) s33` THEN
  LIBC_PLT_TAC SIGN44_EXEC 33 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN44_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN44_RALLOWED) 38 THEN
  SIGN44_RFCOPY_TAC `32768` `t0h:num->int32` `zs':num` `s38:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (39--41) THEN
  SIGN44_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of t0h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC SIGN44_EXEC (43--44) THEN
  SIGN44_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat`;
    `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC SIGN44_EXEC (46--47) THEN
  SIGN44_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat)`;
    `pc:num`; `read X30 s`] 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (49--52) THEN
  SIGN44_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_ct0 t0h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 53 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  ARM_STEPS_TAC SIGN44_EXEC [54] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 95232) =
      word 0)`]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (55--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints, whose result is the value of x22 for  *)
(* the decision.                                                             *)
(* ------------------------------------------------------------------------- *)

let SIGN44_TAIL_STMT =
 `?f_tail.
    !e sig B sp0 ct (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 sp0 /\
      PAIRWISE nonoverlapping
       [(sig,2420); (B,44064); (word_add sp0 (word 4496),160); (sp0,4496)] /\
      ALL (nonoverlapping (word pc,libmldsa_size))
       [(sig,2420); (B,44064); (sp0,4496)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_mc /\
                read PC s = word(pc + mldsa44_signature_internal_loop3_exit1) /\
                read SP s = word_add sp0 (word 4496) /\
                read X19 s = word_add B (word 20480) /\
                read X26 s = word_add B (word 44032) /\
                read X25 s = word_add B (word 16384) /\
                read (memory :> bytes64 (word_add sp0 (word 4592))) s = sig /\
                read (memory :> bytes64 (word_add sp0 (word 4616))) s =
                word_add B (word 43008) /\
                (!j. j < 32
                     ==> read (memory :> bytes8
                                (word_add B (word(44032 + j)))) s = ct j) /\
                (!j. j < 1024
                     ==> read (memory :> bytes32
                                (word_add B (word(16384 + 4 * j)))) s = x j) /\
                (!j. j < 768
                     ==> read (memory :> bytes8
                                (word_add B (word(43008 + j)))) s = b j) /\
                read events s = e)
           (\s. read PC s = word(pc + mldsa44_signature_internal_join2) /\
                read X22 s =
                word_zx(mld_pack_hints_ret 80 4
                         (mld_polyvec_make_hint_88 x b)) /\
                (!j. j < 32
                     ==> read (memory :> bytes8 (word_add sig (word j))) s =
                         ct j) /\
                (mld_pack_hints_ret 80 4 (mld_polyvec_make_hint_88 x b) =
                 word 0
                 ==> !t. t < 84
                         ==> read (memory :> bytes8
                                    (word_add sig (word(2336 + t)))) s =
                             mld_pack_hints 80 4
                              (mld_polyvec_make_hint_88 x b) t) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_tail sig B sp0 pc x b /\
                   memaccess_inbounds e2
                    [sig,2420; B,44064; word_add sp0 (word 4496),160; sp0,4496]
                    [sig,2420; B,44064; sp0,4496]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X22; X30] ,,
            MAYCHANGE
             [memory :> bytes(sig,32);
              memory :> bytes(word_add sig (word 2336),84);
              memory :> bytes(word_add B (word 20480),1024);
              memory :> bytes(sp0,4496)])`;;

let SIGN44_TAIL = prove
 (SIGN44_TAIL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PH" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (B:int64) (sp0:int64) (pc:num) (x:num->int32) (b:num->byte).
     f_ev_tail sig B sp0 pc x b:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `B:int64`; `sp0:int64`;
    `ct:num->byte`; `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; C_RETURN; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--4) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN44_EXEC "H_PC"
   [`read X0 s`; `read X1 s`; `ct:num->byte`; `pc:num`; `read X30 s`]
   [`pc:num`; `sig:int64`; `B:int64`; `sp0:int64`; `x:num->int32`;
    `b:num->byte`] 5 THEN
  ARM_STEPS_TAC SIGN44_EXEC (6--10) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN44_EXEC "H_PH"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `x:num->int32`;
    `b:num->byte`; `pc:num`; `read SP s`; `read X30 s`]
   [`pc:num`; `sig:int64`; `B:int64`; `sp0:int64`; `x:num->int32`;
    `b:num->byte`] 11 THEN
  ARM_STEPS_TAC SIGN44_EXEC [12] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt and the test of x22: to join4 on success, else  *)
(* to the update of kappa.                                                   *)
(* ------------------------------------------------------------------------- *)

let SIGN44_CLEAN_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_clean.
        !e ok B sp pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\
          nonoverlapping (B,44064) (sp,160) /\
          ALL (nonoverlapping (B,44064))
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa44_signature_internal_join2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 20480) /\
                    read X20 s = word_add B (word 40960) /\
                    read X22 s = (if ok then word 0 else word 4294967295) /\
                    read X23 s = word_add B (word 41984) /\
                    read X26 s = word_add B (word 44032) /\
                    read X25 s = word_add B (word 16384) /\
                    read X27 s = word_add B (word 24576) /\
                    read (memory :> bytes64 (word_add sp (word 120))) s =
                    word_add B (word 43008) /\
                    read (memory :> bytes64 (word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s =
                    (if ok then word(pc + mldsa44_signature_internal_join4)
                     else word(pc + mldsa44_signature_internal_loop1_next1)) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_clean ok B sp mf pc /\
                       memaccess_inbounds e2
                        [B,44064; sp,160; word(pc + got_memset),8; ea,el]
                        [B,44064]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X24; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 16384),4096);
                  memory :> bytes(word_add B (word 20480),4096);
                  memory :> bytes(word_add B (word 24576),4096);
                  memory :> bytes(word_add B (word 40960),1024);
                  memory :> bytes(word_add B (word 41984),1024);
                  memory :> bytes(word_add B (word 43008),768);
                  memory :> bytes(word_add B (word 44032),32)])`;;

let SIGN44_CLEAN_MEMSET_TAC n =
  LIBC_PLT_TAC SIGN44_EXEC n THEN
  SIGN_LIBC_CALL_TAC "H_MEMSET" SIGN44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref [`pc:num`; `ok:bool`; `B:int64`; `sp:int64`; `mf:int64`]) (n + 5);;

let SIGN44_CLEAN = prove
 (SIGN44_CLEAN_STMT,
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
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  BOOL_CASES_TAC `ok:bool` THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--4) THEN
  SIGN44_CLEAN_MEMSET_TAC 4 THEN
  ARM_STEPS_TAC SIGN44_EXEC (10--13) THEN SIGN44_CLEAN_MEMSET_TAC 13 THEN
  ARM_STEPS_TAC SIGN44_EXEC (19--22) THEN SIGN44_CLEAN_MEMSET_TAC 22 THEN
  ARM_STEPS_TAC SIGN44_EXEC (28--32) THEN SIGN44_CLEAN_MEMSET_TAC 32 THEN
  ARM_STEPS_TAC SIGN44_EXEC (38--41) THEN SIGN44_CLEAN_MEMSET_TAC 41 THEN
  ARM_STEPS_TAC SIGN44_EXEC (47--50) THEN SIGN44_CLEAN_MEMSET_TAC 50 THEN
  ARM_STEPS_TAC SIGN44_EXEC (56--58) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt: y, w, w1 and its packing, c~ with the inlined    *)
(* SHAKE256 calls, the challenge and its NTT.                                *)
(* ------------------------------------------------------------------------- *)

let SIGN44_HEAD_STMT =
 `!mf mc ea el ev.
    memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
    ==> ?f_head.
        !e B sp0 A mu rhop n C guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ n < 16382 /\
          num_of_bytelist(list_of_seq
           (mld_sign_ctilde 4 192 mu
             (mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
               (mld_sign_w 4 A
                 (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)))))
           32) = C /\
          mld_poly_challenge_terminates 39 32 C /\
          PAIRWISE nonoverlapping
           [(B,44064); (word_add sp0 (word 4496),160);
            (word_add sp0 (word 48744),208);
            (sp0,4496)] /\
          ALLPAIRS nonoverlapping
           [(B,44064); (word_add sp0 (word 48744),208);
            (sp0,4496)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa44_signature_internal_loop1) /\
                    read SP s = word_add sp0 (word 4496) /\
                    read X19 s = word_add B (word 20480) /\
                    read X21 s = word_add sp0 (word 48744) /\
                    read X23 s = word_add B (word 41984) /\
                    read X26 s = word_add B (word 44032) /\
                    read X25 s = word_add B (word 16384) /\
                    read X27 s = word_add B (word 24576) /\
                    read (memory :> bytes16 (word_add sp0 (word 4604))) s =
                    word(4 * n) /\
                    read (memory :> bytes64 (word_add sp0 (word 4616))) s =
                    word_add B (word 43008) /\
                    read (memory :> bytes64 (word_add sp0 (word 4624))) s =
                    word_add B (word 43776) /\
                    read (memory :> bytes64 (word_add sp0 (word 4632))) s = B /\
                    read (memory :> bytes64 (word_add sp0 (word 4640))) s =
                    word_add B (word 36864) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4096
                         ==> read (memory :> bytes32
                                    (word_add B (word(4 * j)))) s = A j) /\
                    read (memory :> bytes(word_add B (word 43904),64)) s = mu /\
                    read (memory :> bytes(word_add B (word 43968),64)) s =
                    rhop /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa44_signature_internal_loop2) /\
                    read X22 s = word 0 /\
                    read X24 s = word_add B (word 24576) /\
                    read X28 s = word_add B (word 36864) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(24576 + 4 * j)))) s =
                             mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)
                              j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(16384 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_88
                              (mld_sign_w 4 A
                                (mld_sign_y mld_poly_uniform_gamma1_17 rhop
                                  (4 * n))) j) /\
                    (!j. j < 768
                         ==> read (memory :> bytes8
                                    (word_add B (word(43008 + j)))) s =
                             mld_sign_w1
                              (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
                              192
                              (mld_sign_w 4 A
                                (mld_sign_y mld_poly_uniform_gamma1_17 rhop
                                  (4 * n))) j) /\
                    read (memory :> bytes(word_add B (word 44032),32)) s = C /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(41984 + 4 * j)))) s =
                             mld_poly_ntt (mld_poly_challenge 39 32 C) j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_head B sp0 guard mf mc pc C /\
                       memaccess_inbounds e2
                        [B,44064; word_add sp0 (word 4496),160;
                         word_add sp0 (word 48744),208;
                         sp0,4496;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [B,44064; word_add sp0 (word 48744),208;
                         sp0,4496]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X22; X24; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 16384),4096);
                  memory :> bytes(word_add B (word 20480),4096);
                  memory :> bytes(word_add B (word 24576),4096);
                  memory :> bytes(word_add B (word 41984),1024);
                  memory :> bytes(word_add B (word 43008),768);
                  memory :> bytes(word_add B (word 44032),32);
                  memory :> bytes(word_add sp0 (word 48744),208);
                  memory :> bytes(sp0,4496)])`;;

let SIGN44_W1 =
 `mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
   (mld_sign_w 4 A (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)))`;;

let SIGN44_W1NUM = mk_comb(`num_of_bytelist`,
  list_mk_comb(`list_of_seq:(num->byte)->num->(byte)list`,[SIGN44_W1; `768`]));;

let SIGN44_ABSORBED =
  list_mk_comb(`mld_keccak_absorb`,
    [`136`; `word 0:1600 word`; `0`; `832`;
     mk_binop `(+):num->num->num` `mu:num`
      (mk_binop `( * ):num->num->num` `2 EXP 512` SIGN44_W1NUM)]);;

let SIGN44_S2 = mk_comb(`FST:(1600 word#num)->1600 word`,SIGN44_ABSORBED);;

let SIGN44_S3 =
  list_mk_comb(`mld_keccak_finalize`,[`136`; `31`; SIGN44_S2; `16`]);;

let SIGN44_HCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN44_EXEC name ilist
   [`pc:num`; `B:int64`; `sp0:int64`; `guard:int64`; `mf:int64`; `mc:int64`;
    `C:num`] n;;

let SIGN44_HEAD = prove
 (SIGN44_HEAD_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th)
     "H_GAMMA" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_CHAL"
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memcpy_full_contract mc ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th) "H_YVEC"
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
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
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_WORD_ZX_16_32_64]) THEN
  SIGN44_HCALL_TAC "H_GAMMA"
   [`read X0 s`; `read X1 s`; `rhop:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_Y_KAPPA]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (7--11) THEN
  SIGN44_HCALL_TAC "H_YVEC"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `A:num->int32`;
    `mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)`;
    `pc:num`; `read SP s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC SIGN44_EXEC (13--14) THEN
  SIGN44_HCALL_TAC "H_CADDQ"
   [`read X0 s`;
    `mld_polyvec_map mld_poly_invntt_tomont
      (mld_polyvec_matrix_pointwise_montgomery 4 A
        (mld_polyvec_map mld_poly_ntt
          (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n))))`;
    `pc:num`; `read SP s`; `read X30 s`] 15 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (16--20) THEN
  SIGN44_HCALL_TAC "H_DEC"
   [`read X0 s`; `read X1 s`;
    `mld_sign_w 4 A (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n))`;
    `read X2 s`; `pc:num`; `read SP s`; `read X30 s`] 21 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w1]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (22--23) THEN
  SIGN44_HCALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 24 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (25--28) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 48744):int64` THEN
  SIGN44_HCALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `64`; `word 0:1600 word`; `0`; `mu:num`;
    `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 768 ==> read (memory :> bytes8
         (word_add B (word (43008 + j)))) s = f j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  MLD_H_BOUND_TAC `word_add B (word 43904):int64` THEN
  ARM_STEPS_TAC SIGN44_EXEC (30--33) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 48744):int64` THEN
  SIGN44_HCALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `768`;
    `FST(mld_keccak_absorb 136 (word 0) 0 64 mu)`; `64`; SIGN44_W1NUM;
    `pc:num`; `read SP s`; `read X30 s`] 34 THEN
  MP_TAC(SPECL [`64`; `768`; `mu:num`; SIGN44_W1NUM]
               MLD_SHAKE256_ABSORB_APPEND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV SIGN_NUMERAL_CONV) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(CONV_RULE SIGN_NUMERAL_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (35--36) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 48744):int64` THEN
  MLD_H_GUARD_ADDR_TAC THEN
  SIGN44_HCALL_TAC "H_FINALIZE"
   [`read X0 s`; SIGN44_S2; `16`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 37 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN44_EXEC (38--41) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 48744):int64` THEN
  SIGN44_HCALL_TAC "H_SQUEEZE"
   [`read X0 s`; `32`; `read X2 s`; SIGN44_S3; `136`;
    `pc:num`; `read SP s`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC SIGN44_EXEC (43--44) THEN
  SIGN44_HCALL_TAC "H_RELEASE" [`read X0 s`; `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC SIGN44_EXEC (46--57) THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add B (word 44032),32)) s57 = C`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde; mld_shake256_byte; mld_shake256_state;
                MLD_KECCAK_ABSORB_SND] THEN
    CONV_TAC SIGN_NUMERAL_CONV THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
   `read (memory :> bytes (word_add B (word 44032),32)) s57 =
    num_of_bytelist l`) (concl th))) THEN
  SIGN44_HCALL_TAC "H_CHAL"
   [`read X0 s`; `read X1 s`; `C:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 58 THEN
  ARM_STEPS_TAC SIGN44_EXEC (59--62) THEN
  SIGN44_HCALL_TAC "H_NTT"
   [`read X0 s`; `mld_poly_challenge 39 32 C`; `pc:num`; `read X30 s`] 63 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt, from loop1 to join4 or loop1_next1, with the events a    *)
(* function of the declassified record (C,r,x,b).                            *)
(* ------------------------------------------------------------------------- *)

let SIGN44_ATT_STMT =
 `!mf mc ea el ev.
    memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
    ==> ?f_att.
        !e sig B sp0 A s1h s2h t0h mu rhop n C r x b guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ n < 16382 /\
          mld_sign_attempt_declass 4 4 32 39 mld_poly_uniform_gamma1_17
           130994 95154 95232 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
           192 mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80
           A s1h s2h t0h mu rhop (4 * n) = (C,r,x,b) /\
          mld_poly_challenge_terminates 39 32 C /\
          PAIRWISE nonoverlapping
           [(sig,2420); (B,44064); (word_add sp0 (word 4496),160);
            (word_add sp0 (word 48744),208);
            (sp0,4496)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (B,44064); (word_add sp0 (word 48744),208);
            (sp0,4496)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word(pc + mldsa44_signature_internal_loop1) /\
                    read SP s = word_add sp0 (word 4496) /\
                    read X19 s = word_add B (word 20480) /\
                    read X20 s = word_add B (word 40960) /\
                    read X21 s = word_add sp0 (word 48744) /\
                    read X23 s = word_add B (word 41984) /\
                    read X26 s = word_add B (word 44032) /\
                    read X25 s = word_add B (word 16384) /\
                    read X27 s = word_add B (word 24576) /\
                    read (memory :> bytes64 (word_add sp0 (word 4592))) s =
                    sig /\
                    read (memory :> bytes64 (word_add sp0 (word 4608))) s =
                    word_add B (word 32768) /\
                    read (memory :> bytes16 (word_add sp0 (word 4604))) s =
                    word(4 * n) /\
                    read (memory :> bytes64 (word_add sp0 (word 4616))) s =
                    word_add B (word 43008) /\
                    read (memory :> bytes64 (word_add sp0 (word 4624))) s =
                    word_add B (word 43776) /\
                    read (memory :> bytes64 (word_add sp0 (word 4632))) s = B /\
                    read (memory :> bytes64 (word_add sp0 (word 4640))) s =
                    word_add B (word 36864) /\
                    read (memory :> bytes64 (word_add sp0 (word 4648))) s =
                    word_add B (word 28672) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4096
                         ==> read (memory :> bytes32
                                    (word_add B (word(4 * j)))) s = A j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(36864 + 4 * j)))) s =
                             s1h j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(28672 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 1024
                         ==> read (memory :> bytes32
                                    (word_add B (word(32768 + 4 * j)))) s =
                             t0h j) /\
                    read (memory :> bytes(word_add B (word 43904),64)) s = mu /\
                    read (memory :> bytes(word_add B (word 43968),64)) s =
                    rhop /\
                    read events s = e)
               (\s. read PC s =
                    (if r = 13
                     then word(pc + mldsa44_signature_internal_join4)
                     else word(pc + mldsa44_signature_internal_loop1_next1)) /\
                    read X22 s = (if r = 13 then word 0 else word 4294967295) /\
                    (r = 13
                     ==> !t. t < 2420
                             ==> read (memory :> bytes8
                                        (word_add sig (word t))) s =
                                 mld_sign_attempt_sig 4 4 32 39
                                  mld_poly_uniform_gamma1_17 mld_polyz_pack_17
                                  576
                                  (mld_polyw1_pack_88 o
                                   mld_poly_decompose_hi_88)
                                  192 mld_poly_decompose_lo_88
                                  mld_polyvec_make_hint_88 80
                                  A s1h s2h t0h mu rhop (4 * n) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_att sig B sp0 guard mf mc pc C r x b /\
                       memaccess_inbounds e2
                        [sig,2420; B,44064; word_add sp0 (word 4496),160;
                         word_add sp0 (word 48744),208;
                         sp0,4496;
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
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,2420; B,44064; word_add sp0 (word 48744),208;
                         sp0,4496]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X22; X24; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_add B (word 16384),4096);
                  memory :> bytes(word_add B (word 20480),4096);
                  memory :> bytes(word_add B (word 24576),4096);
                  memory :> bytes(word_add B (word 40960),1024);
                  memory :> bytes(word_add B (word 41984),1024);
                  memory :> bytes(word_add B (word 43008),768);
                  memory :> bytes(word_add B (word 44032),32);
                  memory :> bytes(word_add sp0 (word 48744),208);
                  memory :> bytes(sp0,4496)])`;;

let SIGN44_AALLOWED =
  [`sig:int64`; `B:int64`; `sp0:int64`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `C:num`; `r:num`; `x:num->int32`; `b:num->byte`];;

let SIGN44_ACALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN44_EXEC name ilist
    SIGN44_AALLOWED n;;

let SIGN44_CPH = `mld_poly_ntt (mld_poly_challenge 39 32 C)`;;
let SIGN44_Y = `mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)`;;
let SIGN44_W =
  `mld_sign_w 4 A (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n))`;;
let SIGN44_R0 =
  list_mk_comb(`mld_sign_r0`,
    [`mld_poly_decompose_lo_88`; SIGN44_W; `s2h:num->int32`; SIGN44_CPH]);;
let SIGN44_CT0 =
  list_mk_comb(`mld_sign_ct0`,[`t0h:num->int32`; SIGN44_CPH]);;
let SIGN44_CT =
  `mld_sign_ctilde 4 192 mu
    (mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
      (mld_sign_w 4 A (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n))))`;;
let SIGN44_SP = `word_add sp0 (word 4496):int64`;;

let SIGN44_SIGATT =
 `mld_sign_attempt_sig 4 4 32 39 mld_poly_uniform_gamma1_17 mld_polyz_pack_17
   576 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
   mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80
   A s1h s2h t0h mu rhop (4 * n)`;;

let SIGN44_ATT_MID = subst [SIGN44_SIGATT,`SIGATT:num->byte`]
 `\s. read SP s = word_add sp0 (word 4496) /\
      read X19 s = word_add B (word 20480) /\
      read X20 s = word_add B (word 40960) /\
      read X22 s = (if r = 13 then word 0 else word 4294967295) /\
      read X23 s = word_add B (word 41984) /\
      read X26 s = word_add B (word 44032) /\
      read X25 s = word_add B (word 16384) /\
      read X27 s = word_add B (word 24576) /\
      read (memory :> bytes64 (word_add sp0 (word 4616))) s =
      word_add B (word 43008) /\
      read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
      read (memory :> bytes(ea,el)) s = ev /\
      (r = 13
       ==> !t. t < 2420
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   SIGATT t)`;;

let SIGN44_ZCASE_TAC =
  SUBGOAL_THEN `r <= 4 /\ ~(r = 13)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 4` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 4 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SIGN44_ACALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `B:int64`; SIGN44_SP; `s1h:num->int32`;
    SIGN44_CPH; SIGN44_Y; `pc:num`] 2 THEN
  SIGN_PC_SIMP_TAC THEN
  SIGN44_ACALL_TAC "H_ZFAIL"
   [`r:num`; `sig:int64`; `B:int64`; SIGN44_SP; `s1h:num->int32`;
    SIGN44_CPH; SIGN44_Y; `pc:num`] 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_PATH_DISCHARGE_TAC;;

let SIGN44_WCASE_TAC =
  SUBGOAL_THEN `(r - 4) DIV 2 <= 4 /\ (r - 4) DIV 2 < 4 /\ ~(r = 13) /\
                2 * (r - 4) DIV 2 <= r - 4`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 12` THEN UNDISCH_TAC `4 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SIGN44_R0; SIGN44_CT0; `95154`; `95232`; `r - 4`;
                `(r - 4) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `4 <= r`] o
      check (fun th -> can (term_match []
        `4 <= r ==> (!j. j < r - 4 /\ j < 8 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 4` THEN UNDISCH_TAC `r < 12` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SIGN44_ACALL_TAC "H_RPRE"
   [`(r - 4) DIV 2`; `B:int64`; SIGN44_SP; SIGN44_W; `s2h:num->int32`;
    `t0h:num->int32`; SIGN44_CPH; `pc:num`] 3 THEN
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `4 <= r /\ r < 12 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 4)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 4) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SIGN44_ACALL_TAC "H_RFAIL1"
     [`(r - 4) DIV 2`; `B:int64`; SIGN44_SP; SIGN44_W; `s2h:num->int32`;
      SIGN44_CPH; `pc:num`] 4;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 4) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (SPECL [`4`; `r:num`] SIGN_ODD_ROW)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r - 5` o REWRITE_RULE[ASSUME `4 <= r`] o
      check (fun th -> can (term_match []
        `4 <= r ==> (!j. j < r - 4 /\ j < 8 ==> P j)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `r < 12` THEN ARITH_TAC; DISCH_TAC] THEN
    SIGN44_ACALL_TAC "H_RFAIL2"
     [`(r - 4) DIV 2`; `B:int64`; SIGN44_SP; SIGN44_W; `s2h:num->int32`;
      `t0h:num->int32`; SIGN44_CPH; `pc:num`] 4] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_PATH_DISCHARGE_TAC;;

let SIGN44_TCASE_TAC =
  SUBGOAL_THEN `12 <= r /\ 4 <= 4` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 12)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SIGN44_R0; SIGN44_CT0; `95154`; `95232`; `8`; `4`]
               SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `4 <= r`] o
      check (fun th -> can (term_match []
        `4 <= r ==> (!j. j < r - 4 /\ j < 8 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `12 <= r` THEN UNDISCH_TAC `j < 8` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SIGN44_ACALL_TAC "H_RPRE"
   [`4`; `B:int64`; SIGN44_SP; SIGN44_W; `s2h:num->int32`;
    `t0h:num->int32`; SIGN44_CPH; `pc:num`] 3 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read PC s = x`) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_LT_CONV) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 12 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 12 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add B (word (43008 + j)))) s3 =
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
      `read (memory :> bytes (word_add B (word 44032),32)) s = C`) (concl th)
    then FIRST_ASSUM(fun cth ->
           if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
           then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES_OFF
                            (TRANS th (SYM cth)))
           else NO_TAC)
    else NO_TAC) THEN
  SIGN44_ACALL_TAC "H_TAIL"
   [`sig:int64`; `B:int64`; `sp0:int64`; SIGN44_CT; `x:num->int32`;
    `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `12 <= r ==> (r = 13 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `word_zx (mld_pack_hints_ret 80 4 (mld_polyvec_make_hint_88 x b)):int64 =
    (if r = 13 then word 0 else word 4294967295)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC SIGN_PACK_HINTS_RET_ZX THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `mld_pack_hints_ret 80 4 (mld_polyvec_make_hint_88 x b) = word 0`
    ASSUME_TAC THENL
     [REWRITE_TAC[mld_pack_hints_ret] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      ASM_REWRITE_TAC[GSYM NOT_LT];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `mld_pack_hints_ret 80 4 h = word 0 ==> P`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[mld_sign_attempt_sig] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[mld_sign_cphat] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `2420 = (32 + 4 * 576) + 84` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SIGN_SIG_ASSEMBLE THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> can (term_match []
        `!t. t < 576 * 4
             ==> read (memory :> bytes8 (word_add sig (word (32 + t)))) s =
                 P t`) (concl th)));
    SIGN_PATH_DISCHARGE_TAC];;

let SIGN44_PATHS_TAC =
  ASM_CASES_TAC `r < 4` THENL
   [SIGN44_ZCASE_TAC;
    SUBGOAL_THEN `4 <= r /\ 4 <= 4` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 4)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `4 <= r ==> (!i. i < 4 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SIGN44_ACALL_TAC "H_ZPRE"
     [`4`; `sig:int64`; `B:int64`; SIGN44_SP; `s1h:num->int32`;
      SIGN44_CPH; SIGN44_Y; `pc:num`] 2 THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_CASES_TAC `r < 12` THENL [SIGN44_WCASE_TAC; SIGN44_TCASE_TAC]];;
let SIGN44_ACLEAN_TAC =
  FULL_INIT_TAC THEN
  SIGN44_ACALL_TAC "H_CLEAN"
   [`r = 13`; `B:int64`; SIGN44_SP; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;
let SIGN44_ATT = prove
 (SIGN44_ATT_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
   FIRST_X_ASSUM(fun th ->
     if is_conj(concl th) then
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN44_HEAD th) "H_HEAD"
     else NO_TAC) THEN
   FIRST_ASSUM(fun th ->
     if can (term_match [] `memcpy_full_contract mc ea el ev`) (concl th) then
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN44_ZPRE th) "H_ZPRE" THEN
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN44_ZFAIL th) "H_ZFAIL" THEN
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN44_RPRE th) "H_RPRE" THEN
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN44_RFAIL1 th) "H_RFAIL1" THEN
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN44_RFAIL2 th) "H_RFAIL2"
     else NO_TAC) THEN
   FIRST_ASSUM(fun th ->
     if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
     ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN44_CLEAN th) "H_CLEAN"
     else NO_TAC) THEN
   ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_TAIL "H_TAIL" THEN
   CONCRETIZE_F_EVENTS_TAC
    `\(sig:int64) (B:int64) (sp0:int64) (guard:int64) (mf:int64) (mc:int64)
      (pc:num) (C:num) (r:num) (x:num->int32) (b:num->byte).
      APPEND (f_ev_cl sig B sp0 guard mf mc pc C r x b)
       (APPEND
         (if r < 4 then f_ev_pz sig B sp0 guard mf mc pc C r x b
          else if r < 12
          then if EVEN (r - 4) then f_ev_pw1 sig B sp0 guard mf mc pc C r x b
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
               fst SIGN44_EXEC] THEN
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
   ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa44_signature_internal_join2`
     SIGN44_ATT_MID THEN
   CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    SIGN44_ACALL_TAC "H_HEAD"
     [`B:int64`; `sp0:int64`; `A:num->int32`; `mu:num`; `rhop:num`; `n:num`;
      `C:num`; `guard:int64`; `pc:num`] 1 THEN
    SIGN44_PATHS_TAC;
    SIGN44_ACLEAN_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The facts about the attempts that the main proof needs, for D =           *)
(* mld_sign_declass_44 and its number of attempts.                           *)
(* ------------------------------------------------------------------------- *)

let SIGN44_ATT_ARGS =
 `mld_sign_attempt_declass 4 4 32 39 mld_poly_uniform_gamma1_17
   130994 95154 95232 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
   192 mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80
   (mld_polyvec_matrix_expand 4 (mld_sk_rho skb))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. skb(128 + j))))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. skb(512 + j))))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. skb(896 + j))))
   MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU)`;;

let SIGN44_DECLASS_FACTS = prove
 (`!skb MU RND.
        0 < mld_sign_natt 16382 13 (mld_sign_declass_44 skb MU RND) /\
        mld_sign_natt 16382 13 (mld_sign_declass_44 skb MU RND) <= 16382 /\
        (!i. i < mld_sign_natt 16382 13 (mld_sign_declass_44 skb MU RND)
             ==> mld_sign_declass_44 skb MU RND i =
                 mld_sign_attempt_declass 4 4 32 39 mld_poly_uniform_gamma1_17
                  130994 95154 95232
                  (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
                  192 mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80
                  (mld_polyvec_matrix_expand 4 (mld_sk_rho skb))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(128 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(512 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 416 mld_polyt0_unpack
                      (\j. skb(896 + j))))
                  MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU) (4 * i)) /\
        (!i. i + 1 < mld_sign_natt 16382 13 (mld_sign_declass_44 skb MU RND)
             ==> ~(FST(SND(mld_sign_declass_44 skb MU RND i)) = 13)) /\
        (mld_sign_ok_44 skb MU RND <=>
         FST(SND(mld_sign_declass_44 skb MU RND
                  (mld_sign_natt 16382 13 (mld_sign_declass_44 skb MU RND) -
                   1))) = 13) /\
        (~mld_sign_ok_44 skb MU RND
         ==> mld_sign_natt 16382 13 (mld_sign_declass_44 skb MU RND) =
             16382) /\
        mld_sign_sig_44 skb MU RND =
        (if mld_sign_ok_44 skb MU RND
         then mld_sign_attempt_sig 4 4 32 39 mld_poly_uniform_gamma1_17
               mld_polyz_pack_17 576
               (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
               mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80
               (mld_polyvec_matrix_expand 4 (mld_sk_rho skb))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                   (\j. skb(128 + j))))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                   (\j. skb(512 + j))))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 416 mld_polyt0_unpack
                   (\j. skb(896 + j))))
               MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU)
               (4 * (mld_sign_natt 16382 13 (mld_sign_declass_44 skb MU RND) -
                     1))
         else \t. word 0) /\
        (mld_sign_terminates_44 skb MU RND
         ==> !i. i < mld_sign_natt 16382 13 (mld_sign_declass_44 skb MU RND)
                 ==> mld_poly_challenge_terminates 39 32
                      (FST(mld_sign_declass_44 skb MU RND i)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_declass_44; mld_sign_ok_44; mld_sign_sig_44;
              mld_sign_terminates_44] THEN
  MP_TAC(SPECL
   [`4`; `4`; `mld_polyeta_unpack_2`; `96`; `32`; `39`;
    `mld_poly_uniform_gamma1_17`; `130994`; `95154`; `95232`;
    `mld_polyw1_pack_88 o mld_poly_decompose_hi_88`; `192`;
    `mld_poly_decompose_lo_88`; `mld_polyvec_make_hint_88`; `80`; `16382`;
    `skb:num->byte`; `MU:num`; `RND:num`] SIGN_NATT_DECLASS) THEN
  CONV_TAC(LAND_CONV(LAND_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL
   [`4`; `4`; `mld_polyeta_unpack_2`; `96`; `32`; `39`;
    `mld_poly_uniform_gamma1_17`; `130994`; `95154`; `95232`;
    `mld_polyw1_pack_88 o mld_poly_decompose_hi_88`; `192`;
    `mld_poly_decompose_lo_88`; `mld_polyvec_make_hint_88`; `80`; `16382`;
    `skb:num->byte`; `MU:num`; `RND:num`] SIGN_NATTEMPTS_PROPS) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
  ABBREV_TAC
   `N = mld_sign_nattempts 4 4 mld_polyeta_unpack_2 96 32 39
         mld_poly_uniform_gamma1_17 130994 95154 95232
         (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
         mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80 16382
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
(* (mld_sign_natt 16382 13 D, with D what is declassified): an attempt that  *)
(* is followed by another (i + 1 < N), the successful last one, or the last  *)
(* one after which the signature is zeroed (16382 attempts, all rejected),   *)
(* then those of the epilogue; all of it twice, for the two positions of     *)
(* the buffers, at stackpointer + 5248 if stackpointer is a multiple of 32   *)
(* and at stackpointer + 5232 otherwise.                                     *)
(* ------------------------------------------------------------------------- *)

let SIGN44_TEMPLATE =
 `\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (rnd:int64)
   (sk:int64) (ext:int64) (rh:num)
   (D:num->num#num#(num->int32)#(num->byte)) (guard:int64) (mf:int64)
   (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
   if aligned 32 stackpointer then
     APPEND
      (f_ev_epila sig m mlen pre prelen rnd sk ext rh D guard mf mc pc
                  stackpointer returnaddress)
      (APPEND
        (ENUMERATEL (mld_sign_natt 16382 13 D)
          (\i. if i + 1 < mld_sign_natt 16382 13 D
               then f_ev_conta sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i
               else if FST(SND(D i)) = 13
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
        (ENUMERATEL (mld_sign_natt 16382 13 D)
          (\i. if i + 1 < mld_sign_natt 16382 13 D
               then f_ev_contu sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i
               else if FST(SND(D i)) = 13
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
(* its buffers and kappa = 4 * i (the 32-bit word at sp + 108); after the    *)
(* last attempt x22 holds the result and sig the signature.                  *)
(* ------------------------------------------------------------------------- *)

let SIGN44_INV b =
  let nm n = mk_small_numeral n in
  subst
   [nm b,`oBB:num`; nm(b + 36864),`oS1:num`; nm(b + 28672),`oS2:num`;
    nm(b + 32768),`oT0:num`; nm(b + 43008),`oW1P:num`;
    nm(b + 43776),`oSEED:num`; nm(b + 43904),`oMUO:num`;
    nm(b + 43968),`oRHO:num`; nm(b + 20480),`oSCR:num`;
    nm(b + 40960),`oTT:num`; nm(b + 41984),`oCP:num`; nm(b + 44032),`oCT:num`;
    nm(b + 16384),`oW0:num`; nm(b + 24576),`oYY:num`]
  `\i s.
     read SP s = word_add stackpointer (word 5072) /\
     read (memory :> bytes64 (word_add stackpointer (word 5072))) s =
     x19_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5080))) s =
     x20_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5088))) s =
     x21_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5096))) s =
     x22_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5104))) s =
     x23_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5112))) s =
     x24_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5120))) s =
     x25_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5128))) s =
     x26_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5136))) s =
     x27_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5144))) s =
     x28_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5152))) s =
     returnaddress /\
     read (memory :> bytes64 (word_add stackpointer (word 49528))) s =
     canary /\
     read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
       s = guard /\
     read (memory :> bytes64 guard) s = canary /\
     read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
     read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\
     read (memory :> bytes(ea,el)) s = ev /\
     read (memory :> bytes64 (word_add stackpointer (word 5168))) s = sig /\
     read (memory :> bytes64 (word_add stackpointer (word 5184))) s =
     word_add stackpointer (word oT0) /\
     read (memory :> bytes64 (word_add stackpointer (word 5192))) s =
     word_add stackpointer (word oW1P) /\
     read (memory :> bytes64 (word_add stackpointer (word 5200))) s =
     word_add stackpointer (word oSEED) /\
     read (memory :> bytes64 (word_add stackpointer (word 5208))) s =
     word_add stackpointer (word oBB) /\
     read (memory :> bytes64 (word_add stackpointer (word 5216))) s =
     word_add stackpointer (word oS1) /\
     read (memory :> bytes64 (word_add stackpointer (word 5224))) s =
     word_add stackpointer (word oS2) /\
     (!j. j < 4096
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oBB + 4 * j)))) s =
              mld_polyvec_matrix_expand 4 rh j) /\
     (!j. j < 1024
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oS1 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                 (\j. skb(128 + j))) j) /\
     (!j. j < 1024
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oS2 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                 (\j. skb(512 + j))) j) /\
     (!j. j < 1024
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oT0 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 416 mld_polyt0_unpack
                 (\j. skb(896 + j))) j) /\
     read (memory :> bytes(word_add stackpointer (word oMUO),64)) s = MU /\
     read (memory :> bytes(word_add stackpointer (word oRHO),64)) s =
     mld_sign_rhoprime (\j. skb(32 + j)) RND MU /\
     (i < mld_sign_natt 16382 13 D
      ==> read X19 s = word_add stackpointer (word oSCR) /\
          read X20 s = word_add stackpointer (word oTT) /\
          read X21 s = word_add stackpointer (word 49320) /\
          read X23 s = word_add stackpointer (word oCP) /\
          read X26 s = word_add stackpointer (word oCT) /\
          read X25 s = word_add stackpointer (word oW0) /\
          read X27 s = word_add stackpointer (word oYY) /\
          read (memory :> bytes32 (word_add stackpointer (word 5180))) s =
          word(4 * i)) /\
     (i = mld_sign_natt 16382 13 D
      ==> read X22 s =
          (if mld_sign_ok_44 skb MU RND then word 0 else word 4294967292) /\
          (!t. t < 2420
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   mld_sign_sig_44 skb MU RND t))`;;

let SIGN44_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 5263 5248 5232;;

let SIGN44_MALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `rnd:int64`; `sk:int64`; `ext:int64`; `rh:num`;
   `D:num->num#num#(num->int32)#(num->byte)`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let SIGN44_MCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN44_EXEC name ilist
    SIGN44_MALLOWED n;;

let SIGN44_NUMV s b k = subst [mk_small_numeral(b + k), mk_var(s,`:num`)];;

(* ------------------------------------------------------------------------- *)
(* The start: the callees as assumptions, the template, the frame (with the  *)
(* stack pointer at its bottom), the abbreviations rh and D (the arguments   *)
(* of the events), mu, the canary, the preserved registers and the facts     *)
(* about the attempts.                                                       *)
(* ------------------------------------------------------------------------- *)

let SIGN44_START_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if is_conj(concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN44_ATT th) "H_ATT"
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th) "H_MEXP"
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET"
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_H" THEN
  CONCRETIZE_F_EVENTS_TAC SIGN44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`;
    `pre:int64`; `prelen:num`; `rnd:int64`; `sk:int64`; `ext:int64`;
    `skb:num->byte`; `M:num`; mk_var("PRE",`:num`); `RND:num`; `MU:num`;
    `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 49536 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC `rh = mld_sk_rho skb` THEN
  ABBREV_TAC `D = mld_sign_declass_44 skb MU RND` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `MU = (if p then a else b)`) (concl th))) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 49536):int64)` THEN
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
  MP_TAC(SPECL [`skb:num->byte`; `MU:num`; `RND:num`] SIGN44_DECLASS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The prologue, up to the start of the first attempt: unpack_sk, then on    *)
(* ext either mld_H44 for mu (from tr, the prefix and m) or the inlined copy *)
(* of 64 bytes from m (as four 128-bit words), then mld_H44 for rho'' (from  *)
(* the key, rnd and mu) and the matrix expansion. The offsets from b are     *)
(* those of rho, tr and the key in the seed buffer, mu and rho''.            *)
(* ------------------------------------------------------------------------- *)

let SIGN44_RHO_TAC b =
  let pat = SIGN44_NUMV "oRHO" b 43776
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

let SIGN44_PROL_TAIL_TAC b n0 =
  let sn k = mk_var("s"^string_of_int k,`:armstate`) in
  let nh = n0 + 19 and nm = n0 + 28 in
  let kpat = SIGN44_NUMV "oKEY" b 43872
   `!j. j < 32 ==> read (memory :> bytes8
         (word_add stackpointer (word (oKEY + j)))) s = f j`
  and rgoal = SIGN44_NUMV "oRHO" b 43968
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    mld_sign_rhoprime (\j. skb(32 + j)) RND MU`
  and rpat = SIGN44_NUMV "oRHO" b 43968
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    num_of_bytelist l` in
  ARM_STEPS_TAC SIGN44_EXEC (n0--(nh - 1)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] kpat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN44_MCALL_TAC "H_H"
   [`read X0 s`; `64`; `read X2 s`; `32`; `read X4 s`; `32`;
    `read X6 s`; `64`;
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
  ARM_STEPS_TAC SIGN44_EXEC ((nh + 1)--(nm - 1)) THEN
  SIGN44_RHO_TAC b THEN
  SIGN44_MCALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; `rh:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] nm THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `0 = n <=> n = 0`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  SIGN_SEL_DISCHARGE_TAC;;

let SIGN44_MU_TAC b n =
  let sv = mk_var("s"^string_of_int n,`:armstate`) in
  let mgoal = subst [sv,`s:armstate`] (SIGN44_NUMV "oMU" b 43904
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s = MU`)
  and mpat = subst [sv,`s:armstate`] (SIGN44_NUMV "oMU" b 43904
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

let SIGN44_PROL_H_TAC b =
  let tpat = SIGN44_NUMV "oTR" b 43808
   `!j. j < 64 ==> read (memory :> bytes8
         (word_add stackpointer (word (oTR + j)))) s = f j` in
  ARM_STEPS_TAC SIGN44_EXEC [43] THEN
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  ARM_STEPS_TAC SIGN44_EXEC (44--52) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] tpat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN44_MCALL_TAC "H_H"
   [`read X0 s`; `64`; `read X2 s`; `64`; `read X4 s`; `prelen:num`;
    `read X6 s`; `mlen:num`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(64 + j)) 64)`;
    mk_var("PRE",`:num`); `M:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 53 THEN
  FIRST_ASSUM(fun th ->
    if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE
          [ASSUME `word_zx(ext:int64) = (word 0:int32)`] th)
    else NO_TAC) THEN
  SIGN44_MU_TAC b 53 THEN
  SIGN44_PROL_TAIL_TAC b 54;;

let SIGN44_M128_TAC s =
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

let SIGN44_PROL_X_TAC b =
  let mu = SIGN44_NUMV "oMU" b 43904
   `word_add stackpointer (word oMU):int64` in
  let mgoal = SIGN44_NUMV "oMU" b 43904
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s50 = MU`
  and mpat = SIGN44_NUMV "oMU" b 43904
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s50 =
    M MOD 2 EXP 512` in
  ARM_STEPS_TAC SIGN44_EXEC [43] THEN
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  SIGN44_M128_TAC `s43:armstate` THEN
  ARM_STEPS_TAC SIGN44_EXEC (44--50) THEN
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
  SIGN44_PROL_TAIL_TAC b 51;;

let SIGN44_PROL_TAC b =
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN44_EXEC (1--5) THEN
  MEXP_BUFFER_TAC SIGN44_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC SIGN44_EXEC (6--6) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC SIGN44_EXEC (7--41) THEN
  SIGN44_MCALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `read X6 s`; `skb:num->byte`; `pc:num`; `read SP s`;
    `read X30 s`] 42 THEN
  ASM_CASES_TAC `word_zx(ext:int64) = (word 0:int32)` THENL
   [SIGN44_PROL_H_TAC b; SIGN44_PROL_X_TAC b];;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop over the attempts: the facts about attempt i     *)
(* (its record D i as mld_sign_attempt_declass gives it, the termination of  *)
(* its challenge, and the result and signature if it is the last), the       *)
(* attempt as one step (ATT, with B = stackpointer + b and sp0 =             *)
(* stackpointer + 576), then the three exits: on success to join4; on        *)
(* rejection kappa += 4, then back to loop1 or, after the last attempt, -4   *)
(* in x22 and the zeroing of the signature with memset, to join4. The        *)
(* equations for mld_sign_ok_44 and mld_sign_sig_44 are made conditional on  *)
(* ~(i + 1 < N) before any call, which would otherwise rewrite the           *)
(* postcondition with them.                                                  *)
(* ------------------------------------------------------------------------- *)

let SIGN44_BALLOWED = SIGN44_MALLOWED @ [`i:num`];;

let SIGN44_ATT_ILIST b =
  [`sig:int64`; mk_comb(`word_add stackpointer:int64->int64`,
                        mk_comb(`word:num->int64`,mk_small_numeral b));
   `word_add stackpointer (word 576):int64`;
   `mld_polyvec_matrix_expand 4 rh`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 96 mld_polyeta_unpack_2
       (\j. (skb:num->byte)(128 + j)))`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 96 mld_polyeta_unpack_2
       (\j. (skb:num->byte)(512 + j)))`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 416 mld_polyt0_unpack
       (\j. (skb:num->byte)(896 + j)))`;
   `MU:num`; `mld_sign_rhoprime (\j. (skb:num->byte)(32 + j)) RND MU`;
   `i:num`; `FST((D:num->num#num#(num->int32)#(num->byte)) i)`;
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i))`;
   `FST(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `SND(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `guard:int64`; `pc:num`];;

let SIGN44_DANGER =
  [`mld_sign_ok_44 skb MU RND <=> P`;
   `mld_sign_sig_44 skb MU RND = x`];;

let SIGN44_BODY_INIT_TAC =
  let nth = UNDISCH(MP (ARITH_RULE
   `i < mld_sign_natt 16382 13 D
    ==> ~(i + 1 < mld_sign_natt 16382 13 D)
    ==> mld_sign_natt 16382 13 D - 1 = i`)
   (ASSUME `i < mld_sign_natt 16382 13 D`)) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ASSUME `i < mld_sign_natt 16382 13 D`;
              ASSUME `~(i = mld_sign_natt 16382 13 D)`] THEN
  SUBGOAL_THEN `i < 16382` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 16382 13 D`; `mld_sign_natt 16382 13 D <= 16382`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i < mld_sign_natt 16382 13 D
              ==> (D:num->num#num#(num->int32)#(num->byte)) i = x`)
         (concl th)
    then
      let th1 = MP (SPEC `i:num` th)
                   (ASSUME `i < mld_sign_natt 16382 13 D`) in
      let tup = `FST((D:num->num#num#(num->int32)#(num->byte)) i),
                 FST(SND(D i)),FST(SND(SND(D i))),SND(SND(SND(D i)))` in
      ASSUME_TAC(TRANS (SYM th1) (SYM(REWRITE_CONV[PAIR] tup)))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i < mld_sign_natt 16382 13 D
              ==> mld_poly_challenge_terminates 39 32
                   (FST((D:num->num#num#(num->int32)#(num->byte)) i))`)
         (concl th)
    then ASSUME_TAC(MP (SPEC `i:num` th)
                       (ASSUME `i < mld_sign_natt 16382 13 D`))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i + 1 < mld_sign_natt 16382 13 D
              ==> ~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) =
                    13)`)
         (concl th)
    then ASSUME_TAC(SPEC `i:num` th)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `mld_sign_ok_44 skb MU RND <=> P`) (concl th)
    then ASSUME_TAC(DISCH `~(i + 1 < mld_sign_natt 16382 13 D)`
                     (REWRITE_RULE[nth] th))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `mld_sign_sig_44 skb MU RND = x`) (concl th)
    then ASSUME_TAC(DISCH `~(i + 1 < mld_sign_natt 16382 13 D)`
                     (REWRITE_RULE[nth] th))
    else NO_TAC);;

let SIGN44_BODY_ATT_TAC b =
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes32
             (word_add stackpointer (word 5180))) s0 = word (4 * i)`)
           (concl th)
    then ASSUME_TAC(MATCH_MP SIGN_BYTES16_OF_BYTES32
          (CONJ th (MP (ARITH_RULE `i < 16382 ==> 4 * i < 65536`)
                       (ASSUME `i < 16382`))))
    else NO_TAC) THEN
  REMOVE_THEN "H_ATT" (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_O2_mc,SIGN44_EXEC,0x0,
       mldsa_native_libmldsa_gcc12_O2_mc,th)
      (`e:(uarch_event)list`::SIGN44_ATT_ILIST b) 1 THENL
     [REPEAT(CONJ_TAC THENL
        [SIGN_NUMS_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
      FULL_EXISTS_E2_TAC (ref SIGN44_BALLOWED);
      LABEL_TAC "H_ATT" th]);;

let SIGN44_BODY_DISCHARGE_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN44_CASE_TH = ASSUME
  `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13`;;

let SIGN44_NCASE_TH = ASSUME
  `~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13)`;;

let SIGN44_LAST_TAC cth =
  SUBGOAL_THEN `i + 1 = mld_sign_natt 16382 13 D` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 16382 13 D`; `~(i + 1 < mld_sign_natt 16382 13 D)`]
    THEN ARITH_TAC;
    DISCH_THEN(fun th -> ASSUME_TAC(EQT_INTRO th))] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `~(i + 1 < mld_sign_natt 16382 13 D)
          ==> (mld_sign_ok_44 skb MU RND <=> P)`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[cth]
          (MP th (ASSUME `~(i + 1 < mld_sign_natt 16382 13 D)`)))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `~(i + 1 < mld_sign_natt 16382 13 D)
          ==> mld_sign_sig_44 skb MU RND = x`) (concl th)
    then FIRST_ASSUM(fun oth ->
           let c = concl oth in
           if c = `mld_sign_ok_44 skb MU RND` ||
              c = `~mld_sign_ok_44 skb MU RND`
           then ASSUME_TAC(REWRITE_RULE[oth]
                 (MP th (ASSUME `~(i + 1 < mld_sign_natt 16382 13 D)`)))
           else NO_TAC)
    else NO_TAC);;

let SIGN44_SUCC_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read X22 s = (if b then x else y)`) (concl th))) THEN
  REWRITE_TAC[SIGN44_CASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13 ==> P`)
    (concl th))) THEN
  REWRITE_TAC[SIGN44_CASE_TH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 16382 13 D)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> can (term_match []
     `i + 1 < mld_sign_natt 16382 13 D ==> P`) (concl th))) THEN
    REWRITE_TAC[SIGN44_CASE_TH];
    ALL_TAC] THEN
  SIGN44_LAST_TAC SIGN44_CASE_TH THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN44_BODY_DISCHARGE_TAC;;

let SIGN44_MEMSET_TAC allowed n =
  LIBC_PLT_TAC SIGN44_EXEC n THEN
  SIGN_LIBC_CALL_TAC "H_MEMSET" SIGN44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref allowed) (n + 5);;

let SIGN44_KAPPA_TAC =
  SUBGOAL_THEN `4 * i + 4 < 65536` ASSUME_TAC THENL
   [UNDISCH_TAC `i < 16382` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_KAPPA_ZX; SIGN_KAPPA_CMP]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`4 * i`; `4`; `65528`]
                                         SIGN_KAPPA_NEXT)
                               (CONJ (ASSUME `4 * i + 4 < 65536`)
                                     (ARITH_RULE `65528 < 65536`))]);;

let SIGN44_CONT_TAC =
  SUBGOAL_THEN `~(4 * i + 4 = 65528)` ASSUME_TAC THENL
   [UNDISCH_TAC `i + 1 < 16382` THEN ARITH_TAC; ALL_TAC] THEN
  SIGN_PC_SIMP_TAC THEN
  SUBGOAL_THEN `i + 1 < mld_sign_natt 16382 13 D` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match []
           `~(i + 1 < mld_sign_natt 16382 13 D)
            ==> (mld_sign_ok_44 skb MU RND <=> P)`) (concl th)
      then ASSUME_TAC(REWRITE_RULE[SIGN44_NCASE_TH]
            (MP th (ASSUME `~(i + 1 < mld_sign_natt 16382 13 D)`)))
      else NO_TAC) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `~mld_sign_ok_44 skb MU RND ==> P`) (concl th)
      then MP_TAC(MP th (ASSUME `~mld_sign_ok_44 skb MU RND`))
      else NO_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 16382 13 D`; `~(i + 1 < mld_sign_natt 16382 13 D)`;
      `i + 1 < 16382`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i + 1 = mld_sign_natt 16382 13 D)` ASSUME_TAC THENL
   [UNDISCH_TAC `i + 1 < mld_sign_natt 16382 13 D` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
  SIGN44_BODY_DISCHARGE_TAC;;

let SIGN44_EXH_TAC =
  SUBGOAL_THEN `4 * i + 4 = 65528` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(i + 1 < 16382)`; `i < 16382`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIGN_PC_SIMP_TAC THEN
  ARM_STEPS_TAC SIGN44_EXEC (11--16) THEN
  SIGN44_MEMSET_TAC SIGN44_BALLOWED 16 THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 16382 13 D)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mld_sign_natt 16382 13 D <= 16382`; `~(i + 1 < 16382)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SIGN44_LAST_TAC SIGN44_NCASE_TH THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `!i. i < 2420 ==> read (memory :> bytes8 (word_add sig (word i))) s =
                      word_zx(word 0:int64)`) (concl th))) THEN
  REWRITE_TAC[WORD_ZX_0] THEN DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN44_BODY_DISCHARGE_TAC;;

let SIGN44_FAIL_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read X22 s = (if b then x else y)`) (concl th))) THEN
  REWRITE_TAC[SIGN44_NCASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13 ==> P`)
    (concl th))) THEN
  ARM_STEPS_TAC SIGN44_EXEC (2--10) THEN
  SIGN44_KAPPA_TAC THEN
  ASM_CASES_TAC `i + 1 < 16382` THENL [SIGN44_CONT_TAC; SIGN44_EXH_TAC];;

let SIGN44_BODY_TAC b =
  SIGN44_BODY_INIT_TAC THEN SIGN44_BODY_ATT_TAC b THEN
  ASM_CASES_TAC
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13` THENL
   [SIGN44_SUCC_TAC; SIGN44_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The epilogue, from join4: the memsets of s2, t0, s1 and the matrix, the   *)
(* inlined zeroing of the 256 bytes of the seed buffer and the check of the  *)
(* canary.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SIGN44_EPIL_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN44_EPIL_TAC =
  SIGN_DROP_TAC SIGN44_DANGER THEN
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC SIGN44_EXEC (1--5) THEN
  SIGN44_MEMSET_TAC SIGN44_MALLOWED 5 THEN
  ARM_STEPS_TAC SIGN44_EXEC (11--15) THEN
  SIGN44_MEMSET_TAC SIGN44_MALLOWED 15 THEN
  ARM_STEPS_TAC SIGN44_EXEC (21--25) THEN
  SIGN44_MEMSET_TAC SIGN44_MALLOWED 25 THEN
  ARM_STEPS_TAC SIGN44_EXEC (31--35) THEN
  SIGN44_MEMSET_TAC SIGN44_MALLOWED 35 THEN
  ARM_STEPS_TAC SIGN44_EXEC (41--51) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC SIGN44_EXEC (52--69) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SIGN_RET_ZX] THEN
  SIGN44_EPIL_DISCHARGE_TAC;;

let SIGN44_MAIN_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `mld_sign_natt 16382 13 D`
   `pc + mldsa44_signature_internal_loop1`
   `pc + mldsa44_signature_internal_join4` (SIGN44_INV b) THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC; SIGN44_PROL_TAC b; SIGN44_BODY_TAC b; SIGN44_EPIL_TAC];;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  SIGN44_START_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    SIGN44_MAIN_TAC 5248;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    SIGN44_MAIN_TAC 5232]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
