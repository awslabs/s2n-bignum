(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with the secret key, all the attempts (ML-DSA-65): the proof (see *)
(* signature_internal_65_spec.ml), with the tools of                         *)
(* utils/mldsa_native_signing.ml, as for AArch64, with the x86 code, whose   *)
(* frame is aligned to 32 bytes (see utils/mldsa_native_realign.ml), the     *)
(* buffers and the pointers to them that the code saves being at fixed       *)
(* offsets from bot, the bottom of the aligned frame.                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/signature_internal_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_hash.ml";;
needs "x86/proofs/utils/mldsa_native_wrap.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;

let SIGN65_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The proof is in parts, each a FULL lemma for a segment of the code, with  *)
(* the frame at bot (RSP = bot + 5190 in the loop over the attempts, RBP =   *)
(* bot + 73014): the loop over z up to an index m (ZPRE), the exit at a z    *)
(* whose norm check fails (ZFAIL), the loop over the rows of w0 up to a row  *)
(* m (RPRE), the exits at a row whose first or second check fails (RFAIL1,   *)
(* RFAIL2), the packing of c~ and the hints (TAIL), the cleanup and the      *)
(* decision (CLEAN), and the start of an attempt up to the NTT of the        *)
(* challenge (HEAD). The attempt (ATT) follows from them, with one path for  *)
(* each kind of result r of mld_sign_attempt_declass: r < 5 (z_r fails), 5   *)
(* <= r < 17 (the check r - 5 of the rows fails), 17 (too many hints) and 18 *)
(* (success). The buffers: c~ at bot + 5318, the seed buffer (rho, tr, key,  *)
(* mu at + 5510, rho'' at + 5574) at + 5382, w1 packed at + 5638, the        *)
(* challenge at + 6406 (whose address the code keeps in R14 between the      *)
(* attempts), the SHAKE256 context and the polynomial of z at + 7430, s1 at  *)
(* + 8454, y at + 13574, a scratch polynomial at + 18694, t0 at + 23814, s2  *)
(* at + 29958, w at + 36102 and the matrix at + 42246; the pointers to them  *)
(* that the code saves are at + 5190 to + 5310, with kappa (a 32-bit word)   *)
(* at + 5258 and the saved registers at + 72966 to + 73014.                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check.                                                               *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ZPRE_STMT =
 `?f_zpre.
    !e m sig bot s1h cphat y pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 7430)) /\
      aligned 16 (word_add bot (word 18694)) /\ m <= 5 /\
      (!i. i < m
           ==> mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) =
               word 0) /\
      nonoverlapping (sig,3309) (bot,73030) /\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,3309); (bot,73030)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s = word(pc + mldsa65_signature_internal_loop1) /\
                read RSP s = word_add bot (word 5190) /\
                read RBP s = word_add bot (word 73014) /\
                read RBX s = word_add bot (word 18694) /\
                read R12 s = word_add bot (word 7430) /\
                read R15 s = word_add bot (word 7430) /\
                read R14 s = word 0 /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                read (memory :> bytes64 (word_add bot (word 5278))) s =
                word_add bot (word 6406) /\
                read (memory :> bytes64 (word_add bot (word 5294))) s =
                word_add bot (word 13574) /\
                read (memory :> bytes64 (word_add bot (word 5270))) s = sig /\
                read (memory :> bytes64 (word_add bot (word 5262))) s =
                word_add bot (word 8454) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(6406 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 1280
                     ==> read (memory :> bytes32
                                (word_add bot (word(13574 + 4 * j)))) s =
                         y j) /\
                (!j. j < 1280
                     ==> read (memory :> bytes32
                                (word_add bot (word(8454 + 4 * j)))) s =
                         s1h j) /\
                read events s = e)
           (\s. read RIP s =
                (if m < 5
                 then word(pc + mldsa65_signature_internal_loop1)
                 else word(pc + mldsa65_signature_internal_loop1_exit1)) /\
                read RSP s = word_add bot (word 5190) /\
                read R14 s = word m /\
                read R15 s = word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                (!t. t < 640 * m
                     ==> read (memory :> bytes8
                                (word_add sig (word(48 + t)))) s =
                         mld_polyvec_pack 640 mld_polyz_pack_19
                          (mld_polyvec (mld_sign_z s1h cphat y)) t) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_zpre m sig bot pc /\
                   memaccess_inbounds e2
                    [sig,3309; bot,73030; word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [sig,3309; bot,73030]))
           (MAYCHANGE [RSP; R13; R14; R15] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,5190);
              memory :> bytes(word_add bot (word 5302),4);
              memory :> bytes(word_add bot (word 5310),8);
              memory :> bytes(word_add bot (word 7430),1024);
              memory :> bytes(word_add bot (word 18694),1024);
              memory :> bytes(word_add sig (word 48),3200)])`;;

let SIGN65_ZALLOWED = [`pc:num`; `sig:int64`; `bot:int64`; `i:num`];;

let SIGN65_ZCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN65_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    SIGN65_ZALLOWED n;;

let SIGN65_ZPRE_INV =
 `\i s. read RSP s = word_add bot (word 5190) /\
        read RBP s = word_add bot (word 73014) /\
        read RBX s = word_add bot (word 18694) /\
        read R12 s = word_add bot (word 7430) /\
        read R15 s = word_add bot (word 7430) /\
        read R14 s = word i /\
        (read DF s <=> false) /\
        read (memory :> bytes64 (word_add bot (word 5310))) s =
        word_add bot (word 18694) /\
        read (memory :> bytes64 (word_add bot (word 5278))) s =
        word_add bot (word 6406) /\
        read (memory :> bytes64 (word_add bot (word 5294))) s =
        word_add bot (word 13574) /\
        read (memory :> bytes64 (word_add bot (word 5270))) s = sig /\
        read (memory :> bytes64 (word_add bot (word 5262))) s =
        word_add bot (word 8454) /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add bot (word(6406 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 1280
             ==> read (memory :> bytes32 (word_add bot (word(13574 + 4 * j))))
                   s = y j) /\
        (!j. j < 1280
             ==> read (memory :> bytes32 (word_add bot (word(8454 + 4 * j))))
                   s = s1h j) /\
        (!t. t < 640 * i
             ==> read (memory :> bytes8 (word_add sig (word(48 + t)))) s =
                 mld_polyvec_pack 640 mld_polyz_pack_19
                  (mld_polyvec (mld_sign_z s1h cphat y)) t)`;;

(*** The copy of polynomial i of a vector at soff from bot to doff ***)

let SIGN65_COPY_TAC doff soff f n zs s =
  MP_TAC(SPECL [`bot:int64`; doff; soff; `i:num`; n; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** The address of polynomial i of a vector at off from bot, in RSI ***)

let SIGN65_POLY_ADDR_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SHL_WORD; ARITH_RULE `2 EXP 10 = 1024`])
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(1024 * i):int64) = 1024 * i`;
    MULT_CLAUSES; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

(*** The steps of the loop body up to the norm check of z_i ***)

let SIGN65_ZHEAD_TAC =
  SUBGOAL_THEN `val(word(1024 * i):int64) = 1024 * i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN65_EXEC (1--8) THEN
  SIGN65_POLY_ADDR_TAC THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add bot (word(8454 + 1024 * i)),
                                         1024)) s8` THEN
  MOVSQ_STEP_TAC SIGN65_EXEC 9 128 THEN
  SIGN65_COPY_TAC `7430` `8454` `s1h:num->int32` `1280` `zs:num`
    `s9:x86state` THEN
  X86_STEPS_TAC SIGN65_EXEC (10--12) THEN
  SIGN65_ZCALL_TAC "H_PW"
   [`read RDI s`; `read RSI s`; `mld_poly_of s1h i`; `cphat:num->int32`] 13
  THEN
  X86_STEPS_TAC SIGN65_EXEC (14--15) THEN
  SIGN65_ZCALL_TAC "H_INV"
   [`read RDI s`; `mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat`]
   16 THEN
  X86_STEPS_TAC SIGN65_EXEC (17--21) THEN
  SIGN65_POLY_ADDR_TAC THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add bot (word(13574 + 1024 * i)),
                                          1024)) s21` THEN
  MOVSQ_STEP_TAC SIGN65_EXEC 22 128 THEN
  SIGN65_COPY_TAC `18694` `13574` `y:num->int32` `1280` `zs':num`
    `s22:x86state` THEN
  X86_STEPS_TAC SIGN65_EXEC (23--25) THEN
  SIGN65_ZCALL_TAC "H_ADD"
   [`read RDI s`; `read RSI s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat)`;
    `mld_poly_of y i`] 26 THEN
  X86_STEPS_TAC SIGN65_EXEC (27--28) THEN
  SIGN65_ZCALL_TAC "H_RED"
   [`read RDI s`;
    `mld_poly_add
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat))
      (mld_poly_of y i)`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  X86_STEPS_TAC SIGN65_EXEC (30--32) THEN
  SIGN65_ZCALL_TAC "H_CHK"
   [`read RDI s`; `mld_sign_z s1h cphat y i`; `read RSI s`] 33 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_REDUCE_CONV
    `word_zx (word 524092:int64):int32`]);;

let SIGN65_ZBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 5` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SIGN65_ZHEAD_TAC THEN
  SUBGOAL_THEN
   `mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) = word 0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) = word 0`;
   WORD_ZX_0]) THEN
  X86_STEPS_TAC SIGN65_EXEC (34--39) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  X86_STEPS_TAC SIGN65_EXEC (40--40) THEN
  SIGN65_ZCALL_TAC "H_PZ"
   [`read RDI s`; `read RSI s`; `mld_sign_z s1h cphat y i`; `i:num`] 41 THEN
  X86_STEPS_TAC SIGN65_EXEC (42--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SIGN_TEST_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_19`; `640`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_19_LOCAL] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN65_ZPRE = prove
 (SIGN65_ZPRE_STMT,
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
    MLDSA_NATIVE_PACK_SIG_Z_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PZ" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sig:int64) (bot:int64) (pc:num).
     APPEND (f_ev_back m sig bot pc)
      (APPEND (ENUMERATEL m (\i. f_ev_zit sig bot pc i))
              (f_ev_front m sig bot pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:num`; `sig:int64`; `bot:int64`;
    `s1h:num->int32`; `cphat:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_loop1`
     `if m < 5 then pc + mldsa65_signature_internal_loop1
      else pc + mldsa65_signature_internal_loop1_exit1`
     SIGN65_ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN65_ZBODY_TAC;
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
(* the cleanup (join3, through join6 and join7) with R13 = -1 as a 32-bit    *)
(* integer and R14 pointing to the challenge again.                          *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ZFAIL_STMT =
 `?f_zfail.
    !e i sig bot s1h cphat y pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 7430)) /\
      aligned 16 (word_add bot (word 18694)) /\ i < 5 /\
      ~(mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) =
        word 0) /\
      nonoverlapping (sig,3309) (bot,73030) /\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,3309); (bot,73030)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s = word(pc + mldsa65_signature_internal_loop1) /\
                read RSP s = word_add bot (word 5190) /\
                read RBP s = word_add bot (word 73014) /\
                read RBX s = word_add bot (word 18694) /\
                read R12 s = word_add bot (word 7430) /\
                read R15 s = word_add bot (word 7430) /\
                read R14 s = word i /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                read (memory :> bytes64 (word_add bot (word 5278))) s =
                word_add bot (word 6406) /\
                read (memory :> bytes64 (word_add bot (word 5294))) s =
                word_add bot (word 13574) /\
                read (memory :> bytes64 (word_add bot (word 5262))) s =
                word_add bot (word 8454) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(6406 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 1280
                     ==> read (memory :> bytes32
                                (word_add bot (word(13574 + 4 * j)))) s =
                         y j) /\
                (!j. j < 1280
                     ==> read (memory :> bytes32
                                (word_add bot (word(8454 + 4 * j)))) s =
                         s1h j) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa65_signature_internal_join3) /\
                read RSP s = word_add bot (word 5190) /\
                read R13 s = word 4294967295 /\
                read R14 s = word_add bot (word 6406) /\
                read R15 s = word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_zfail i sig bot pc /\
                   memaccess_inbounds e2
                    [sig,3309; bot,73030; word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [sig,3309; bot,73030]))
           (MAYCHANGE [RSP; R13; R14; R15] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,5190);
              memory :> bytes(word_add bot (word 5302),4);
              memory :> bytes(word_add bot (word 5310),8);
              memory :> bytes(word_add bot (word 7430),1024);
              memory :> bytes(word_add bot (word 18694),1024)])`;;

let SIGN65_ZFAIL = prove
 (SIGN65_ZFAIL_STMT,
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
   `\(i:num) (sig:int64) (bot:int64) (pc:num).
     f_ev_zfail i sig bot pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `i:num`; `sig:int64`; `bot:int64`;
    `s1h:num->int32`; `cphat:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SIGN65_ZHEAD_TAC THEN
  X86_STEPS_TAC SIGN65_EXEC (34--34) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) =
      word 0)`]) THEN
  X86_STEPS_TAC SIGN65_EXEC (35--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass, leaving the rows of x of the hints, from loop1_exit1, where R12     *)
(* points to the polynomial of z, which the code saves twice.                *)
(* ------------------------------------------------------------------------- *)

let SIGN65_RPRE_STMT =
 `?f_rpre.
    !e m bot w s2h t0h cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 18694)) /\
      aligned 16 (word_add bot (word 36102)) /\ m <= 6 /\
      (!j. j < m
           ==> mld_poly_chknorm
                (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat j)
                (word 261692) = word 0 /\
               mld_poly_chknorm (mld_sign_ct0 t0h cphat j) (word 261888) =
               word 0) /\
      nonoverlapping (word pc,libmldsa_size) (bot,73030)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s =
                word(pc + mldsa65_signature_internal_loop1_exit1) /\
                read RSP s = word_add bot (word 5190) /\
                read RBP s = word_add bot (word 73014) /\
                read RBX s = word_add bot (word 18694) /\
                read R12 s = word_add bot (word 7430) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 5278))) s =
                word_add bot (word 6406) /\
                read (memory :> bytes64 (word_add bot (word 5238))) s =
                word_add bot (word 29958) /\
                read (memory :> bytes64 (word_add bot (word 5286))) s =
                word_add bot (word 36102) /\
                read (memory :> bytes64 (word_add bot (word 5230))) s =
                word_add bot (word 23814) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(6406 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(29958 + 4 * j)))) s =
                         s2h j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(23814 + 4 * j)))) s =
                         t0h j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(36102 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                read events s = e)
           (\s. read RIP s =
                (if m < 6
                 then word(pc + mldsa65_signature_internal_loop2)
                 else word(pc + mldsa65_signature_internal_loop2_exit1)) /\
                read RSP s = word_add bot (word 5190) /\
                read R14 s = word_add bot (word 6406) /\
                read R13 s = word(1024 * m) /\
                read (memory :> bytes64 (word_add bot (word 5302))) s =
                word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 7430) /\
                (!j. j < 256 * m
                     ==> read (memory :> bytes32
                                (word_add bot (word(36102 + 4 * j)))) s =
                         mld_sign_hint_x 6 mld_poly_decompose_lo_32 w s2h
                          t0h cphat j) /\
                (!j. 256 * m <= j /\ j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(36102 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_rpre m bot pc /\
                   memaccess_inbounds e2
                    [bot,73030; word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [bot,73030]))
           (MAYCHANGE [RSP; R12; R13; R14; R15] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,5190);
              memory :> bytes(word_add bot (word 5310),8);
              memory :> bytes(word_add bot (word 5302),8);
              memory :> bytes(word_add bot (word 18694),1024);
              memory :> bytes(word_add bot (word 36102),6144)])`;;

let SIGN65_RALLOWED = [`pc:num`; `bot:int64`; `i:num`];;

let SIGN65_RCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN65_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    SIGN65_RALLOWED n;;

let SIGN65_RPRE_INV =
 `\i s. read RSP s = word_add bot (word 5190) /\
        read RBP s = word_add bot (word 73014) /\
        read RBX s = word_add bot (word 18694) /\
        read R14 s = word_add bot (word 6406) /\
        read R13 s = word(1024 * i) /\
        (read DF s <=> false) /\
        read (memory :> bytes64 (word_add bot (word 5238))) s =
        word_add bot (word 29958) /\
        read (memory :> bytes64 (word_add bot (word 5286))) s =
        word_add bot (word 36102) /\
        read (memory :> bytes64 (word_add bot (word 5230))) s =
        word_add bot (word 23814) /\
        read (memory :> bytes64 (word_add bot (word 5302))) s =
        word_add bot (word 7430) /\
        read (memory :> bytes64 (word_add bot (word 5310))) s =
        word_add bot (word 7430) /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add bot (word(6406 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 1536
             ==> read (memory :> bytes32 (word_add bot (word(29958 + 4 * j))))
                   s = s2h j) /\
        (!j. j < 1536
             ==> read (memory :> bytes32 (word_add bot (word(23814 + 4 * j))))
                   s = t0h j) /\
        (!j. j < 256 * i
             ==> read (memory :> bytes32 (word_add bot (word(36102 + 4 * j))))
                   s =
                 mld_sign_hint_x 6 mld_poly_decompose_lo_32 w s2h t0h cphat
                  j) /\
        (!j. 256 * i <= j /\ j < 1536
             ==> read (memory :> bytes32 (word_add bot (word(36102 + 4 * j))))
                   s = mld_polyvec_map mld_poly_decompose_lo_32 w j)`;;

let SIGN65_RTEST = prove
 (`!j. 1024 * j + 18446744073709546496 = 18446744073709551616 <=> j + 1 = 6`,
  ARITH_TAC);;

let SIGN65_RFSLICE_TAC s =
  MP_TAC(SPECL [`bot:int64`; `36102`; `1536`; `mld_poly_decompose_lo_32`;
                `w:num->int32`; `i:num`; s] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; s]
             `!j. 256 * i <= j /\ j < 1536
                  ==> read (memory :> bytes32
                             (word_add bot (word (36102 + 4 * j))))
                        s = Q j`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 6` THEN ARITH_TAC; STRIP_TAC];;

let SIGN65_RCOPY_TAC soff f zs s =
  MP_TAC(SPECL [`bot:int64`; `18694`; soff; `i:num`; `1536`; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 6` THEN ARITH_TAC; DISCH_TAC];;

let SIGN65_RADDR_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(1024 * i):int64) = 1024 * i`;
    MULT_CLAUSES; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;
(*** The setup of row i, and its first part, up to the norm check of      ***)
(*** w0 - c s2                                                            ***)

let SIGN65_ROW_SETUP_TAC =
  SUBGOAL_THEN `val(word(1024 * i):int64) = 1024 * i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `i:num` o MATCH_MP SIGN_ALIGNED_OFF o
    check (fun th ->
      concl th = `aligned 16 (word_add (bot:int64) (word 36102))`));;

let SIGN65_ROW_HEAD_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN65_EXEC (1--5) THEN
  SIGN65_RADDR_TAC THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add bot (word(29958 + 1024 * i)),
                                         1024)) s5` THEN
  MOVSQ_STEP_TAC SIGN65_EXEC 6 128 THEN
  SIGN65_RCOPY_TAC `29958` `s2h:num->int32` `zs:num` `s6:x86state` THEN
  X86_STEPS_TAC SIGN65_EXEC (7--9) THEN
  SIGN65_RCALL_TAC "H_PW"
   [`read RDI s`; `read RSI s`; `mld_poly_of s2h i`; `cphat:num->int32`] 10
  THEN
  X86_STEPS_TAC SIGN65_EXEC (11--12) THEN
  SIGN65_RCALL_TAC "H_INV"
   [`read RDI s`; `mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat`]
   13 THEN
  SIGN65_RFSLICE_TAC `s13:x86state` THEN
  X86_STEPS_TAC SIGN65_EXEC (14--18) THEN SIGN65_RADDR_TAC THEN
  SIGN65_RCALL_TAC "H_SUB"
   [`read RDI s`; `read RSI s`;
    `mld_poly_decompose_lo_32 (mld_poly_of w i)`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat)`] 19 THEN
  X86_STEPS_TAC SIGN65_EXEC (20--21) THEN
  SIGN65_RCALL_TAC "H_RED"
   [`read RDI s`;
    `mld_poly_sub (mld_poly_decompose_lo_32 (mld_poly_of w i))
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat))`] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  X86_STEPS_TAC SIGN65_EXEC (23--25) THEN
  SIGN65_RCALL_TAC "H_CHK"
   [`read RDI s`; `mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i`;
    `read RSI s`] 26 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_REDUCE_CONV
    `word_zx (word 261692:int64):int32`]);;

(*** The second part, from the first check passing to the norm check of   ***)
(*** c t0                                                                 ***)

let SIGN65_ROW_MID_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
      (word 261692) = word 0`; WORD_ZX_0]) THEN
  X86_STEPS_TAC SIGN65_EXEC (27--32) THEN SIGN65_RADDR_TAC THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add bot (word(23814 + 1024 * i)),
                                          1024)) s32` THEN
  MOVSQ_STEP_TAC SIGN65_EXEC 33 128 THEN
  SIGN65_RCOPY_TAC `23814` `t0h:num->int32` `zs':num` `s33:x86state` THEN
  X86_STEPS_TAC SIGN65_EXEC (34--36) THEN
  SIGN65_RCALL_TAC "H_PW"
   [`read RDI s`; `read RSI s`; `mld_poly_of t0h i`; `cphat:num->int32`] 37
  THEN
  X86_STEPS_TAC SIGN65_EXEC (38--39) THEN
  SIGN65_RCALL_TAC "H_INV"
   [`read RDI s`; `mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat`]
   40 THEN
  X86_STEPS_TAC SIGN65_EXEC (41--42) THEN
  SIGN65_RCALL_TAC "H_RED"
   [`read RDI s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat)`] 43 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  X86_STEPS_TAC SIGN65_EXEC (44--46) THEN
  SIGN65_RCALL_TAC "H_CHK"
   [`read RDI s`; `mld_sign_ct0 t0h cphat i`; `read RSI s`] 47 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_REDUCE_CONV
    `word_zx (word 261888:int64):int32`]);;

let SIGN65_RBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 6` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SIGN65_ROW_SETUP_TAC THEN SIGN65_ROW_HEAD_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SIGN65_ROW_MID_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) = word 0`;
   WORD_ZX_0]) THEN
  X86_STEPS_TAC SIGN65_EXEC (48--53) THEN
  SIGN65_RCALL_TAC "H_ADD"
   [`read RDI s`; `read RSI s`;
    `mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i`;
    `mld_sign_ct0 t0h cphat i`] 54 THEN
  X86_STEPS_TAC SIGN65_EXEC (55--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN LOOP_TEST_TAC THEN
  REWRITE_TAC[SIGN65_RTEST] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM WORD_ADD; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
      NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN65_RSETUP_TAC tmpl vars =
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
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC vars THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let SIGN65_RPRE = prove
 (SIGN65_RPRE_STMT,
  SIGN65_RSETUP_TAC
   `\(m:num) (bot:int64) (pc:num).
     APPEND (f_ev_back m bot pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit bot pc i))
              (f_ev_front bot pc))
     :(uarch_event)list`
   [`e:(uarch_event)list`; `m:num`; `bot:int64`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_loop2`
     `if m < 6 then pc + mldsa65_signature_internal_loop2
      else pc + mldsa65_signature_internal_loop2_exit1`
     SIGN65_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN X86_STEPS_TAC SIGN65_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN65_RBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SIGN_BETA_ALL_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN X86_STEPS_TAC SIGN65_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0;
                    WORD_ADD_0] THEN
    SIGN_CONCRETE_DISCHARGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exits from the loop over the rows at a row whose first check (w0 - c  *)
(* s2) or second check (c t0) fails, to the cleanup (join3, through join6    *)
(* and join7) with R13 = -1 as a 32-bit integer, R12 and R15 pointing to the *)
(* polynomial of z again and the pointer to the scratch polynomial saved.    *)
(* ------------------------------------------------------------------------- *)

let SIGN65_RFAIL1_STMT =
 `?f_rfail1.
    !e i bot w s2h cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 18694)) /\
      aligned 16 (word_add bot (word 36102)) /\ i < 6 /\
      ~(mld_poly_chknorm
         (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
         (word 261692) = word 0) /\
      nonoverlapping (word pc,libmldsa_size) (bot,73030)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s = word(pc + mldsa65_signature_internal_loop2) /\
                read RSP s = word_add bot (word 5190) /\
                read RBP s = word_add bot (word 73014) /\
                read RBX s = word_add bot (word 18694) /\
                read R14 s = word_add bot (word 6406) /\
                read R13 s = word(1024 * i) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 5238))) s =
                word_add bot (word 29958) /\
                read (memory :> bytes64 (word_add bot (word 5286))) s =
                word_add bot (word 36102) /\
                read (memory :> bytes64 (word_add bot (word 5302))) s =
                word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 7430) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(6406 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(29958 + 4 * j)))) s =
                         s2h j) /\
                (!j. 256 * i <= j /\ j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(36102 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa65_signature_internal_join3) /\
                read RSP s = word_add bot (word 5190) /\
                read R12 s = word_add bot (word 7430) /\
                read R13 s = word 4294967295 /\
                read R14 s = word_add bot (word 6406) /\
                read R15 s = word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_rfail1 i bot pc /\
                   memaccess_inbounds e2
                    [bot,73030; word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [bot,73030]))
           (MAYCHANGE [RSP; R12; R13; R14; R15] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,5190);
              memory :> bytes(word_add bot (word 5310),8);
              memory :> bytes(word_add bot (word 18694),1024);
              memory :> bytes(word_add bot (word 36102),6144)])`;;

let SIGN65_RFAIL1 = prove
 (SIGN65_RFAIL1_STMT,
  SIGN65_RSETUP_TAC
   `\(i:num) (bot:int64) (pc:num). f_ev_rfail1 i bot pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `bot:int64`; `w:num->int32`;
    `s2h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN65_ROW_SETUP_TAC THEN SIGN65_ROW_HEAD_TAC THEN
  X86_STEPS_TAC SIGN65_EXEC (27--27) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
       (word 261692) = word 0)`]) THEN
  X86_STEPS_TAC SIGN65_EXEC (28--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SIGN65_RFAIL2_STMT =
 `?f_rfail2.
    !e i bot w s2h t0h cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 18694)) /\
      aligned 16 (word_add bot (word 36102)) /\ i < 6 /\
      mld_poly_chknorm
       (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
       (word 261692) = word 0 /\
      ~(mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) =
        word 0) /\
      nonoverlapping (word pc,libmldsa_size) (bot,73030)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s = word(pc + mldsa65_signature_internal_loop2) /\
                read RSP s = word_add bot (word 5190) /\
                read RBP s = word_add bot (word 73014) /\
                read RBX s = word_add bot (word 18694) /\
                read R14 s = word_add bot (word 6406) /\
                read R13 s = word(1024 * i) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 5238))) s =
                word_add bot (word 29958) /\
                read (memory :> bytes64 (word_add bot (word 5286))) s =
                word_add bot (word 36102) /\
                read (memory :> bytes64 (word_add bot (word 5230))) s =
                word_add bot (word 23814) /\
                read (memory :> bytes64 (word_add bot (word 5302))) s =
                word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 7430) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(6406 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(29958 + 4 * j)))) s =
                         s2h j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(23814 + 4 * j)))) s =
                         t0h j) /\
                (!j. 256 * i <= j /\ j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(36102 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa65_signature_internal_join3) /\
                read RSP s = word_add bot (word 5190) /\
                read R12 s = word_add bot (word 7430) /\
                read R13 s = word 4294967295 /\
                read R14 s = word_add bot (word 6406) /\
                read R15 s = word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_rfail2 i bot pc /\
                   memaccess_inbounds e2
                    [bot,73030; word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [bot,73030]))
           (MAYCHANGE [RSP; R12; R13; R14; R15] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,5190);
              memory :> bytes(word_add bot (word 5310),8);
              memory :> bytes(word_add bot (word 18694),1024);
              memory :> bytes(word_add bot (word 36102),6144)])`;;

let SIGN65_RFAIL2 = prove
 (SIGN65_RFAIL2_STMT,
  SIGN65_RSETUP_TAC
   `\(i:num) (bot:int64) (pc:num). f_ev_rfail2 i bot pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `bot:int64`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN65_ROW_SETUP_TAC THEN SIGN65_ROW_HEAD_TAC THEN SIGN65_ROW_MID_TAC THEN
  X86_STEPS_TAC SIGN65_EXEC (48--48) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) =
      word 0)`]) THEN
  X86_STEPS_TAC SIGN65_EXEC (49--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints, whose result is the value of R13 for  *)
(* the decision, with R12 and R15 pointing to the polynomial of z again and  *)
(* the pointer to the scratch polynomial saved.                              *)
(* ------------------------------------------------------------------------- *)

let SIGN65_TAIL_STMT =
 `?f_tail.
    !e sig bot ct (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      nonoverlapping (sig,3309) (bot,73030) /\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,3309); (bot,73030)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s =
                word(pc + mldsa65_signature_internal_loop2_exit1) /\
                read RSP s = word_add bot (word 5190) /\
                read RBP s = word_add bot (word 73014) /\
                read RBX s = word_add bot (word 18694) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 5270))) s = sig /\
                read (memory :> bytes64 (word_add bot (word 5222))) s =
                word_add bot (word 5318) /\
                read (memory :> bytes64 (word_add bot (word 5302))) s =
                word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5246))) s =
                word_add bot (word 5638) /\
                read (memory :> bytes64 (word_add bot (word 5286))) s =
                word_add bot (word 36102) /\
                (!j. j < 48
                     ==> read (memory :> bytes8
                                (word_add bot (word(5318 + j)))) s = ct j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(36102 + 4 * j)))) s =
                         x j) /\
                (!j. j < 768
                     ==> read (memory :> bytes8
                                (word_add bot (word(5638 + j)))) s = b j) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa65_signature_internal_join3) /\
                read RSP s = word_add bot (word 5190) /\
                read R12 s = word_add bot (word 7430) /\
                read R13 s =
                word_zx(mld_pack_hints_ret 55 6
                         (mld_polyvec_make_hint_32 x b)) /\
                read R15 s = word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                (!j. j < 48
                     ==> read (memory :> bytes8 (word_add sig (word j))) s =
                         ct j) /\
                (mld_pack_hints_ret 55 6 (mld_polyvec_make_hint_32 x b) =
                 word 0
                 ==> !t. t < 61
                         ==> read (memory :> bytes8
                                    (word_add sig (word(3248 + t)))) s =
                             mld_pack_hints 55 6
                              (mld_polyvec_make_hint_32 x b) t) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_tail sig bot pc x b /\
                   memaccess_inbounds e2 [sig,3309; bot,73030]
                    [sig,3309; bot,73030]))
           (MAYCHANGE [RSP; R12; R13; R15] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(sig,48);
              memory :> bytes(word_add sig (word 3248),61);
              memory :> bytes(bot,5190);
              memory :> bytes(word_add bot (word 5310),8);
              memory :> bytes(word_add bot (word 18694),1024)])`;;

let SIGN65_TAIL = prove
 (SIGN65_TAIL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PH" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (bot:int64) (pc:num) (x:num->int32) (b:num->byte).
     f_ev_tail sig bot pc x b:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `bot:int64`;
    `ct:num->byte`; `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; C_RETURN; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN65_EXEC (1--7) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN65_EXEC "H_PC"
   [`read RDI s`; `read RSI s`; `ct:num->byte`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   [`pc:num`; `sig:int64`; `bot:int64`; `x:num->int32`; `b:num->byte`] 8
  THEN
  X86_STEPS_TAC SIGN65_EXEC (9--13) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN65_EXEC "H_PH"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `x:num->int32`;
    `b:num->byte`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   [`pc:num`; `sig:int64`; `bot:int64`; `x:num->int32`; `b:num->byte`] 14
  THEN
  X86_STEPS_TAC SIGN65_EXEC (15--15) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt and the test of R13: to join5 on success, else  *)
(* to the test of R13 against -1 at +0x4ca, which has no label, before the   *)
(* update of kappa.                                                          *)
(* ------------------------------------------------------------------------- *)

let SIGN65_CMP_OFF =
  mk_small_numeral(layout "mldsa65_signature_internal" + 0x4ca);;

let SIGN65_CLEAN_STMT = subst [SIGN65_CMP_OFF,`cmpoff:num`]
 `?f_clean.
    !e ok bot pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 5318)) /\
      nonoverlapping (word pc,libmldsa_size) (bot,73030)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s = word(pc + mldsa65_signature_internal_join3) /\
                read RBP s = word_add bot (word 73014) /\
                read RBX s = word_add bot (word 18694) /\
                read R12 s = word_add bot (word 7430) /\
                read R13 s = (if ok then word 0 else word 4294967295) /\
                (read DF s <=> false) /\
                read R14 s = word_add bot (word 6406) /\
                read (memory :> bytes64 (word_add bot (word 5286))) s =
                word_add bot (word 36102) /\
                read (memory :> bytes64 (word_add bot (word 5246))) s =
                word_add bot (word 5638) /\
                read (memory :> bytes64 (word_add bot (word 5294))) s =
                word_add bot (word 13574) /\
                read (memory :> bytes64 (word_add bot (word 5222))) s =
                word_add bot (word 5318) /\
                read events s = e)
           (\s. read RIP s =
                (if ok then word(pc + mldsa65_signature_internal_join5)
                 else word(pc + cmpoff)) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_clean ok bot pc /\
                   memaccess_inbounds e2 [bot,73030] [bot,73030]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(word_add bot (word 5318),48);
              memory :> bytes(word_add bot (word 5638),768);
              memory :> bytes(word_add bot (word 6406),1024);
              memory :> bytes(word_add bot (word 7430),1024);
              memory :> bytes(word_add bot (word 13574),5120);
              memory :> bytes(word_add bot (word 18694),5120);
              memory :> bytes(word_add bot (word 36102),6144)])`;;

let SIGN65_CLEAN = prove
 (SIGN65_CLEAN_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (bot:int64) (pc:num).
     if ok then f_ev_clean_ok bot pc else f_ev_clean_bad bot pc
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `ok:bool`; `bot:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BOOL_CASES_TAC `ok:bool` THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN65_EXEC (1--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt: y, w, w1 and its packing, c~ with the inlined    *)
(* SHAKE256 calls (and the zeroing of the context with REP STOSQ), the       *)
(* challenge and its NTT.                                                    *)
(* ------------------------------------------------------------------------- *)

let SIGN65_HEAD_STMT =
 `?f_head.
    !e bot A mu rhop n C pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      n < 13106 /\
      num_of_bytelist(list_of_seq
       (mld_sign_ctilde 6 128 mu
         (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
           (mld_sign_w 5 A
             (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)))))
       48) = C /\
      mld_poly_challenge_terminates 49 48 C /\
      nonoverlapping (word pc,libmldsa_size) (bot,73030)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s = word(pc + mldsa65_signature_internal_join2) /\
                read RSP s = word_add bot (word 5190) /\
                read RBP s = word_add bot (word 73014) /\
                read R14 s = word_add bot (word 6406) /\
                read R15 s = word_add bot (word 7430) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 5294))) s =
                word_add bot (word 13574) /\
                read (memory :> bytes32 (word_add bot (word 5258))) s =
                word(5 * n) /\
                read (memory :> bytes64 (word_add bot (word 5198))) s =
                word_add bot (word 5574) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                read (memory :> bytes64 (word_add bot (word 5286))) s =
                word_add bot (word 36102) /\
                read (memory :> bytes64 (word_add bot (word 5214))) s =
                word_add bot (word 42246) /\
                read (memory :> bytes64 (word_add bot (word 5246))) s =
                word_add bot (word 5638) /\
                read (memory :> bytes64 (word_add bot (word 5206))) s =
                word_add bot (word 5510) /\
                read (memory :> bytes64 (word_add bot (word 5222))) s =
                word_add bot (word 5318) /\
                (!j. j < 7680
                     ==> read (memory :> bytes32
                                (word_add bot (word(42246 + 4 * j)))) s =
                         A j) /\
                read (memory :> bytes(word_add bot (word 5510),64)) s = mu /\
                read (memory :> bytes(word_add bot (word 5574),64)) s =
                rhop /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa65_signature_internal_loop1) /\
                read RSP s = word_add bot (word 5190) /\
                read R13 s = word 0 /\
                read R14 s = word 0 /\
                read (memory :> bytes64 (word_add bot (word 5278))) s =
                word_add bot (word 6406) /\
                (!j. j < 1280
                     ==> read (memory :> bytes32
                                (word_add bot (word(13574 + 4 * j)))) s =
                         mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)
                          j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(36102 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32
                          (mld_sign_w 5 A
                            (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                              (5 * n))) j) /\
                (!j. j < 768
                     ==> read (memory :> bytes8
                                (word_add bot (word(5638 + j)))) s =
                         mld_sign_w1
                          (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                          128
                          (mld_sign_w 5 A
                            (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                              (5 * n))) j) /\
                read (memory :> bytes(word_add bot (word 5318),48)) s = C /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(6406 + 4 * j)))) s =
                         mld_poly_ntt (mld_poly_challenge 49 48 C) j) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_head bot pc C /\
                   memaccess_inbounds e2
                    [bot,73030;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024]
                    [bot,73030]))
           (MAYCHANGE [RSP; R13; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,5190);
              memory :> bytes(word_add bot (word 5278),8);
              memory :> bytes(word_add bot (word 5318),48);
              memory :> bytes(word_add bot (word 5638),768);
              memory :> bytes(word_add bot (word 6406),1024);
              memory :> bytes(word_add bot (word 7430),208);
              memory :> bytes(word_add bot (word 13574),5120);
              memory :> bytes(word_add bot (word 18694),5120);
              memory :> bytes(word_add bot (word 36102),6144)])`;;

let SIGN65_W1 =
 `mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   (mld_sign_w 5 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)))`;;

let SIGN65_W1NUM = mk_comb(`num_of_bytelist`,
  list_mk_comb(`list_of_seq:(num->byte)->num->(byte)list`,[SIGN65_W1; `768`]));;

let SIGN65_ABSORBED =
  list_mk_comb(`mld_keccak_absorb`,
    [`136`; `word 0:1600 word`; `0`; `832`;
     mk_binop `(+):num->num->num` `mu:num`
      (mk_binop `( * ):num->num->num` `2 EXP 512` SIGN65_W1NUM)]);;

let SIGN65_S2 = mk_comb(`FST:(1600 word#num)->1600 word`,SIGN65_ABSORBED);;

let SIGN65_S3 =
  list_mk_comb(`mld_keccak_finalize`,[`136`; `31`; SIGN65_S2; `16`]);;

let SIGN65_HCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN65_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   [`pc:num`; `bot:int64`; `C:num`] n;;
let SIGN65_HEAD = prove
 (SIGN65_HEAD_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_GAMMA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_YVEC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_CADDQ_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
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
    MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CHAL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(bot:int64) (pc:num) (C:num). f_ev_head bot pc C:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `bot:int64`; `A:num->int32`;
    `mu:num`; `rhop:num`; `n:num`; `C:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN65_EXEC (1--5) THEN
  SIGN65_HCALL_TAC "H_GAMMA"
   [`read RDI s`; `read RSI s`; `rhop:num`; `read RDX s`] 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_Y_KAPPA]) THEN
  X86_STEPS_TAC SIGN65_EXEC (7--12) THEN
  SIGN65_HCALL_TAC "H_YVEC"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `A:num->int32`;
    `mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)`] 13 THEN
  X86_STEPS_TAC SIGN65_EXEC (14--15) THEN
  SIGN65_HCALL_TAC "H_CADDQ"
   [`read RDI s`;
    `mld_polyvec_map mld_poly_invntt_tomont
      (mld_polyvec_matrix_pointwise_montgomery 5 A
        (mld_polyvec_map mld_poly_ntt
          (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))))`] 16 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w]) THEN
  X86_STEPS_TAC SIGN65_EXEC (17--21) THEN
  SIGN65_HCALL_TAC "H_DEC"
   [`read RDI s`; `read RSI s`;
    `mld_sign_w 5 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))`;
    `read RDX s`] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w1]) THEN
  X86_STEPS_TAC SIGN65_EXEC (23--24) THEN
  SIGN65_HCALL_TAC "H_INIT" [`read RDI s`] 25 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC SIGN65_EXEC (26--29) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 7430):int64` THEN
  SIGN65_HCALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `64`; `word 0:1600 word`; `0`; `mu:num`] 30
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 768 ==> read (memory :> bytes8
         (word_add bot (word (5638 + j)))) s = f j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  MLD_H_BOUND_TAC `word_add bot (word 5510):int64` THEN
  X86_STEPS_TAC SIGN65_EXEC (31--34) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 7430):int64` THEN
  SIGN65_HCALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `768`;
    `FST(mld_keccak_absorb 136 (word 0) 0 64 mu)`; `64`; SIGN65_W1NUM] 35
  THEN
  MP_TAC(SPECL [`64`; `768`; `mu:num`; SIGN65_W1NUM]
               MLD_SHAKE256_ABSORB_APPEND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV SIGN_NUMERAL_CONV) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(CONV_RULE SIGN_NUMERAL_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC SIGN65_EXEC (36--37) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 7430):int64` THEN
  SIGN65_HCALL_TAC "H_FINALIZE" [`read RDI s`; SIGN65_S2; `16`] 38 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC SIGN65_EXEC (39--43) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 7430):int64` THEN
  SIGN65_HCALL_TAC "H_SQUEEZE"
   [`read RDI s`; `48`; `read RDX s`; SIGN65_S3; `136`] 44 THEN
  X86_STEPS_TAC SIGN65_EXEC (45--46) THEN
  SIGN65_HCALL_TAC "H_RELEASE" [`read RDI s`] 47 THEN
  X86_STEPS_TAC SIGN65_EXEC (48--54) THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add bot (word 5318),48)) s54 = C`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde; mld_shake256_byte; mld_shake256_state;
                MLD_KECCAK_ABSORB_SND] THEN
    CONV_TAC SIGN_NUMERAL_CONV THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
   `read (memory :> bytes (word_add bot (word 5318),48)) s54 =
    num_of_bytelist l`) (concl th))) THEN
  X86_STEPS_TAC SIGN65_EXEC (55--55) THEN
  SIGN65_HCALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; `C:num`] 56 THEN
  X86_STEPS_TAC SIGN65_EXEC (57--58) THEN
  SIGN65_HCALL_TAC "H_NTT" [`read RDI s`; `mld_poly_challenge 49 48 C`] 59 THEN
  X86_STEPS_TAC SIGN65_EXEC (60--61) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt, from join2 to join5 or the test at +0x4ca, with the      *)
(* events a function of the declassified record (C,r,x,b).                   *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ATT_STMT = subst [SIGN65_CMP_OFF,`cmpoff:num`]
 `?f_att.
    !e sig bot A s1h s2h t0h mu rhop n C r x b pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 5318)) /\
      aligned 16 (word_add bot (word 7430)) /\
      aligned 16 (word_add bot (word 18694)) /\
      aligned 16 (word_add bot (word 36102)) /\ n < 13106 /\
      mld_sign_attempt_declass 6 5 48 49 mld_poly_uniform_gamma1_19
       524092 261692 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
       128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
       A s1h s2h t0h mu rhop (5 * n) = (C,r,x,b) /\
      mld_poly_challenge_terminates 49 48 C /\
      nonoverlapping (sig,3309) (bot,73030) /\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,3309); (bot,73030)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s = word(pc + mldsa65_signature_internal_join2) /\
                read RSP s = word_add bot (word 5190) /\
                read RBP s = word_add bot (word 73014) /\
                read RBX s = word_add bot (word 18694) /\
                read R12 s = word_add bot (word 7430) /\
                read R14 s = word_add bot (word 6406) /\
                read R15 s = word_add bot (word 7430) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 5198))) s =
                word_add bot (word 5574) /\
                read (memory :> bytes64 (word_add bot (word 5214))) s =
                word_add bot (word 42246) /\
                read (memory :> bytes64 (word_add bot (word 5206))) s =
                word_add bot (word 5510) /\
                read (memory :> bytes64 (word_add bot (word 5230))) s =
                word_add bot (word 23814) /\
                read (memory :> bytes64 (word_add bot (word 5238))) s =
                word_add bot (word 29958) /\
                read (memory :> bytes64 (word_add bot (word 5222))) s =
                word_add bot (word 5318) /\
                read (memory :> bytes64 (word_add bot (word 5262))) s =
                word_add bot (word 8454) /\
                read (memory :> bytes64 (word_add bot (word 5246))) s =
                word_add bot (word 5638) /\
                read (memory :> bytes64 (word_add bot (word 5270))) s = sig /\
                read (memory :> bytes32 (word_add bot (word 5258))) s =
                word(5 * n) /\
                read (memory :> bytes64 (word_add bot (word 5286))) s =
                word_add bot (word 36102) /\
                read (memory :> bytes64 (word_add bot (word 5294))) s =
                word_add bot (word 13574) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                (!j. j < 7680
                     ==> read (memory :> bytes32
                                (word_add bot (word(42246 + 4 * j)))) s =
                         A j) /\
                (!j. j < 1280
                     ==> read (memory :> bytes32
                                (word_add bot (word(8454 + 4 * j)))) s =
                         s1h j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(29958 + 4 * j)))) s =
                         s2h j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add bot (word(23814 + 4 * j)))) s =
                         t0h j) /\
                read (memory :> bytes(word_add bot (word 5510),64)) s = mu /\
                read (memory :> bytes(word_add bot (word 5574),64)) s =
                rhop /\
                read events s = e)
           (\s. read RIP s =
                (if r = 18 then word(pc + mldsa65_signature_internal_join5)
                 else word(pc + cmpoff)) /\
                read RSP s = word_add bot (word 5190) /\
                read R12 s = word_add bot (word 7430) /\
                read R13 s = (if r = 18 then word 0 else word 4294967295) /\
                read R14 s = word_add bot (word 6406) /\
                read R15 s = word_add bot (word 7430) /\
                read (memory :> bytes64 (word_add bot (word 5310))) s =
                word_add bot (word 18694) /\
                (r = 18
                 ==> !t. t < 3309
                         ==> read (memory :> bytes8
                                    (word_add sig (word t))) s =
                             mld_sign_attempt_sig 6 5 48 49
                              mld_poly_uniform_gamma1_19 mld_polyz_pack_19
                              640
                              (mld_polyw1_pack_32 o
                               mld_poly_decompose_hi_32)
                              128 mld_poly_decompose_lo_32
                              mld_polyvec_make_hint_32 55
                              A s1h s2h t0h mu rhop (5 * n) t) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_att sig bot pc C r x b /\
                   memaccess_inbounds e2
                    [sig,3309; bot,73030;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [sig,3309; bot,73030]))
           (MAYCHANGE [RSP; R12; R13; R14; R15] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(sig,3309);
              memory :> bytes(bot,5190);
              memory :> bytes(word_add bot (word 5278),8);
              memory :> bytes(word_add bot (word 5302),8);
              memory :> bytes(word_add bot (word 5310),8);
              memory :> bytes(word_add bot (word 5318),48);
              memory :> bytes(word_add bot (word 5638),768);
              memory :> bytes(word_add bot (word 6406),1024);
              memory :> bytes(word_add bot (word 7430),1024);
              memory :> bytes(word_add bot (word 13574),5120);
              memory :> bytes(word_add bot (word 18694),5120);
              memory :> bytes(word_add bot (word 36102),6144)])`;;

let SIGN65_AALLOWED =
  [`sig:int64`; `bot:int64`; `pc:num`; `C:num`; `r:num`; `x:num->int32`;
   `b:num->byte`];;

let SIGN65_ACALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN65_EXEC name ilist
    SIGN65_AALLOWED n;;

let SIGN65_CPH = `mld_poly_ntt (mld_poly_challenge 49 48 C)`;;
let SIGN65_Y = `mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)`;;
let SIGN65_W =
  `mld_sign_w 5 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))`;;
let SIGN65_R0 =
  list_mk_comb(`mld_sign_r0`,
    [`mld_poly_decompose_lo_32`; SIGN65_W; `s2h:num->int32`; SIGN65_CPH]);;
let SIGN65_CT0 =
  list_mk_comb(`mld_sign_ct0`,[`t0h:num->int32`; SIGN65_CPH]);;
let SIGN65_CT =
  `mld_sign_ctilde 6 128 mu
    (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
      (mld_sign_w 5 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))))`;;

let SIGN65_SIGATT =
 `mld_sign_attempt_sig 6 5 48 49 mld_poly_uniform_gamma1_19 mld_polyz_pack_19
   640 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
   A s1h s2h t0h mu rhop (5 * n)`;;

let SIGN65_ATT_MID = subst [SIGN65_SIGATT,`SIGATT:num->byte`]
 `\s. read RSP s = word_add bot (word 5190) /\
      read RBP s = word_add bot (word 73014) /\
      read RBX s = word_add bot (word 18694) /\
      read R12 s = word_add bot (word 7430) /\
      read R13 s = (if r = 18 then word 0 else word 4294967295) /\
      read R14 s = word_add bot (word 6406) /\
      read R15 s = word_add bot (word 7430) /\
      (read DF s <=> false) /\
      read (memory :> bytes64 (word_add bot (word 5222))) s =
      word_add bot (word 5318) /\
      read (memory :> bytes64 (word_add bot (word 5246))) s =
      word_add bot (word 5638) /\
      read (memory :> bytes64 (word_add bot (word 5286))) s =
      word_add bot (word 36102) /\
      read (memory :> bytes64 (word_add bot (word 5294))) s =
      word_add bot (word 13574) /\
      read (memory :> bytes64 (word_add bot (word 5310))) s =
      word_add bot (word 18694) /\
      (r = 18
       ==> !t. t < 3309
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   SIGATT t)`;;

let SIGN65_ZCASE_TAC =
  SUBGOAL_THEN `r <= 5 /\ ~(r = 18)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 5` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 5 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SIGN65_ACALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `bot:int64`; `s1h:num->int32`;
    SIGN65_CPH; SIGN65_Y; `pc:num`] 2 THEN
  SIGN_PC_SIMP_TAC THEN
  SIGN65_ACALL_TAC "H_ZFAIL"
   [`r:num`; `sig:int64`; `bot:int64`; `s1h:num->int32`;
    SIGN65_CPH; SIGN65_Y; `pc:num`] 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_PATH_DISCHARGE_TAC;;

let SIGN65_WCASE_TAC =
  SUBGOAL_THEN `(r - 5) DIV 2 <= 6 /\ (r - 5) DIV 2 < 6 /\ ~(r = 18) /\
                2 * (r - 5) DIV 2 <= r - 5`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 17` THEN UNDISCH_TAC `5 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SIGN65_R0; SIGN65_CT0; `261692`; `261888`; `r - 5`;
                `(r - 5) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 5` THEN UNDISCH_TAC `r < 17` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SIGN65_ACALL_TAC "H_RPRE"
   [`(r - 5) DIV 2`; `bot:int64`; SIGN65_W; `s2h:num->int32`;
    `t0h:num->int32`; SIGN65_CPH; `pc:num`] 3 THEN
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `5 <= r /\ r < 17 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 5)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 5) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SIGN65_ACALL_TAC "H_RFAIL1"
     [`(r - 5) DIV 2`; `bot:int64`; SIGN65_W; `s2h:num->int32`;
      SIGN65_CPH; `pc:num`] 4;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 5) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (SPECL [`5`; `r:num`] SIGN_ODD_ROW)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r - 6` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `r < 17` THEN ARITH_TAC; DISCH_TAC] THEN
    SIGN65_ACALL_TAC "H_RFAIL2"
     [`(r - 5) DIV 2`; `bot:int64`; SIGN65_W; `s2h:num->int32`;
      `t0h:num->int32`; SIGN65_CPH; `pc:num`] 4] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_PATH_DISCHARGE_TAC;;

let SIGN65_TCASE_TAC =
  SUBGOAL_THEN `17 <= r /\ 6 <= 6` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 17)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SIGN65_R0; SIGN65_CT0; `261692`; `261888`; `12`; `6`]
               SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `17 <= r` THEN UNDISCH_TAC `j < 12` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SIGN65_ACALL_TAC "H_RPRE"
   [`6`; `bot:int64`; SIGN65_W; `s2h:num->int32`;
    `t0h:num->int32`; SIGN65_CPH; `pc:num`] 3 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read RIP s = x`) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_LT_CONV) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 17 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 17 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add bot (word (5638 + j)))) s3 =
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
      `read (memory :> bytes (word_add bot (word 5318),48)) s = C`) (concl th)
    then FIRST_ASSUM(fun cth ->
           if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
           then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES_OFF
                            (TRANS th (SYM cth)))
           else NO_TAC)
    else NO_TAC) THEN
  SIGN65_ACALL_TAC "H_TAIL"
   [`sig:int64`; `bot:int64`; SIGN65_CT; `x:num->int32`;
    `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `17 <= r ==> (r = 18 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `word_zx (mld_pack_hints_ret 55 6 (mld_polyvec_make_hint_32 x b)):int64 =
    (if r = 18 then word 0 else word 4294967295)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC SIGN_PACK_HINTS_RET_ZX THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `mld_pack_hints_ret 55 6 (mld_polyvec_make_hint_32 x b) = word 0`
    ASSUME_TAC THENL
     [REWRITE_TAC[mld_pack_hints_ret] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      ASM_REWRITE_TAC[GSYM NOT_LT];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `mld_pack_hints_ret 55 6 h = word 0 ==> P`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[mld_sign_attempt_sig] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[mld_sign_cphat] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `3309 = (48 + 5 * 640) + 61` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SIGN_SIG_ASSEMBLE THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> can (term_match []
        `!t. t < 640 * 5
             ==> read (memory :> bytes8 (word_add sig (word (48 + t)))) s =
                 P t`) (concl th)));
    SIGN_PATH_DISCHARGE_TAC];;

let SIGN65_PATHS_TAC =
  ASM_CASES_TAC `r < 5` THENL
   [SIGN65_ZCASE_TAC;
    SUBGOAL_THEN `5 <= r /\ 5 <= 5` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 5)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `5 <= r ==> (!i. i < 5 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SIGN65_ACALL_TAC "H_ZPRE"
     [`5`; `sig:int64`; `bot:int64`; `s1h:num->int32`;
      SIGN65_CPH; SIGN65_Y; `pc:num`] 2 THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_CASES_TAC `r < 17` THENL [SIGN65_WCASE_TAC; SIGN65_TCASE_TAC]];;

let SIGN65_ACLEAN_TAC =
  FULL_INIT_TAC THEN
  SIGN65_ACALL_TAC "H_CLEAN" [`r = 18`; `bot:int64`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let SIGN65_ATT = prove
 (SIGN65_ATT_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_HEAD "H_HEAD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_ZPRE "H_ZPRE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_ZFAIL "H_ZFAIL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_RPRE "H_RPRE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_RFAIL1 "H_RFAIL1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_RFAIL2 "H_RFAIL2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_CLEAN "H_CLEAN" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_TAIL "H_TAIL" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (bot:int64) (pc:num) (C:num) (r:num) (x:num->int32)
     (b:num->byte).
     APPEND (f_ev_cl sig bot pc C r x b)
      (APPEND
        (if r < 5 then f_ev_pz sig bot pc C r x b
         else if r < 17
         then if EVEN (r - 5) then f_ev_pw1 sig bot pc C r x b
              else f_ev_pw2 sig bot pc C r x b
         else f_ev_pt sig bot pc C r x b)
        (f_ev_hd sig bot pc C r x b))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `bot:int64`;
    `A:num->int32`; `s1h:num->int32`; `s2h:num->int32`; `t0h:num->int32`;
    `mu:num`; `rhop:num`; `n:num`; `C:num`; `r:num`; `x:num->int32`;
    `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
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
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa65_signature_internal_join3`
    SIGN65_ATT_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    SIGN65_ACALL_TAC "H_HEAD"
     [`bot:int64`; `A:num->int32`; `mu:num`; `rhop:num`; `n:num`;
      `C:num`; `pc:num`] 1 THEN
    SIGN65_PATHS_TAC;
    SIGN65_ACLEAN_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The facts about the attempts that the main proof needs, for D =           *)
(* mld_sign_declass_65 and its number of attempts.                           *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ATT_ARGS =
 `mld_sign_attempt_declass 6 5 48 49 mld_poly_uniform_gamma1_19
   524092 261692 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
   128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
   (mld_polyvec_matrix_expand 5 (mld_sk_rho skb))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\j. skb(128 + j))))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\j. skb(768 + j))))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. skb(1536 + j))))
   MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU)`;;

let SIGN65_DECLASS_FACTS = prove
 (`!skb MU RND.
        0 < mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) /\
        mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) <= 13106 /\
        (!i. i < mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND)
             ==> mld_sign_declass_65 skb MU RND i =
                 mld_sign_attempt_declass 6 5 48 49 mld_poly_uniform_gamma1_19
                  524092 261692 261888
                  (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                  128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
                  (mld_polyvec_matrix_expand 5 (mld_sk_rho skb))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                      (\j. skb(128 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                      (\j. skb(768 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 416 mld_polyt0_unpack
                      (\j. skb(1536 + j))))
                  MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU) (5 * i)) /\
        (!i. i + 1 < mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND)
             ==> ~(FST(SND(mld_sign_declass_65 skb MU RND i)) = 18)) /\
        (mld_sign_ok_65 skb MU RND <=>
         FST(SND(mld_sign_declass_65 skb MU RND
                  (mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) -
                   1))) = 18) /\
        (~mld_sign_ok_65 skb MU RND
         ==> mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) =
             13106) /\
        mld_sign_sig_65 skb MU RND =
        (if mld_sign_ok_65 skb MU RND
         then mld_sign_attempt_sig 6 5 48 49 mld_poly_uniform_gamma1_19
               mld_polyz_pack_19 640
               (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
               mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
               (mld_polyvec_matrix_expand 5 (mld_sk_rho skb))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                   (\j. skb(128 + j))))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                   (\j. skb(768 + j))))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 416 mld_polyt0_unpack
                   (\j. skb(1536 + j))))
               MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU)
               (5 * (mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) -
                     1))
         else \t. word 0) /\
        (mld_sign_terminates_65 skb MU RND
         ==> !i. i < mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND)
                 ==> mld_poly_challenge_terminates 49 48
                      (FST(mld_sign_declass_65 skb MU RND i)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_declass_65; mld_sign_ok_65; mld_sign_sig_65;
              mld_sign_terminates_65] THEN
  MP_TAC(SPECL
   [`6`; `5`; `mld_polyeta_unpack_4`; `128`; `48`; `49`;
    `mld_poly_uniform_gamma1_19`; `524092`; `261692`; `261888`;
    `mld_polyw1_pack_32 o mld_poly_decompose_hi_32`; `128`;
    `mld_poly_decompose_lo_32`; `mld_polyvec_make_hint_32`; `55`; `13106`;
    `skb:num->byte`; `MU:num`; `RND:num`] SIGN_NATT_DECLASS) THEN
  CONV_TAC(LAND_CONV(LAND_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL
   [`6`; `5`; `mld_polyeta_unpack_4`; `128`; `48`; `49`;
    `mld_poly_uniform_gamma1_19`; `524092`; `261692`; `261888`;
    `mld_polyw1_pack_32 o mld_poly_decompose_hi_32`; `128`;
    `mld_poly_decompose_lo_32`; `mld_polyvec_make_hint_32`; `55`; `13106`;
    `skb:num->byte`; `MU:num`; `RND:num`] SIGN_NATTEMPTS_PROPS) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
  ABBREV_TAC
   `N = mld_sign_nattempts 6 5 mld_polyeta_unpack_4 128 48 49
         mld_poly_uniform_gamma1_19 524092 261692 261888
         (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
         mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55 13106
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
(* (mld_sign_natt 13106 18 D, with D what is declassified): an attempt that  *)
(* is followed by another (i + 1 < N), the successful last one, or the last  *)
(* one after which the signature is zeroed (13106 attempts, all rejected),   *)
(* then those of the epilogue. The buffers are at fixed offsets from bot,    *)
(* the bottom of the aligned frame (see utils/mldsa_native_realign.ml),      *)
(* which REALIGN_UNBOT_TAC expands before the events are matched with the    *)
(* template.                                                                 *)
(* ------------------------------------------------------------------------- *)

let SIGN65_TEMPLATE =
 `\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (rnd:int64)
   (sk:int64) (ext:int64) (rh:num)
   (D:num->num#num#(num->int32)#(num->byte)) (mf:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND
    (f_ev_epil sig m mlen pre prelen rnd sk ext rh D mf pc stackpointer
               returnaddress)
    (APPEND
      (ENUMERATEL (mld_sign_natt 13106 18 D)
        (\i. if i + 1 < mld_sign_natt 13106 18 D
             then f_ev_cont sig m mlen pre prelen rnd sk ext rh D mf pc
                    stackpointer returnaddress i
             else if FST(SND(D i)) = 18
             then f_ev_succ sig m mlen pre prelen rnd sk ext rh D mf pc
                    stackpointer returnaddress i
             else f_ev_exh sig m mlen pre prelen rnd sk ext rh D mf pc
                    stackpointer returnaddress i))
      (if word_zx ext = (word 0:int32)
       then f_ev_prolh sig m mlen pre prelen rnd sk ext rh D mf pc
              stackpointer returnaddress
       else f_ev_prolx sig m mlen pre prelen rnd sk ext rh D mf pc
              stackpointer returnaddress))
   :(uarch_event)list`;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop over the attempts: the saved registers (and the *)
(* stack pointer saved in R10 by the prologue), the return address, the GOT  *)
(* entry of memset and the region (ea,el) that it may read, the pointers in  *)
(* the frame, the matrix, s1, s2 and t0 (in NTT form), mu and rho'' do not   *)
(* change; before attempt i the registers of the loop hold the addresses of  *)
(* its buffers and kappa = 5 * i (the 32-bit word at bot + 5258); after the  *)
(* last attempt R13 holds the result and sig the signature.                  *)
(* ------------------------------------------------------------------------- *)

let SIGN65_INV =
 `\i s.
   read RSP s = word_add bot (word 5190) /\
   read RBP s = word_add bot (word 73014) /\
   read (memory :> bytes64 (word_add bot (word 72966))) s = rbx_init /\
   read (memory :> bytes64 (word_add bot (word 72974))) s =
   word_add stackpointer (word 73069) /\
   read (memory :> bytes64 (word_add bot (word 72982))) s = r12_init /\
   read (memory :> bytes64 (word_add bot (word 72990))) s = r13_init /\
   read (memory :> bytes64 (word_add bot (word 72998))) s = r14_init /\
   read (memory :> bytes64 (word_add bot (word 73006))) s = r15_init /\
   read (memory :> bytes64 (word_add bot (word 73014))) s = rbp_init /\
   read (memory :> bytes64 (word_add stackpointer (word 73061))) s =
   returnaddress /\
   (read DF s <=> false) /\
   read (memory :> bytes64 (word(pc + got_memset))) s = mf /\
   read (memory :> bytes(ea,el)) s = ev /\
   read (memory :> bytes64 (word_add bot (word 5190))) s =
   word_add bot (word 5382) /\
   read (memory :> bytes64 (word_add bot (word 5198))) s =
   word_add bot (word 5574) /\
   read (memory :> bytes64 (word_add bot (word 5206))) s =
   word_add bot (word 5510) /\
   read (memory :> bytes64 (word_add bot (word 5214))) s =
   word_add bot (word 42246) /\
   read (memory :> bytes64 (word_add bot (word 5222))) s =
   word_add bot (word 5318) /\
   read (memory :> bytes64 (word_add bot (word 5230))) s =
   word_add bot (word 23814) /\
   read (memory :> bytes64 (word_add bot (word 5238))) s =
   word_add bot (word 29958) /\
   read (memory :> bytes64 (word_add bot (word 5246))) s =
   word_add bot (word 5638) /\
   read (memory :> bytes64 (word_add bot (word 5262))) s =
   word_add bot (word 8454) /\
   read (memory :> bytes64 (word_add bot (word 5270))) s = sig /\
   read (memory :> bytes64 (word_add bot (word 5286))) s =
   word_add bot (word 36102) /\
   read (memory :> bytes64 (word_add bot (word 5294))) s =
   word_add bot (word 13574) /\
   read (memory :> bytes64 (word_add bot (word 5310))) s =
   word_add bot (word 18694) /\
   (!j. j < 7680
        ==> read (memory :> bytes32 (word_add bot (word(42246 + 4 * j)))) s =
            mld_polyvec_matrix_expand 5 rh j) /\
   (!j. j < 1280
        ==> read (memory :> bytes32 (word_add bot (word(8454 + 4 * j)))) s =
            mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 128 mld_polyeta_unpack_4
               (\j. skb(128 + j))) j) /\
   (!j. j < 1536
        ==> read (memory :> bytes32 (word_add bot (word(29958 + 4 * j)))) s =
            mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 128 mld_polyeta_unpack_4
               (\j. skb(768 + j))) j) /\
   (!j. j < 1536
        ==> read (memory :> bytes32 (word_add bot (word(23814 + 4 * j)))) s =
            mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 416 mld_polyt0_unpack
               (\j. skb(1536 + j))) j) /\
   read (memory :> bytes(word_add bot (word 5510),64)) s = MU /\
   read (memory :> bytes(word_add bot (word 5574),64)) s =
   mld_sign_rhoprime (\j. skb(32 + j)) RND MU /\
   (i < mld_sign_natt 13106 18 D
    ==> read RBX s = word_add bot (word 18694) /\
        read R12 s = word_add bot (word 7430) /\
        read R14 s = word_add bot (word 6406) /\
        read R15 s = word_add bot (word 7430) /\
        read (memory :> bytes32 (word_add bot (word 5258))) s =
        word(5 * i)) /\
   (i = mld_sign_natt 13106 18 D
    ==> read R13 s =
        (if mld_sign_ok_65 skb MU RND then word 0 else word 4294967292) /\
        (!t. t < 3309
             ==> read (memory :> bytes8 (word_add sig (word t))) s =
                 mld_sign_sig_65 skb MU RND t))`;;

let SIGN65_MALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `rnd:int64`; `sk:int64`; `ext:int64`; `rh:num`;
   `D:num->num#num#(num->int32)#(num->byte)`; `mf:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let SIGN65_MCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SIGN65_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   SIGN65_MALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The start: the callees and the contract of memset as assumptions, the     *)
(* template, the frame (with the stack pointer at its bottom, the aligned    *)
(* part (bot,73030) of utils/mldsa_native_realign.ml, since the code aligns  *)
(* the stack pointer first, and the alignment of its buffers), the           *)
(* abbreviations rh and D (the arguments of the events), mu, the preserved   *)
(* registers and the facts about the attempts.                               *)
(* ------------------------------------------------------------------------- *)

let SIGN65_START_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_ATT "H_ATT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_MEXP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_H" THEN
  CONCRETIZE_F_EVENTS_TAC SIGN65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `rh = mld_sk_rho skb` THEN
  ABBREV_TAC `D = mld_sign_declass_65 skb MU RND` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `MU = (if p then a else b)`) (concl th))) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  REALIGN_TAC 73061 THEN REALIGN_FRAME_TAC 73061 73061 THEN
  REALIGN_NONOV_TAC 73030
   [`sig:int64,3309`; `m:int64,mlen:num`; `pre:int64,prelen:num`;
    `rnd:int64,32`; `sk:int64,4032`; `word pc:int64,51232`;
    `word(pc + got_memset):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 73061):int64,8`;
    `word_add stackpointer (word 73069):int64,16`] THEN
  REALIGN_ALIGNED_TAC [5318; 7430; 18694; 36102; 73014] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
  MP_TAC(SPECL [`skb:num->byte`; `MU:num`; `RND:num`] SIGN65_DECLASS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The prologue, up to the start of the first attempt: the alignment of the  *)
(* stack pointer, with RSP the value of the AND after step 2, the saved      *)
(* registers, unpack_sk, then on ext either mld_H65 for mu (from tr, the     *)
(* prefix and m) or the inlined copy of 64 bytes from m (as four 128-bit     *)
(* words), then mld_H65 for rho'' (from the key, rnd and mu) and the matrix  *)
(* expansion, from step n0 at join1.                                         *)
(* ------------------------------------------------------------------------- *)

let SIGN65_PROL_TAIL_TAC n0 =
  let sn k = mk_var("s"^string_of_int k,`:x86state`) in
  let nh = n0 + 15 and nm = n0 + 21 in
  let kpat =
   `!j. j < 32 ==> read (memory :> bytes8
         (word_add bot (word (5478 + j)))) s = f j`
  and rgoal =
   `read (memory :> bytes (word_add bot (word 5574),64)) s =
    mld_sign_rhoprime (\j. skb(32 + j)) RND MU`
  and rpat =
   `read (memory :> bytes (word_add bot (word 5574),64)) s =
    num_of_bytelist l` in
  X86_STEPS_TAC SIGN65_EXEC (n0--(nh - 1)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] kpat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN65_MCALL_TAC "H_H"
   [`read RDI s`; `64`; `read RDX s`; `32`; `read R8 s`; `32`;
    `word_add bot (word 5510):int64`; `64`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(32 + j)) 32)`;
    `RND:num`; `MU:num`] nh THEN
  SUBGOAL_THEN (subst [sn nh,`s:x86state`] rgoal) ASSUME_TAC THENL
   [REWRITE_TAC[mld_sign_rhoprime] THEN CONV_TAC SIGN_NUM_ARITH_CONV THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE SIGN_NUM_ARITH_CONV o
      check (fun th -> can (term_match [] rpat) (concl th)));
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] rpat) (concl th))) THEN
  X86_STEPS_TAC SIGN65_EXEC ((nh + 1)--(nm - 1)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 32 ==> read (memory :> bytes8
         (word_add bot (word (5382 + j)))) s = f j`) (concl th)
    then FIRST_ASSUM(fun rth ->
           if is_eq(concl rth) && is_var(rhs(concl rth)) &&
              name_of(rhs(concl rth)) = "rh"
           then ASSUME_TAC(TRANS
                  (REWRITE_RULE[ETA_AX]
                    (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
                  (REWRITE_RULE[mld_sk_rho] rth))
           else NO_TAC)
    else NO_TAC) THEN
  SIGN65_MCALL_TAC "H_MEXP" [`read RDI s`; `read RSI s`; `rh:num`] nm THEN
  X86_STEPS_TAC SIGN65_EXEC ((nm + 1)--(nm + 13)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `0 = n <=> n = 0`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  REALIGN_UNBOT_TAC THEN SIGN_SEL_DISCHARGE_TAC;;

let SIGN65_PROL_H_TAC =
  X86_STEPS_TAC SIGN65_EXEC (40--40) THEN
  FIRST_ASSUM(fun th ->
    if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE
          [ASSUME `word_zx(ext:int64) = (word 0:int32)`] th)
    else NO_TAC) THEN
  X86_STEPS_TAC SIGN65_EXEC (41--51) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 64 ==> read (memory :> bytes8
         (word_add bot (word (5414 + j)))) s = f j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN65_MCALL_TAC "H_H"
   [`read RDI s`; `64`; `read RDX s`; `64`; `read R8 s`; `prelen:num`;
    `m:int64`; `mlen:num`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(64 + j)) 64)`;
    mk_var("PRE'",`:num`); `M:num`] 52 THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add bot (word 5510),64)) s52 = MU`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" &&
         not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_mu] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV));
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
   `read (memory :> bytes (word_add bot (word 5510),64)) s52 =
    num_of_bytelist l`) (concl th))) THEN
  X86_STEPS_TAC SIGN65_EXEC (53--54) THEN
  SIGN65_PROL_TAIL_TAC 55;;

let SIGN65_PROL_X_TAC =
  X86_STEPS_TAC SIGN65_EXEC (40--40) THEN
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
                         `s40:x86state`] SIGN_BYTES128_OF_BYTES) THEN
           ASM_REWRITE_TAC[] THEN
           ANTS_TAC THENL [UNDISCH_TAC `64 <= mlen` THEN ARITH_TAC;
                           CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                           REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC])
         [0;1;2;3]
    else NO_TAC) THEN
  SIGN_GHOST_REGS_TAC [`YMM1`; `YMM2`; `YMM3`; `YMM4`] "s40" THEN
  X86_STEPS_TAC SIGN65_EXEC (41--51) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_SUBWORD_JOIN_128]) THEN
  MP_TAC(SPECL [`word_add bot (word 5510):int64`; `M:num`; `4`;
                `s51:x86state`] SIGN_BYTES_OF_BYTES128) THEN
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
  SUBGOAL_THEN
   `read (memory :> bytes (word_add bot (word 5510),64)) s51 = MU`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" &&
         not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
   `read (memory :> bytes (word_add bot (word 5510),64)) s51 =
    M MOD 2 EXP 512`) (concl th))) THEN
  SIGN65_PROL_TAIL_TAC 52;;

let SIGN65_PROL_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN65_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SIGN65_EXEC (3--21) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIGN_BYTES32_OF_BYTES64 o check (fun th ->
    can (term_match [] `read (memory :> bytes64
      (word_add stackpointer (word 73077))) s = ext`) (concl th))) THEN
  X86_STEPS_TAC SIGN65_EXEC (22--35) THEN
  SIGN65_MCALL_TAC "H_UNPACK"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `read R9 s`; `sk:int64`; `skb:num->byte`] 36 THEN
  X86_STEPS_TAC SIGN65_EXEC (37--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN
  ASM_CASES_TAC `word_zx(ext:int64) = (word 0:int32)` THENL
   [SIGN65_PROL_H_TAC; SIGN65_PROL_X_TAC];;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop over the attempts: the facts about attempt i     *)
(* (its record D i as mld_sign_attempt_declass gives it, the termination of  *)
(* its challenge, and the result and signature if it is the last), the       *)
(* attempt as one step (ATT), then the three exits: on success to join5; on  *)
(* rejection kappa += 5, then back to join2 or, after the last attempt, -4   *)
(* in R13 and the zeroing of the signature, which gcc inlines, to join5. The *)
(* equations for mld_sign_ok_65 and mld_sign_sig_65 are made conditional on  *)
(* ~(i + 1 < N) before any call, which would otherwise rewrite the           *)
(* postcondition with them.                                                  *)
(* ------------------------------------------------------------------------- *)

let SIGN65_BALLOWED = SIGN65_MALLOWED @ [`i:num`];;

let SIGN65_ATT_ILIST =
  [`sig:int64`; `bot:int64`; `mld_polyvec_matrix_expand 5 rh`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 128 mld_polyeta_unpack_4
       (\j. (skb:num->byte)(128 + j)))`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 128 mld_polyeta_unpack_4
       (\j. (skb:num->byte)(768 + j)))`;
   `mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 416 mld_polyt0_unpack
       (\j. (skb:num->byte)(1536 + j)))`;
   `MU:num`; `mld_sign_rhoprime (\j. (skb:num->byte)(32 + j)) RND MU`;
   `i:num`; `FST((D:num->num#num#(num->int32)#(num->byte)) i)`;
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i))`;
   `FST(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `SND(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `pc:num`];;

let SIGN65_DANGER =
  [`mld_sign_ok_65 skb MU RND <=> P`;
   `mld_sign_sig_65 skb MU RND = x`];;

let SIGN65_BODY_INIT_TAC =
  let nth = UNDISCH(MP (ARITH_RULE
   `i < mld_sign_natt 13106 18 D
    ==> ~(i + 1 < mld_sign_natt 13106 18 D)
    ==> mld_sign_natt 13106 18 D - 1 = i`)
   (ASSUME `i < mld_sign_natt 13106 18 D`)) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ASSUME `i < mld_sign_natt 13106 18 D`;
              ASSUME `~(i = mld_sign_natt 13106 18 D)`] THEN
  SUBGOAL_THEN `i < 13106` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 13106 18 D`; `mld_sign_natt 13106 18 D <= 13106`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i < mld_sign_natt 13106 18 D
              ==> (D:num->num#num#(num->int32)#(num->byte)) i = x`)
         (concl th)
    then
      let th1 = MP (SPEC `i:num` th)
                   (ASSUME `i < mld_sign_natt 13106 18 D`) in
      let tup = `FST((D:num->num#num#(num->int32)#(num->byte)) i),
                 FST(SND(D i)),FST(SND(SND(D i))),SND(SND(SND(D i)))` in
      ASSUME_TAC(TRANS (SYM th1) (SYM(REWRITE_CONV[PAIR] tup)))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i < mld_sign_natt 13106 18 D
              ==> mld_poly_challenge_terminates 49 48
                   (FST((D:num->num#num#(num->int32)#(num->byte)) i))`)
         (concl th)
    then ASSUME_TAC(MP (SPEC `i:num` th)
                       (ASSUME `i < mld_sign_natt 13106 18 D`))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i + 1 < mld_sign_natt 13106 18 D
              ==> ~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) =
                    18)`)
         (concl th)
    then ASSUME_TAC(SPEC `i:num` th)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `mld_sign_ok_65 skb MU RND <=> P`) (concl th)
    then ASSUME_TAC(DISCH `~(i + 1 < mld_sign_natt 13106 18 D)`
                     (REWRITE_RULE[nth] th))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `mld_sign_sig_65 skb MU RND = x`) (concl th)
    then ASSUME_TAC(DISCH `~(i + 1 < mld_sign_natt 13106 18 D)`
                     (REWRITE_RULE[nth] th))
    else NO_TAC);;

let SIGN65_BODY_ATT_TAC =
  FULL_INIT_TAC THEN
  REMOVE_THEN "H_ATT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_O2_mc,SIGN65_EXEC,0x0,
       mldsa_native_libmldsa_gcc12_O2_mc,th)
      (`e:(uarch_event)list`::SIGN65_ATT_ILIST) 1 THENL
     [REPEAT(CONJ_TAC THENL
        [SIGN_NUMS_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
      FULL_EXISTS_E2_TAC (ref SIGN65_BALLOWED);
      LABEL_TAC "H_ATT" th]);;

let SIGN65_BODY_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN65_CASE_TH = ASSUME
  `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18`;;

let SIGN65_NCASE_TH = ASSUME
  `~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18)`;;

let SIGN65_LAST_TAC cth =
  SUBGOAL_THEN `i + 1 = mld_sign_natt 13106 18 D` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 13106 18 D`; `~(i + 1 < mld_sign_natt 13106 18 D)`]
    THEN ARITH_TAC;
    DISCH_THEN(fun th -> ASSUME_TAC(EQT_INTRO th))] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `~(i + 1 < mld_sign_natt 13106 18 D)
          ==> (mld_sign_ok_65 skb MU RND <=> P)`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[cth]
          (MP th (ASSUME `~(i + 1 < mld_sign_natt 13106 18 D)`)))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `~(i + 1 < mld_sign_natt 13106 18 D)
          ==> mld_sign_sig_65 skb MU RND = x`) (concl th)
    then FIRST_ASSUM(fun oth ->
           let c = concl oth in
           if c = `mld_sign_ok_65 skb MU RND` ||
              c = `~mld_sign_ok_65 skb MU RND`
           then ASSUME_TAC(REWRITE_RULE[oth]
                 (MP th (ASSUME `~(i + 1 < mld_sign_natt 13106 18 D)`)))
           else NO_TAC)
    else NO_TAC);;

let SIGN65_SUCC_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read R13 s = (if b then x else y)`) (concl th))) THEN
  REWRITE_TAC[SIGN65_CASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18 ==> P`)
    (concl th))) THEN
  REWRITE_TAC[SIGN65_CASE_TH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 13106 18 D)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> can (term_match []
     `i + 1 < mld_sign_natt 13106 18 D ==> P`) (concl th))) THEN
    REWRITE_TAC[SIGN65_CASE_TH];
    ALL_TAC] THEN
  SIGN65_LAST_TAC SIGN65_CASE_TH THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN65_BODY_DISCHARGE_TAC;;

let SIGN65_KAPPA_TAC =
  SUBGOAL_THEN `5 * i + 5 < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `i < 13106` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD; WORD_ZX_ZX_32_64_32]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`5 * i + 5`; `65530`]
                                         SIGN_VAL_WORD_SUB_EQ_0_32)
                               (CONJ (ASSUME `5 * i + 5 < 2 EXP 32`)
                                     (ARITH_RULE `65530 < 2 EXP 32`))]);;

let SIGN65_CONT_TAC =
  SUBGOAL_THEN `~(5 * i + 5 = 65530)` ASSUME_TAC THENL
   [UNDISCH_TAC `i + 1 < 13106` THEN ARITH_TAC; ALL_TAC] THEN
  SIGN_PC_SIMP_TAC THEN
  SUBGOAL_THEN `i + 1 < mld_sign_natt 13106 18 D` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match []
           `~(i + 1 < mld_sign_natt 13106 18 D)
            ==> (mld_sign_ok_65 skb MU RND <=> P)`) (concl th)
      then ASSUME_TAC(REWRITE_RULE[SIGN65_NCASE_TH]
            (MP th (ASSUME `~(i + 1 < mld_sign_natt 13106 18 D)`)))
      else NO_TAC) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `~mld_sign_ok_65 skb MU RND ==> P`) (concl th)
      then MP_TAC(MP th (ASSUME `~mld_sign_ok_65 skb MU RND`))
      else NO_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 13106 18 D`; `~(i + 1 < mld_sign_natt 13106 18 D)`;
      `i + 1 < 13106`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i + 1 = mld_sign_natt 13106 18 D)` ASSUME_TAC THENL
   [UNDISCH_TAC `i + 1 < mld_sign_natt 13106 18 D` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
  SIGN65_BODY_DISCHARGE_TAC;;

let SIGN65_EXH_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [SIGN_SUFFIX_UNIFY_TAC;
    SIGN_STOS_GEN_TAC `sig:int64` 3309 THEN SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN65_EXH_TAC =
  SUBGOAL_THEN `5 * i + 5 = 65530` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(i + 1 < 13106)`; `i < 13106`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIGN_PC_SIMP_TAC THEN
  X86_STEPS_TAC SIGN65_EXEC (8--18) THEN
  SIGN_STOS_PREP_TAC `sig:int64` 3309 THEN
  SIGN_STOS_STEP_TAC SIGN65_EXEC 19 THEN
  SIGN_STOS_DONE_TAC `sig:int64` 3309 19 THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIGN_BYTES8_ZERO o check (fun th ->
    can (term_match [] `read (memory :> bytes(sig,3309)) s = 0`) (concl th)))
  THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 13106 18 D)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mld_sign_natt 13106 18 D <= 13106`; `~(i + 1 < 13106)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SIGN65_LAST_TAC SIGN65_NCASE_TH THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN65_EXH_DISCHARGE_TAC;;

let SIGN65_FAIL_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read R13 s = (if b then x else y)`) (concl th))) THEN
  REWRITE_TAC[SIGN65_NCASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18 ==> P`)
    (concl th))) THEN
  X86_STEPS_TAC SIGN65_EXEC (2--7) THEN
  SIGN65_KAPPA_TAC THEN
  ASM_CASES_TAC `i + 1 < 13106` THENL [SIGN65_CONT_TAC; SIGN65_EXH_TAC];;

let SIGN65_BODY_TAC =
  SIGN65_BODY_INIT_TAC THEN SIGN65_BODY_ATT_TAC THEN
  ASM_CASES_TAC
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18` THENL
   [SIGN65_SUCC_TAC; SIGN65_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The epilogue, from join5: the zeroing of s2, t0 and s1 with REP STOSQ, of *)
(* the matrix with memset, through its PLT stub, and of the 256 bytes of the *)
(* seed buffer with REP STOSQ, the restoring of the registers and the        *)
(* return.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SIGN65_EPIL_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN
  SIGN_BETA_ALL_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN65_EPIL_TAC =
  SIGN_DROP_TAC SIGN65_DANGER THEN
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC SIGN65_EXEC (1--19) THEN
  LIBC_PLT_TAC SIGN65_EXEC (layout "plt_memset") (layout "got_memset") 19
  THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" SIGN65_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref SIGN65_MALLOWED) 21 THEN
  X86_STEPS_TAC SIGN65_EXEC (22--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SIGN_RET_ZX] THEN
  SIGN65_EPIL_DISCHARGE_TAC;;

let SIGN65_MAIN_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mld_sign_natt 13106 18 D`
   `pc + mldsa65_signature_internal_join2`
   `pc + mldsa65_signature_internal_join5` SIGN65_INV THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC; SIGN65_PROL_TAC; SIGN65_BODY_TAC; SIGN65_EPIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  SIGN65_START_TAC THEN SIGN65_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
