(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with the secret key, all the attempts (ML-DSA-65): the proof (see *)
(* signature_internal_65_spec.ml).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/signature_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/unpack_sk_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/H_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_expand_eager_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_uniform_gamma1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_pointwise_montgomery_yvec_eager_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyveck_caddq_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyveck_decompose_pack_w1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_challenge_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_add_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_chknorm_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/pack_sig_z_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/pack_sig_c_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/pack_sig_h_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_4_spec.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;

(* ------------------------------------------------------------------------- *)
(* The proof is in parts, each a FULL lemma for a segment of the code (sp0   *)
(* is the bottom of the frames of the callees, below the frame of the        *)
(* function, which is at sp0 + 5088, and B the base of the buffers, 32-byte  *)
(* aligned). The code of an attempt checks z (the loop over z: ZPRE for the  *)
(* first m polynomials, ZFAIL for the exit at a polynomial whose check       *)
(* fails), then both checks of each row of w0 (the loop over the rows: RPRE  *)
(* for the first m rows, RFAIL1 and RFAIL2 for the exit at a row whose first *)
(* (w0 - c s2) or second (c t0) check fails), and packs c~ and the hints     *)
(* (TAIL). The cleanup and the decision (CLEAN) and the start of an attempt  *)
(* up to the NTT of the challenge (HEAD) are the others. The attempt (ATT)   *)
(* follows from them, with one path for each kind of result r of             *)
(* mld_sign_attempt_declass: r < 5 (z_r fails), 5 <= r < 17 (the check r - 5 *)
(* of the rows fails), 17 (too many hints) and 18 (success).                 *)
(* ------------------------------------------------------------------------- *)
let SIGN65_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_EXEC;;
let SIGN65_MC = mldsa_native_libmldsa_gcc12_Os_mc;;

let SIGN_SHL10 = prove(`!i. word_shl (word i:int64) 10 = word(1024 * i)`,
  GEN_TAC THEN CONV_TAC WORD_RULE);;

let SIGN_LOOP4_TEST = prove
 (`!i. i < 5
       ==> (val (word_add (word i:int64) (word 18446744073709551612)) = 0 <=>
            i + 1 = 5)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIGN_ADD_SWAP = prove
 (`!(b:int64) x y. word_add (word x) (word_add b (word y)) =
                   word_add b (word (y + x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let SIGN_SHL_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (find_term (fun t ->
         try fst(dest_const t) = "word_shl" with Failure _ -> false)) c ||
       can (term_match [] `read X1 s = word_add (word_add b x) (word y)`) c ||
       can (term_match [] `read X0 s = word_add (word_add b x) (word y)`) c ||
       can (term_match [] `read X2 s = word_add (word_add b x) (word y)`) c ||
       can (term_match [] `read X1 s = word_add (word x) (word_add b (word y))`) c ||
       can (term_match [] `read X0 s = word_add (word x) (word_add b (word y))`) c ||
       can (term_match [] `read X2 s = word_add (word x) (word_add b (word y))`) c
    then REWRITE_RULE[SIGN_SHL10; SIGN_ADD_SWAP; GSYM WORD_ADD_ASSOC;
                      GSYM WORD_ADD] th
    else th);;




(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check (sp0 is the bottom of the frames of the callees, below the     *)
(* frame of the function, and B the base of the buffers).                    *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ZPRE_STMT =
 `!mf mc ea el ev.
    memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
    ==> ?f_zpre.
        !e m sig B sp0 s1h cphat y guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ m <= 5 /\
          (!i. i < m
               ==> mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) =
                   word 0) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (B,67632); (sp0,5248)] /\
          ALLPAIRS nonoverlapping [(sig,3309); (B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_loop2) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X20 s = word_add B (word 49152) /\
                    read X22 s = word_add B (word 64512) /\
                    read X23 s = sig /\
                    read X25 s = word_add B (word 65536) /\
                    read X26 s = word 524092 /\
                    read X27 s = word_add B (word 54272) /\
                    read X28 s = word 0 /\
                    read (memory :> bytes64 (word_add sp0 (word 5224))) s =
                    word_add B (word 59392) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s =
                      mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1280
                         ==> read (memory :> bytes32
                                    (word_add B (word(54272 + 4 * j)))) s =
                             y j) /\
                    (!j. j < 1280
                         ==> read (memory :> bytes32
                                    (word_add B (word(59392 + 4 * j)))) s =
                             s1h j) /\
                    read events s = e)
               (\s. read PC s =
                    (if m < 5
                     then word(pc + mldsa65_signature_internal_loop2)
                     else word(pc + mldsa65_signature_internal_loop2_exit1)) /\
                    read X28 s = word m /\
                    (!t. t < 640 * m
                         ==> read (memory :> bytes8
                                    (word_add sig (word(48 + t)))) s =
                             mld_polyvec_pack 640 mld_polyz_pack_19
                              (mld_polyvec (mld_sign_z s1h cphat y)) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_zpre m sig B sp0 guard mf mc pc /\
                       memaccess_inbounds e2
                        [sig,3309; B,67632; sp0,5248;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_zetas),1024]
                        [sig,3309; B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 49152),1024);
                  memory :> bytes(word_add B (word 64512),1024);
                  memory :> bytes(word_add sig (word 48),3200);
                  memory :> bytes(sp0,5088);
                  memory :> bytes(word_add sp0 (word 5240),8)])`;;

let SIGN65_ZALLOWED =
  [`pc:num`; `sig:int64`; `B:int64`; `sp0:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `i:num`];;

let SIGN65_ZCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC name ilist SIGN65_ZALLOWED n;;

let SIGN65_COPY_TAC doff soff f n zs s =
  MP_TAC(SPECL [`B:int64`; doff; soff; `i:num`; n; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 5` THEN ARITH_TAC;
    DISCH_TAC];;

let SIGN65_ZPRE_INV =
 `\i s. read SP s = word_add sp0 (word 5088) /\
        read X20 s = word_add B (word 49152) /\
        read X22 s = word_add B (word 64512) /\
        read X23 s = sig /\
        read X25 s = word_add B (word 65536) /\
        read X26 s = word 524092 /\
        read X27 s = word_add B (word 54272) /\
        read X28 s = word i /\
        read (memory :> bytes64 (word_add sp0 (word 5224))) s =
        word_add B (word 59392) /\
        read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
          s = guard /\
        read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
        mf /\
        read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
        mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add B (word(65536 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 1280
             ==> read (memory :> bytes32 (word_add B (word(54272 + 4 * j))))
                   s = y j) /\
        (!j. j < 1280
             ==> read (memory :> bytes32 (word_add B (word(59392 + 4 * j))))
                   s = s1h j) /\
        (!t. t < 640 * i
             ==> read (memory :> bytes8 (word_add sig (word(48 + t)))) s =
                 mld_polyvec_pack 640 mld_polyz_pack_19
                  (mld_polyvec (mld_sign_z s1h cphat y)) t)`;;

let SIGN65_ZBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--7) THEN
  SIGN_SHL_TAC THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(59392 + 1024 * i)),
                                         1024)) s7` THEN
  LIBC_PLT_TAC SIGN65_EXEC 7 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN65_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN65_ZALLOWED) 12 THEN
  SIGN65_COPY_TAC `64512` `59392` `s1h:num->int32` `1280` `zs:num`
    `s12:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (13--15) THEN
  SIGN65_ZCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s1h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC SIGN65_EXEC (17--18) THEN
  SIGN65_ZCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat`;
    `pc:num`; `read X30 s`] 19 THEN
  ARM_STEPS_TAC SIGN65_EXEC (20--24) THEN
  SIGN_SHL_TAC THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(54272 + 1024 * i)),
                                          1024)) s24` THEN
  LIBC_PLT_TAC SIGN65_EXEC 24 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN65_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN65_ZALLOWED) 29 THEN
  SIGN65_COPY_TAC `49152` `54272` `y:num->int32` `1280` `zs':num`
    `s29:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (30--32) THEN
  SIGN65_ZCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat)`;
    `mld_poly_of y i`; `pc:num`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC SIGN65_EXEC (34--35) THEN
  SIGN65_ZCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_add
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat))
      (mld_poly_of y i)`;
    `pc:num`; `read X30 s`] 36 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (37--39) THEN
  SIGN65_ZCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_z s1h cphat y i`; `read X1 s`;
    `pc:num`; `read X30 s`] 40 THEN
  SUBGOAL_THEN
   `mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) = word 0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV
    (CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) = word 0`]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (41--46) THEN
  SUBGOAL_THEN `i < 5` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 5` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_zx(word_zx(word i:int64):int32):int64 = word i`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `i < 5` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIGN65_ZCALL_TAC "H_PZ"
   [`read X0 s`; `read X1 s`; `mld_sign_z s1h cphat y i`; `i:num`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 47 THEN
  ARM_STEPS_TAC SIGN65_EXEC (48--49) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SIGN_LOOP4_TEST] THEN REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_19`; `640`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_19_LOCAL] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN65_CALLEES_TAC calls =
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  MAP_EVERY (fun (fth,name) -> ASSUME_CALLEE_SAFETY_TAILED_TAC fth name)
   calls;;

let SIGN65_ZCALLEES =
 [MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_PW";
  MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_INV";
  MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_ADD";
  MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_RED";
  MLDSA_NATIVE_POLY_CHKNORM_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_CHK";
  MLDSA_NATIVE_PACK_SIG_Z_65_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_PZ"];;

let SIGN65_ZPRE_CALLEES_TAC calls =
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memcpy_full_contract mc ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY"
    else NO_TAC) THEN
  MAP_EVERY (fun (fth,name) ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
      then ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP fth th) name
      else NO_TAC))
   (filter (fun (fth,_) -> is_imp(snd(strip_forall(concl fth)))) calls) THEN
  MAP_EVERY (fun (fth,name) -> ASSUME_CALLEE_SAFETY_TAILED_TAC fth name)
   (filter (fun (fth,_) -> not(is_imp(snd(strip_forall(concl fth))))) calls);;

let SIGN65_ZPRE_ASYNC = prove_async
 (SIGN65_ZPRE_STMT,
  REPEAT GEN_TAC THEN SIGN65_ZPRE_CALLEES_TAC SIGN65_ZCALLEES THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sig:int64) (B:int64) (sp0:int64) (guard:int64) (mf:int64)
     (mc:int64) (pc:num).
     APPEND (f_ev_back m sig B sp0 guard mf mc pc)
      (APPEND (ENUMERATEL m (\i. f_ev_zit sig B sp0 guard mf mc pc i))
              (f_ev_front m sig B sp0 guard mf mc pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:num`; `sig:int64`; `B:int64`; `sp0:int64`;
    `s1h:num->int32`; `cphat:num->int32`; `y:num->int32`; `guard:int64`;
    `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD]) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_loop2`
     `if m < 5 then pc + mldsa65_signature_internal_loop2
      else pc + mldsa65_signature_internal_loop2_exit1`
     SIGN65_ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN65_ZBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    SIGN_BETA_ALL_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT;
                    ENUMERATEL; APPEND] THEN
    SIGN_NIL_EVENTS_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exit from the loop over z at a polynomial whose norm check fails, to  *)
(* the cleanup (join3) with x26 = -1.                                        *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ZFAIL_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_zfail.
        !e i B sp0 s1h cphat y pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ i < 5 /\
          ~(mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) =
            word 0) /\
          PAIRWISE nonoverlapping [(B,67632); (sp0,5248)] /\
          ALLPAIRS nonoverlapping [(B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_loop2) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X20 s = word_add B (word 49152) /\
                    read X22 s = word_add B (word 64512) /\
                    read X25 s = word_add B (word 65536) /\
                    read X26 s = word 524092 /\
                    read X27 s = word_add B (word 54272) /\
                    read X28 s = word i /\
                    read (memory :> bytes64 (word_add sp0 (word 5224))) s =
                    word_add B (word 59392) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s =
                      mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1280
                         ==> read (memory :> bytes32
                                    (word_add B (word(54272 + 4 * j)))) s =
                             y j) /\
                    (!j. j < 1280
                         ==> read (memory :> bytes32
                                    (word_add B (word(59392 + 4 * j)))) s =
                             s1h j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa65_signature_internal_join3) /\
                    read X26 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_zfail i B sp0 mc pc /\
                       memaccess_inbounds e2
                        [B,67632; sp0,5248; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024]
                        [B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X26; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 49152),1024);
                  memory :> bytes(word_add B (word 64512),1024);
                  memory :> bytes(sp0,5088);
                  memory :> bytes(word_add sp0 (word 5240),8)])`;;

let SIGN65_ZFALLOWED = [`pc:num`; `B:int64`; `sp0:int64`; `mc:int64`; `i:num`];;

let SIGN65_ZFCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC name ilist SIGN65_ZFALLOWED n;;

let SIGN65_ZFCOPY_TAC doff soff f n zs s =
  MP_TAC(SPECL [`B:int64`; doff; soff; `i:num`; n; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 5` THEN ARITH_TAC; DISCH_TAC];;

let SIGN65_ZFAIL_ASYNC = prove_async
 (SIGN65_ZFAIL_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  SIGN65_CALLEES_TAC (butlast SIGN65_ZCALLEES) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(i:num) (B:int64) (sp0:int64) (mc:int64) (pc:num).
     f_ev_zfail i B sp0 mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `i:num`; `B:int64`; `sp0:int64`;
    `s1h:num->int32`; `cphat:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--7) THEN
  SIGN_SHL_TAC THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(59392 + 1024 * i)),
                                         1024)) s7` THEN
  LIBC_PLT_TAC SIGN65_EXEC 7 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN65_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN65_ZFALLOWED) 12 THEN
  SIGN65_ZFCOPY_TAC `64512` `59392` `s1h:num->int32` `1280` `zs:num`
    `s12:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (13--15) THEN
  SIGN65_ZFCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s1h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC SIGN65_EXEC (17--18) THEN
  SIGN65_ZFCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat`;
    `pc:num`; `read X30 s`] 19 THEN
  ARM_STEPS_TAC SIGN65_EXEC (20--24) THEN
  SIGN_SHL_TAC THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(54272 + 1024 * i)),
                                          1024)) s24` THEN
  LIBC_PLT_TAC SIGN65_EXEC 24 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN65_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN65_ZFALLOWED) 29 THEN
  SIGN65_ZFCOPY_TAC `49152` `54272` `y:num->int32` `1280` `zs':num`
    `s29:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (30--32) THEN
  SIGN65_ZFCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat)`;
    `mld_poly_of y i`; `pc:num`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC SIGN65_EXEC (34--35) THEN
  SIGN65_ZFCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_add
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s1h i) cphat))
      (mld_poly_of y i)`;
    `pc:num`; `read X30 s`] 36 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (37--39) THEN
  SIGN65_ZFCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_z s1h cphat y i`; `read X1 s`;
    `pc:num`; `read X30 s`] 40 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV
    (CHANGED_CONV WORD_REDUCE_CONV))) THEN
  ARM_STEPS_TAC SIGN65_EXEC [41] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_z s1h cphat y i) (word 524092) =
      word 0)`]) THEN
  ARM_STEPS_TAC SIGN65_EXEC [42] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass, leaving the rows of x of the hints.                                 *)
(* ------------------------------------------------------------------------- *)

let SIGN65_RPRE_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rpre.
        !e m B sp0 w s2h t0h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ m <= 6 /\
          (!j. j < m
               ==> mld_poly_chknorm
                    (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat j)
                    (word 261692) = word 0 /\
                   mld_poly_chknorm (mld_sign_ct0 t0h cphat j) (word 261888) =
                   word 0) /\
          PAIRWISE nonoverlapping [(B,67632); (sp0,5248)] /\
          ALLPAIRS nonoverlapping [(B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                    word(pc + mldsa65_signature_internal_loop2_exit1) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X20 s = word_add B (word 49152) /\
                    read X24 s = word_add B (word 30720) /\
                    read X25 s = word_add B (word 65536) /\
                    read (memory :> bytes64 (word_add sp0 (word 5216))) s =
                    word_add B (word 36864) /\
                    read (memory :> bytes64 (word_add sp0 (word 5232))) s =
                    word_add B (word 43008) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s =
                      mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(36864 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(43008 + 4 * j)))) s =
                             t0h j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(30720 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                    read events s = e)
               (\s. read PC s =
                    (if m < 6
                     then word(pc + mldsa65_signature_internal_loop3)
                     else word(pc + mldsa65_signature_internal_loop3_exit1)) /\
                    read X26 s = word(1024 * m) /\
                    (!j. j < 256 * m
                         ==> read (memory :> bytes32
                                    (word_add B (word(30720 + 4 * j)))) s =
                             mld_sign_hint_x 6 mld_poly_decompose_lo_32 w s2h
                              t0h cphat j) /\
                    (!j. 256 * m <= j /\ j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(30720 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rpre m B sp0 mc pc /\
                       memaccess_inbounds e2
                        [B,67632; sp0,5248; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024]
                        [B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X26; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 49152),1024);
                  memory :> bytes(word_add B (word 30720),6144);
                  memory :> bytes(sp0,5088)])`;;

let SIGN65_RALLOWED = [`pc:num`; `B:int64`; `sp0:int64`; `mc:int64`; `i:num`];;

let SIGN65_RCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC name ilist SIGN65_RALLOWED n;;

let SIGN65_RCOPY_TAC soff f zs s =
  MP_TAC(SPECL [`B:int64`; `49152`; soff; `i:num`; `1536`; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 6` THEN ARITH_TAC;
    DISCH_TAC];;

let SIGN65_RPRE_INV =
 `\i s. read SP s = word_add sp0 (word 5088) /\
        read X20 s = word_add B (word 49152) /\
        read X24 s = word_add B (word 30720) /\
        read X25 s = word_add B (word 65536) /\
        read X26 s = word(1024 * i) /\
        read (memory :> bytes64 (word_add sp0 (word 5216))) s =
        word_add B (word 36864) /\
        read (memory :> bytes64 (word_add sp0 (word 5232))) s =
        word_add B (word 43008) /\
        read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
        mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add B (word(65536 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 1536
             ==> read (memory :> bytes32 (word_add B (word(36864 + 4 * j))))
                   s = s2h j) /\
        (!j. j < 1536
             ==> read (memory :> bytes32 (word_add B (word(43008 + 4 * j))))
                   s = t0h j) /\
        (!j. j < 256 * i
             ==> read (memory :> bytes32 (word_add B (word(30720 + 4 * j))))
                   s =
                 mld_sign_hint_x 6 mld_poly_decompose_lo_32 w s2h t0h cphat
                  j) /\
        (!j. 256 * i <= j /\ j < 1536
             ==> read (memory :> bytes32 (word_add B (word(30720 + 4 * j))))
                   s = mld_polyvec_map mld_poly_decompose_lo_32 w j)`;;

let SIGN_LOOPR_TEST = prove
 (`!i. i < 6
       ==> (val (word_add (word(1024 * i):int64) (word 18446744073709546496)) =
            0 <=> i + 1 = 6)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIGN65_RFSLICE_TAC s =
  MP_TAC(SPECL [`B:int64`; `30720`; `1536`; `mld_poly_decompose_lo_32`;
                `w:num->int32`; `i:num`; s] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; s]
             `!j. 256 * i <= j /\ j < 1536
                  ==> read (memory :> bytes32
                             (word_add B (word (30720 + 4 * j))))
                        s = Q j`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 6` THEN ARITH_TAC; STRIP_TAC];;

let SIGN65_RFCOPY_TAC soff f zs s =
  MP_TAC(SPECL [`B:int64`; `49152`; soff; `i:num`; `1536`; f; zs; s]
               SIGN_COPY_POLY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 6` THEN ARITH_TAC; DISCH_TAC];;

let SIGN65_RBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 6` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 6` THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--6) THEN SIGN_SHL_TAC THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(36864 + 1024 * i)),
                                         1024)) s6` THEN
  LIBC_PLT_TAC SIGN65_EXEC 6 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN65_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN65_RALLOWED) 11 THEN
  SIGN65_RCOPY_TAC `36864` `s2h:num->int32` `zs:num` `s11:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (12--14) THEN
  SIGN65_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s2h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC SIGN65_EXEC (16--17) THEN
  SIGN65_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat`;
    `pc:num`; `read X30 s`] 18 THEN
  SIGN65_RFSLICE_TAC `s18:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (19--21) THEN SIGN_SHL_TAC THEN
  SIGN65_RCALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`;
    `mld_poly_decompose_lo_32 (mld_poly_of w i)`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat)`;
    `pc:num`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC SIGN65_EXEC (23--24) THEN SIGN_SHL_TAC THEN
  SIGN65_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_sub (mld_poly_decompose_lo_32 (mld_poly_of w i))
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat))`;
    `pc:num`; `read X30 s`] 25 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (26--29) THEN SIGN_SHL_TAC THEN
  SIGN65_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 30 THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
      (word 261692) = word 0`]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (31--36) THEN SIGN_SHL_TAC THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(43008 + 1024 * i)),
                                          1024)) s36` THEN
  LIBC_PLT_TAC SIGN65_EXEC 36 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN65_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN65_RALLOWED) 41 THEN
  SIGN65_RFCOPY_TAC `43008` `t0h:num->int32` `zs':num` `s41:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (42--44) THEN
  SIGN65_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of t0h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC SIGN65_EXEC (46--47) THEN
  SIGN65_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat`;
    `pc:num`; `read X30 s`] 48 THEN
  ARM_STEPS_TAC SIGN65_EXEC (49--50) THEN
  SIGN65_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat)`;
    `pc:num`; `read X30 s`] 51 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (52--54) THEN
  SIGN65_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_ct0 t0h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 55 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) = word 0`]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (56--60) THEN SIGN_SHL_TAC THEN
  SIGN65_RCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`;
    `mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i`;
    `mld_sign_ct0 t0h cphat i`; `pc:num`; `read X30 s`] 61 THEN
  ARM_STEPS_TAC SIGN65_EXEC (62--64) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SIGN_LOOPR_TEST] THEN REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN65_RLOOP_CALLEES =
 [MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_PW";
  MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_INV";
  MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_ADD";
  MLDSA_NATIVE_POLY_SUB_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_SUB";
  MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_RED";
  MLDSA_NATIVE_POLY_CHKNORM_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_CHK"];;

let SIGN65_RPRE_ASYNC = prove_async
 (SIGN65_RPRE_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  SIGN65_CALLEES_TAC SIGN65_RLOOP_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (B:int64) (sp0:int64) (mc:int64) (pc:num).
     APPEND (f_ev_back m B sp0 mc pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit B sp0 mc pc i))
              (f_ev_front B sp0 mc pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:num`; `B:int64`; `sp0:int64`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_loop3`
     `if m < 6 then pc + mldsa65_signature_internal_loop3
      else pc + mldsa65_signature_internal_loop3_exit1`
     SIGN65_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--1) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN65_RBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0;
                    WORD_ADD_0] THEN
    SIGN_CONCRETE_DISCHARGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exits from the loop over the rows at a row whose first check (w0 - c  *)
(* s2) or second check (c t0) fails, to the cleanup (join3) with x26 = -1.   *)
(* ------------------------------------------------------------------------- *)

let SIGN65_RFAIL1_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rfail1.
        !e i B sp0 w s2h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ i < 6 /\
          ~(mld_poly_chknorm
             (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
             (word 261692) = word 0) /\
          PAIRWISE nonoverlapping [(B,67632); (sp0,5248)] /\
          ALLPAIRS nonoverlapping [(B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_loop3) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X20 s = word_add B (word 49152) /\
                    read X24 s = word_add B (word 30720) /\
                    read X25 s = word_add B (word 65536) /\
                    read X26 s = word(1024 * i) /\
                    read (memory :> bytes64 (word_add sp0 (word 5216))) s =
                    word_add B (word 36864) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s =
                      mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(36864 + 4 * j)))) s =
                             s2h j) /\
                    (!j. 256 * i <= j /\ j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(30720 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa65_signature_internal_join3) /\
                    read X26 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rfail1 i B sp0 mc pc /\
                       memaccess_inbounds e2
                        [B,67632; sp0,5248; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024]
                        [B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X26; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 49152),1024);
                  memory :> bytes(word_add B (word 30720),6144);
                  memory :> bytes(sp0,5088)])`;;

let SIGN65_RFAIL_SETUP_TAC tmpl vars =
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  SIGN65_CALLEES_TAC SIGN65_RLOOP_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC vars THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]);;

(*** The first part of a row, up to the norm check of w0 - c s2 ***)

let SIGN65_ROW_HEAD_TAC =
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--6) THEN SIGN_SHL_TAC THEN
  ABBREV_TAC `zs = read (memory :> bytes(word_add B (word(36864 + 1024 * i)),
                                         1024)) s6` THEN
  LIBC_PLT_TAC SIGN65_EXEC 6 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN65_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs:num`;
     `read X30 s`] (ref SIGN65_RALLOWED) 11 THEN
  SIGN65_RFCOPY_TAC `36864` `s2h:num->int32` `zs:num` `s11:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (12--14) THEN
  SIGN65_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of s2h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC SIGN65_EXEC (16--17) THEN
  SIGN65_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat`;
    `pc:num`; `read X30 s`] 18 THEN
  SIGN65_RFSLICE_TAC `s18:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (19--21) THEN SIGN_SHL_TAC THEN
  SIGN65_RCALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`;
    `mld_poly_decompose_lo_32 (mld_poly_of w i)`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat)`;
    `pc:num`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC SIGN65_EXEC (23--24) THEN SIGN_SHL_TAC THEN
  SIGN65_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_sub (mld_poly_decompose_lo_32 (mld_poly_of w i))
      (mld_poly_invntt_tomont
        (mld_poly_pointwise_montgomery (mld_poly_of s2h i) cphat))`;
    `pc:num`; `read X30 s`] 25 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (26--29) THEN SIGN_SHL_TAC THEN
  SIGN65_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 30 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV)));;

let SIGN65_RFAIL1_ASYNC = prove_async
 (SIGN65_RFAIL1_STMT,
  SIGN65_RFAIL_SETUP_TAC
   `\(i:num) (B:int64) (sp0:int64) (mc:int64) (pc:num).
     f_ev_rfail1 i B sp0 mc pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `B:int64`; `sp0:int64`; `w:num->int32`;
    `s2h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN65_ROW_HEAD_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC [31] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
       (word 261692) = word 0)`]) THEN
  ARM_STEPS_TAC SIGN65_EXEC [33] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SIGN65_RFAIL2_STMT =
 `!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> ?f_rfail2.
        !e i B sp0 w s2h t0h cphat pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ i < 6 /\
          mld_poly_chknorm
           (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
           (word 261692) = word 0 /\
          ~(mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) =
            word 0) /\
          PAIRWISE nonoverlapping [(B,67632); (sp0,5248)] /\
          ALLPAIRS nonoverlapping [(B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_loop3) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X20 s = word_add B (word 49152) /\
                    read X24 s = word_add B (word 30720) /\
                    read X25 s = word_add B (word 65536) /\
                    read X26 s = word(1024 * i) /\
                    read (memory :> bytes64 (word_add sp0 (word 5216))) s =
                    word_add B (word 36864) /\
                    read (memory :> bytes64 (word_add sp0 (word 5232))) s =
                    word_add B (word 43008) /\
                    read (memory :> bytes64 (word(pc + got_memcpy))) s =
                      mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             cphat j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(36864 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(43008 + 4 * j)))) s =
                             t0h j) /\
                    (!j. 256 * i <= j /\ j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(30720 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa65_signature_internal_join3) /\
                    read X26 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_rfail2 i B sp0 mc pc /\
                       memaccess_inbounds e2
                        [B,67632; sp0,5248; word(pc + got_memcpy),8;
                         ea,el; word(pc + rodata_mld_zetas),1024]
                        [B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X26; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 49152),1024);
                  memory :> bytes(word_add B (word 30720),6144);
                  memory :> bytes(sp0,5088)])`;;

let SIGN65_RFAIL2_ASYNC = prove_async
 (SIGN65_RFAIL2_STMT,
  SIGN65_RFAIL_SETUP_TAC
   `\(i:num) (B:int64) (sp0:int64) (mc:int64) (pc:num).
     f_ev_rfail2 i B sp0 mc pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `B:int64`; `sp0:int64`; `w:num->int32`;
    `s2h:num->int32`; `t0h:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN65_ROW_HEAD_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `mld_poly_chknorm (mld_sign_r0 mld_poly_decompose_lo_32 w s2h cphat i)
      (word 261692) = word 0`]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (31--36) THEN SIGN_SHL_TAC THEN
  ABBREV_TAC `zs' = read (memory :> bytes(word_add B (word(43008 + 1024 * i)),
                                          1024)) s36` THEN
  LIBC_PLT_TAC SIGN65_EXEC 36 THEN
  SIGN_LIBC_CALL_TAC "H_MEMCPY" SIGN65_EXEC
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `zs':num`;
     `read X30 s`] (ref SIGN65_RALLOWED) 41 THEN
  SIGN65_RFCOPY_TAC `43008` `t0h:num->int32` `zs':num` `s41:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (42--44) THEN
  SIGN65_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; `mld_poly_of t0h i`; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC SIGN65_EXEC (46--47) THEN
  SIGN65_RCALL_TAC "H_INV"
   [`read X0 s`; `mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat`;
    `pc:num`; `read X30 s`] 48 THEN
  ARM_STEPS_TAC SIGN65_EXEC (49--50) THEN
  SIGN65_RCALL_TAC "H_RED"
   [`read X0 s`;
    `mld_poly_invntt_tomont
      (mld_poly_pointwise_montgomery (mld_poly_of t0h i) cphat)`;
    `pc:num`; `read X30 s`] 51 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (52--54) THEN
  SIGN65_RCALL_TAC "H_CHK"
   [`read X0 s`; `mld_sign_ct0 t0h cphat i`;
    `read X1 s`; `pc:num`; `read X30 s`] 55 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  ARM_STEPS_TAC SIGN65_EXEC [56] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   `~(mld_poly_chknorm (mld_sign_ct0 t0h cphat i) (word 261888) =
      word 0)`]) THEN
  ARM_STEPS_TAC SIGN65_EXEC [57] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints, whose result is the value of x26 for  *)
(* the decision.                                                             *)
(* ------------------------------------------------------------------------- *)

let SIGN65_TAIL_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_tail.
        !e sig B sp0 ct (x:num->int32) (b:num->byte) pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\
          PAIRWISE nonoverlapping [(sig,3309); (B,67632); (sp0,5248)] /\
          ALLPAIRS nonoverlapping [(sig,3309); (B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                      word(pc + mldsa65_signature_internal_loop3_exit1) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X20 s = word_add B (word 49152) /\
                    read X23 s = sig /\
                    read X24 s = word_add B (word 30720) /\
                    read (memory :> bytes64 (word_add sp0 (word 5192))) s =
                    word_add B (word 66560) /\
                    read (memory :> bytes64 (word_add sp0 (word 5200))) s =
                    word_add B (word 67584) /\
                    read (memory :> bytes64 (word(pc + got_memset))) s =
                      mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 48
                         ==> read (memory :> bytes8
                                    (word_add B (word(67584 + j)))) s = ct j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(30720 + 4 * j)))) s =
                             x j) /\
                    (!j. j < 768
                         ==> read (memory :> bytes8
                                    (word_add B (word(66560 + j)))) s = b j) /\
                    read events s = e)
               (\s. read PC s =
                    word(pc + mldsa65_signature_internal_join3) /\
                    read X26 s =
                    word_zx(mld_pack_hints_ret 55 6
                             (mld_polyvec_make_hint_32 x b)) /\
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
                       e2 = f_tail sig B sp0 mf pc x b /\
                       memaccess_inbounds e2
                        [sig,3309; B,67632; sp0,5248;
                         word(pc + got_memset),8; ea,el]
                        [sig,3309; B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X26; X30] ,,
                MAYCHANGE
                 [memory :> bytes(sig,48);
                  memory :> bytes(word_add sig (word 3248),61);
                  memory :> bytes(word_add B (word 49152),1024);
                  memory :> bytes(sp0,5088)])`;;

let SIGN65_TAIL_ASYNC = prove_async
 (SIGN65_TAIL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(K ALL_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_PACK_SIG_H_65_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_PH" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_C_65_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_PC" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (B:int64) (sp0:int64) (mf:int64) (pc:num) (x:num->int32)
     (b:num->byte). f_ev_tail sig B sp0 mf pc x b:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `B:int64`; `sp0:int64`;
    `ct:num->byte`; `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; C_RETURN; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--3) THEN
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC "H_PC"
   [`read X0 s`; `read X1 s`; `ct:num->byte`; `pc:num`; `read X30 s`]
   [`pc:num`; `sig:int64`; `B:int64`; `sp0:int64`; `mf:int64`;
    `x:num->int32`; `b:num->byte`] 4 THEN
  ARM_STEPS_TAC SIGN65_EXEC (5--9) THEN
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC "H_PH"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `x:num->int32`;
    `b:num->byte`; `pc:num`; `read SP s`; `read X30 s`]
   [`pc:num`; `sig:int64`; `B:int64`; `sp0:int64`; `mf:int64`;
    `x:num->int32`; `b:num->byte`] 10 THEN
  ARM_STEPS_TAC SIGN65_EXEC (11--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt (the buffers of the attempt are zeroed) and     *)
(* the test of x26: to the zeroing of the buffers of the key on success, else *)
(* to the update of kappa.                                                   *)
(* ------------------------------------------------------------------------- *)

let SIGN65_CLEAN_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_clean.
        !e ok B sp0 pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\
          nonoverlapping (B,67632) (sp0,5248) /\
          ALLPAIRS nonoverlapping [(B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                      word(pc + mldsa65_signature_internal_join3) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X20 s = word_add B (word 49152) /\
                    read X22 s = word_add B (word 64512) /\
                    read X24 s = word_add B (word 30720) /\
                    read X25 s = word_add B (word 65536) /\
                    read X26 s = (if ok then word 0 else word 4294967295) /\
                    read X27 s = word_add B (word 54272) /\
                    read (memory :> bytes64 (word_add sp0 (word 5192))) s =
                    word_add B (word 66560) /\
                    read (memory :> bytes64 (word_add sp0 (word 5200))) s =
                    word_add B (word 67584) /\
                    read (memory :> bytes64 (word(pc + got_memset))) s =
                      mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s =
                    (if ok then word(pc + mldsa65_signature_internal_join5)
                     else word(pc + mldsa65_signature_internal_loop1_next1)) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_clean ok B sp0 mf pc /\
                       memaccess_inbounds e2
                        [B,67632; sp0,5248; word(pc + got_memset),8; ea,el]
                        [B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 30720),6144);
                  memory :> bytes(word_add B (word 49152),5120);
                  memory :> bytes(word_add B (word 54272),5120);
                  memory :> bytes(word_add B (word 64512),1024);
                  memory :> bytes(word_add B (word 65536),1024);
                  memory :> bytes(word_add B (word 66560),768);
                  memory :> bytes(word_add B (word 67584),48);
                  memory :> bytes(sp0,5088)])`;;

let SIGN65_CLEAN_ZERO_TAC n len =
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC "H_ZERO"
   [`read X0 s`; mk_small_numeral len; `pc:num`; `read SP s`; `read X30 s`]
   [`pc:num`; `ok:bool`; `B:int64`; `sp0:int64`; `mf:int64`] n;;

let SIGN65_CLEAN_ASYNC = prove_async
 (SIGN65_CLEAN_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
     "H_ZERO") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (B:int64) (sp0:int64) (mf:int64) (pc:num).
     if ok then f_ev_clean_ok B sp0 mf pc else f_ev_clean_bad B sp0 mf pc
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `ok:bool`; `B:int64`; `sp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  BOOL_CASES_TAC `ok:bool` THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--3) THEN
  SIGN65_CLEAN_ZERO_TAC 4 1024 THEN ARM_STEPS_TAC SIGN65_EXEC (5--7) THEN
  SIGN65_CLEAN_ZERO_TAC 8 1024 THEN ARM_STEPS_TAC SIGN65_EXEC (9--11) THEN
  SIGN65_CLEAN_ZERO_TAC 12 6144 THEN ARM_STEPS_TAC SIGN65_EXEC (13--15) THEN
  SIGN65_CLEAN_ZERO_TAC 16 768 THEN ARM_STEPS_TAC SIGN65_EXEC (17--19) THEN
  SIGN65_CLEAN_ZERO_TAC 20 5120 THEN ARM_STEPS_TAC SIGN65_EXEC (21--23) THEN
  SIGN65_CLEAN_ZERO_TAC 24 5120 THEN ARM_STEPS_TAC SIGN65_EXEC (25--27) THEN
  SIGN65_CLEAN_ZERO_TAC 28 48 THEN ARM_STEPS_TAC SIGN65_EXEC [29] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt: y, w, w1 and its packing, c~ (mld_H65 of mu and  *)
(* w1 packed), the challenge and its NTT.                                    *)
(* ------------------------------------------------------------------------- *)

let SIGN65_HEAD_STMT =
 `!mf mc ea el ev.
    memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
    ==> ?f_head.
        !e B sp0 A mu rhop n C guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ n < 13106 /\
          num_of_bytelist(list_of_seq
           (mld_sign_ctilde 6 128 mu
             (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
               (mld_sign_w 5 A
                 (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)))))
           48) = C /\
          mld_poly_challenge_terminates 49 48 C /\
          PAIRWISE nonoverlapping [(B,67632); (sp0,5248)] /\
          ALLPAIRS nonoverlapping [(B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                      word(pc + mldsa65_signature_internal_loop1) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X19 s = B /\
                    read X21 s = word_add B (word 67328) /\
                    read (memory :> bytes64 (word_add sp0 (word 5192))) s =
                    word_add B (word 66560) /\
                    read (memory :> bytes64 (word_add sp0 (word 5200))) s =
                    word_add B (word 67584) /\
                    read (memory :> bytes16 (word_add sp0 (word 5212))) s =
                    word(5 * n) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 7680
                         ==> read (memory :> bytes32
                                    (word_add B (word(4 * j)))) s = A j) /\
                    read (memory :> bytes(word_add B (word 67456),64)) s =
                      mu /\
                    read (memory :> bytes(word_add B (word 67520),64)) s =
                    rhop /\
                    read events s = e)
               (\s. read PC s =
                    word(pc + mldsa65_signature_internal_loop2) /\
                    read X20 s = word_add B (word 49152) /\
                    read X22 s = word_add B (word 64512) /\
                    read X24 s = word_add B (word 30720) /\
                    read X25 s = word_add B (word 65536) /\
                    read X26 s = word 524092 /\
                    read X27 s = word_add B (word 54272) /\
                    read X28 s = word 0 /\
                    (!j. j < 1280
                         ==> read (memory :> bytes32
                                    (word_add B (word(54272 + 4 * j)))) s =
                             mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)
                              j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(30720 + 4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32
                              (mld_sign_w 5 A
                                (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                                  (5 * n))) j) /\
                    (!j. j < 768
                         ==> read (memory :> bytes8
                                    (word_add B (word(66560 + j)))) s =
                             mld_sign_w1
                              (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                              128
                              (mld_sign_w 5 A
                                (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                                  (5 * n))) j) /\
                    read (memory :> bytes(word_add B (word 67584),48)) s =
                      C /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(65536 + 4 * j)))) s =
                             mld_poly_ntt (mld_poly_challenge 49 48 C) j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_head B sp0 guard mf mc pc C /\
                       memaccess_inbounds e2
                        [B,67632; sp0,5248; word 0,0;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X20; X22; X24; X25; X26; X27; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 30720),6144);
                  memory :> bytes(word_add B (word 49152),5120);
                  memory :> bytes(word_add B (word 54272),5120);
                  memory :> bytes(word_add B (word 65536),1024);
                  memory :> bytes(word_add B (word 66560),768);
                  memory :> bytes(word_add B (word 67584),48);
                  memory :> bytes(sp0,5088)])`;;

let SIGN65_W1 =
 `mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   (mld_sign_w 5 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)))`;;

let SIGN65_W1NUM = mk_comb(`num_of_bytelist`,
  list_mk_comb(`list_of_seq:(num->byte)->num->(byte)list`,[SIGN65_W1; `768`]));;

let SIGN65_HCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC name ilist
   [`pc:num`; `B:int64`; `sp0:int64`; `guard:int64`; `mf:int64`; `mc:int64`;
    `C:num`] n;;

let SIGN65_HEAD_ASYNC = prove_async
 (SIGN65_HEAD_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    MAP_EVERY (fun (fth,name) ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP fth th) name)
     [MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL,
      "H_GAMMA";
      MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_CHAL";
      MLDSA_NATIVE_H_65_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_H"]
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memcpy_full_contract mc ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL
       th) "H_YVEC"
    else NO_TAC) THEN
  MAP_EVERY (fun (fth,name) -> ASSUME_CALLEE_SAFETY_TAILED_TAC fth name)
   [MLDSA_NATIVE_POLYVECK_CADDQ_65_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_CADDQ";
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL,
    "H_DEC";
    MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_NTT"] THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(B:int64) (sp0:int64) (guard:int64) (mf:int64) (mc:int64) (pc:num)
     (C:num). f_ev_head B sp0 guard mf mc pc C:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `B:int64`; `sp0:int64`; `A:num->int32`;
    `mu:num`; `rhop:num`; `n:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_WORD_ZX_16_32_64]) THEN
  SIGN65_HCALL_TAC "H_GAMMA"
   [`read X0 s`; `read X1 s`; `rhop:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 10 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_Y_KAPPA]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (11--18) THEN
  SIGN65_HCALL_TAC "H_YVEC"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `A:num->int32`;
    `mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)`;
    `pc:num`; `read SP s`; `read X30 s`] 19 THEN
  ARM_STEPS_TAC SIGN65_EXEC (20--22) THEN
  SIGN65_HCALL_TAC "H_CADDQ"
   [`read X0 s`;
    `mld_polyvec_map mld_poly_invntt_tomont
      (mld_polyvec_matrix_pointwise_montgomery 5 A
        (mld_polyvec_map mld_poly_ntt
          (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))))`;
    `pc:num`; `read SP s`; `read X30 s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (24--29) THEN
  SIGN65_HCALL_TAC "H_DEC"
   [`read X0 s`; `read X1 s`;
    `mld_sign_w 5 A (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))`;
    `read X2 s`; `pc:num`; `read SP s`; `read X30 s`] 30 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w1]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (31--38) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 768 ==> read (memory :> bytes8
         (word_add B (word (66560 + j)))) s = f j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SUBGOAL_THEN `read (memory :> bytes(word 0,0)) s38 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (val(word_add sp0 (word 4480):int64),608)
      (0,0)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[]; ALL_TAC] THEN
  SIGN65_HCALL_TAC "H_H"
   [`read X0 s`; `48`; `read X2 s`; `64`; `read X4 s`; `768`; `read X6 s`; `0`;
    `mu:num`; SIGN65_W1NUM; `0`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 39 THEN
  ARM_STEPS_TAC SIGN65_EXEC (40--42) THEN
  SUBGOAL_THEN
   (subst [SIGN65_W1NUM,`W1NUM:num`]
    `num_of_bytelist
      (list_of_seq
        (mld_shake256_byte (64 + 768 + 0)
          (mu + 2 EXP (8 * 64) * (W1NUM + 2 EXP (8 * 768) * 0)))
        48) = C`)
   ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C" &&
         can (term_match [] `num_of_bytelist l = C`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde] THEN CONV_TAC SIGN_NUMERAL_CONV THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  SIGN65_HCALL_TAC "H_CHAL"
   [`read X0 s`; `read X1 s`; `C:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 43 THEN
  ARM_STEPS_TAC SIGN65_EXEC (44--45) THEN
  SIGN65_HCALL_TAC "H_NTT"
   [`read X0 s`; `mld_poly_challenge 49 48 C`; `pc:num`; `read X30 s`] 46 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SIGN65_ZPRE = par_await SIGN65_ZPRE_ASYNC;;
let SIGN65_ZFAIL = par_await SIGN65_ZFAIL_ASYNC;;
let SIGN65_RPRE = par_await SIGN65_RPRE_ASYNC;;
let SIGN65_RFAIL1 = par_await SIGN65_RFAIL1_ASYNC;;
let SIGN65_RFAIL2 = par_await SIGN65_RFAIL2_ASYNC;;

(* ------------------------------------------------------------------------- *)
(* A whole attempt, from loop1 to join5 (success) or loop1_next1 (reject),   *)
(* with the events a function of the declassified record (C,r,x,b).         *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ATT_STMT =
 `!mf mc ea el ev.
    memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
    ==> ?f_att.
        !e sig B sp0 A s1h s2h t0h mu rhop n C r x b guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ n < 13106 /\
          mld_sign_attempt_declass 6 5 48 49 mld_poly_uniform_gamma1_19
           524092 261692 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
           128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
           A s1h s2h t0h mu rhop (5 * n) = (C,r,x,b) /\
          mld_poly_challenge_terminates 49 48 C /\
          PAIRWISE nonoverlapping
           [(sig,3309); (B,67632); (sp0,5248)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (B,67632); (sp0,5248)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                      word(pc + mldsa65_signature_internal_loop1) /\
                    read SP s = word_add sp0 (word 5088) /\
                    read X19 s = B /\
                    read X21 s = word_add B (word 67328) /\
                    read X23 s = sig /\
                    read (memory :> bytes64 (word_add sp0 (word 5192))) s =
                    word_add B (word 66560) /\
                    read (memory :> bytes64 (word_add sp0 (word 5200))) s =
                    word_add B (word 67584) /\
                    read (memory :> bytes16 (word_add sp0 (word 5212))) s =
                    word(5 * n) /\
                    read (memory :> bytes64 (word_add sp0 (word 5216))) s =
                    word_add B (word 36864) /\
                    read (memory :> bytes64 (word_add sp0 (word 5224))) s =
                    word_add B (word 59392) /\
                    read (memory :> bytes64 (word_add sp0 (word 5232))) s =
                    word_add B (word 43008) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 7680
                         ==> read (memory :> bytes32
                                    (word_add B (word(4 * j)))) s = A j) /\
                    (!j. j < 1280
                         ==> read (memory :> bytes32
                                    (word_add B (word(59392 + 4 * j)))) s =
                             s1h j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(36864 + 4 * j)))) s =
                             s2h j) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(43008 + 4 * j)))) s =
                             t0h j) /\
                    read (memory :> bytes(word_add B (word 67456),64)) s =
                      mu /\
                    read (memory :> bytes(word_add B (word 67520),64)) s =
                    rhop /\
                    read events s = e)
               (\s. read PC s =
                    (if r = 18
                     then word(pc + mldsa65_signature_internal_join5)
                     else word(pc + mldsa65_signature_internal_loop1_next1)) /\
                    read X26 s =
                      (if r = 18 then word 0 else word 4294967295) /\
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
                       e2 = f_att sig B sp0 guard mf mc pc C r x b /\
                       memaccess_inbounds e2
                        [sig,3309; B,67632; sp0,5248; word 0,0;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,3309; B,67632; sp0,5248]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X20; X22; X24; X25; X26; X27; X28; X30] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_add B (word 30720),6144);
                  memory :> bytes(word_add B (word 49152),5120);
                  memory :> bytes(word_add B (word 54272),5120);
                  memory :> bytes(word_add B (word 64512),1024);
                  memory :> bytes(word_add B (word 65536),1024);
                  memory :> bytes(word_add B (word 66560),768);
                  memory :> bytes(word_add B (word 67584),48);
                  memory :> bytes(sp0,5088);
                  memory :> bytes(word_add sp0 (word 5240),8)])`;;

let SIGN65_ATTALLOWED =
  [`sig:int64`; `B:int64`; `sp0:int64`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `C:num`; `r:num`; `x:num->int32`; `b:num->byte`];;

let SIGN65_ATTCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC name ilist SIGN65_ATTALLOWED n;;

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
 `\s. read SP s = word_add sp0 (word 5088) /\
      read X20 s = word_add B (word 49152) /\
      read X22 s = word_add B (word 64512) /\
      read X24 s = word_add B (word 30720) /\
      read X25 s = word_add B (word 65536) /\
      read X26 s = (if r = 18 then word 0 else word 4294967295) /\
      read X27 s = word_add B (word 54272) /\
      read (memory :> bytes64 (word_add sp0 (word 5192))) s =
      word_add B (word 66560) /\
      read (memory :> bytes64 (word_add sp0 (word 5200))) s =
      word_add B (word 67584) /\
      read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
        mf /\
      read (memory :> bytes(ea,el)) s = ev /\
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
  SIGN65_ATTCALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `B:int64`; `sp0:int64`; `s1h:num->int32`;
    SIGN65_CPH; SIGN65_Y; `guard:int64`; `pc:num`] 2 THEN
  SIGN_PC_SIMP_TAC THEN
  SIGN65_ATTCALL_TAC "H_ZFAIL"
   [`r:num`; `B:int64`; `sp0:int64`; `s1h:num->int32`;
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
  SIGN65_ATTCALL_TAC "H_RPRE"
   [`(r - 5) DIV 2`; `B:int64`; `sp0:int64`; SIGN65_W; `s2h:num->int32`;
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
    SIGN65_ATTCALL_TAC "H_RFAIL1"
     [`(r - 5) DIV 2`; `B:int64`; `sp0:int64`; SIGN65_W; `s2h:num->int32`;
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
    SIGN65_ATTCALL_TAC "H_RFAIL2"
     [`(r - 5) DIV 2`; `B:int64`; `sp0:int64`; SIGN65_W; `s2h:num->int32`;
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
  SIGN65_ATTCALL_TAC "H_RPRE"
   [`6`; `B:int64`; `sp0:int64`; SIGN65_W; `s2h:num->int32`;
    `t0h:num->int32`; SIGN65_CPH; `pc:num`] 3 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read PC s = x`) (concl th))) THEN
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
        ==> read (memory :> bytes8 (word_add B (word (66560 + j)))) s3 =
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
      `read (memory :> bytes (word_add B (word 67584),48)) s = C`) (concl th)
    then FIRST_ASSUM(fun cth ->
           if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
           then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES_OFF
                            (TRANS th (SYM cth)))
           else NO_TAC)
    else NO_TAC) THEN
  SIGN65_ATTCALL_TAC "H_TAIL"
   [`sig:int64`; `B:int64`; `sp0:int64`; SIGN65_CT; `x:num->int32`;
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
    SIGN65_ATTCALL_TAC "H_ZPRE"
     [`5`; `sig:int64`; `B:int64`; `sp0:int64`; `s1h:num->int32`;
      SIGN65_CPH; SIGN65_Y; `guard:int64`; `pc:num`] 2 THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_CASES_TAC `r < 17` THENL [SIGN65_WCASE_TAC; SIGN65_TCASE_TAC]];;
let SIGN65_ACLEAN_TAC =
  FULL_INIT_TAC THEN
  SIGN65_ATTCALL_TAC "H_CLEAN"
   [`r = 18`; `B:int64`; `sp0:int64`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let SIGN65_TAIL = par_await SIGN65_TAIL_ASYNC;;
let SIGN65_CLEAN = par_await SIGN65_CLEAN_ASYNC;;
let SIGN65_HEAD = par_await SIGN65_HEAD_ASYNC;;

let SIGN65_ATT_ASYNC = prove_async
 (SIGN65_ATT_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN65_HEAD th) "H_HEAD" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN65_ZPRE th) "H_ZPRE"
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memcpy_full_contract mc ea el ev`) (concl th) then
    MAP_EVERY (fun (fth,name) ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP fth th) name)
     [SIGN65_ZFAIL,"H_ZFAIL"; SIGN65_RPRE,"H_RPRE";
      SIGN65_RFAIL1,"H_RFAIL1"; SIGN65_RFAIL2,"H_RFAIL2"]
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    MAP_EVERY (fun (fth,name) ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP fth th) name)
     [SIGN65_TAIL,"H_TAIL"; SIGN65_CLEAN,"H_CLEAN"]
    else NO_TAC) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (B:int64) (sp0:int64) (guard:int64) (mf:int64) (mc:int64)
      (pc:num) (C:num) (r:num) (x:num->int32) (b:num->byte).
      APPEND (f_ev_cl sig B sp0 guard mf mc pc C r x b)
       (APPEND
         (if r < 5 then f_ev_pz sig B sp0 guard mf mc pc C r x b
          else if r < 17
          then if EVEN (r - 5) then f_ev_pw1 sig B sp0 guard mf mc pc C r x b
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
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa65_signature_internal_join3`
    SIGN65_ATT_MID THEN
  CONJ_TAC THENL
  [FULL_INIT_TAC THEN
   SIGN65_ATTCALL_TAC "H_HEAD"
    [`B:int64`; `sp0:int64`; `A:num->int32`; `mu:num`; `rhop:num`; `n:num`;
     `C:num`; `guard:int64`; `pc:num`] 1 THEN
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

let SIGN65_DECLASS_FACTS_ASYNC = prove_async
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
(* then those of the epilogue; all of it twice, for the two positions of     *)
(* the buffers, at stackpointer + 5248 if stackpointer is a multiple of 32   *)
(* and at stackpointer + 5264 otherwise.                                     *)
(* ------------------------------------------------------------------------- *)

let SIGN65_TEMPLATE =
 `\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (rnd:int64)
   (sk:int64) (ext:int64) (rh:num)
   (D:num->num#num#(num->int32)#(num->byte)) (guard:int64) (mf:int64)
   (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
   if aligned 32 stackpointer then
     APPEND
      (f_ev_epila sig m mlen pre prelen rnd sk ext rh D guard mf mc pc
                  stackpointer returnaddress)
      (APPEND
        (ENUMERATEL (mld_sign_natt 13106 18 D)
          (\i. if i + 1 < mld_sign_natt 13106 18 D
               then f_ev_conta sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i
               else if FST(SND(D i)) = 18
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
        (ENUMERATEL (mld_sign_natt 13106 18 D)
          (\i. if i + 1 < mld_sign_natt 13106 18 D
               then f_ev_contu sig m mlen pre prelen rnd sk ext rh D guard mf
                      mc pc stackpointer returnaddress i
               else if FST(SND(D i)) = 18
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
(* change; before attempt i kappa = 5 * i (the 32-bit word at sp + 124);     *)
(* after the last attempt x26 holds the result and sig the signature.        *)
(* ------------------------------------------------------------------------- *)

let SIGN65_INV b =
  let nm n = mk_small_numeral n in
  subst
   [nm b,`oBB:num`; nm(b + 59392),`oS1:num`; nm(b + 36864),`oS2:num`;
    nm(b + 43008),`oT0:num`; nm(b + 66560),`oW1P:num`;
    nm(b + 67328),`oSEED:num`; nm(b + 67456),`oMUO:num`;
    nm(b + 67520),`oRHO:num`; nm(b + 67584),`oCT:num`]
  `\i s.
     read SP s = word_add stackpointer (word 5088) /\
     read (memory :> bytes64 (word_add stackpointer (word 5088))) s =
     x19_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5096))) s =
     x20_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5104))) s =
     x21_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5112))) s =
     x22_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5120))) s =
     x23_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5128))) s =
     x24_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5136))) s =
     x25_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5144))) s =
     x26_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5152))) s =
     x27_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5160))) s =
     x28_init /\
     read (memory :> bytes64 (word_add stackpointer (word 5168))) s =
     returnaddress /\
     read (memory :> bytes64 (word_add stackpointer (word 72904))) s =
     canary /\
     read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
       s = guard /\
     read (memory :> bytes64 guard) s = canary /\
     read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
       mf /\
     read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
       mc /\
     read (memory :> bytes(ea,el)) s = ev /\
     read X19 s = word_add stackpointer (word oBB) /\
     read X21 s = word_add stackpointer (word oSEED) /\
     read X23 s = sig /\
     read (memory :> bytes64 (word_add stackpointer (word 5192))) s =
     word_add stackpointer (word oW1P) /\
     read (memory :> bytes64 (word_add stackpointer (word 5200))) s =
     word_add stackpointer (word oCT) /\
     read (memory :> bytes64 (word_add stackpointer (word 5216))) s =
     word_add stackpointer (word oS2) /\
     read (memory :> bytes64 (word_add stackpointer (word 5224))) s =
     word_add stackpointer (word oS1) /\
     read (memory :> bytes64 (word_add stackpointer (word 5232))) s =
     word_add stackpointer (word oT0) /\
     (!j. j < 7680
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oBB + 4 * j)))) s =
              mld_polyvec_matrix_expand 5 rh j) /\
     (!j. j < 1280
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oS1 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                 (\j. skb(128 + j))) j) /\
     (!j. j < 1536
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oS2 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                 (\j. skb(768 + j))) j) /\
     (!j. j < 1536
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (oT0 + 4 * j)))) s =
              mld_polyvec_map mld_poly_ntt
               (mld_polyvec_unpack 416 mld_polyt0_unpack
                 (\j. skb(1536 + j))) j) /\
     read (memory :> bytes(word_add stackpointer (word oMUO),64)) s = MU /\
     read (memory :> bytes(word_add stackpointer (word oRHO),64)) s =
     mld_sign_rhoprime (\j. skb(32 + j)) RND MU /\
     (i < mld_sign_natt 13106 18 D
      ==> read (memory :> bytes32 (word_add stackpointer (word 5212))) s =
          word(5 * i)) /\
     (i = mld_sign_natt 13106 18 D
      ==> read X26 s =
          (if mld_sign_ok_65 skb MU RND then word 0 else word 4294967292) /\
          (!t. t < 3309
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   mld_sign_sig_65 skb MU RND t))`;;

let SIGN65_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 5279 5248 5264;;

let SIGN65_MALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `rnd:int64`; `sk:int64`; `ext:int64`; `rh:num`;
   `D:num->num#num#(num->int32)#(num->byte)`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let SIGN65_MCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC name ilist SIGN65_MALLOWED n;;

let SIGN65_NUMV s b k = subst [mk_small_numeral(b + k), mk_var(s,`:num`)];;

(* ------------------------------------------------------------------------- *)
(* The start: the callees as assumptions, the template, the frame (with the  *)
(* stack pointer at its bottom), the abbreviations rh and D (the arguments   *)
(* of the events), mu, the canary, the preserved registers and the facts     *)
(* about the attempts.                                                       *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ATT = par_await SIGN65_ATT_ASYNC;;
let SIGN65_DECLASS_FACTS = par_await SIGN65_DECLASS_FACTS_ASYNC;;

let SIGN65_START_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if is_conj(concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN65_ATT th) "H_ATT"
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    MAP_EVERY (fun (fth,name) ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP fth th) name)
     [MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL,
      "H_MEXP";
      MLDSA_NATIVE_H_65_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_H";
      MLDSA_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_ZERO"]
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_UNPACK_SK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  CONCRETIZE_F_EVENTS_TAC SIGN65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`;
    `pre:int64`; `prelen:num`; `rnd:int64`; `sk:int64`; `ext:int64`;
    `skb:num->byte`; `M:num`; mk_var("PRE",`:num`); `RND:num`; `MU:num`;
    `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 72912 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC `rh = mld_sk_rho skb` THEN
  ABBREV_TAC `D = mld_sign_declass_65 skb MU RND` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `MU = (if p then a else b)`) (concl th))) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 72912):int64)` THEN
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
  MP_TAC(SPECL [`skb:num->byte`; `MU:num`; `RND:num`] SIGN65_DECLASS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The prologue, up to the start of the first attempt: unpack_sk, then on    *)
(* ext either mld_H65 for mu (from tr, the prefix and m) or the inlined copy *)
(* of 64 bytes from m (as four 128-bit words), then mld_H65 for rho'' (from  *)
(* the key, rnd and mu) and the matrix expansion. The offsets from b are     *)
(* those of rho, tr and the key in the seed buffer, mu and rho''.            *)
(* ------------------------------------------------------------------------- *)

let SIGN65_RHO_TAC b =
  let pat = SIGN65_NUMV "oRHO" b 67328
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

let SIGN65_PROL_TAIL_TAC b n0 =
  let sn k = mk_var("s"^string_of_int k,`:armstate`) in
  let nh = n0 + 9 and nm = n0 + 13 in
  let kpat = SIGN65_NUMV "oKEY" b 67424
   `!j. j < 32 ==> read (memory :> bytes8
         (word_add stackpointer (word (oKEY + j)))) s = f j`
  and rgoal = SIGN65_NUMV "oRHO" b 67520
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    mld_sign_rhoprime (\j. skb(32 + j)) RND MU`
  and rpat = SIGN65_NUMV "oRHO" b 67520
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    num_of_bytelist l` in
  ARM_STEPS_TAC SIGN65_EXEC (n0--(nh - 1)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] kpat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN65_MCALL_TAC "H_H"
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
  ARM_STEPS_TAC SIGN65_EXEC ((nh + 1)--(nm - 1)) THEN
  SIGN65_RHO_TAC b THEN
  SIGN65_MCALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; `rh:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] nm THEN
  ARM_STEPS_TAC SIGN65_EXEC ((nm + 1)--(nm + 7)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `0 = n <=> n = 0`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  SIGN_SEL_DISCHARGE_TAC;;

let SIGN65_MU_TAC b n =
  let sv = mk_var("s"^string_of_int n,`:armstate`) in
  let mgoal = subst [sv,`s:armstate`] (SIGN65_NUMV "oMU" b 67456
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s = MU`)
  and mpat = subst [sv,`s:armstate`] (SIGN65_NUMV "oMU" b 67456
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

let SIGN65_PROL_H_TAC b =
  let tpat = SIGN65_NUMV "oTR" b 67360
   `!j. j < 64 ==> read (memory :> bytes8
         (word_add stackpointer (word (oTR + j)))) s = f j` in
  ARM_STEPS_TAC SIGN65_EXEC (45--46) THEN
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  ARM_STEPS_TAC SIGN65_EXEC (47--54) THEN
  SIGN_SHL_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] tpat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN65_MCALL_TAC "H_H"
   [`read X0 s`; `64`; `read X2 s`; `64`; `read X4 s`; `prelen:num`;
    `read X6 s`; `mlen:num`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(64 + j)) 64)`;
    mk_var("PRE",`:num`); `M:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 55 THEN
  FIRST_ASSUM(fun th ->
    if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE
          [ASSUME `word_zx(ext:int64) = (word 0:int32)`] th)
    else NO_TAC) THEN
  SIGN65_MU_TAC b 55 THEN
  SIGN65_PROL_TAIL_TAC b 56;;

let SIGN65_M128_TAC s =
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

let SIGN65_PROL_X_TAC b =
  let mu = SIGN65_NUMV "oMU" b 67456
   `word_add stackpointer (word oMU):int64` in
  let mgoal = SIGN65_NUMV "oMU" b 67456
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s51 = MU`
  and mpat = SIGN65_NUMV "oMU" b 67456
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s51 =
    M MOD 2 EXP 512` in
  ARM_STEPS_TAC SIGN65_EXEC (45--46) THEN
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  SIGN65_M128_TAC `s46:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (47--51) THEN
  MP_TAC(SPECL [mu; `M:num`; `4`; `s51:armstate`] SIGN_BYTES_OF_BYTES128) THEN
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
  SIGN65_PROL_TAIL_TAC b 52;;

let SIGN65_PROL_TAC b =
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (8--12) THEN
  MEXP_BUFFER_TAC SIGN65_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC SIGN65_EXEC (13--43) THEN
  SIGN65_MCALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `read X6 s`; `skb:num->byte`; `pc:num`; `read SP s`;
    `read X30 s`] 44 THEN
  ASM_CASES_TAC `word_zx(ext:int64) = (word 0:int32)` THENL
   [SIGN65_PROL_H_TAC b; SIGN65_PROL_X_TAC b];;

(*** The bytes of a region that is zero ***)

let SIGN_BYTES_ZERO = prove
 (`!(a:int64) n (s:armstate).
        read (memory :> bytes(a,n)) s = 0
        ==> !j. j < n
                ==> read (memory :> bytes8 (word_add a (word j))) s = word 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `0`; `j:num`; `s:armstate`]
               READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_SIMP_TAC[DIV_0; MOD_0; ARITH_RULE `j + 1 <= n <=> j < n`] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop over the attempts: the facts about attempt i     *)
(* (its record D i as mld_sign_attempt_declass gives it, the termination of  *)
(* its challenge, and the result and signature if it is the last), the       *)
(* attempt as one step (ATT, with B = stackpointer + b and sp0 =             *)
(* stackpointer + 640), then the three exits: on success to join4; on        *)
(* rejection kappa += 4, then back to loop1 or, after the last attempt, -4   *)
(* in x23 and the zeroing of the signature with memset, to join4. The        *)
(* equations for mld_sign_ok_65 and mld_sign_sig_65 are made conditional on  *)
(* ~(i + 1 < N) before any call, which would otherwise rewrite the           *)
(* postcondition with them.                                                  *)
(* ------------------------------------------------------------------------- *)

let SIGN65_BALLOWED = SIGN65_MALLOWED @ [`i:num`];;

let SIGN65_ATT_ILIST b =
  [`sig:int64`; mk_comb(`word_add stackpointer:int64->int64`,
                        mk_comb(`word:num->int64`,mk_small_numeral b));
   `stackpointer:int64`;
   `mld_polyvec_matrix_expand 5 rh`;
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
   `guard:int64`; `pc:num`];;

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

let SIGN65_BODY_ATT_TAC b =
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes32
             (word_add stackpointer (word 5212))) s0 = word (5 * i)`)
           (concl th)
    then ASSUME_TAC(MATCH_MP SIGN_BYTES16_OF_BYTES32
          (CONJ th (MP (ARITH_RULE `i < 13106 ==> 5 * i < 65536`)
                       (ASSUME `i < 13106`))))
    else NO_TAC) THEN
  REMOVE_THEN "H_ATT" (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (SIGN65_MC,SIGN65_EXEC,0x0,SIGN65_MC,th)
      (`e:(uarch_event)list`::SIGN65_ATT_ILIST b) 1 THENL
     [REPEAT(CONJ_TAC THENL
        [SIGN_NUMS_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
      FULL_EXISTS_E2_TAC (ref SIGN65_BALLOWED);
      LABEL_TAC "H_ATT" th]);;

let SIGN65_BODY_DISCHARGE_TAC =
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
    `read X26 s = (if b then x else y)`) (concl th))) THEN
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

let SIGN65_MEMSET_TAC allowed n =
  LIBC_PLT_TAC SIGN65_EXEC n THEN
  SIGN_LIBC_CALL_TAC "H_MEMSET" SIGN65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref allowed) (n + 5);;

let SIGN65_KAPPA_TAC =
  SUBGOAL_THEN `5 * i + 5 < 65536` ASSUME_TAC THENL
   [UNDISCH_TAC `i < 13106` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_KAPPA_ZX; SIGN_KAPPA_CMP]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`5 * i`; `5`; `65530`]
                                         SIGN_KAPPA_NEXT)
                               (CONJ (ASSUME `5 * i + 5 < 65536`)
                                     (ARITH_RULE `65530 < 65536`))]);;

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

let SIGN65_EXH_TAC =
  SUBGOAL_THEN `5 * i + 5 = 65530` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(i + 1 < 13106)`; `i < 13106`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIGN_PC_SIMP_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (11--14) THEN
  FULL_CALL_TAC SIGN65_MC SIGN65_EXEC "H_ZERO"
   [`read X0 s`; `3309`; `pc:num`; `read SP s`; `read X30 s`]
   SIGN65_BALLOWED 15 THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 13106 18 D)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mld_sign_natt 13106 18 D <= 13106`; `~(i + 1 < 13106)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SIGN65_LAST_TAC SIGN65_NCASE_TH THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIGN_BYTES_ZERO o check (fun th ->
    can (term_match [] `read (memory :> bytes(a,3309)) s = 0`) (concl th))) THEN
  DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN65_BODY_DISCHARGE_TAC;;

let SIGN65_FAIL_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read X26 s = (if b then x else y)`) (concl th))) THEN
  REWRITE_TAC[SIGN65_NCASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18 ==> P`)
    (concl th))) THEN
  ARM_STEPS_TAC SIGN65_EXEC (2--10) THEN
  SIGN65_KAPPA_TAC THEN
  ASM_CASES_TAC `i + 1 < 13106` THENL [SIGN65_CONT_TAC; SIGN65_EXH_TAC];;

let SIGN65_BODY_TAC b =
  SIGN65_BODY_INIT_TAC THEN SIGN65_BODY_ATT_TAC b THEN
  ASM_CASES_TAC
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18` THENL
   [SIGN65_SUCC_TAC; SIGN65_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The epilogue, from join5: the zeroing of s2, t0, s1, the matrix and the   *)
(* seed buffer, and the check of the canary.                                 *)
(* ------------------------------------------------------------------------- *)

let SIGN65_EPIL_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN65_EPIL_TAC =
  SIGN_DROP_TAC SIGN65_DANGER THEN
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (1--3) THEN
  SIGN65_MCALL_TAC "H_ZERO"
   [`read X0 s`; `6144`; `pc:num`; `read SP s`; `read X30 s`] 4 THEN
  ARM_STEPS_TAC SIGN65_EXEC (5--7) THEN
  SIGN65_MCALL_TAC "H_ZERO"
   [`read X0 s`; `6144`; `pc:num`; `read SP s`; `read X30 s`] 8 THEN
  ARM_STEPS_TAC SIGN65_EXEC (9--11) THEN
  SIGN65_MCALL_TAC "H_ZERO"
   [`read X0 s`; `5120`; `pc:num`; `read SP s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC SIGN65_EXEC (13--15) THEN
  SIGN65_MCALL_TAC "H_ZERO"
   [`read X0 s`; `30720`; `pc:num`; `read SP s`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC SIGN65_EXEC (17--19) THEN
  SIGN65_MCALL_TAC "H_ZERO"
   [`read X0 s`; `256`; `pc:num`; `read SP s`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC SIGN65_EXEC (21--21) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (22--39) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SIGN_RET_ZX] THEN
  SIGN65_EPIL_DISCHARGE_TAC;;

let SIGN65_MAIN_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `mld_sign_natt 13106 18 D`
   `pc + mldsa65_signature_internal_loop1`
   `pc + mldsa65_signature_internal_join5` (SIGN65_INV b) THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC; SIGN65_PROL_TAC b; SIGN65_BODY_TAC b; SIGN65_EPIL_TAC];;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  SIGN65_START_TAC THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    SIGN65_MAIN_TAC 5248;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    SIGN65_MAIN_TAC 5264]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
