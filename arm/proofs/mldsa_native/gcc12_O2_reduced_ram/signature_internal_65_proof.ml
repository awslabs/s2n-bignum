(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with the secret key, all the attempts (ML-DSA-65): the proof (see *)
(* signature_internal_65_spec.ml).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_sk_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/H_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_caddq_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_decompose_pack_w1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_gamma1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyeta_unpack_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyt0_unpack_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_chknorm_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_z_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_c_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_h_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let SIGN65_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The proof is in parts, each a FULL lemma for a segment of the code (sp is *)
(* the stack pointer in the loop, sp0 = sp - 1568 the bottom of the frames   *)
(* of the callees, and B the base of the buffers, 32-byte aligned). The loop *)
(* over z up to an index m (ZPRE), the exit at a z whose norm check fails    *)
(* (ZFAIL), the loop over the rows of w0 up to a row m (RPRE), the exits at  *)
(* a row whose first or second check fails (RFAIL1, RFAIL2), the packing of  *)
(* c~ and the hints (TAIL), the cleanup and the decision (CLEAN), and the    *)
(* start of an attempt up to the NTT of the challenge (HEAD). The attempt    *)
(* (ATT) follows from them, with one path for each kind of result r of       *)
(* mld_sign_attempt_declass: r < 4 (z_r fails), 4 <= r < 12 (the check r - 4 *)
(* of the rows fails), 12 (too many hints) and 13 (success). Unlike the      *)
(* eager code, the code keeps neither the matrix nor s1, s2 and t0 in NTT    *)
(* form: each polynomial of s1, s2 and t0 is unpacked from the secret key    *)
(* and transformed where it is used, each entry of the matrix is sampled     *)
(* from rho where it is used (in w = A y), and y is sampled again from rho'' *)
(* for z.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check. Polynomial i of z is computed from polynomial i of s1,        *)
(* unpacked from the secret key (at s1p, a pointer into it that              *)
(* mldsa65_unpack_sk leaves at B + 11456) and transformed, and from          *)
(* polynomial i of y, sampled again from rho'' (at B + 11232, which the     *)
(* structure at B + 11360 points to and holds with the nonce k) with the     *)
(* nonce k + i.                                                              *)
(* ------------------------------------------------------------------------- *)

(*** The offset of polynomial i of s1 in the secret key, as the code
     computes it (x23 shifted left by 7) ***)

let SIGN65_SHL7_ASYNC = prove_async
 (`!i. word_shl (word i:int64) 7 = word(128 * i)`,
  REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIGN65_S1H =
  `mld_polyvec_map mld_poly_ntt
    (mld_polyvec_unpack 128 mld_polyeta_unpack_4 (s1b:num->byte))`;;

let SIGN65_YY = `mld_sign_y mld_poly_uniform_gamma1_19 rhop k`;;

let SIGN65_ZPRE_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_zpre.
        !e m sig B sp s1p s1b cphat rhop k guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ m <= 5 /\
          (!i. i < m
               ==> mld_poly_chknorm
                    (mld_sign_z
                      (mld_polyvec_map mld_poly_ntt
                        (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s1b))
                      cphat (mld_sign_y mld_poly_uniform_gamma1_19 rhop k) i)
                    (word 524092) =
                   word 0) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (B,11464); (sp,112);
            (word_sub sp (word 1328),1328)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (B,11464); (word_sub sp (word 1328),1328)]
           [(s1p,640); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_loop2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 9248) /\
                    read X20 s = word_add B (word 7200) /\
                    read X22 s = B /\
                    read X24 s = word_add B (word 8224) /\
                    read X26 s = word_add B (word 11264) /\
                    read X23 s = word 0 /\
                    read (memory :> bytes64 (word_add sp (word 96))) s = sig /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64 (word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes64 (word_add B (word 11456))) s = s1p /\
                    read (memory :> bytes64 (word_add B (word 11360))) s =
                    word_add B (word 11232) /\
                    read (memory :> bytes16 (word_add B (word 11368))) s =
                    word k /\
                    read (memory :> bytes(word_add B (word 11232),64)) s =
                    rhop /\
                    (!j. j < 640
                         ==> read (memory :> bytes8 (word_add s1p (word j))) s =
                             s1b j) /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(8224 + 4 * j)))) s =
                             cphat j) /\
                    read events s = e)
               (\s. read PC s =
                    (if m < 5
                     then word(pc + mldsa65_signature_internal_loop2)
                     else word(pc + mldsa65_signature_internal_loop2_exit1)) /\
                    read X23 s = word m /\
                    (!t. t < 640 * m
                         ==> read (memory :> bytes8
                                    (word_add sig (word(48 + t)))) s =
                             mld_polyvec_pack 640 mld_polyz_pack_19
                              (mld_polyvec
                                (mld_sign_z
                                  (mld_polyvec_map mld_poly_ntt
                                    (mld_polyvec_unpack 128
                                      mld_polyeta_unpack_4 s1b))
                                  cphat
                                  (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                                    k))) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_zpre m sig B sp s1p guard mf pc /\
                       memaccess_inbounds e2
                        [sig,3309; B,11464; sp,112;
                         word_sub sp (word 1328),1328; s1p,640;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,3309; B,11464; word_sub sp (word 1328),1328]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X23; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 7200),1024);
                  memory :> bytes(word_add B (word 9248),1024);
                  memory :> bytes(word_add sig (word 48),3200);
                  memory :> bytes(word_sub sp (word 1328),1328)])`;;

let SIGN65_ZALLOWED =
  [`pc:num`; `sig:int64`; `B:int64`; `sp:int64`; `s1p:int64`;
   `guard:int64`; `mf:int64`; `i:num`];;

let SIGN65_ZCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc SIGN65_EXEC name
   ilist SIGN65_ZALLOWED n;;

let SIGN65_ZPRE_INV =
 `\i s. read SP s = sp /\
        read X19 s = word_add B (word 9248) /\
        read X20 s = word_add B (word 7200) /\
        read X22 s = B /\
        read X24 s = word_add B (word 8224) /\
        read X26 s = word_add B (word 11264) /\
        read X23 s = word i /\
        read (memory :> bytes64 (word_add sp (word 96))) s = sig /\
        read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
          s = guard /\
        read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
        mf /\
        read (memory :> bytes(ea,el)) s = ev /\
        read (memory :> bytes64 (word_add B (word 11456))) s = s1p /\
        read (memory :> bytes64 (word_add B (word 11360))) s =
                    word_add B (word 11232) /\
        read (memory :> bytes16 (word_add B (word 11368))) s = word k /\
        read (memory :> bytes(word_add B (word 11232),64)) s = rhop /\
        (!j. j < 640
             ==> read (memory :> bytes8 (word_add s1p (word j))) s = s1b j) /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add B (word(8224 + 4 * j))))
                   s = cphat j) /\
        (!t. t < 640 * i
             ==> read (memory :> bytes8 (word_add sig (word(48 + t)))) s =
                 mld_polyvec_pack 640 mld_polyz_pack_19
                  (mld_polyvec
                    (mld_sign_z
                      (mld_polyvec_map mld_poly_ntt
                        (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s1b))
                      cphat (mld_sign_y mld_poly_uniform_gamma1_19 rhop k)))
                  t)`;;

(*** The polynomials of s1 and y as the specification gives them ***)

let SIGN65_S1U = `mld_polyvec_unpack 128 mld_polyeta_unpack_4 (s1b:num->byte)`;;

let SIGN65_S1_TAC =
  MLD_LAZY_REPOLY_TAC
   `mld_polyeta_unpack_4 (\j. (s1b:num->byte)(128 * i + j))`
   (mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1U),`i:num`))
   [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC];;

let SIGN65_S1H_TAC =
  MLD_LAZY_REPOLY_TAC
   (mk_comb(`mld_poly_ntt`,mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1U),`i:num`)))
   (mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1H),`i:num`))
   [MLD_POLY_OF_POLYVEC_MAP];;

let SIGN65_SHL7 = par_await SIGN65_SHL7_ASYNC;;

let SIGN65_ZBODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 5` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 5` THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN65_SHL7]) THEN
  VEC_SLICE_TAC
   `!j. j < 128
        ==> read(memory :> bytes8(word_add s1p (word(128 * i + j)))) s4 =
            (s1b:num->byte)(128 * i + j)` THEN
  SIGN65_ZCALL_TAC "H_ETA"
   [`read X0 s`; `read X1 s`; `\j. (s1b:num->byte)(128 * i + j)`; `pc:num`;
    `read X30 s`] 5 THEN
  SIGN65_S1_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (6--7) THEN
  SIGN65_ZCALL_TAC "H_NTT"
   [`read X0 s`; mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1U),`i:num`);
    `pc:num`; `read X30 s`] 8 THEN
  SIGN65_S1H_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (9--11) THEN
  SIGN65_ZCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1H),`i:num`);
    `cphat:num->int32`; `pc:num`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC SIGN65_EXEC (13--14) THEN
  SIGN65_ZCALL_TAC "H_INV"
   [`read X0 s`;
    list_mk_comb(`mld_poly_pointwise_montgomery`,
                 [mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1H),`i:num`);
                  `cphat:num->int32`]);
    `pc:num`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC SIGN65_EXEC (16--20) THEN
  SIGN65_ZCALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `rhop:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 21;;

let SIGN65_ZPW =
  list_mk_comb(`mld_poly_pointwise_montgomery`,
               [mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1H),`i:num`);
                `cphat:num->int32`]);;

let SIGN65_ZY = mk_comb(mk_comb(`mld_poly_of`,SIGN65_YY),`i:num`);;

let SIGN65_ZADD =
  list_mk_comb(`mld_poly_add`,
               [mk_comb(`mld_poly_invntt_tomont`,SIGN65_ZPW); SIGN65_ZY]);;

let SIGN65_ZI =
  list_mk_comb(`mld_sign_z`,[SIGN65_S1H; `cphat:num->int32`; SIGN65_YY;
                             `i:num`]);;

let SIGN65_ZBODY2_TAC =
  MLD_LAZY_SIGN_Y_TAC `mld_poly_uniform_gamma1_19` THEN
  ARM_STEPS_TAC SIGN65_EXEC (22--24) THEN
  SIGN65_ZCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_invntt_tomont`,SIGN65_ZPW);
    SIGN65_ZY; `pc:num`; `read X30 s`] 25 THEN
  ARM_STEPS_TAC SIGN65_EXEC (26--27) THEN
  SIGN65_ZCALL_TAC "H_RED" [`read X0 s`; SIGN65_ZADD; `pc:num`; `read X30 s`]
   28 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (29--32) THEN
  SIGN65_ZCALL_TAC "H_CHK"
   [`read X0 s`; SIGN65_ZI; `read X1 s`; `pc:num`; `read X30 s`] 33 THEN
  SUBGOAL_THEN (mk_eq(list_mk_comb(`mld_poly_chknorm`,
                                   [SIGN65_ZI; `word 524092:int32`]),
                      `word 0:int32`))
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV))) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `mld_poly_chknorm z b = word 0:int32`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  ARM_STEPS_TAC SIGN65_EXEC (34--39) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i /\
    word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
    word(i + 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 5` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIGN65_ZCALL_TAC "H_PZ"
   [`read X0 s`; `read X1 s`; SIGN65_ZI; `i:num`; `pc:num`; `read X30 s`]
   40 THEN
  ARM_STEPS_TAC SIGN65_EXEC (41--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN
  REWRITE_TAC[ARITH_RULE
   `i + 18446744073709551612 = 18446744073709551616 <=> i + 1 = 5`] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_19`; `640`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_19_LOCAL] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN65_ZPRE_ASYNC = prove_async
 (SIGN65_ZPRE_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_G1") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ETA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CHK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_Z_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PZ" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sig:int64) (B:int64) (sp:int64) (s1p:int64) (guard:int64)
     (mf:int64) (pc:num).
     APPEND (f_ev_back m sig B sp s1p guard mf pc)
      (APPEND (ENUMERATEL m (\i. f_ev_zit sig B sp s1p guard mf pc i))
              (f_ev_front m sig B sp s1p guard mf pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:num`; `sig:int64`; `B:int64`; `sp:int64`;
    `s1p:int64`; `s1b:num->byte`; `cphat:num->int32`; `rhop:num`; `k:num`;
    `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
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
      SIGN65_ZBODY1_TAC THEN SIGN65_ZBODY2_TAC;
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
(* the cleanup (join2) with x23 = -1.                                        *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ZFAIL_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_zfail.
        !e i sig B sp s1p s1b cphat rhop k guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\ i < 5 /\
          ~(mld_poly_chknorm
             (mld_sign_z
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s1b))
               cphat (mld_sign_y mld_poly_uniform_gamma1_19 rhop k) i)
             (word 524092) = word 0) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (B,11464); (sp,112);
            (word_sub sp (word 1328),1328)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (B,11464); (word_sub sp (word 1328),1328)]
           [(s1p,640); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_loop2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 9248) /\
                    read X20 s = word_add B (word 7200) /\
                    read X22 s = B /\
                    read X24 s = word_add B (word 8224) /\
                    read X26 s = word_add B (word 11264) /\
                    read X23 s = word i /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64 (word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes64 (word_add B (word 11456))) s = s1p /\
                    read (memory :> bytes64 (word_add B (word 11360))) s =
                    word_add B (word 11232) /\
                    read (memory :> bytes16 (word_add B (word 11368))) s =
                    word k /\
                    read (memory :> bytes(word_add B (word 11232),64)) s =
                    rhop /\
                    (!j. j < 640
                         ==> read (memory :> bytes8 (word_add s1p (word j))) s =
                             s1b j) /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(8224 + 4 * j)))) s =
                             cphat j) /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa65_signature_internal_join2) /\
                    read X23 s = word 4294967295 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_zfail i sig B sp s1p guard mf pc /\
                       memaccess_inbounds e2
                        [sig,3309; B,11464; sp,112;
                         word_sub sp (word 1328),1328; s1p,640;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,3309; B,11464; word_sub sp (word 1328),1328]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X23; X30] ,,
                MAYCHANGE
                 [memory :> bytes(word_add B (word 7200),1024);
                  memory :> bytes(word_add B (word 9248),1024);
                  memory :> bytes(word_sub sp (word 1328),1328)])`;;

(*** The calls of a polynomial of z up to its norm check (from loop2, with  ***)
(*** the call tactic ctac)                                                  ***)

let SIGN65_ZHEAD_TAC ctac =
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN65_SHL7]) THEN
  VEC_SLICE_TAC
   `!j. j < 128
        ==> read(memory :> bytes8(word_add s1p (word(128 * i + j)))) s4 =
            (s1b:num->byte)(128 * i + j)` THEN
  ctac "H_ETA"
   [`read X0 s`; `read X1 s`; `\j. (s1b:num->byte)(128 * i + j)`; `pc:num`;
    `read X30 s`] 5 THEN
  SIGN65_S1_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (6--7) THEN
  ctac "H_NTT"
   [`read X0 s`; mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1U),`i:num`);
    `pc:num`; `read X30 s`] 8 THEN
  SIGN65_S1H_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (9--11) THEN
  ctac "H_PW"
   [`read X0 s`; `read X1 s`; mk_comb(mk_comb(`mld_poly_of`,SIGN65_S1H),`i:num`);
    `cphat:num->int32`; `pc:num`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC SIGN65_EXEC (13--14) THEN
  ctac "H_INV" [`read X0 s`; SIGN65_ZPW; `pc:num`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC SIGN65_EXEC (16--20) THEN
  ctac "H_G1"
   [`read X0 s`; `read X1 s`; `rhop:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 21 THEN
  MLD_LAZY_SIGN_Y_TAC `mld_poly_uniform_gamma1_19` THEN
  ARM_STEPS_TAC SIGN65_EXEC (22--24) THEN
  ctac "H_ADD"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_invntt_tomont`,SIGN65_ZPW);
    SIGN65_ZY; `pc:num`; `read X30 s`] 25 THEN
  ARM_STEPS_TAC SIGN65_EXEC (26--27) THEN
  ctac "H_RED" [`read X0 s`; SIGN65_ZADD; `pc:num`; `read X30 s`] 28 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (29--32) THEN
  ctac "H_CHK"
   [`read X0 s`; SIGN65_ZI; `read X1 s`; `pc:num`; `read X30 s`] 33 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV)));;

let SIGN65_ZFCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc SIGN65_EXEC name
   ilist SIGN65_ZALLOWED n;;

let SIGN65_ZSETUP_TAC tmpl vars =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_G1") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ETA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CHK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_Z_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PZ" THEN
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC vars THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]);;

let SIGN65_ZFAIL_ASYNC = prove_async
 (SIGN65_ZFAIL_STMT,
  SIGN65_ZSETUP_TAC
   `\(i:num) (sig:int64) (B:int64) (sp:int64) (s1p:int64)
     (guard:int64) (mf:int64) (pc:num).
     f_ev_zfail i sig B sp s1p guard mf pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `sig:int64`; `B:int64`; `sp:int64`;
    `s1p:int64`; `s1b:num->byte`; `cphat:num->int32`;
    `rhop:num`; `k:num`; `guard:int64`; `pc:num`] THEN
  SIGN65_ZHEAD_TAC SIGN65_ZFCALL_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC [34] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0;
   ASSUME (mk_neg(mk_eq(list_mk_comb(`mld_poly_chknorm`,
                                     [SIGN65_ZI; `word 524092:int32`]),
                        `word 0:int32`)))]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (35--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass, leaving the rows of x of the hints. Polynomial i of s2 and of t0 is *)
(* unpacked from the secret key (at s2p and t0p, pointers into it that       *)
(* mldsa65_unpack_sk leaves at B + 11392 and B + 11424) and transformed.     *)
(* ------------------------------------------------------------------------- *)

let SIGN65_S2U = `mld_polyvec_unpack 128 mld_polyeta_unpack_4 (s2b:num->byte)`;;
let SIGN65_S2H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SIGN65_S2U);;
let SIGN65_T0U = `mld_polyvec_unpack 416 mld_polyt0_unpack (t0b:num->byte)`;;
let SIGN65_T0H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SIGN65_T0U);;

let SIGN65_POLY v = mk_comb(mk_comb(`mld_poly_of`,v),`i:num`);;

let SIGN65_RPRE_STMT =
 `?f_rpre.
    !e m B w s2p s2b t0p t0b cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      m <= 6 /\
      (!j. j < m
           ==> mld_poly_chknorm
                (mld_sign_r0 mld_poly_decompose_lo_32 w
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s2b))
                  cphat j)
                (word 261692) = word 0 /\
               mld_poly_chknorm
                (mld_sign_ct0
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 416 mld_polyt0_unpack t0b))
                  cphat j) (word 261888) =
               word 0) /\
      ALL (nonoverlapping (B,11464))
       [(s2p,768); (t0p,2496); (word pc,libmldsa_size)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read PC s =
                word(pc + mldsa65_signature_internal_loop2_exit1) /\
                read X19 s = word_add B (word 9248) /\
                read X22 s = B /\
                read X24 s = word_add B (word 8224) /\
                read (memory :> bytes64 (word_add B (word 11392))) s = s2p /\
                read (memory :> bytes64 (word_add B (word 11424))) s = t0p /\
                (!j. j < 768
                     ==> read (memory :> bytes8 (word_add s2p (word j))) s =
                         s2b j) /\
                (!j. j < 2496
                     ==> read (memory :> bytes8 (word_add t0p (word j))) s =
                         t0b j) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add B (word(8224 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32 (word_add B (word(4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                read events s = e)
           (\s. read PC s =
                (if m < 6
                 then word(pc + mldsa65_signature_internal_loop3)
                 else word(pc + mldsa65_signature_internal_loop3_exit1)) /\
                read X23 s = word_add B (word(1024 * m)) /\
                read X25 s = word(416 * m) /\
                read X27 s = word(128 * m) /\
                (!j. j < 256 * m
                     ==> read (memory :> bytes32 (word_add B (word(4 * j)))) s =
                         mld_sign_hint_x 6 mld_poly_decompose_lo_32 w
                          (mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s2b))
                          (mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 416 mld_polyt0_unpack t0b))
                          cphat j) /\
                (!j. 256 * m <= j /\ j < 1536
                     ==> read (memory :> bytes32 (word_add B (word(4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_rpre m B s2p t0p pc /\
                   memaccess_inbounds e2
                    [B,11464; s2p,768; t0p,2496;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_invntt_tomont_consts),48;
                     word(pc + mldsa_poly_reduce_consts),16;
                     word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                     word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                    [B,11464]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X23; X25; X27; X30] ,,
            MAYCHANGE
             [memory :> bytes(word_add B (word 9248),1024);
              memory :> bytes(B,6144)])`;;

let SIGN65_RALLOWED =
  [`pc:num`; `B:int64`; `s2p:int64`; `t0p:int64`; `i:num`];;

let SIGN65_RCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc SIGN65_EXEC name
   ilist SIGN65_RALLOWED n;;

let SIGN65_R0 =
  list_mk_comb(`mld_sign_r0`,
    [`mld_poly_decompose_lo_32`; `w:num->int32`; SIGN65_S2H;
     `cphat:num->int32`; `i:num`]);;

let SIGN65_CT0I =
  list_mk_comb(`mld_sign_ct0`,[SIGN65_T0H; `cphat:num->int32`; `i:num`]);;

let SIGN65_S2PW =
  list_mk_comb(`mld_poly_pointwise_montgomery`,
               [SIGN65_POLY SIGN65_S2H; `cphat:num->int32`]);;

let SIGN65_T0PW =
  list_mk_comb(`mld_poly_pointwise_montgomery`,
               [SIGN65_POLY SIGN65_T0H; `cphat:num->int32`]);;

let SIGN65_RPRE_INV =
 `\i s. read X19 s = word_add B (word 9248) /\
        read X22 s = B /\
        read X24 s = word_add B (word 8224) /\
        read X23 s = word_add B (word(1024 * i)) /\
        read X25 s = word(416 * i) /\
        read X27 s = word(128 * i) /\
        read (memory :> bytes64 (word_add B (word 11392))) s = s2p /\
        read (memory :> bytes64 (word_add B (word 11424))) s = t0p /\
        (!j. j < 768
             ==> read (memory :> bytes8 (word_add s2p (word j))) s = s2b j) /\
        (!j. j < 2496
             ==> read (memory :> bytes8 (word_add t0p (word j))) s = t0b j) /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add B (word(8224 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 256 * i
             ==> read (memory :> bytes32 (word_add B (word(4 * j)))) s =
                 mld_sign_hint_x 6 mld_poly_decompose_lo_32 w
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s2b))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 416 mld_polyt0_unpack t0b))
                  cphat j) /\
        (!j. 256 * i <= j /\ j < 1536
             ==> read (memory :> bytes32 (word_add B (word(4 * j)))) s =
                 mld_polyvec_map mld_poly_decompose_lo_32 w j)`;;

(*** The w0 row i, from the facts for the rows from i on (at offset 0) ***)

let SIGN65_ROW_SLICE =
  REWRITE_RULE[ADD_CLAUSES]
   (SPECL [`B:int64`; `0`; `1536`; `mld_poly_decompose_lo_32`]
          SIGN_ROW_SLICE);;

let SIGN65_RFSLICE_TAC s =
  MP_TAC(SPECL [`w:num->int32`; `i:num`; s] SIGN65_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; s]
             `!j. 256 * i <= j /\ j < 1536
                  ==> read (memory :> bytes32 (word_add B (word (4 * j))))
                        s = Q j`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 6` THEN ARITH_TAC; STRIP_TAC];;

(*** The first part of a row, up to the norm check of w0 - c s2 ***)

let SIGN65_ROW_HEAD_TAC =
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--4) THEN
  VEC_SLICE_TAC
   `!j. j < 128
        ==> read(memory :> bytes8(word_add s2p (word(128 * i + j)))) s4 =
            (s2b:num->byte)(128 * i + j)` THEN
  SIGN65_RCALL_TAC "H_ETA"
   [`read X0 s`; `read X1 s`; `\j. (s2b:num->byte)(128 * i + j)`; `pc:num`;
    `read X30 s`] 5 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyeta_unpack_4 (\j. (s2b:num->byte)(128 * i + j))`
   (SIGN65_POLY SIGN65_S2U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SIGN65_EXEC (6--7) THEN
  SIGN65_RCALL_TAC "H_NTT"
   [`read X0 s`; SIGN65_POLY SIGN65_S2U; `pc:num`; `read X30 s`] 8 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SIGN65_POLY SIGN65_S2U))
   (SIGN65_POLY SIGN65_S2H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SIGN65_EXEC (9--11) THEN
  SIGN65_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; SIGN65_POLY SIGN65_S2H; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC SIGN65_EXEC (13--14) THEN
  SIGN65_RCALL_TAC "H_INV" [`read X0 s`; SIGN65_S2PW; `pc:num`; `read X30 s`]
   15 THEN
  SIGN65_RFSLICE_TAC `s15:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (16--18) THEN
  SIGN65_RCALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`;
    `mld_poly_decompose_lo_32 (mld_poly_of w i)`;
    mk_comb(`mld_poly_invntt_tomont`,SIGN65_S2PW); `pc:num`; `read X30 s`]
   19 THEN
  ARM_STEPS_TAC SIGN65_EXEC (20--21) THEN
  SIGN65_RCALL_TAC "H_RED"
   [`read X0 s`;
    list_mk_comb(`mld_poly_sub`,
     [`mld_poly_decompose_lo_32 (mld_poly_of w i)`;
      mk_comb(`mld_poly_invntt_tomont`,SIGN65_S2PW)]);
    `pc:num`; `read X30 s`] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (23--26) THEN
  SIGN65_RCALL_TAC "H_CHK"
   [`read X0 s`; SIGN65_R0; `read X1 s`; `pc:num`; `read X30 s`] 27 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV)));;

(*** The second part, from the first check to the norm check of c t0 ***)

let SIGN65_ROW_MID_TAC =
  ARM_STEPS_TAC SIGN65_EXEC (28--32) THEN
  VEC_SLICE_TAC
   `!j. j < 416
        ==> read(memory :> bytes8(word_add t0p (word(416 * i + j)))) s32 =
            (t0b:num->byte)(416 * i + j)` THEN
  SIGN65_RCALL_TAC "H_T0"
   [`read X0 s`; `read X1 s`; `\j. (t0b:num->byte)(416 * i + j)`; `pc:num`;
    `read X30 s`] 33 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyt0_unpack (\j. (t0b:num->byte)(416 * i + j))`
   (SIGN65_POLY SIGN65_T0U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SIGN65_EXEC (34--35) THEN
  SIGN65_RCALL_TAC "H_NTT"
   [`read X0 s`; SIGN65_POLY SIGN65_T0U; `pc:num`; `read X30 s`] 36 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SIGN65_POLY SIGN65_T0U))
   (SIGN65_POLY SIGN65_T0H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SIGN65_EXEC (37--39) THEN
  SIGN65_RCALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; SIGN65_POLY SIGN65_T0H; `cphat:num->int32`;
    `pc:num`; `read X30 s`] 40 THEN
  ARM_STEPS_TAC SIGN65_EXEC (41--42) THEN
  SIGN65_RCALL_TAC "H_INV" [`read X0 s`; SIGN65_T0PW; `pc:num`; `read X30 s`]
   43 THEN
  ARM_STEPS_TAC SIGN65_EXEC (44--45) THEN
  SIGN65_RCALL_TAC "H_RED"
   [`read X0 s`; mk_comb(`mld_poly_invntt_tomont`,SIGN65_T0PW); `pc:num`;
    `read X30 s`] 46 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (47--49) THEN
  SIGN65_RCALL_TAC "H_CHK"
   [`read X0 s`; SIGN65_CT0I; `read X1 s`; `pc:num`; `read X30 s`] 50 THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(CHANGED_CONV WORD_REDUCE_CONV)));;

let SIGN65_RCHK1 =
  mk_eq(list_mk_comb(`mld_poly_chknorm`,[SIGN65_R0; `word 261692:int32`]),
        `word 0:int32`);;

let SIGN65_RCHK2 =
  mk_eq(list_mk_comb(`mld_poly_chknorm`,[SIGN65_CT0I; `word 261888:int32`]),
        `word 0:int32`);;

let SIGN65_RBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 6` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m` THEN UNDISCH_TAC `m <= 6` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SIGN65_ROW_HEAD_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME SIGN65_RCHK1]) THEN
  SIGN65_ROW_MID_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME SIGN65_RCHK2]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (51--55) THEN
  SIGN65_RCALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; SIGN65_R0; SIGN65_CT0I; `pc:num`; `read X30 s`]
   56 THEN
  ARM_STEPS_TAC SIGN65_EXEC (57--60) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN
  REWRITE_TAC[ARITH_RULE
   `416 * i + 18446744073709549536 = 18446744073709551616 <=> i + 1 = 6`] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES]
        (SPECL [`B:int64`; `0`] SIGN_ROW_JOIN)) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN65_RPRE_ASYNC = prove_async
 (SIGN65_RPRE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ETA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_T0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_SUB_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CHK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (B:int64) (s2p:int64) (t0p:int64) (pc:num).
     APPEND (f_ev_back m B s2p t0p pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit B s2p t0p pc i))
              (f_ev_front B s2p t0p pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:num`; `B:int64`; `w:num->int32`;
    `s2p:int64`; `s2b:num->byte`; `t0p:int64`; `t0b:num->byte`;
    `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_loop3`
     `if m < 6 then pc + mldsa65_signature_internal_loop3
      else pc + mldsa65_signature_internal_loop3_exit1`
     SIGN65_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN65_RBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SIGN_BETA_ALL_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0;
                    WORD_ADD_0] THEN
    SIGN_CONCRETE_DISCHARGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exits from the loop over the rows at a row whose first check (w0 - c  *)
(* s2) or second check (c t0) fails, to join2 with x23 = -1.                 *)
(* ------------------------------------------------------------------------- *)

let SIGN65_RFAIL_PRE =
 `aligned_bytes_loaded s (word pc)
    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
  read PC s = word(pc + mldsa65_signature_internal_loop3) /\
  read X19 s = word_add B (word 9248) /\
  read X22 s = B /\
  read X24 s = word_add B (word 8224) /\
  read X23 s = word_add B (word(1024 * i)) /\
  read X25 s = word(416 * i) /\
  read X27 s = word(128 * i) /\
  read (memory :> bytes64 (word_add B (word 11392))) s = s2p /\
  read (memory :> bytes64 (word_add B (word 11424))) s = t0p /\
  (!j. j < 768
       ==> read (memory :> bytes8 (word_add s2p (word j))) s = s2b j) /\
  (!j. j < 2496
       ==> read (memory :> bytes8 (word_add t0p (word j))) s = t0b j) /\
  (!j. j < 256
       ==> read (memory :> bytes32 (word_add B (word(8224 + 4 * j)))) s =
           cphat j) /\
  (!j. 256 * i <= j /\ j < 1536
       ==> read (memory :> bytes32 (word_add B (word(4 * j)))) s =
           mld_polyvec_map mld_poly_decompose_lo_32 w j) /\
  read events s = e`;;

let SIGN65_RFAIL_STMT f chk =
  let pre = mk_abs(`s:armstate`,SIGN65_RFAIL_PRE) in
  let fv = mk_var(f,`:num->int64->int64->int64->num->(uarch_event)list`) in
  let body = subst [pre,`PREC:armstate->bool`; fv,`f_rfail:num->int64->int64->int64->num->(uarch_event)list`;
         chk,`CHKC:bool`]
   `aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
    i < 6 /\ CHKC /\
    ALL (nonoverlapping (B,11464))
     [(s2p,768); (t0p,2496); (word pc,libmldsa_size)]
    ==> ensures arm PREC
         (\s. read PC s = word(pc + mldsa65_signature_internal_join2) /\
              read X23 s = word 4294967295 /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_rfail i B s2p t0p pc /\
                 memaccess_inbounds e2
                  [B,11464; s2p,768; t0p,2496;
                   word(pc + rodata_mld_zetas),1024;
                   word(pc + mldsa_poly_invntt_tomont_consts),48;
                   word(pc + mldsa_poly_reduce_consts),16;
                   word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                   word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                  [B,11464]))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [X23; X30] ,,
          MAYCHANGE
           [memory :> bytes(word_add B (word 9248),1024);
            memory :> bytes(B,6144)])` in
  mk_exists(fv,list_mk_forall
   ([`e:(uarch_event)list`; `i:num`; `B:int64`; `w:num->int32`;
     `s2p:int64`; `s2b:num->byte`; `t0p:int64`; `t0b:num->byte`;
     `cphat:num->int32`; `pc:num`],body));;

let SIGN65_RFAIL1_STMT =
  SIGN65_RFAIL_STMT "f_rfail1" (mk_neg(subst [`i:num`,`i:num`] SIGN65_RCHK1));;

let SIGN65_RFAIL2_STMT =
  SIGN65_RFAIL_STMT "f_rfail2" (mk_conj(SIGN65_RCHK1,mk_neg SIGN65_RCHK2));;

let SIGN65_RFAIL_SETUP_TAC tmpl =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ETA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_T0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_SUB_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CHK" THEN
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `i:num`; `B:int64`; `w:num->int32`;
    `s2p:int64`; `s2b:num->byte`; `t0p:int64`; `t0b:num->byte`;
    `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let SIGN65_RFAIL1_ASYNC = prove_async
 (SIGN65_RFAIL1_STMT,
  SIGN65_RFAIL_SETUP_TAC
   `\(i:num) (B:int64) (s2p:int64) (t0p:int64) (pc:num).
     f_ev_rfail1 i B s2p t0p pc:(uarch_event)list` THEN
  SIGN65_ROW_HEAD_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC [28] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0;
                              ASSUME(mk_neg SIGN65_RCHK1)]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (29--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SIGN65_RFAIL2_ASYNC = prove_async
 (SIGN65_RFAIL2_STMT,
  SIGN65_RFAIL_SETUP_TAC
   `\(i:num) (B:int64) (s2p:int64) (t0p:int64) (pc:num).
     f_ev_rfail2 i B s2p t0p pc:(uarch_event)list` THEN
  SIGN65_ROW_HEAD_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME SIGN65_RCHK1]) THEN
  SIGN65_ROW_MID_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC [51] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0;
                              ASSUME(mk_neg SIGN65_RCHK2)]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (52--53) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints, whose result is the value of x23 for  *)
(* the decision.                                                             *)
(* ------------------------------------------------------------------------- *)

let SIGN65_TAIL_STMT =
 `?f_tail.
    !e sig B sp ct (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 sp /\
      PAIRWISE nonoverlapping
       [(sig,3309); (B,11464); (sp,128); (word_sub sp (word 96),96)] /\
      ALL (nonoverlapping (word pc,libmldsa_size))
       [(sig,3309); (B,11464); (sp,128); (word_sub sp (word 96),96)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read PC s = word(pc + mldsa65_signature_internal_loop3_exit1) /\
                read SP s = sp /\
                read X19 s = word_add B (word 9248) /\
                read X22 s = B /\
                read X28 s = word_add B (word 11296) /\
                read (memory :> bytes64 (word_add sp (word 96))) s = sig /\
                read (memory :> bytes64 (word_add sp (word 112))) s =
                word_add B (word 10272) /\
                (!j. j < 48
                     ==> read (memory :> bytes8
                                (word_add B (word(11296 + j)))) s = ct j) /\
                (!j. j < 1536
                     ==> read (memory :> bytes32
                                (word_add B (word(4 * j)))) s = x j) /\
                (!j. j < 768
                     ==> read (memory :> bytes8
                                (word_add B (word(10272 + j)))) s = b j) /\
                read events s = e)
           (\s. read PC s = word(pc + mldsa65_signature_internal_join2) /\
                read X23 s =
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
                   e2 = f_tail sig B sp pc x b /\
                   memaccess_inbounds e2
                    [sig,3309; B,11464; sp,128; word_sub sp (word 96),96]
                    [sig,3309; B,11464; word_sub sp (word 96),96]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X23; X30] ,,
            MAYCHANGE
             [memory :> bytes(sig,48);
              memory :> bytes(word_add sig (word 3248),61);
              memory :> bytes(word_add B (word 9248),1024);
              memory :> bytes(word_sub sp (word 96),96)])`;;

let SIGN65_TAIL_ASYNC = prove_async
 (SIGN65_TAIL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_C_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PH" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (B:int64) (sp:int64) (pc:num) (x:num->int32) (b:num->byte).
     f_ev_tail sig B sp pc x b:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `B:int64`; `sp:int64`;
    `ct:num->byte`; `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; C_RETURN; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--4) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc SIGN65_EXEC
   "H_PC" [`read X0 s`; `read X1 s`; `ct:num->byte`; `pc:num`; `read X30 s`]
   [`pc:num`; `sig:int64`; `B:int64`; `sp:int64`; `x:num->int32`;
    `b:num->byte`] 5 THEN
  ARM_STEPS_TAC SIGN65_EXEC (6--10) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc SIGN65_EXEC
   "H_PH"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `x:num->int32`;
    `b:num->byte`; `pc:num`; `read SP s`; `read X30 s`]
   [`pc:num`; `sig:int64`; `B:int64`; `sp:int64`; `x:num->int32`;
    `b:num->byte`] 11 THEN
  ARM_STEPS_TAC SIGN65_EXEC [12] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt and the test of x23: to join4 on success, else  *)
(* to the update of kappa.                                                   *)
(* ------------------------------------------------------------------------- *)

let SIGN65_CLEAN_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_clean.
        !e ok B sp pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp /\
          nonoverlapping (B,11464) (sp,136) /\
          ALL (nonoverlapping (B,11464))
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_join2) /\
                    read SP s = sp /\
                    read X19 s = word_add B (word 9248) /\
                    read X20 s = word_add B (word 7200) /\
                    read X22 s = B /\
                    read X23 s = (if ok then word 0 else word 4294967295) /\
                    read X24 s = word_add B (word 8224) /\
                    read X28 s = word_add B (word 11296) /\
                    read (memory :> bytes64 (word_add sp (word 112))) s =
                    word_add B (word 10272) /\
                    read (memory :> bytes64 (word_add sp (word 120))) s =
                    word_add B (word 11360) /\
                    read (memory :> bytes64 (word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s =
                    (if ok then word(pc + mldsa65_signature_internal_join4)
                     else word(pc + mldsa65_signature_internal_loop1_next1)) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_clean ok B sp mf pc /\
                       memaccess_inbounds e2
                        [B,11464; sp,136; word(pc + got_memset),8; ea,el]
                        [B,11464]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X25; X30] ,,
                MAYCHANGE
                 [memory :> bytes(B,6144);
                  memory :> bytes(word_add B (word 7200),1024);
                  memory :> bytes(word_add B (word 8224),1024);
                  memory :> bytes(word_add B (word 9248),1024);
                  memory :> bytes(word_add B (word 10272),768);
                  memory :> bytes(word_add B (word 11296),48);
                  memory :> bytes(word_add B (word 11360),16)])`;;

let SIGN65_CLEAN_MEMSET_TAC n =
  LIBC_PLT_TAC SIGN65_EXEC n THEN
  SIGN_LIBC_CALL_TAC "H_MEMSET" SIGN65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref [`pc:num`; `ok:bool`; `B:int64`; `sp:int64`; `mf:int64`]) (n + 5);;

let SIGN65_CLEAN_ASYNC = prove_async
 (SIGN65_CLEAN_STMT,
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
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  BOOL_CASES_TAC `ok:bool` THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--4) THEN
  SIGN65_CLEAN_MEMSET_TAC 4 THEN
  ARM_STEPS_TAC SIGN65_EXEC (10--13) THEN SIGN65_CLEAN_MEMSET_TAC 13 THEN
  ARM_STEPS_TAC SIGN65_EXEC (19--22) THEN SIGN65_CLEAN_MEMSET_TAC 22 THEN
  ARM_STEPS_TAC SIGN65_EXEC (28--32) THEN SIGN65_CLEAN_MEMSET_TAC 32 THEN
  ARM_STEPS_TAC SIGN65_EXEC (38--41) THEN SIGN65_CLEAN_MEMSET_TAC 41 THEN
  ARM_STEPS_TAC SIGN65_EXEC (47--52) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt: w = A y with the matrix and y sampled on demand  *)
(* (mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy, whose result      *)
(* made nonnegative is mld_sign_w by MLD_LAZY_SIGN_W), w1 and its packing,   *)
(* c~ with the inlined SHAKE256 calls, the challenge and its NTT. The frame  *)
(* of the function is at sp0 + 1568, above the stack of the callees, with    *)
(* the SHAKE256 context at sp0 + 13240.                                      *)
(* ------------------------------------------------------------------------- *)

let SIGN65_Y = `mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)`;;
let SIGN65_W =
  `mld_sign_w 5 (mld_polyvec_matrix_expand 5 rh)
    (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))`;;
let SIGN65_YVL =
  `mld_polyvec_matrix_yvec_lazy 5 rh
    (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))`;;

let SIGN65_HEAD_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_head.
        !e B sp0 rh mu rhop n C guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ n < 13106 /\
          mld_matrix_terminates 6 5 rh /\
          num_of_bytelist(list_of_seq
           (mld_sign_ctilde 6 128 mu
             (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
               (mld_sign_w 5 (mld_polyvec_matrix_expand 5 rh)
                 (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)))))
           48) = C /\
          mld_poly_challenge_terminates 49 48 C /\
          PAIRWISE nonoverlapping
           [(B,11464); (word_add sp0 (word 1568),176);
            (word_add sp0 (word 13240),208); (sp0,1568)] /\
          ALLPAIRS nonoverlapping
           [(B,11464); (word_add sp0 (word 13240),208); (sp0,1568)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_loop1) /\
                    read SP s = word_add sp0 (word 1568) /\
                    read X19 s = word_add B (word 9248) /\
                    read X21 s = word_add sp0 (word 13240) /\
                    read X22 s = B /\
                    read X24 s = word_add B (word 8224) /\
                    read X26 s = word_add B (word 11264) /\
                    read X28 s = word_add B (word 11296) /\
                    read (memory :> bytes16 (word_add sp0 (word 1676))) s =
                    word(5 * n) /\
                    read (memory :> bytes64 (word_add sp0 (word 1680))) s =
                    word_add B (word 10272) /\
                    read (memory :> bytes64 (word_add sp0 (word 1688))) s =
                    word_add B (word 11360) /\
                    read (memory :> bytes64 (word_add sp0 (word 1696))) s =
                    word_add B (word 11040) /\
                    read (memory :> bytes64 (word_add sp0 (word 1704))) s =
                    word_add B (word 6144) /\
                    read (memory :> bytes64 (word_add sp0 (word 1712))) s =
                    word_add B (word 11232) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add B (word 7168),32)) s = rh /\
                    read (memory :> bytes(word_add B (word 11168),64)) s = mu /\
                    read (memory :> bytes(word_add B (word 11232),64)) s =
                    rhop /\
                    read events s = e)
               (\s. read PC s = word(pc + mldsa65_signature_internal_loop2) /\
                    read X23 s = word 0 /\
                    read (memory :> bytes64 (word_add B (word 11360))) s =
                    word_add B (word 11232) /\
                    read (memory :> bytes16 (word_add B (word 11368))) s =
                    word(5 * n) /\
                    (!j. j < 1536
                         ==> read (memory :> bytes32
                                    (word_add B (word(4 * j)))) s =
                             mld_polyvec_map mld_poly_decompose_lo_32
                              (mld_sign_w 5 (mld_polyvec_matrix_expand 5 rh)
                                (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                                  (5 * n))) j) /\
                    (!j. j < 768
                         ==> read (memory :> bytes8
                                    (word_add B (word(10272 + j)))) s =
                             mld_sign_w1
                              (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                              128
                              (mld_sign_w 5 (mld_polyvec_matrix_expand 5 rh)
                                (mld_sign_y mld_poly_uniform_gamma1_19 rhop
                                  (5 * n))) j) /\
                    read (memory :> bytes(word_add B (word 11296),48)) s = C /\
                    (!j. j < 256
                         ==> read (memory :> bytes32
                                    (word_add B (word(8224 + 4 * j)))) s =
                             mld_poly_ntt (mld_poly_challenge 49 48 C) j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_head B sp0 rh guard mf pc C /\
                       memaccess_inbounds e2
                        [B,11464; word_add sp0 (word 1568),176;
                         word_add sp0 (word 13240),208; sp0,1568;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [B,11464; word_add sp0 (word 13240),208; sp0,1568]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X23; X30] ,,
                MAYCHANGE
                 [memory :> bytes(B,6144);
                  memory :> bytes(word_add B (word 6144),1024);
                  memory :> bytes(word_add B (word 8224),1024);
                  memory :> bytes(word_add B (word 9248),1024);
                  memory :> bytes(word_add B (word 10272),768);
                  memory :> bytes(word_add B (word 11296),48);
                  memory :> bytes(word_add B (word 11360),16);
                  memory :> bytes(word_add sp0 (word 13240),208);
                  memory :> bytes(sp0,1568)])`;;

let SIGN65_W1 =
 `mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   (mld_sign_w 5 (mld_polyvec_matrix_expand 5 rh)
     (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)))`;;

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
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc SIGN65_EXEC name
   ilist
   [`pc:num`; `B:int64`; `sp0:int64`; `rh:num`; `guard:int64`; `mf:int64`;
    `C:num`] n;;

(*** The result of the product made nonnegative, as mld_sign_w ***)

let SIGN65_WEQ =
  let j = `j:num` in
  mk_forall(j,mk_imp(`j < 1536`,
    mk_eq(mk_comb(mk_comb(`mld_polyvec_map mld_poly_caddq`,SIGN65_YVL),j),
          mk_comb(SIGN65_W,j))));;

let SIGN65_W_TAC =
  let old = mk_comb(`mld_polyvec_map mld_poly_caddq`,SIGN65_YVL) in
  SUBGOAL_THEN SIGN65_WEQ (fun weq ->
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if not(is_forall c) || not(can (find_term ((=) old)) c) ||
         not(can (find_term (fun t -> is_const t && name_of t = "read")) c)
      then NO_TAC
      else
        let i = fst(dest_forall c) in
        SUBGOAL_THEN (subst [SIGN65_W,old] c) ASSUME_TAC THENL
         [X_GEN_TAC i THEN DISCH_THEN(fun ith ->
            REWRITE_TAC[MP (SPEC i th) ith] THEN
            MATCH_MP_TAC weq THEN ACCEPT_TAC ith);
          ALL_TAC])) THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`6`; `5`; `rh:num`; SIGN65_Y; `j:num`] MLD_LAZY_SIGN_W) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[MLD_LAZY_SIGN_Y_BOUND];
    ALL_TAC];;

let SIGN65_WORD_ZX_KAPPA_ASYNC = prove_async
 (`!x:int16. word_zx(word_zx(word_zx x:int64):int32):int16 = x`,
  CONV_TAC WORD_BLAST);;

let SIGN65_WORD_ZX_KAPPA = par_await SIGN65_WORD_ZX_KAPPA_ASYNC;;

let SIGN65_HEAD_ASYNC = prove_async
 (SIGN65_HEAD_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_YVEC" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_CHAL") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_CADDQ_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_DEC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_ABSORB_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_FINALIZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_RELEASE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_RELEASE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(B:int64) (sp0:int64) (rh:num) (guard:int64) (mf:int64) (pc:num)
     (C:num). f_ev_head B sp0 rh guard mf pc C:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `B:int64`; `sp0:int64`; `rh:num`; `mu:num`;
    `rhop:num`; `n:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  SUBGOAL_THEN `val(word(5 * n):int16) = 5 * n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `n < 13106` THEN ARITH_TAC;
    ALL_TAC] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_WORD_ZX_16_32_64; SIGN_WORD_ZX_ZX_16]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN65_WORD_ZX_KAPPA]) THEN
  SIGN65_HCALL_TAC "H_YVEC"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `rh:num`;
    `word_add B (word 11232):int64`; `rhop:num`; `word(5 * n):int16`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 9 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(5 * n):int16) = 5 * n`]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (10--11) THEN
  SIGN65_HCALL_TAC "H_CADDQ"
   [`read X0 s`; SIGN65_YVL; `pc:num`; `read SP s`; `read X30 s`] 12 THEN
  SIGN65_W_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (13--17) THEN
  SIGN65_HCALL_TAC "H_DEC"
   [`read X0 s`; `read X1 s`; SIGN65_W; `read X2 s`; `pc:num`; `read SP s`;
    `read X30 s`] 18 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w1]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (19--20) THEN
  SIGN65_HCALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 21 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (22--26) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 13240):int64` THEN
  SIGN65_HCALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `64`; `word 0:1600 word`; `0`; `mu:num`;
    `pc:num`; `read SP s`; `read X30 s`] 27 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 768 ==> read (memory :> bytes8
         (word_add B (word (10272 + j)))) s = f j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  MLD_H_BOUND_TAC `word_add B (word 11168):int64` THEN
  ARM_STEPS_TAC SIGN65_EXEC (28--31) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 13240):int64` THEN
  SIGN65_HCALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `768`;
    `FST(mld_keccak_absorb 136 (word 0) 0 64 mu)`; `64`; SIGN65_W1NUM;
    `pc:num`; `read SP s`; `read X30 s`] 32 THEN
  MP_TAC(SPECL [`64`; `768`; `mu:num`; SIGN65_W1NUM]
               MLD_SHAKE256_ABSORB_APPEND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV SIGN_NUMERAL_CONV) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(CONV_RULE SIGN_NUMERAL_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (33--34) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 13240):int64` THEN
  MLD_H_GUARD_ADDR_TAC THEN
  SIGN65_HCALL_TAC "H_FINALIZE"
   [`read X0 s`; SIGN65_S2; `16`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 35 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC SIGN65_EXEC (36--39) THEN
  KECCAK_STATE_AT_TAC `word_add sp0 (word 13240):int64` THEN
  SIGN65_HCALL_TAC "H_SQUEEZE"
   [`read X0 s`; `48`; `read X2 s`; SIGN65_S3; `136`;
    `pc:num`; `read SP s`; `read X30 s`] 40 THEN
  ARM_STEPS_TAC SIGN65_EXEC (41--42) THEN
  SIGN65_HCALL_TAC "H_RELEASE" [`read X0 s`; `pc:num`; `read X30 s`] 43 THEN
  ARM_STEPS_TAC SIGN65_EXEC (44--54) THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add B (word 11296),48)) s54 = C`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde; mld_shake256_byte; mld_shake256_state;
                MLD_KECCAK_ABSORB_SND] THEN
    CONV_TAC SIGN_NUMERAL_CONV THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
   `read (memory :> bytes (word_add B (word 11296),48)) s54 =
    num_of_bytelist l`) (concl th))) THEN
  SIGN65_HCALL_TAC "H_CHAL"
   [`read X0 s`; `read X1 s`; `C:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 55 THEN
  ARM_STEPS_TAC SIGN65_EXEC (56--58) THEN
  SIGN65_HCALL_TAC "H_NTT"
   [`read X0 s`; `mld_poly_challenge 49 48 C`; `pc:num`; `read X30 s`] 59 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* One attempt, from loop1 to join4 (success) or loop1_next1, for the result *)
(* (C,r,x,b) of mld_sign_attempt_declass with the matrix expanded from rho   *)
(* and s1, s2 and t0 unpacked from the secret key and transformed.           *)
(* ------------------------------------------------------------------------- *)

let SIGN65_ATT_STMT =
 `!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> ?f_att.
        !e sig B sp0 rh s1p s1b s2p s2b t0p t0b mu rhop n C r x b guard pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 sp0 /\ n < 13106 /\
          mld_matrix_terminates 6 5 rh /\
          mld_sign_attempt_declass 6 5 48 49 mld_poly_uniform_gamma1_19
           524092 261692 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
           128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
           (mld_polyvec_matrix_expand 5 rh)
           (mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s1b))
           (mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s2b))
           (mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 416 mld_polyt0_unpack t0b))
           mu rhop (5 * n) = (C,r,x,b) /\
          mld_poly_challenge_terminates 49 48 C /\
          PAIRWISE nonoverlapping
           [(sig,3309); (B,11464); (word_add sp0 (word 1568),176);
            (word_add sp0 (word 13240),208); (sp0,1568)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (B,11464); (word_add sp0 (word 1568),176);
            (word_add sp0 (word 13240),208); (sp0,1568)]
           [(s1p,640); (s2p,768); (t0p,2496); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word(pc + mldsa65_signature_internal_loop1) /\
                    read SP s = word_add sp0 (word 1568) /\
                    read X19 s = word_add B (word 9248) /\
                    read X20 s = word_add B (word 7200) /\
                    read X21 s = word_add sp0 (word 13240) /\
                    read X22 s = B /\
                    read X24 s = word_add B (word 8224) /\
                    read X26 s = word_add B (word 11264) /\
                    read X28 s = word_add B (word 11296) /\
                    read (memory :> bytes64 (word_add sp0 (word 1664))) s =
                    sig /\
                    read (memory :> bytes16 (word_add sp0 (word 1676))) s =
                    word(5 * n) /\
                    read (memory :> bytes64 (word_add sp0 (word 1680))) s =
                    word_add B (word 10272) /\
                    read (memory :> bytes64 (word_add sp0 (word 1688))) s =
                    word_add B (word 11360) /\
                    read (memory :> bytes64 (word_add sp0 (word 1696))) s =
                    word_add B (word 11040) /\
                    read (memory :> bytes64 (word_add sp0 (word 1704))) s =
                    word_add B (word 6144) /\
                    read (memory :> bytes64 (word_add sp0 (word 1712))) s =
                    word_add B (word 11232) /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add B (word 7168),32)) s = rh /\
                    read (memory :> bytes(word_add B (word 11168),64)) s = mu /\
                    read (memory :> bytes(word_add B (word 11232),64)) s =
                    rhop /\
                    read (memory :> bytes64 (word_add B (word 11456))) s = s1p /\
                    read (memory :> bytes64 (word_add B (word 11392))) s = s2p /\
                    read (memory :> bytes64 (word_add B (word 11424))) s = t0p /\
                    (!j. j < 640
                         ==> read (memory :> bytes8 (word_add s1p (word j))) s =
                             s1b j) /\
                    (!j. j < 768
                         ==> read (memory :> bytes8 (word_add s2p (word j))) s =
                             s2b j) /\
                    (!j. j < 2496
                         ==> read (memory :> bytes8 (word_add t0p (word j))) s =
                             t0b j) /\
                    read events s = e)
               (\s. read PC s =
                    (if r = 18
                     then word(pc + mldsa65_signature_internal_join4)
                     else word(pc + mldsa65_signature_internal_loop1_next1)) /\
                    read X23 s = (if r = 18 then word 0 else word 4294967295) /\
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
                                  (mld_polyvec_matrix_expand 5 rh)
                                  (mld_polyvec_map mld_poly_ntt
                                    (mld_polyvec_unpack 128
                                      mld_polyeta_unpack_4 s1b))
                                  (mld_polyvec_map mld_poly_ntt
                                    (mld_polyvec_unpack 128
                                      mld_polyeta_unpack_4 s2b))
                                  (mld_polyvec_map mld_poly_ntt
                                    (mld_polyvec_unpack 416
                                      mld_polyt0_unpack t0b))
                                  mu rhop (5 * n) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_att sig B sp0 rh s1p s2p t0p guard mf pc C r x b /\
                       memaccess_inbounds e2
                        [sig,3309; B,11464; word_add sp0 (word 1568),176;
                         word_add sp0 (word 13240),208; sp0,1568;
                         s1p,640; s2p,768; t0p,2496;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,3309; B,11464; word_add sp0 (word 13240),208;
                         sp0,1568]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18; X23; X25; X27; X30] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(B,6144);
                  memory :> bytes(word_add B (word 6144),1024);
                  memory :> bytes(word_add B (word 7200),1024);
                  memory :> bytes(word_add B (word 8224),1024);
                  memory :> bytes(word_add B (word 9248),1024);
                  memory :> bytes(word_add B (word 10272),768);
                  memory :> bytes(word_add B (word 11296),48);
                  memory :> bytes(word_add B (word 11360),16);
                  memory :> bytes(word_add sp0 (word 13240),208);
                  memory :> bytes(sp0,1568)])`;;

let SIGN65_AALLOWED =
  [`sig:int64`; `B:int64`; `sp0:int64`; `rh:num`; `s1p:int64`; `s2p:int64`;
   `t0p:int64`; `guard:int64`; `mf:int64`; `pc:num`; `C:num`; `r:num`;
   `x:num->int32`; `b:num->byte`];;

let SIGN65_ACALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc SIGN65_EXEC name
   ilist SIGN65_AALLOWED n;;

let SIGN65_CPH = `mld_poly_ntt (mld_poly_challenge 49 48 C)`;;
let SIGN65_AR0 =
  list_mk_comb(`mld_sign_r0`,
    [`mld_poly_decompose_lo_32`; SIGN65_W; SIGN65_S2H; SIGN65_CPH]);;
let SIGN65_ACT0 = list_mk_comb(`mld_sign_ct0`,[SIGN65_T0H; SIGN65_CPH]);;
let SIGN65_CT =
  `mld_sign_ctilde 6 128 mu
    (mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
      (mld_sign_w 5 (mld_polyvec_matrix_expand 5 rh)
        (mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n))))`;;
let SIGN65_SP = `word_add sp0 (word 1568):int64`;;

let SIGN65_SIGATT =
 `mld_sign_attempt_sig 6 5 48 49 mld_poly_uniform_gamma1_19 mld_polyz_pack_19
   640 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
   (mld_polyvec_matrix_expand 5 rh)
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s1b))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 128 mld_polyeta_unpack_4 s2b))
   (mld_polyvec_map mld_poly_ntt
     (mld_polyvec_unpack 416 mld_polyt0_unpack t0b))
   mu rhop (5 * n)`;;

let SIGN65_ATT_MID = subst [SIGN65_SIGATT,`SIGATT:num->byte`]
 `\s. read SP s = word_add sp0 (word 1568) /\
      read X19 s = word_add B (word 9248) /\
      read X20 s = word_add B (word 7200) /\
      read X22 s = B /\
      read X23 s = (if r = 18 then word 0 else word 4294967295) /\
      read X24 s = word_add B (word 8224) /\
      read X28 s = word_add B (word 11296) /\
      read (memory :> bytes64 (word_add sp0 (word 1680))) s =
      word_add B (word 10272) /\
      read (memory :> bytes64 (word_add sp0 (word 1688))) s =
      word_add B (word 11360) /\
      read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
      read (memory :> bytes(ea,el)) s = ev /\
      (r = 18
       ==> !t. t < 3309
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   SIGATT t)`;;

let SIGN65_ZARGS =
  [`r:num`; `sig:int64`; `B:int64`; SIGN65_SP; `s1p:int64`; `s1b:num->byte`;
   SIGN65_CPH; `rhop:num`; `5 * n`; `guard:int64`; `pc:num`];;

let SIGN65_RARGS m =
  [m; `B:int64`; SIGN65_W; `s2p:int64`; `s2b:num->byte`; `t0p:int64`;
   `t0b:num->byte`; SIGN65_CPH; `pc:num`];;

let SIGN65_ZCASE_TAC =
  SUBGOAL_THEN `r <= 5 /\ ~(r = 18)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 5` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 5 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SIGN65_ACALL_TAC "H_ZPRE" SIGN65_ZARGS 2 THEN
  SIGN_PC_SIMP_TAC THEN
  SIGN65_ACALL_TAC "H_ZFAIL" SIGN65_ZARGS 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_PATH_DISCHARGE_TAC;;

let SIGN65_WCASE_TAC =
  SUBGOAL_THEN `(r - 5) DIV 2 <= 6 /\ (r - 5) DIV 2 < 6 /\ ~(r = 18) /\
                2 * (r - 5) DIV 2 <= r - 5`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 17` THEN UNDISCH_TAC `5 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SIGN65_AR0; SIGN65_ACT0; `261692`; `261888`; `r - 5`;
                `(r - 5) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 5` THEN UNDISCH_TAC `r < 17` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SIGN65_ACALL_TAC "H_RPRE" (SIGN65_RARGS `(r - 5) DIV 2`) 3 THEN
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `5 <= r /\ r < 17 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 5)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 5) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SIGN65_ACALL_TAC "H_RFAIL1" (SIGN65_RARGS `(r - 5) DIV 2`) 4;
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
    SIGN65_ACALL_TAC "H_RFAIL2" (SIGN65_RARGS `(r - 5) DIV 2`) 4] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_PATH_DISCHARGE_TAC;;

let SIGN65_TCASE_TAC =
  SUBGOAL_THEN `17 <= r /\ 6 <= 6` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 17)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SIGN65_AR0; SIGN65_ACT0; `261692`; `261888`; `12`; `6`]
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
  SIGN65_ACALL_TAC "H_RPRE" (SIGN65_RARGS `6`) 3 THEN
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
        ==> read (memory :> bytes8 (word_add B (word (10272 + j)))) s3 =
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
      `read (memory :> bytes (word_add B (word 11296),48)) s = C`) (concl th)
    then FIRST_ASSUM(fun cth ->
           if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
           then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES_OFF
                            (TRANS th (SYM cth)))
           else NO_TAC)
    else NO_TAC) THEN
  SIGN65_ACALL_TAC "H_TAIL"
   [`sig:int64`; `B:int64`; SIGN65_SP; SIGN65_CT; `x:num->int32`;
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
    SIGN65_ACALL_TAC "H_ZPRE" (`5`::tl SIGN65_ZARGS) 2 THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_CASES_TAC `r < 17` THENL [SIGN65_WCASE_TAC; SIGN65_TCASE_TAC]];;

let SIGN65_ACLEAN_TAC =
  FULL_INIT_TAC THEN
  SIGN65_ACALL_TAC "H_CLEAN"
   [`r = 18`; `B:int64`; SIGN65_SP; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let SIGN65_ZPRE = par_await SIGN65_ZPRE_ASYNC;;
let SIGN65_ZFAIL = par_await SIGN65_ZFAIL_ASYNC;;
let SIGN65_RPRE = par_await SIGN65_RPRE_ASYNC;;
let SIGN65_RFAIL1 = par_await SIGN65_RFAIL1_ASYNC;;
let SIGN65_RFAIL2 = par_await SIGN65_RFAIL2_ASYNC;;
let SIGN65_TAIL = par_await SIGN65_TAIL_ASYNC;;
let SIGN65_CLEAN = par_await SIGN65_CLEAN_ASYNC;;
let SIGN65_HEAD = par_await SIGN65_HEAD_ASYNC;;

let SIGN65_ATT_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN65_HEAD th) "H_HEAD" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN65_ZPRE th) "H_ZPRE" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN65_ZFAIL th) "H_ZFAIL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN65_CLEAN th) "H_CLEAN") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_RPRE "H_RPRE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_RFAIL1 "H_RFAIL1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_RFAIL2 "H_RFAIL2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN65_TAIL "H_TAIL" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (B:int64) (sp0:int64) (rh:num) (s1p:int64) (s2p:int64)
     (t0p:int64) (guard:int64) (mf:int64) (pc:num) (C:num) (r:num) (x:num->int32)
     (b:num->byte).
     APPEND (f_ev_cl sig B sp0 rh s1p s2p t0p guard mf pc C r x b)
      (APPEND
        (if r < 5 then f_ev_pz sig B sp0 rh s1p s2p t0p guard mf pc C r x b
         else if r < 17
         then if EVEN (r - 5)
              then f_ev_pw1 sig B sp0 rh s1p s2p t0p guard mf pc C r x b
              else f_ev_pw2 sig B sp0 rh s1p s2p t0p guard mf pc C r x b
         else f_ev_pt sig B sp0 rh s1p s2p t0p guard mf pc C r x b)
        (f_ev_hd sig B sp0 rh s1p s2p t0p guard mf pc C r x b))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `B:int64`; `sp0:int64`; `rh:num`;
    `s1p:int64`; `s1b:num->byte`; `s2p:int64`; `s2b:num->byte`;
    `t0p:int64`; `t0b:num->byte`; `mu:num`; `rhop:num`; `n:num`; `C:num`;
    `r:num`; `x:num->int32`; `b:num->byte`; `guard:int64`; `pc:num`] THEN
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
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]);;

let SIGN65_ATT_ASYNC = prove_async
 (SIGN65_ATT_STMT,
  SIGN65_ATT_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa65_signature_internal_join2`
    SIGN65_ATT_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    SIGN65_ACALL_TAC "H_HEAD"
     [`B:int64`; `sp0:int64`; `rh:num`; `mu:num`; `rhop:num`; `n:num`;
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
(* the buffers, at stackpointer + 1760 if stackpointer is a multiple of 32   *)
(* and at stackpointer + 1744 otherwise.                                     *)
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
(* stackpointer + b (B) and the frame at stackpointer + 1568: the saved      *)
(* registers, the canary, the pointers in the frame, rho (where the          *)
(* expansion of the matrix on demand reads it), mu, rho'', the pointers to   *)
(* s1, s2 and t0 in the secret key and the key itself do not change; before  *)
(* attempt i the registers of the loop hold the addresses of its buffers and *)
(* kappa = 5 * i (the 32-bit word at sp + 108); after the last attempt x23   *)
(* holds the result and sig the signature.                                   *)
(* ------------------------------------------------------------------------- *)

let SIGN65_INV b =
  let nm n = mk_small_numeral n in
  subst
   [nm b,`oBB:num`; nm(b + 6144),`oMAT:num`; nm(b + 7168),`oRHO:num`;
    nm(b + 7200),`oTT:num`; nm(b + 8224),`oCP:num`; nm(b + 9248),`oSCR:num`;
    nm(b + 10272),`oW1P:num`; nm(b + 11040),`oSEED:num`;
    nm(b + 11168),`oMUO:num`; nm(b + 11232),`oRHOP:num`;
    nm(b + 11264),`oX26:num`; nm(b + 11296),`oCT:num`;
    nm(b + 11360),`oYI:num`; nm(b + 11392),`oS2:num`; nm(b + 11424),`oT0:num`;
    nm(b + 11456),`oS1:num`]
  `\i s.
     read SP s = word_add stackpointer (word 1568) /\
     read (memory :> bytes64 (word_add stackpointer (word 1568))) s =
     x19_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1576))) s =
     x20_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1584))) s =
     x21_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1592))) s =
     x22_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1600))) s =
     x23_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1608))) s =
     x24_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1616))) s =
     x25_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1624))) s =
     x26_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1632))) s =
     x27_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1640))) s =
     x28_init /\
     read (memory :> bytes64 (word_add stackpointer (word 1648))) s =
     returnaddress /\
     read (memory :> bytes64 (word_add stackpointer (word 13448))) s =
     canary /\
     read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
       s = guard /\
     read (memory :> bytes64 guard) s = canary /\
     read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
     read (memory :> bytes(ea,el)) s = ev /\
     read X22 s = word_add stackpointer (word oBB) /\
     read (memory :> bytes64 (word_add stackpointer (word 1664))) s = sig /\
     read (memory :> bytes64 (word_add stackpointer (word 1680))) s =
     word_add stackpointer (word oW1P) /\
     read (memory :> bytes64 (word_add stackpointer (word 1688))) s =
     word_add stackpointer (word oYI) /\
     read (memory :> bytes64 (word_add stackpointer (word 1696))) s =
     word_add stackpointer (word oSEED) /\
     read (memory :> bytes64 (word_add stackpointer (word 1704))) s =
     word_add stackpointer (word oMAT) /\
     read (memory :> bytes64 (word_add stackpointer (word 1712))) s =
     word_add stackpointer (word oRHOP) /\
     read (memory :> bytes(word_add stackpointer (word oRHO),32)) s = rh /\
     read (memory :> bytes(word_add stackpointer (word oMUO),64)) s = MU /\
     read (memory :> bytes(word_add stackpointer (word oRHOP),64)) s =
     mld_sign_rhoprime (\j. skb(32 + j)) RND MU /\
     read (memory :> bytes64 (word_add stackpointer (word oS1))) s =
     word_add sk (word 128) /\
     read (memory :> bytes64 (word_add stackpointer (word oS2))) s =
     word_add sk (word 768) /\
     read (memory :> bytes64 (word_add stackpointer (word oT0))) s =
     word_add sk (word 1536) /\
     (!j. j < 4032
          ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\
     (i < mld_sign_natt 13106 18 D
      ==> read X19 s = word_add stackpointer (word oSCR) /\
          read X20 s = word_add stackpointer (word oTT) /\
          read X21 s = word_add stackpointer (word 13240) /\
          read X24 s = word_add stackpointer (word oCP) /\
          read X26 s = word_add stackpointer (word oX26) /\
          read X28 s = word_add stackpointer (word oCT) /\
          read (memory :> bytes32 (word_add stackpointer (word 1676))) s =
          word(5 * i)) /\
     (i = mld_sign_natt 13106 18 D
      ==> read X23 s =
          (if mld_sign_ok_65 skb MU RND then word 0 else word 4294967292) /\
          (!t. t < 3309
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   mld_sign_sig_65 skb MU RND t))`;;

let SIGN65_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 1775 1760 1744;;

let SIGN65_MALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `rnd:int64`; `sk:int64`; `ext:int64`; `rh:num`;
   `D:num->num#num#(num->int32)#(num->byte)`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let SIGN65_MCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc SIGN65_EXEC name
   ilist SIGN65_MALLOWED n;;

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
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SIGN65_ATT th) "H_ATT"
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th) then
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET"
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_MEXP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_H_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_H" THEN
  CONCRETIZE_F_EVENTS_TAC SIGN65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`;
    `pre:int64`; `prelen:num`; `rnd:int64`; `sk:int64`; `ext:int64`;
    `skb:num->byte`; `M:num`; mk_var("PRE",`:num`); `RND:num`; `MU:num`;
    `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13456 THEN
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
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 13456):int64)` THEN
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
(* The prologue, up to the start of the first attempt: unpack_sk (rho, tr    *)
(* and the key into the seed buffer, the pointers to s1, s2 and t0 in the    *)
(* key into their slots), then on ext either mld_H44 for mu (from tr, the    *)
(* prefix and m) or the inlined copy of 64 bytes from m (as four 128-bit     *)
(* words), then mld_H44 for rho'' (from the key, rnd and mu) and the copy of *)
(* rho into the structure of the matrix sampled on demand. The offsets from  *)
(* b are those of tr and the key in the seed buffer, mu, rho'' and rho.      *)
(* ------------------------------------------------------------------------- *)

let SIGN65_RHO_TAC b =
  let pat = SIGN65_NUMV "oRHO" b 7168
   `!j. j < 32 ==> read (memory :> bytes8
         (word_add stackpointer (word (oRHO + j)))) s = f j` in
  FIRST_ASSUM(fun th0 ->
    let th = CONV_RULE(REWRITE_CONV[ADD_ASSOC] THENC SIGN_NUM_ARITH_CONV) th0 in
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
  let nh = n0 + 29 in
  let nm = nh + 7 in
  let kpat = SIGN65_NUMV "oKEY" b 11136
   `!j. j < 32 ==> read (memory :> bytes8
         (word_add stackpointer (word (oKEY + j)))) s = f j`
  and rgoal = SIGN65_NUMV "oRHO" b 11232
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    mld_sign_rhoprime (\j. skb(32 + j)) RND MU`
  and rpat = SIGN65_NUMV "oRHO" b 11232
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
  SIGN65_MCALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; `skb:num->byte`; `pc:num`; `read X30 s`] nm THEN
  ARM_STEPS_TAC SIGN65_EXEC [nm + 1] THEN
  SIGN65_RHO_TAC b THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `0 = n <=> n = 0`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  SIGN_SEL_DISCHARGE_TAC;;

let SIGN65_MU_TAC b n =
  let sv = mk_var("s"^string_of_int n,`:armstate`) in
  let mgoal = subst [sv,`s:armstate`] (SIGN65_NUMV "oMU" b 11168
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s = MU`)
  and mpat = subst [sv,`s:armstate`] (SIGN65_NUMV "oMU" b 11168
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
  let tpat = SIGN65_NUMV "oTR" b 11072
   `!j. j < 64 ==> read (memory :> bytes8
         (word_add stackpointer (word (oTR + j)))) s = f j` in
  ARM_STEPS_TAC SIGN65_EXEC [44] THEN
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  ARM_STEPS_TAC SIGN65_EXEC (45--53) THEN
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
    `read X30 s`] 54 THEN
  FIRST_ASSUM(fun th ->
    if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE
          [ASSUME `word_zx(ext:int64) = (word 0:int32)`] th)
    else NO_TAC) THEN
  SIGN65_MU_TAC b 54 THEN
  SIGN65_PROL_TAIL_TAC b 55;;

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
  let mu = SIGN65_NUMV "oMU" b 11168
   `word_add stackpointer (word oMU):int64` in
  let mgoal = SIGN65_NUMV "oMU" b 11168
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s51 = MU`
  and mpat = SIGN65_NUMV "oMU" b 11168
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s51 =
    M MOD 2 EXP 512` in
  ARM_STEPS_TAC SIGN65_EXEC [44] THEN
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  SIGN65_M128_TAC `s44:armstate` THEN
  ARM_STEPS_TAC SIGN65_EXEC (45--51) THEN
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
  FULL_INIT_TAC THEN ARM_STEPS_TAC SIGN65_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (4--8) THEN
  MEXP_BUFFER_TAC SIGN65_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC SIGN65_EXEC (9--42) THEN
  SIGN65_MCALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `read X6 s`; `skb:num->byte`; `pc:num`; `read X30 s`] 43 THEN
  ASM_CASES_TAC `word_zx(ext:int64) = (word 0:int32)` THENL
   [SIGN65_PROL_H_TAC b; SIGN65_PROL_X_TAC b];;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop over the attempts: the facts about attempt i     *)
(* (its record D i as mld_sign_attempt_declass gives it, the termination of  *)
(* its challenge, and the result and signature if it is the last), the       *)
(* attempt as one step (ATT, with B = stackpointer + b, sp0 = stackpointer   *)
(* and s1, s2 and t0 at their offsets in the secret key), then the three     *)
(* exits: on success to join4; on rejection kappa += 5, then back to loop1   *)
(* or, after the last attempt, -4 in x23 and the zeroing of the signature    *)
(* with memset, to join4. The equations for mld_sign_ok_65 and               *)
(* mld_sign_sig_65 are made conditional on ~(i + 1 < N) before any call,     *)
(* which would otherwise rewrite the postcondition with them.                *)
(* ------------------------------------------------------------------------- *)

let SIGN65_BALLOWED = SIGN65_MALLOWED @ [`i:num`];;

let SIGN65_ATT_ILIST b =
  [`sig:int64`; mk_comb(`word_add stackpointer:int64->int64`,
                        mk_comb(`word:num->int64`,mk_small_numeral b));
   `stackpointer:int64`; `rh:num`;
   `word_add sk (word 128):int64`; `\j. (skb:num->byte)(128 + j)`;
   `word_add sk (word 768):int64`; `\j. (skb:num->byte)(768 + j)`;
   `word_add sk (word 1536):int64`; `\j. (skb:num->byte)(1536 + j)`;
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

(*** The bytes of s1, s2 and t0 in the secret key, as ATT takes them ***)

let SIGN65_SK_SLICE_TAC =
  MAP_EVERY (fun (off,len) ->
    let t = subst [mk_small_numeral off,`off:num`; mk_small_numeral len,`len:num`]
     `!j. j < len
          ==> read (memory :> bytes8 (word_add sk (word (off + j)))) s0 =
              (skb:num->byte)(off + j)` in
    SUBGOAL_THEN t ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC (mk_binop `(<):num->num->bool` `j:num`
                    (mk_small_numeral len)) THEN ARITH_TAC;
      ALL_TAC]) [128,640; 768,768; 1536,2496];;

let SIGN65_BODY_ATT_TAC b =
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes32
             (word_add stackpointer (word 1676))) s0 = word (5 * i)`)
           (concl th)
    then ASSUME_TAC(MATCH_MP SIGN_BYTES16_OF_BYTES32
          (CONJ th (MP (ARITH_RULE `i < 13106 ==> 5 * i < 65536`)
                       (ASSUME `i < 13106`))))
    else NO_TAC) THEN
  SIGN65_SK_SLICE_TAC THEN
  REMOVE_THEN "H_ATT" (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc,SIGN65_EXEC,0x0,
       mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc,th)
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
    `read X23 s = (if b then x else y)`) (concl th))) THEN
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
  ARM_STEPS_TAC SIGN65_EXEC (11--16) THEN
  SIGN65_MEMSET_TAC SIGN65_BALLOWED 16 THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 13106 18 D)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mld_sign_natt 13106 18 D <= 13106`; `~(i + 1 < 13106)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SIGN65_LAST_TAC SIGN65_NCASE_TH THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `!i. i < 3309 ==> read (memory :> bytes8 (word_add sig (word i))) s =
                      word_zx(word 0:int64)`) (concl th))) THEN
  REWRITE_TAC[WORD_ZX_0] THEN DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN65_BODY_DISCHARGE_TAC;;

let SIGN65_FAIL_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read X23 s = (if b then x else y)`) (concl th))) THEN
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
(* The epilogue, from join4: the zeroing of the pointers to s1, s2 and t0,   *)
(* the memset of the structure of the matrix (with rho), the inlined zeroing *)
(* of the 256 bytes of the seed buffer and the check of the canary.          *)
(* ------------------------------------------------------------------------- *)

let SIGN65_EPIL_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN65_EPIL_TAC =
  SIGN_DROP_TAC SIGN65_DANGER THEN
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (1--11) THEN
  SIGN65_MEMSET_TAC SIGN65_MALLOWED 11 THEN
  ARM_STEPS_TAC SIGN65_EXEC (17--27) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC SIGN65_EXEC (28--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SIGN_RET_ZX] THEN
  SIGN65_EPIL_DISCHARGE_TAC;;

let SIGN65_MAIN_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `mld_sign_natt 13106 18 D`
   `pc + mldsa65_signature_internal_loop1`
   `pc + mldsa65_signature_internal_join4` (SIGN65_INV b) THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC; SIGN65_PROL_TAC b; SIGN65_BODY_TAC b; SIGN65_EPIL_TAC];;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  SIGN65_START_TAC THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    SIGN65_MAIN_TAC 1760;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    SIGN65_MAIN_TAC 1744]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
