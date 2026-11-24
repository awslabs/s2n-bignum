(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with the secret key, all the attempts (ML-DSA-44): the proof (see *)
(* signature_internal_44_spec.ml), with the tools of                         *)
(* utils/mldsa_native_signing.ml and utils/mldsa_native_signing_rr.ml, as    *)
(* for AArch64, with the x86 code, whose frame is aligned to 32 bytes (see   *)
(* utils/mldsa_native_realign.ml), the buffers and the pointers to them that *)
(* the code saves being at fixed offsets from bot, the bottom of the aligned *)
(* frame.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_eq_spec.ml";;
needs "x86/proofs/utils/mldsa_native_hash.ml";;
needs "x86/proofs/utils/mldsa_native_wrap.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;
needs "x86/proofs/utils/mldsa_native_signing_rr.ml";;

let SIGN44_EXEC =
  MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_EXEC;;

let SIGN44_MC = mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc;;

(* ------------------------------------------------------------------------- *)
(* The proof is in parts, each a FULL lemma for a segment of the code, with  *)
(* the frame at bot (RSP = bot + 1678 in the loop over the attempts, RBP =   *)
(* bot + 11262): the loop over z up to an index m (ZPRE), the exit at a z    *)
(* whose norm check fails (ZFAIL), the loop over the rows of w0 up to a row  *)
(* m (RPRE), the exits at a row whose first or second check fails (RFAIL1,   *)
(* RFAIL2), the packing of c~ and the hints (TAIL), the cleanup and the      *)
(* decision (CLEAN), and the start of an attempt up to the NTT of the        *)
(* challenge (HEAD). The attempt (ATT) follows from them, with one path for  *)
(* each kind of result r of mld_sign_attempt_declass: r < 4 (z_r fails), 4   *)
(* <= r < 12 (the check r - 4 of the rows fails), 12 (too many hints) and 13 *)
(* (success). The buffers: the pointers into the secret key for s1, t0 and   *)
(* s2 (the structures that unpack_sk fills) at bot + 1806, + 1838 and +      *)
(* 1870, the structure of y (the address of rho'' and kappa) at + 1902, c~   *)
(* at + 1934, the seed buffer (rho, tr, key, mu at + 2094, rho'' at + 2158)  *)
(* at + 1966, w1 packed at + 2222, the polynomial of y_i, also used as       *)
(* scratch, at + 2990, the challenge at + 4014, the SHAKE256 context and the *)
(* polynomial of z at + 5038, the structure of the matrix (a polynomial and  *)
(* rho at + 7086) at + 6062 and w at + 7118; the pointers to them that the   *)
(* code saves are at + 1694 to + 1798, with kappa (a 16-bit word) at + 1790, *)
(* and the saved registers at + 11214 to + 11262. s1, s2 and t0 in the NTT   *)
(* domain and y, which the code does not keep, are the vectors of the model  *)
(* (SIGN44_S1H, SIGN44_S2H, SIGN44_T0H and mld_sign_y), polynomial by        *)
(* polynomial (see utils/mldsa_native_signing_rr.ml).                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The vectors of the model that the parts use: s1 in the NTT domain, from   *)
(* the secret key skb, y from rho'' and kappa, and z_i.                      *)
(* ------------------------------------------------------------------------- *)

let SIGN44_S1H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 96 mld_polyeta_unpack_2
     (\j. (skb:num->byte)(128 + j)))`;;

let SIGN44_YK = `mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa`;;

let SIGN44_ZI = list_mk_comb(`mld_sign_z`,
  [SIGN44_S1H; `cphat:num->int32`; SIGN44_YK; `i:num`]);;

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check: polynomial i of s1 unpacked from the secret key into the      *)
(* scratch polynomial at bot + 5038 and transformed, its product with the    *)
(* challenge, y_i sampled again at bot + 2990 from rho'' (whose address the  *)
(* structure of y at bot + 1902 holds, with kappa) and z_i packed.           *)
(* ------------------------------------------------------------------------- *)

let SIGN44_ZPRE_STMT =
 `?f_zpre.
    !e m sig sk skb bot rhop kappa cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 1678)) /\
      aligned 16 (word_add bot (word 2990)) /\
      aligned 16 (word_add bot (word 5038)) /\ m <= 4 /\
      (!i. i < m
           ==> mld_poly_chknorm
                (mld_sign_z
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(128 + j))))
                  cphat (mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa) i)
                (word 130994) =
               word 0) /\
      nonoverlapping (sig,2420) (bot,11278) /\
      ALL (nonoverlapping (sk,2560)) [(sig,2420); (bot,11278)] /\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,2420); (bot,11278)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s = word(pc + mldsa44_signature_internal_loop1) /\
                read RSP s = word_add bot (word 1678) /\
                read RBP s = word_add bot (word 11262) /\
                read RBX s = word_add bot (word 5038) /\
                read R12 s = word_add bot (word 2990) /\
                read R15 s = word_add bot (word 4014) /\
                read R14 s = word 0 /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1806))) s =
                word_add sk (word 128) /\
                read (memory :> bytes64 (word_add bot (word 1902))) s =
                word_add bot (word 2158) /\
                read (memory :> bytes16 (word_add bot (word 1910))) s =
                word kappa /\
                read (memory :> bytes64 (word_add bot (word 1782))) s = sig /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(4014 + 4 * j)))) s =
                         cphat j) /\
                read (memory :> bytes(word_add bot (word 2158),64)) s = rhop /\
                (!j. j < 2560
                     ==> read (memory :> bytes8 (word_add sk (word j))) s =
                         skb j) /\
                read events s = e)
           (\s. read RIP s =
                (if m < 4
                 then word(pc + mldsa44_signature_internal_loop1)
                 else word(pc + mldsa44_signature_internal_loop1_exit1)) /\
                read RSP s = word_add bot (word 1678) /\
                read R14 s = word m /\
                (!t. t < 576 * m
                     ==> read (memory :> bytes8
                                (word_add sig (word(32 + t)))) s =
                         mld_polyvec_pack 576 mld_polyz_pack_17
                          (mld_polyvec
                            (mld_sign_z
                              (mld_polyvec_map mld_poly_ntt
                                (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                                  (\j. skb(128 + j))))
                              cphat
                              (mld_sign_y mld_poly_uniform_gamma1_17 rhop
                                kappa))) t) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_zpre m sig sk bot pc /\
                   memaccess_inbounds e2
                    [sig,2420; sk,2560; bot,11278;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [sig,2420; bot,11278]))
           (MAYCHANGE [RSP; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,1678);
              memory :> bytes(word_add bot (word 2990),1024);
              memory :> bytes(word_add bot (word 5038),1024);
              memory :> bytes(word_add sig (word 32),2304)])`;;

let SIGN44_ZALLOWED =
  [`pc:num`; `sig:int64`; `sk:int64`; `bot:int64`; `i:num`];;

let SIGN44_ZCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN44_MC SIGN44_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    SIGN44_ZALLOWED n;;

let SIGN44_ZPRE_INV =
 `\i s. read RSP s = word_add bot (word 1678) /\
        read RBP s = word_add bot (word 11262) /\
        read RBX s = word_add bot (word 5038) /\
        read R12 s = word_add bot (word 2990) /\
        read R15 s = word_add bot (word 4014) /\
        read R14 s = word i /\
        (read DF s <=> false) /\
        read (memory :> bytes64 (word_add bot (word 1806))) s =
        word_add sk (word 128) /\
        read (memory :> bytes64 (word_add bot (word 1902))) s =
        word_add bot (word 2158) /\
        read (memory :> bytes16 (word_add bot (word 1910))) s = word kappa /\
        read (memory :> bytes64 (word_add bot (word 1782))) s = sig /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add bot (word(4014 + 4 * j))))
                   s = cphat j) /\
        read (memory :> bytes(word_add bot (word 2158),64)) s = rhop /\
        (!j. j < 2560
             ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\
        (!t. t < 576 * i
             ==> read (memory :> bytes8 (word_add sig (word(32 + t)))) s =
                 mld_polyvec_pack 576 mld_polyz_pack_17
                  (mld_polyvec
                    (mld_sign_z
                      (mld_polyvec_map mld_poly_ntt
                        (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                          (\j. skb(128 + j))))
                      cphat
                      (mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa)))
                  t)`;;

(*** The address of polynomial i of s1 in the secret key, in RSI ***)

let SIGN44_ETA_ADDR = prove
 (`!(sk:int64) i.
     word_add (word_shl (word_add (word i) (word (2 * val (word i:int64)))) 5)
              (word_add sk (word 128)) =
     word_add sk (word(128 + 96 * i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_MUL; WORD_VAL] THEN
  REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC WORD_RULE);;

(*** The steps of the loop body up to the norm check of z_i ***)

let SIGN44_ZHEAD_TAC =
  let s1i = mk_comb(mk_comb(`mld_poly_of`,SIGN44_S1H),`i:num`) in
  let cs1i = list_mk_comb(`mld_poly_pointwise_montgomery`,
                          [s1i; `cphat:num->int32`]) in
  let ics1i = mk_comb(`mld_poly_invntt_tomont`,cs1i) in
  let yi = mk_comb(mk_comb(`mld_poly_of`,SIGN44_YK),`i:num`) in
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN44_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN44_ETA_ADDR]) THEN
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `2560`; `128 + 96 * i`;
                `96`; `s5:x86state`] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  SIGN44_ZCALL_TAC "H_ETA"
   [`read RDI s`; `read RSI s`; `\j. (skb:num->byte)((128 + 96 * i) + j)`]
   6 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyeta_unpack_2` THEN
  X86_STEPS_TAC SIGN44_EXEC (7--8) THEN
  SIGN44_ZCALL_TAC "H_NTT"
   [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                   (\j. (skb:num->byte)(128 + j))) i`] 9 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (10--12) THEN
  SIGN44_ZCALL_TAC "H_PW"
   [`read RDI s`; `read RSI s`; s1i; `cphat:num->int32`] 13 THEN
  X86_STEPS_TAC SIGN44_EXEC (14--15) THEN
  SIGN44_ZCALL_TAC "H_INV" [`read RDI s`; cs1i] 16 THEN
  X86_STEPS_TAC SIGN44_EXEC (17--22) THEN
  SIGN44_ZCALL_TAC "H_GAMMA"
   [`read RDI s`; `read RSI s`; `rhop:num`; `read RDX s`] 23 THEN
  SIGN_GAMMA_POLY_OF_TAC `mld_poly_uniform_gamma1_17` THEN
  X86_STEPS_TAC SIGN44_EXEC (24--26) THEN
  SIGN44_ZCALL_TAC "H_ADD" [`read RDI s`; `read RSI s`; ics1i; yi] 27 THEN
  X86_STEPS_TAC SIGN44_EXEC (28--29) THEN
  SIGN44_ZCALL_TAC "H_RED"
   [`read RDI s`; list_mk_comb(`mld_poly_add`,[ics1i; yi])] 30 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  X86_STEPS_TAC SIGN44_EXEC (31--33) THEN
  SIGN44_ZCALL_TAC "H_CHK" [`read RDI s`; SIGN44_ZI; `read RSI s`] 34 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_REDUCE_CONV
    `word_zx (word 130994:int64):int32`]);;

let SIGN44_ZBODY_TAC =
  let chk = mk_eq(list_mk_comb(`mld_poly_chknorm`,
                               [SIGN44_ZI; `word 130994:int32`]),
                  `word 0:int32`) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 4` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SIGN44_ZHEAD_TAC THEN
  SUBGOAL_THEN chk ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME chk; WORD_ZX_0]) THEN
  X86_STEPS_TAC SIGN44_EXEC (35--40) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  X86_STEPS_TAC SIGN44_EXEC (41--41) THEN
  SIGN44_ZCALL_TAC "H_PZ" [`read RDI s`; `read RSI s`; SIGN44_ZI; `i:num`] 42
  THEN
  X86_STEPS_TAC SIGN44_EXEC (43--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SIGN_TEST_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_17`; `576`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_17_LOCAL] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN44_ZSETUP_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ETA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_GAMMA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CHK";;

let SIGN44_ZPRE = prove
 (SIGN44_ZPRE_STMT,
  SIGN44_ZSETUP_TAC THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_Z_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PZ" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sig:int64) (sk:int64) (bot:int64) (pc:num).
     APPEND (f_ev_back m sig sk bot pc)
      (APPEND (ENUMERATEL m (\i. f_ev_zit sig sk bot pc i))
              (f_ev_front m sig sk bot pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:num`; `sig:int64`; `sk:int64`;
    `skb:num->byte`; `bot:int64`; `rhop:num`; `kappa:num`;
    `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa44_signature_internal_loop1`
     `if m < 4 then pc + mldsa44_signature_internal_loop1
      else pc + mldsa44_signature_internal_loop1_exit1`
     SIGN44_ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN44_ZBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    SIGN_BETA_ALL_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT;
                    ENUMERATEL; APPEND] THEN
    SIGN_NIL_EVENTS_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exit from the loop over z at a polynomial whose norm check fails, to  *)
(* the cleanup (join3, through join7) with RDX = -1 as a 32-bit integer.     *)
(* ------------------------------------------------------------------------- *)

let SIGN44_ZFAIL_STMT =
 `?f_zfail.
    !e i sig sk skb bot rhop kappa cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 2990)) /\
      aligned 16 (word_add bot (word 5038)) /\ i < 4 /\
      ~(mld_poly_chknorm
         (mld_sign_z
           (mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 96 mld_polyeta_unpack_2
               (\j. skb(128 + j))))
           cphat (mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa) i)
         (word 130994) =
        word 0) /\
      nonoverlapping (sig,2420) (bot,11278) /\
      ALL (nonoverlapping (sk,2560)) [(sig,2420); (bot,11278)] /\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,2420); (bot,11278)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s = word(pc + mldsa44_signature_internal_loop1) /\
                read RSP s = word_add bot (word 1678) /\
                read RBP s = word_add bot (word 11262) /\
                read RBX s = word_add bot (word 5038) /\
                read R12 s = word_add bot (word 2990) /\
                read R15 s = word_add bot (word 4014) /\
                read R14 s = word i /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1806))) s =
                word_add sk (word 128) /\
                read (memory :> bytes64 (word_add bot (word 1902))) s =
                word_add bot (word 2158) /\
                read (memory :> bytes16 (word_add bot (word 1910))) s =
                word kappa /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(4014 + 4 * j)))) s =
                         cphat j) /\
                read (memory :> bytes(word_add bot (word 2158),64)) s = rhop /\
                (!j. j < 2560
                     ==> read (memory :> bytes8 (word_add sk (word j))) s =
                         skb j) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa44_signature_internal_join3) /\
                read RSP s = word_add bot (word 1678) /\
                read RDX s = word 4294967295 /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_zfail i sig sk bot pc /\
                   memaccess_inbounds e2
                    [sig,2420; sk,2560; bot,11278;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [sig,2420; bot,11278]))
           (MAYCHANGE [RSP; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,1678);
              memory :> bytes(word_add bot (word 2990),1024);
              memory :> bytes(word_add bot (word 5038),1024)])`;;

let SIGN44_ZFAIL = prove
 (SIGN44_ZFAIL_STMT,
  let chk = mk_neg(mk_eq(list_mk_comb(`mld_poly_chknorm`,
                                      [SIGN44_ZI; `word 130994:int32`]),
                         `word 0:int32`)) in
  SIGN44_ZSETUP_TAC THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(i:num) (sig:int64) (sk:int64) (bot:int64) (pc:num).
     f_ev_zfail i sig sk bot pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `i:num`; `sig:int64`; `sk:int64`;
    `skb:num->byte`; `bot:int64`; `rhop:num`; `kappa:num`;
    `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SIGN44_ZHEAD_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (35--35) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME chk]) THEN
  X86_STEPS_TAC SIGN44_EXEC (36--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* s2 and t0 in the NTT domain, from the secret key skb, as the loop over    *)
(* the rows unpacks and transforms them, polynomial by polynomial.           *)
(* ------------------------------------------------------------------------- *)

let SIGN44_S2H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 96 mld_polyeta_unpack_2
     (\j. (skb:num->byte)(512 + j)))`;;

let SIGN44_T0H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 416 mld_polyt0_unpack
     (\j. (skb:num->byte)(896 + j)))`;;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass, leaving the rows of x of the hints, from loop1_exit1: polynomial i  *)
(* of s2 and of t0 unpacked from the secret key into the scratch polynomial  *)
(* at bot + 2990 and transformed, w0_i - c s2_i in place in w and c t0_i.    *)
(* The code saves RBX, which it uses for the offset of t0_i, and restores it *)
(* after the loop.                                                           *)
(* ------------------------------------------------------------------------- *)

let SIGN44_RPRE_STMT =
 `?f_rpre.
    !e m sk skb bot w cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 2990)) /\
      aligned 16 (word_add bot (word 7118)) /\ m <= 4 /\
      (!j. j < m
           ==> mld_poly_chknorm
                (mld_sign_r0 mld_poly_decompose_lo_88 w
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(512 + j))))
                  cphat j)
                (word 95154) = word 0 /\
               mld_poly_chknorm
                (mld_sign_ct0
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 416 mld_polyt0_unpack
                      (\j. skb(896 + j))))
                  cphat j)
                (word 95232) =
               word 0) /\
      nonoverlapping (sk,2560) (bot,11278) /\
      nonoverlapping (word pc,libmldsa_size) (bot,11278)
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s =
                word(pc + mldsa44_signature_internal_loop1_exit1) /\
                read RSP s = word_add bot (word 1678) /\
                read RBP s = word_add bot (word 11262) /\
                read RBX s = word_add bot (word 5038) /\
                read R12 s = word_add bot (word 2990) /\
                read R15 s = word_add bot (word 4014) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1798))) s =
                word_add bot (word 7118) /\
                read (memory :> bytes64 (word_add bot (word 1870))) s =
                word_add sk (word 512) /\
                read (memory :> bytes64 (word_add bot (word 1838))) s =
                word_add sk (word 896) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(4014 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 2560
                     ==> read (memory :> bytes8 (word_add sk (word j))) s =
                         skb j) /\
                (!j. j < 1024
                     ==> read (memory :> bytes32
                                (word_add bot (word(7118 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_88 w j) /\
                read events s = e)
           (\s. read RIP s =
                (if m < 4
                 then word(pc + mldsa44_signature_internal_loop2)
                 else word(pc + mldsa44_signature_internal_loop2_exit1)) /\
                read RSP s = word_add bot (word 1678) /\
                read RBX s = word(416 * m) /\
                read R13 s = word_add bot (word(7118 + 1024 * m)) /\
                read R14 s = word(96 * m) /\
                read (memory :> bytes64 (word_add bot (word 1750))) s =
                word_add bot (word 5038) /\
                (!j. j < 256 * m
                     ==> read (memory :> bytes32
                                (word_add bot (word(7118 + 4 * j)))) s =
                         mld_sign_hint_x 4 mld_poly_decompose_lo_88 w
                          (mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(512 + j))))
                          (mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 416 mld_polyt0_unpack
                              (\j. skb(896 + j))))
                          cphat j) /\
                (!j. 256 * m <= j /\ j < 1024
                     ==> read (memory :> bytes32
                                (word_add bot (word(7118 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_88 w j) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_rpre m sk bot pc /\
                   memaccess_inbounds e2
                    [sk,2560; bot,11278; word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [bot,11278]))
           (MAYCHANGE [RSP; RBX; R13; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,1678);
              memory :> bytes(word_add bot (word 1750),8);
              memory :> bytes(word_add bot (word 2990),1024);
              memory :> bytes(word_add bot (word 7118),4096)])`;;

let SIGN44_RALLOWED = [`pc:num`; `sk:int64`; `bot:int64`; `i:num`];;

let SIGN44_RCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN44_MC SIGN44_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    SIGN44_RALLOWED n;;

let SIGN44_RPRE_INV =
 `\i s. read RSP s = word_add bot (word 1678) /\
        read RBP s = word_add bot (word 11262) /\
        read RBX s = word(416 * i) /\
        read R12 s = word_add bot (word 2990) /\
        read R13 s = word_add bot (word(7118 + 1024 * i)) /\
        read R14 s = word(96 * i) /\
        read R15 s = word_add bot (word 4014) /\
        (read DF s <=> false) /\
        read (memory :> bytes64 (word_add bot (word 1870))) s =
        word_add sk (word 512) /\
        read (memory :> bytes64 (word_add bot (word 1838))) s =
        word_add sk (word 896) /\
        read (memory :> bytes64 (word_add bot (word 1750))) s =
        word_add bot (word 5038) /\
        (!j. j < 256
             ==> read (memory :> bytes32 (word_add bot (word(4014 + 4 * j))))
                   s = cphat j) /\
        (!j. j < 2560
             ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\
        (!j. j < 256 * i
             ==> read (memory :> bytes32 (word_add bot (word(7118 + 4 * j))))
                   s =
                 mld_sign_hint_x 4 mld_poly_decompose_lo_88 w
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                      (\j. skb(512 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 416 mld_polyt0_unpack
                      (\j. skb(896 + j))))
                  cphat j) /\
        (!j. 256 * i <= j /\ j < 1024
             ==> read (memory :> bytes32 (word_add bot (word(7118 + 4 * j))))
                   s = mld_polyvec_map mld_poly_decompose_lo_88 w j)`;;

let SIGN44_RFSLICE_TAC s =
  MP_TAC(SPECL [`bot:int64`; `7118`; `1024`; `mld_poly_decompose_lo_88`;
                `w:num->int32`; `i:num`; s] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; s]
             `!j. 256 * i <= j /\ j < 1024
                  ==> read (memory :> bytes32
                             (word_add bot (word (7118 + 4 * j))))
                        s = Q j`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 4` THEN ARITH_TAC; STRIP_TAC];;

(*** The setup of row i, and its first part, up to the norm check of      ***)
(*** w0 - c s2                                                            ***)

let SIGN44_ROW_SETUP_TAC =
  FIRST_ASSUM(ASSUME_TAC o SPEC `i:num` o MATCH_MP SIGN_ALIGNED_OFF o
    check (fun th ->
      concl th = `aligned 16 (word_add (bot:int64) (word 7118))`));;

let SIGN44_ROW_HEAD_TAC =
  let s2i = mk_comb(mk_comb(`mld_poly_of`,SIGN44_S2H),`i:num`) in
  let cs2i = list_mk_comb(`mld_poly_pointwise_montgomery`,
                          [s2i; `cphat:num->int32`]) in
  let ics2i = mk_comb(`mld_poly_invntt_tomont`,cs2i) in
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN44_EXEC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `2560`; `512 + 96 * i`;
                `96`; `s4:x86state`] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  SIGN44_RCALL_TAC "H_ETA"
   [`read RDI s`; `read RSI s`; `\j. (skb:num->byte)((512 + 96 * i) + j)`]
   5 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyeta_unpack_2` THEN
  X86_STEPS_TAC SIGN44_EXEC (6--7) THEN
  SIGN44_RCALL_TAC "H_NTT"
   [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                   (\j. (skb:num->byte)(512 + j))) i`] 8 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (9--11) THEN
  SIGN44_RCALL_TAC "H_PW"
   [`read RDI s`; `read RSI s`; s2i; `cphat:num->int32`] 12 THEN
  X86_STEPS_TAC SIGN44_EXEC (13--14) THEN
  SIGN44_RCALL_TAC "H_INV" [`read RDI s`; cs2i] 15 THEN
  SIGN44_RFSLICE_TAC `s15:x86state` THEN
  X86_STEPS_TAC SIGN44_EXEC (16--18) THEN
  SIGN44_RCALL_TAC "H_SUB"
   [`read RDI s`; `read RSI s`;
    `mld_poly_decompose_lo_88 (mld_poly_of w i)`; ics2i] 19 THEN
  X86_STEPS_TAC SIGN44_EXEC (20--21) THEN
  SIGN44_RCALL_TAC "H_RED"
   [`read RDI s`;
    list_mk_comb(`mld_poly_sub`,
     [`mld_poly_decompose_lo_88 (mld_poly_of w i)`; ics2i])] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  X86_STEPS_TAC SIGN44_EXEC (23--25) THEN
  SIGN44_RCALL_TAC "H_CHK"
   [`read RDI s`;
    list_mk_comb(`mld_sign_r0`,
     [`mld_poly_decompose_lo_88`; `w:num->int32`; SIGN44_S2H;
      `cphat:num->int32`; `i:num`]);
    `read RSI s`] 26 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_REDUCE_CONV
    `word_zx (word 95154:int64):int32`]);;

(*** The second part, from the first check passing to the norm check of   ***)
(*** c t0                                                                 ***)

let SIGN44_R0I = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_88`; `w:num->int32`; SIGN44_S2H;
   `cphat:num->int32`; `i:num`]);;

let SIGN44_CT0I = list_mk_comb(`mld_sign_ct0`,
  [SIGN44_T0H; `cphat:num->int32`; `i:num`]);;

let SIGN44_ROW_MID_TAC =
  let t0i = mk_comb(mk_comb(`mld_poly_of`,SIGN44_T0H),`i:num`) in
  let ct0i = list_mk_comb(`mld_poly_pointwise_montgomery`,
                          [t0i; `cphat:num->int32`]) in
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   (mk_eq(list_mk_comb(`mld_poly_chknorm`,[SIGN44_R0I; `word 95154:int32`]),
          `word 0:int32`)); WORD_ZX_0]) THEN
  X86_STEPS_TAC SIGN44_EXEC (27--32) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `2560`; `896 + 416 * i`;
                `416`; `s32:x86state`] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  SIGN44_RCALL_TAC "H_T0"
   [`read RDI s`; `read RSI s`; `\j. (skb:num->byte)((896 + 416 * i) + j)`]
   33 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyt0_unpack` THEN
  X86_STEPS_TAC SIGN44_EXEC (34--35) THEN
  SIGN44_RCALL_TAC "H_NTT"
   [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 416 mld_polyt0_unpack
                   (\j. (skb:num->byte)(896 + j))) i`] 36 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (37--39) THEN
  SIGN44_RCALL_TAC "H_PW"
   [`read RDI s`; `read RSI s`; t0i; `cphat:num->int32`] 40 THEN
  X86_STEPS_TAC SIGN44_EXEC (41--42) THEN
  SIGN44_RCALL_TAC "H_INV" [`read RDI s`; ct0i] 43 THEN
  X86_STEPS_TAC SIGN44_EXEC (44--45) THEN
  SIGN44_RCALL_TAC "H_RED"
   [`read RDI s`; mk_comb(`mld_poly_invntt_tomont`,ct0i)] 46 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  X86_STEPS_TAC SIGN44_EXEC (47--49) THEN
  SIGN44_RCALL_TAC "H_CHK" [`read RDI s`; SIGN44_CT0I; `read RSI s`] 50 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_REDUCE_CONV
    `word_zx (word 95232:int64):int32`]);;

let SIGN44_RTEST = prove
 (`!j. 96 * j + 18446744073709551328 = 18446744073709551616 <=> j + 1 = 4`,
  ARITH_TAC);;

let SIGN44_RBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 4` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SIGN44_ROW_SETUP_TAC THEN SIGN44_ROW_HEAD_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SIGN44_ROW_MID_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   (mk_eq(list_mk_comb(`mld_poly_chknorm`,[SIGN44_CT0I; `word 95232:int32`]),
          `word 0:int32`)); WORD_ZX_0]) THEN
  X86_STEPS_TAC SIGN44_EXEC (51--57) THEN
  SIGN44_RCALL_TAC "H_ADD"
   [`read RDI s`; `read RSI s`; SIGN44_R0I; SIGN44_CT0I] 58 THEN
  X86_STEPS_TAC SIGN44_EXEC (59--61) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN LOOP_TEST_TAC THEN
  REWRITE_TAC[SIGN44_RTEST] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_SIMP_TAC[SIGN_PREFIX_PC] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SIGN44_RSETUP_TAC tmpl vars =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ETA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_T0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_SUB_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CHK" THEN
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC vars THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let SIGN44_RPRE = prove
 (SIGN44_RPRE_STMT,
  SIGN44_RSETUP_TAC
   `\(m:num) (sk:int64) (bot:int64) (pc:num).
     APPEND (f_ev_back m sk bot pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit sk bot pc i))
              (f_ev_front sk bot pc))
     :(uarch_event)list`
   [`e:(uarch_event)list`; `m:num`; `sk:int64`; `skb:num->byte`;
    `bot:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa44_signature_internal_loop2`
     `if m < 4 then pc + mldsa44_signature_internal_loop2
      else pc + mldsa44_signature_internal_loop2_exit1`
     SIGN44_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN X86_STEPS_TAC SIGN44_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      SIGN44_RBODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN X86_STEPS_TAC SIGN44_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0;
                    WORD_ADD_0] THEN
    SIGN_CONCRETE_DISCHARGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exits from the loop over the rows at a row whose first check (w0 - c  *)
(* s2) or second check (c t0) fails, to the cleanup (join3, through join6    *)
(* and join7) with RDX = -1 as a 32-bit integer and RBX restored.            *)
(* ------------------------------------------------------------------------- *)

let SIGN44_RFAIL1_STMT =
 `?f_rfail1.
    !e i sk skb bot w cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 2990)) /\
      aligned 16 (word_add bot (word 7118)) /\ i < 4 /\
      ~(mld_poly_chknorm
         (mld_sign_r0 mld_poly_decompose_lo_88 w
           (mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 96 mld_polyeta_unpack_2
               (\j. skb(512 + j))))
           cphat i)
         (word 95154) = word 0) /\
      nonoverlapping (sk,2560) (bot,11278) /\
      nonoverlapping (word pc,libmldsa_size) (bot,11278)
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s = word(pc + mldsa44_signature_internal_loop2) /\
                read RSP s = word_add bot (word 1678) /\
                read RBP s = word_add bot (word 11262) /\
                read RBX s = word(416 * i) /\
                read R12 s = word_add bot (word 2990) /\
                read R13 s = word_add bot (word(7118 + 1024 * i)) /\
                read R14 s = word(96 * i) /\
                read R15 s = word_add bot (word 4014) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1870))) s =
                word_add sk (word 512) /\
                read (memory :> bytes64 (word_add bot (word 1750))) s =
                word_add bot (word 5038) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(4014 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 2560
                     ==> read (memory :> bytes8 (word_add sk (word j))) s =
                         skb j) /\
                (!j. 256 * i <= j /\ j < 1024
                     ==> read (memory :> bytes32
                                (word_add bot (word(7118 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_88 w j) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa44_signature_internal_join3) /\
                read RSP s = word_add bot (word 1678) /\
                read RBX s = word_add bot (word 5038) /\
                read RDX s = word 4294967295 /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_rfail1 i sk bot pc /\
                   memaccess_inbounds e2
                    [sk,2560; bot,11278; word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [bot,11278]))
           (MAYCHANGE [RSP; RBX; R13; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,1678);
              memory :> bytes(word_add bot (word 2990),1024);
              memory :> bytes(word_add bot (word 7118),4096)])`;;

let SIGN44_RFAIL1 = prove
 (SIGN44_RFAIL1_STMT,
  SIGN44_RSETUP_TAC
   `\(i:num) (sk:int64) (bot:int64) (pc:num).
     f_ev_rfail1 i sk bot pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `sk:int64`; `skb:num->byte`;
    `bot:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN44_ROW_SETUP_TAC THEN SIGN44_ROW_HEAD_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (27--27) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   (mk_neg(mk_eq(list_mk_comb(`mld_poly_chknorm`,
                              [SIGN44_R0I; `word 95154:int32`]),
                 `word 0:int32`)))]) THEN
  X86_STEPS_TAC SIGN44_EXEC (28--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SIGN44_RFAIL2_STMT =
 `?f_rfail2.
    !e i sk skb bot w cphat pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 2990)) /\
      aligned 16 (word_add bot (word 7118)) /\ i < 4 /\
      mld_poly_chknorm
       (mld_sign_r0 mld_poly_decompose_lo_88 w
         (mld_polyvec_map mld_poly_ntt
           (mld_polyvec_unpack 96 mld_polyeta_unpack_2
             (\j. skb(512 + j))))
         cphat i)
       (word 95154) = word 0 /\
      ~(mld_poly_chknorm
         (mld_sign_ct0
           (mld_polyvec_map mld_poly_ntt
             (mld_polyvec_unpack 416 mld_polyt0_unpack
               (\j. skb(896 + j))))
           cphat i)
         (word 95232) =
        word 0) /\
      nonoverlapping (sk,2560) (bot,11278) /\
      nonoverlapping (word pc,libmldsa_size) (bot,11278)
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s = word(pc + mldsa44_signature_internal_loop2) /\
                read RSP s = word_add bot (word 1678) /\
                read RBP s = word_add bot (word 11262) /\
                read RBX s = word(416 * i) /\
                read R12 s = word_add bot (word 2990) /\
                read R13 s = word_add bot (word(7118 + 1024 * i)) /\
                read R14 s = word(96 * i) /\
                read R15 s = word_add bot (word 4014) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1870))) s =
                word_add sk (word 512) /\
                read (memory :> bytes64 (word_add bot (word 1838))) s =
                word_add sk (word 896) /\
                read (memory :> bytes64 (word_add bot (word 1750))) s =
                word_add bot (word 5038) /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(4014 + 4 * j)))) s =
                         cphat j) /\
                (!j. j < 2560
                     ==> read (memory :> bytes8 (word_add sk (word j))) s =
                         skb j) /\
                (!j. 256 * i <= j /\ j < 1024
                     ==> read (memory :> bytes32
                                (word_add bot (word(7118 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_88 w j) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa44_signature_internal_join3) /\
                read RSP s = word_add bot (word 1678) /\
                read RBX s = word_add bot (word 5038) /\
                read RDX s = word 4294967295 /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_rfail2 i sk bot pc /\
                   memaccess_inbounds e2
                    [sk,2560; bot,11278; word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [bot,11278]))
           (MAYCHANGE [RSP; RBX; R13; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,1678);
              memory :> bytes(word_add bot (word 2990),1024);
              memory :> bytes(word_add bot (word 7118),4096)])`;;

let SIGN44_RFAIL2 = prove
 (SIGN44_RFAIL2_STMT,
  SIGN44_RSETUP_TAC
   `\(i:num) (sk:int64) (bot:int64) (pc:num).
     f_ev_rfail2 i sk bot pc:(uarch_event)list`
   [`e:(uarch_event)list`; `i:num`; `sk:int64`; `skb:num->byte`;
    `bot:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  SIGN44_ROW_SETUP_TAC THEN SIGN44_ROW_HEAD_TAC THEN SIGN44_ROW_MID_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (51--51) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; ASSUME
   (mk_neg(mk_eq(list_mk_comb(`mld_poly_chknorm`,
                              [SIGN44_CT0I; `word 95232:int32`]),
                 `word 0:int32`)))]) THEN
  X86_STEPS_TAC SIGN44_EXEC (52--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints, whose result is the value of RDX for  *)
(* the decision, with RBX restored.                                          *)
(* ------------------------------------------------------------------------- *)

let SIGN44_TAIL_STMT =
 `?f_tail.
    !e sig bot ct (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      nonoverlapping (sig,2420) (bot,11278) /\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,2420); (bot,11278)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s =
                word(pc + mldsa44_signature_internal_loop2_exit1) /\
                read RSP s = word_add bot (word 1678) /\
                read RBP s = word_add bot (word 11262) /\
                read R12 s = word_add bot (word 2990) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1782))) s = sig /\
                read (memory :> bytes64 (word_add bot (word 1766))) s =
                word_add bot (word 1934) /\
                read (memory :> bytes64 (word_add bot (word 1750))) s =
                word_add bot (word 5038) /\
                read (memory :> bytes64 (word_add bot (word 1774))) s =
                word_add bot (word 2222) /\
                read (memory :> bytes64 (word_add bot (word 1798))) s =
                word_add bot (word 7118) /\
                (!j. j < 32
                     ==> read (memory :> bytes8
                                (word_add bot (word(1934 + j)))) s = ct j) /\
                (!j. j < 1024
                     ==> read (memory :> bytes32
                                (word_add bot (word(7118 + 4 * j)))) s =
                         x j) /\
                (!j. j < 768
                     ==> read (memory :> bytes8
                                (word_add bot (word(2222 + j)))) s = b j) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa44_signature_internal_join3) /\
                read RSP s = word_add bot (word 1678) /\
                read RBX s = word_add bot (word 5038) /\
                read RDX s =
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
                   e2 = f_tail sig bot pc x b /\
                   memaccess_inbounds e2 [sig,2420; bot,11278]
                    [sig,2420; bot,11278]))
           (MAYCHANGE [RSP; RBX; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(sig,32);
              memory :> bytes(word_add sig (word 2336),84);
              memory :> bytes(bot,1678);
              memory :> bytes(word_add bot (word 2990),1024)])`;;

let SIGN44_TAIL = prove
 (SIGN44_TAIL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_PACK_SIG_H_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PH" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (bot:int64) (pc:num) (x:num->int32) (b:num->byte).
     f_ev_tail sig bot pc x b:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `bot:int64`;
    `ct:num->byte`; `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; C_RETURN; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN44_EXEC (1--5) THEN
  FULL_CALL_TAC SIGN44_MC SIGN44_EXEC "H_PC"
   [`read RDI s`; `read RSI s`; `ct:num->byte`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   [`pc:num`; `sig:int64`; `bot:int64`; `x:num->int32`; `b:num->byte`] 6
  THEN
  X86_STEPS_TAC SIGN44_EXEC (7--11) THEN
  FULL_CALL_TAC SIGN44_MC SIGN44_EXEC "H_PH"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `x:num->int32`;
    `b:num->byte`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   [`pc:num`; `sig:int64`; `bot:int64`; `x:num->int32`; `b:num->byte`] 12
  THEN
  X86_STEPS_TAC SIGN44_EXEC (13--13) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt and the test of RDX: to join5 on success, else  *)
(* to the test of RDX against -1 at +0x483, which has no label, before the   *)
(* update of kappa. The code zeroes the buffers of the attempt with REP      *)
(* STOSQ, and the structure of y and c~ with aligned SSE stores.             *)
(* ------------------------------------------------------------------------- *)

let SIGN44_CMP_OFF =
  mk_small_numeral(layout "mldsa44_signature_internal" + 0x483);;

let SIGN44_CLEAN_STMT = subst [SIGN44_CMP_OFF,`cmpoff:num`]
 `?f_clean.
    !e ok bot pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 1902)) /\
      aligned 16 (word_add bot (word 1934)) /\
      nonoverlapping (word pc,libmldsa_size) (bot,11278)
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s = word(pc + mldsa44_signature_internal_join3) /\
                read RBP s = word_add bot (word 11262) /\
                read RBX s = word_add bot (word 5038) /\
                read R12 s = word_add bot (word 2990) /\
                read R15 s = word_add bot (word 4014) /\
                read RDX s = (if ok then word 0 else word 4294967295) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1798))) s =
                word_add bot (word 7118) /\
                read (memory :> bytes64 (word_add bot (word 1774))) s =
                word_add bot (word 2222) /\
                read (memory :> bytes64 (word_add bot (word 1758))) s =
                word_add bot (word 1902) /\
                read (memory :> bytes64 (word_add bot (word 1766))) s =
                word_add bot (word 1934) /\
                read events s = e)
           (\s. read RIP s =
                (if ok then word(pc + mldsa44_signature_internal_join5)
                 else word(pc + cmpoff)) /\
                read RDX s = (if ok then word 0 else word 4294967295) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_clean ok bot pc /\
                   memaccess_inbounds e2 [bot,11278] [bot,11278]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(word_add bot (word 1902),16);
              memory :> bytes(word_add bot (word 1934),32);
              memory :> bytes(word_add bot (word 2222),768);
              memory :> bytes(word_add bot (word 2990),1024);
              memory :> bytes(word_add bot (word 4014),1024);
              memory :> bytes(word_add bot (word 5038),1024);
              memory :> bytes(word_add bot (word 7118),4096)])`;;

let SIGN44_CLEAN = prove
 (SIGN44_CLEAN_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (bot:int64) (pc:num).
     if ok then f_ev_clean_ok bot pc else f_ev_clean_bad bot pc
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `ok:bool`; `bot:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`bot:int64`; `1934`; `16`] SIGN_ALIGNED_ADD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN
  BOOL_CASES_TAC `ok:bool` THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN44_EXEC (1--26) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt: the structure of y (the address of rho'' and     *)
(* kappa), w from the lazy product with the matrix (whose entries the callee *)
(* samples from rho in the structure of the matrix), made nonnegative, which *)
(* MLD_LAZY_SIGN_W of lazy_eq_spec.ml turns into w = A y of the model (the   *)
(* coefficients of y being below q by MLD_LAZY_SIGN_Y_BOUND), w1 and its     *)
(* packing, c~ with the inlined SHAKE256 calls (and the zeroing of the       *)
(* context with REP STOSQ), the challenge and its NTT.                       *)
(* ------------------------------------------------------------------------- *)

let SIGN44_HEAD_STMT =
 `?f_head.
    !e bot rho mu rhop n C pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 6062)) /\
      aligned 16 (word_add bot (word 7118)) /\
      n < 16382 /\ mld_matrix_terminates 4 4 rho /\
      num_of_bytelist(list_of_seq
       (mld_sign_ctilde 4 192 mu
         (mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
           (mld_sign_w 4 (mld_polyvec_matrix_expand 4 rho)
             (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)))))
       32) = C /\
      mld_poly_challenge_terminates 39 32 C /\
      nonoverlapping (word pc,libmldsa_size) (bot,11278)
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s = word(pc + mldsa44_signature_internal_join2) /\
                read RSP s = word_add bot (word 1678) /\
                read RBP s = word_add bot (word 11262) /\
                read RBX s = word_add bot (word 5038) /\
                read R12 s = word_add bot (word 2990) /\
                read R15 s = word_add bot (word 4014) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1726))) s =
                word_add bot (word 2158) /\
                read (memory :> bytes64 (word_add bot (word 1734))) s =
                word_add bot (word 2094) /\
                read (memory :> bytes64 (word_add bot (word 1742))) s =
                word_add bot (word 6062) /\
                read (memory :> bytes64 (word_add bot (word 1758))) s =
                word_add bot (word 1902) /\
                read (memory :> bytes64 (word_add bot (word 1766))) s =
                word_add bot (word 1934) /\
                read (memory :> bytes64 (word_add bot (word 1774))) s =
                word_add bot (word 2222) /\
                read (memory :> bytes16 (word_add bot (word 1790))) s =
                word(4 * n) /\
                read (memory :> bytes64 (word_add bot (word 1798))) s =
                word_add bot (word 7118) /\
                read (memory :> bytes(word_add bot (word 7086),32)) s = rho /\
                read (memory :> bytes(word_add bot (word 2094),64)) s = mu /\
                read (memory :> bytes(word_add bot (word 2158),64)) s =
                rhop /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa44_signature_internal_loop1) /\
                read RSP s = word_add bot (word 1678) /\
                read R14 s = word 0 /\
                read (memory :> bytes64 (word_add bot (word 1902))) s =
                word_add bot (word 2158) /\
                read (memory :> bytes16 (word_add bot (word 1910))) s =
                word(4 * n) /\
                (!j. j < 1024
                     ==> read (memory :> bytes32
                                (word_add bot (word(7118 + 4 * j)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_88
                          (mld_sign_w 4 (mld_polyvec_matrix_expand 4 rho)
                            (mld_sign_y mld_poly_uniform_gamma1_17 rhop
                              (4 * n))) j) /\
                (!j. j < 768
                     ==> read (memory :> bytes8
                                (word_add bot (word(2222 + j)))) s =
                         mld_sign_w1
                          (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
                          192
                          (mld_sign_w 4 (mld_polyvec_matrix_expand 4 rho)
                            (mld_sign_y mld_poly_uniform_gamma1_17 rhop
                              (4 * n))) j) /\
                read (memory :> bytes(word_add bot (word 1934),32)) s = C /\
                (!j. j < 256
                     ==> read (memory :> bytes32
                                (word_add bot (word(4014 + 4 * j)))) s =
                         mld_poly_ntt (mld_poly_challenge 39 32 C) j) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_head bot pc rho C /\
                   memaccess_inbounds e2
                    [bot,11278;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [bot,11278]))
           (MAYCHANGE [RSP; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(bot,1678);
              memory :> bytes(word_add bot (word 1902),16);
              memory :> bytes(word_add bot (word 1934),32);
              memory :> bytes(word_add bot (word 2222),768);
              memory :> bytes(word_add bot (word 2990),1024);
              memory :> bytes(word_add bot (word 4014),1024);
              memory :> bytes(word_add bot (word 5038),208);
              memory :> bytes(word_add bot (word 6062),1024);
              memory :> bytes(word_add bot (word 7118),4096)])`;;

let SIGN44_W =
 `mld_sign_w 4 (mld_polyvec_matrix_expand 4 rho)
   (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n))`;;

let SIGN44_W1 = mk_comb(
  `mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192`,
  SIGN44_W);;

let SIGN44_W1NUM = mk_comb(`num_of_bytelist`,
  list_mk_comb(`list_of_seq:(num->byte)->num->(byte)list`,
               [SIGN44_W1; `768`]));;

let SIGN44_ABSORBED =
  list_mk_comb(`mld_keccak_absorb`,
    [`136`; `word 0:1600 word`; `0`; `832`;
     mk_binop `(+):num->num->num` `mu:num`
      (mk_binop `( * ):num->num->num` `2 EXP 512` SIGN44_W1NUM)]);;

let SIGN44_S2 = mk_comb(`FST:(1600 word#num)->1600 word`,SIGN44_ABSORBED);;

let SIGN44_S3 =
  list_mk_comb(`mld_keccak_finalize`,[`136`; `31`; SIGN44_S2; `16`]);;

let SIGN44_HCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN44_MC SIGN44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   [`pc:num`; `bot:int64`; `rho:num`; `C:num`] n;;

(*** w from the lazy product, made nonnegative, as w = A y of the model ***)

let SIGN44_LAZY_W_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
   `!i. i < 1024
        ==> read (memory :> bytes32 (word_add B (word (d + 4 * i)))) s =
            mld_polyvec_map mld_poly_caddq x i`) (concl th))) THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
   (SPECL [`4`; `4`; `rho:num`;
           `mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)`]
          MLD_LAZY_SIGN_W)) THEN
  REWRITE_TAC[MLD_LAZY_SIGN_Y_BOUND;
              ASSUME `mld_matrix_terminates 4 4 rho`] THEN
  DISCH_THEN(fun th -> SIMP_TAC[th]) THEN DISCH_TAC;;

let SIGN44_HEAD = prove
 (SIGN44_HEAD_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_YVEC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
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
    MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_CHAL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT"
  THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(bot:int64) (pc:num) (rho:num) (C:num).
     f_ev_head bot pc rho C:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `bot:int64`; `rho:num`;
    `mu:num`; `rhop:num`; `n:num`; `C:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN44_EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_WORD16_OF_ZX]) THEN
  SIGN44_HCALL_TAC "H_YVEC"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
    `word_add bot (word 2158):int64`; `rho:num`; `rhop:num`; `4 * n`] 11
  THEN
  X86_STEPS_TAC SIGN44_EXEC (12--13) THEN
  SIGN44_HCALL_TAC "H_CADDQ"
   [`read RDI s`;
    `mld_polyvec_matrix_yvec_lazy 4 rho
      (mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n))`] 14 THEN
  SIGN44_LAZY_W_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (15--19) THEN
  SIGN44_HCALL_TAC "H_DEC"
   [`read RDI s`; `read RSI s`; SIGN44_W; `read RDX s`] 20 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_w1]) THEN
  X86_STEPS_TAC SIGN44_EXEC (21--22) THEN
  SIGN44_HCALL_TAC "H_INIT" [`read RDI s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC SIGN44_EXEC (24--27) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 5038):int64` THEN
  SIGN44_HCALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `64`; `word 0:1600 word`; `0`; `mu:num`] 28
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 768 ==> read (memory :> bytes8
         (word_add bot (word (2222 + j)))) s = f j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  MLD_H_BOUND_TAC `word_add bot (word 2094):int64` THEN
  X86_STEPS_TAC SIGN44_EXEC (29--32) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 5038):int64` THEN
  SIGN44_HCALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `768`;
    `FST(mld_keccak_absorb 136 (word 0) 0 64 mu)`; `64`; SIGN44_W1NUM] 33
  THEN
  MP_TAC(SPECL [`64`; `768`; `mu:num`; SIGN44_W1NUM]
               MLD_SHAKE256_ABSORB_APPEND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV SIGN_NUMERAL_CONV) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(CONV_RULE SIGN_NUMERAL_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC SIGN44_EXEC (34--35) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 5038):int64` THEN
  SIGN44_HCALL_TAC "H_FINALIZE" [`read RDI s`; SIGN44_S2; `16`] 36 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC SIGN44_EXEC (37--41) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 5038):int64` THEN
  SIGN44_HCALL_TAC "H_SQUEEZE"
   [`read RDI s`; `32`; `read RDX s`; SIGN44_S3; `136`] 42 THEN
  X86_STEPS_TAC SIGN44_EXEC (43--44) THEN
  SIGN44_HCALL_TAC "H_RELEASE" [`read RDI s`] 45 THEN
  X86_STEPS_TAC SIGN44_EXEC (46--52) THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add bot (word 1934),32)) s52 = C`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde; mld_shake256_byte; mld_shake256_state;
                MLD_KECCAK_ABSORB_SND] THEN
    CONV_TAC SIGN_NUMERAL_CONV THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
   `read (memory :> bytes (word_add bot (word 1934),32)) s52 =
    num_of_bytelist l`) (concl th))) THEN
  X86_STEPS_TAC SIGN44_EXEC (53--53) THEN
  SIGN44_HCALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; `C:num`] 54 THEN
  X86_STEPS_TAC SIGN44_EXEC (55--56) THEN
  SIGN44_HCALL_TAC "H_NTT" [`read RDI s`; `mld_poly_challenge 39 32 C`] 57
  THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt, from join2 to join5 or the test at +0x483, with the      *)
(* events a function of rho and the declassified record (C,r,x,b).           *)
(* ------------------------------------------------------------------------- *)

let SIGN44_ATT_STMT = subst [SIGN44_CMP_OFF,`cmpoff:num`]
 `?f_att.
    !e sig sk skb bot rho mu rhop n C r x b pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 (word_add bot (word 1678)) /\
      aligned 16 (word_add bot (word 1902)) /\
      aligned 16 (word_add bot (word 1934)) /\
      aligned 16 (word_add bot (word 2990)) /\
      aligned 16 (word_add bot (word 5038)) /\
      aligned 16 (word_add bot (word 6062)) /\
      aligned 16 (word_add bot (word 7118)) /\ n < 16382 /\
      mld_matrix_terminates 4 4 rho /\
      mld_sign_attempt_declass 4 4 32 39 mld_poly_uniform_gamma1_17
       130994 95154 95232 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
       192 mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80
       (mld_polyvec_matrix_expand 4 rho)
       (mld_polyvec_map mld_poly_ntt
         (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. skb(128 + j))))
       (mld_polyvec_map mld_poly_ntt
         (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. skb(512 + j))))
       (mld_polyvec_map mld_poly_ntt
         (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. skb(896 + j))))
       mu rhop (4 * n) = (C,r,x,b) /\
      mld_poly_challenge_terminates 39 32 C /\
      nonoverlapping (sig,2420) (bot,11278) /\
      ALL (nonoverlapping (sk,2560)) [(sig,2420); (bot,11278)] /\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,2420); (bot,11278)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                read RIP s = word(pc + mldsa44_signature_internal_join2) /\
                read RSP s = word_add bot (word 1678) /\
                read RBP s = word_add bot (word 11262) /\
                read RBX s = word_add bot (word 5038) /\
                read R12 s = word_add bot (word 2990) /\
                read R15 s = word_add bot (word 4014) /\
                (read DF s <=> false) /\
                read (memory :> bytes64 (word_add bot (word 1726))) s =
                word_add bot (word 2158) /\
                read (memory :> bytes64 (word_add bot (word 1734))) s =
                word_add bot (word 2094) /\
                read (memory :> bytes64 (word_add bot (word 1742))) s =
                word_add bot (word 6062) /\
                read (memory :> bytes64 (word_add bot (word 1758))) s =
                word_add bot (word 1902) /\
                read (memory :> bytes64 (word_add bot (word 1766))) s =
                word_add bot (word 1934) /\
                read (memory :> bytes64 (word_add bot (word 1774))) s =
                word_add bot (word 2222) /\
                read (memory :> bytes64 (word_add bot (word 1782))) s = sig /\
                read (memory :> bytes16 (word_add bot (word 1790))) s =
                word(4 * n) /\
                read (memory :> bytes64 (word_add bot (word 1798))) s =
                word_add bot (word 7118) /\
                read (memory :> bytes64 (word_add bot (word 1806))) s =
                word_add sk (word 128) /\
                read (memory :> bytes64 (word_add bot (word 1838))) s =
                word_add sk (word 896) /\
                read (memory :> bytes64 (word_add bot (word 1870))) s =
                word_add sk (word 512) /\
                read (memory :> bytes(word_add bot (word 7086),32)) s = rho /\
                read (memory :> bytes(word_add bot (word 2094),64)) s = mu /\
                read (memory :> bytes(word_add bot (word 2158),64)) s =
                rhop /\
                (!j. j < 2560
                     ==> read (memory :> bytes8 (word_add sk (word j))) s =
                         skb j) /\
                read events s = e)
           (\s. read RIP s =
                (if r = 13 then word(pc + mldsa44_signature_internal_join5)
                 else word(pc + cmpoff)) /\
                read RSP s = word_add bot (word 1678) /\
                read RBX s = word_add bot (word 5038) /\
                read RDX s = (if r = 13 then word 0 else word 4294967295) /\
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
                              (mld_polyvec_matrix_expand 4 rho)
                              (mld_polyvec_map mld_poly_ntt
                                (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                                  (\j. skb(128 + j))))
                              (mld_polyvec_map mld_poly_ntt
                                (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                                  (\j. skb(512 + j))))
                              (mld_polyvec_map mld_poly_ntt
                                (mld_polyvec_unpack 416 mld_polyt0_unpack
                                  (\j. skb(896 + j))))
                              mu rhop (4 * n) t) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_att sig sk bot pc rho C r x b /\
                   memaccess_inbounds e2
                    [sig,2420; sk,2560; bot,11278;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa_poly_reduce_consts),16]
                    [sig,2420; bot,11278]))
           (MAYCHANGE [RSP; RBX; R13; R14] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(sig,2420);
              memory :> bytes(bot,1678);
              memory :> bytes(word_add bot (word 1750),8);
              memory :> bytes(word_add bot (word 1902),16);
              memory :> bytes(word_add bot (word 1934),32);
              memory :> bytes(word_add bot (word 2222),768);
              memory :> bytes(word_add bot (word 2990),1024);
              memory :> bytes(word_add bot (word 4014),1024);
              memory :> bytes(word_add bot (word 5038),1024);
              memory :> bytes(word_add bot (word 6062),1024);
              memory :> bytes(word_add bot (word 7118),4096)])`;;

let SIGN44_AALLOWED =
  [`sig:int64`; `sk:int64`; `bot:int64`; `pc:num`; `rho:num`; `C:num`;
   `r:num`; `x:num->int32`; `b:num->byte`];;

let SIGN44_ACALL_TAC name ilist n =
  FULL_CALL_TAC SIGN44_MC SIGN44_EXEC name ilist SIGN44_AALLOWED n;;

let SIGN44_CPH = `mld_poly_ntt (mld_poly_challenge 39 32 C)`;;
let SIGN44_A = `mld_polyvec_matrix_expand 4 rho`;;
let SIGN44_Y = `mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)`;;
let SIGN44_R0 =
  list_mk_comb(`mld_sign_r0`,
    [`mld_poly_decompose_lo_88`; SIGN44_W; SIGN44_S2H; SIGN44_CPH]);;
let SIGN44_CT0 =
  list_mk_comb(`mld_sign_ct0`,[SIGN44_T0H; SIGN44_CPH]);;
let SIGN44_CT = mk_comb(`mld_sign_ctilde 4 192 mu`,SIGN44_W1);;

let SIGN44_SIGATT = list_mk_comb(
 `mld_sign_attempt_sig 4 4 32 39 mld_poly_uniform_gamma1_17 mld_polyz_pack_17
   576 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
   mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80`,
  [SIGN44_A; SIGN44_S1H; SIGN44_S2H; SIGN44_T0H; `mu:num`; `rhop:num`;
   `4 * n`]);;

let SIGN44_ATT_MID = subst [SIGN44_SIGATT,`SIGATT:num->byte`]
 `\s. read RSP s = word_add bot (word 1678) /\
      read RBP s = word_add bot (word 11262) /\
      read RBX s = word_add bot (word 5038) /\
      read R12 s = word_add bot (word 2990) /\
      read R15 s = word_add bot (word 4014) /\
      read RDX s = (if r = 13 then word 0 else word 4294967295) /\
      (read DF s <=> false) /\
      read (memory :> bytes64 (word_add bot (word 1758))) s =
      word_add bot (word 1902) /\
      read (memory :> bytes64 (word_add bot (word 1766))) s =
      word_add bot (word 1934) /\
      read (memory :> bytes64 (word_add bot (word 1774))) s =
      word_add bot (word 2222) /\
      read (memory :> bytes64 (word_add bot (word 1798))) s =
      word_add bot (word 7118) /\
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
   [`r:num`; `sig:int64`; `sk:int64`; `skb:num->byte`; `bot:int64`;
    `rhop:num`; `4 * n`; SIGN44_CPH; `pc:num`] 2 THEN
  SIGN_PC_SIMP_TAC THEN
  SIGN44_ACALL_TAC "H_ZFAIL"
   [`r:num`; `sig:int64`; `sk:int64`; `skb:num->byte`; `bot:int64`;
    `rhop:num`; `4 * n`; SIGN44_CPH; `pc:num`] 3 THEN
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
   [`(r - 4) DIV 2`; `sk:int64`; `skb:num->byte`; `bot:int64`; SIGN44_W;
    SIGN44_CPH; `pc:num`] 3 THEN
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
     [`(r - 4) DIV 2`; `sk:int64`; `skb:num->byte`; `bot:int64`; SIGN44_W;
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
     [`(r - 4) DIV 2`; `sk:int64`; `skb:num->byte`; `bot:int64`; SIGN44_W;
      SIGN44_CPH; `pc:num`] 4] THEN
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
   [`4`; `sk:int64`; `skb:num->byte`; `bot:int64`; SIGN44_W;
    SIGN44_CPH; `pc:num`] 3 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read RIP s = x`) (concl th))) THEN
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
        ==> read (memory :> bytes8 (word_add bot (word (2222 + j)))) s3 =
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
      `read (memory :> bytes (word_add bot (word 1934),32)) s = C`) (concl th)
    then FIRST_ASSUM(fun cth ->
           if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
           then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES_OFF
                            (TRANS th (SYM cth)))
           else NO_TAC)
    else NO_TAC) THEN
  SIGN44_ACALL_TAC "H_TAIL"
   [`sig:int64`; `bot:int64`; SIGN44_CT; `x:num->int32`;
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
     [`4`; `sig:int64`; `sk:int64`; `skb:num->byte`; `bot:int64`;
      `rhop:num`; `4 * n`; SIGN44_CPH; `pc:num`] 2 THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_CASES_TAC `r < 12` THENL [SIGN44_WCASE_TAC; SIGN44_TCASE_TAC]];;

let SIGN44_ACLEAN_TAC =
  FULL_INIT_TAC THEN
  SIGN44_ACALL_TAC "H_CLEAN" [`r = 13`; `bot:int64`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let SIGN44_ATT = prove
 (SIGN44_ATT_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_HEAD "H_HEAD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_ZPRE "H_ZPRE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_ZFAIL "H_ZFAIL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_RPRE "H_RPRE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_RFAIL1 "H_RFAIL1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_RFAIL2 "H_RFAIL2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_CLEAN "H_CLEAN" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_TAIL "H_TAIL" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (sk:int64) (bot:int64) (pc:num) (rho:num) (C:num) (r:num)
     (x:num->int32) (b:num->byte).
     APPEND (f_ev_cl sig sk bot pc rho C r x b)
      (APPEND
        (if r < 4 then f_ev_pz sig sk bot pc rho C r x b
         else if r < 12
         then if EVEN (r - 4) then f_ev_pw1 sig sk bot pc rho C r x b
              else f_ev_pw2 sig sk bot pc rho C r x b
         else f_ev_pt sig sk bot pc rho C r x b)
        (f_ev_hd sig sk bot pc rho C r x b))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `sk:int64`; `skb:num->byte`;
    `bot:int64`; `rho:num`; `mu:num`; `rhop:num`; `n:num`; `C:num`;
    `r:num`; `x:num->int32`; `b:num->byte`; `pc:num`] THEN
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
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa44_signature_internal_join3`
    SIGN44_ATT_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    SIGN44_ACALL_TAC "H_HEAD"
     [`bot:int64`; `rho:num`; `mu:num`; `rhop:num`; `n:num`;
      `C:num`; `pc:num`] 1 THEN
    SIGN44_PATHS_TAC;
    SIGN44_ACLEAN_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The facts about the attempts that the main proof needs, for D =           *)
(* mld_sign_declass_44 and its number of attempts.                           *)
(* ------------------------------------------------------------------------- *)

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
(* then those of the epilogue. The buffers are at fixed offsets from bot,    *)
(* the bottom of the aligned frame (see utils/mldsa_native_realign.ml),      *)
(* which REALIGN_UNBOT_TAC expands before the events are matched with the    *)
(* template.                                                                 *)
(* ------------------------------------------------------------------------- *)

let SIGN44_TEMPLATE =
 `\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (rnd:int64)
   (sk:int64) (ext:int64) (rh:num)
   (D:num->num#num#(num->int32)#(num->byte)) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND
    (f_ev_epil sig m mlen pre prelen rnd sk ext rh D pc stackpointer
               returnaddress)
    (APPEND
      (ENUMERATEL (mld_sign_natt 16382 13 D)
        (\i. if i + 1 < mld_sign_natt 16382 13 D
             then f_ev_cont sig m mlen pre prelen rnd sk ext rh D pc
                    stackpointer returnaddress i
             else if FST(SND(D i)) = 13
             then f_ev_succ sig m mlen pre prelen rnd sk ext rh D pc
                    stackpointer returnaddress i
             else f_ev_exh sig m mlen pre prelen rnd sk ext rh D pc
                    stackpointer returnaddress i))
      (if word_zx ext = (word 0:int32)
       then f_ev_prolh sig m mlen pre prelen rnd sk ext rh D pc
              stackpointer returnaddress
       else f_ev_prolx sig m mlen pre prelen rnd sk ext rh D pc
              stackpointer returnaddress))
   :(uarch_event)list`;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop over the attempts: the saved registers (and the *)
(* stack pointer saved in R10 by the prologue), the return address, the      *)
(* pointers in the frame (to the buffers and, set by unpack_sk, into the     *)
(* secret key for s1, s2 and t0), rho in the structure of the matrix, the    *)
(* secret key, mu and rho'' do not change; before attempt i the registers of *)
(* the loop hold the addresses of its buffers and kappa = 4 * i (the 16-bit  *)
(* word at bot + 1790); after the last attempt RDX holds the result and sig  *)
(* the signature.                                                            *)
(* ------------------------------------------------------------------------- *)

let SIGN44_INV =
 `\i s.
   read RSP s = word_add bot (word 1678) /\
   read RBP s = word_add bot (word 11262) /\
   read (memory :> bytes64 (word_add bot (word 11214))) s = rbx_init /\
   read (memory :> bytes64 (word_add bot (word 11222))) s =
   word_add stackpointer (word 11317) /\
   read (memory :> bytes64 (word_add bot (word 11230))) s = r12_init /\
   read (memory :> bytes64 (word_add bot (word 11238))) s = r13_init /\
   read (memory :> bytes64 (word_add bot (word 11246))) s = r14_init /\
   read (memory :> bytes64 (word_add bot (word 11254))) s = r15_init /\
   read (memory :> bytes64 (word_add bot (word 11262))) s = rbp_init /\
   read (memory :> bytes64 (word_add stackpointer (word 11309))) s =
   returnaddress /\
   (read DF s <=> false) /\
   read (memory :> bytes64 (word_add bot (word 1718))) s =
   word_add bot (word 1966) /\
   read (memory :> bytes64 (word_add bot (word 1726))) s =
   word_add bot (word 2158) /\
   read (memory :> bytes64 (word_add bot (word 1734))) s =
   word_add bot (word 2094) /\
   read (memory :> bytes64 (word_add bot (word 1742))) s =
   word_add bot (word 6062) /\
   read (memory :> bytes64 (word_add bot (word 1758))) s =
   word_add bot (word 1902) /\
   read (memory :> bytes64 (word_add bot (word 1766))) s =
   word_add bot (word 1934) /\
   read (memory :> bytes64 (word_add bot (word 1774))) s =
   word_add bot (word 2222) /\
   read (memory :> bytes64 (word_add bot (word 1782))) s = sig /\
   read (memory :> bytes64 (word_add bot (word 1798))) s =
   word_add bot (word 7118) /\
   read (memory :> bytes64 (word_add bot (word 1806))) s =
   word_add sk (word 128) /\
   read (memory :> bytes64 (word_add bot (word 1838))) s =
   word_add sk (word 896) /\
   read (memory :> bytes64 (word_add bot (word 1870))) s =
   word_add sk (word 512) /\
   read (memory :> bytes(word_add bot (word 7086),32)) s = rh /\
   (!j. j < 2560
        ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\
   read (memory :> bytes(word_add bot (word 2094),64)) s = MU /\
   read (memory :> bytes(word_add bot (word 2158),64)) s =
   mld_sign_rhoprime (\j. skb(32 + j)) RND MU /\
   (i < mld_sign_natt 16382 13 D
    ==> read RBX s = word_add bot (word 5038) /\
        read R12 s = word_add bot (word 2990) /\
        read R15 s = word_add bot (word 4014) /\
        read (memory :> bytes16 (word_add bot (word 1790))) s =
        word(4 * i)) /\
   (i = mld_sign_natt 16382 13 D
    ==> read RDX s =
        (if mld_sign_ok_44 skb MU RND then word 0 else word 4294967292) /\
        (!t. t < 2420
             ==> read (memory :> bytes8 (word_add sig (word t))) s =
                 mld_sign_sig_44 skb MU RND t))`;;

let SIGN44_MALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `rnd:int64`; `sk:int64`; `ext:int64`; `rh:num`;
   `D:num->num#num#(num->int32)#(num->byte)`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let SIGN44_MCALL_TAC name ilist n =
  FULL_CALL_TAC SIGN44_MC SIGN44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   SIGN44_MALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The start: the callees as assumptions, the template, the frame (with the  *)
(* stack pointer at its bottom, the aligned part (bot,11278) of              *)
(* utils/mldsa_native_realign.ml, since the code aligns the stack pointer    *)
(* first, and the alignment of its buffers), the abbreviations rh and D (the *)
(* arguments of the events), mu, the preserved registers and the facts about *)
(* the attempts.                                                             *)
(* ------------------------------------------------------------------------- *)

let SIGN44_START_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC SIGN44_ATT "H_ATT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_MEXP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_H_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_H" THEN
  CONCRETIZE_F_EVENTS_TAC SIGN44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `rh = mld_sk_rho skb` THEN
  ABBREV_TAC `D = mld_sign_declass_44 skb MU RND` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SIGN44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `MU = (if p then a else b)`) (concl th))) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  REALIGN_TAC 11309 THEN REALIGN_FRAME_TAC 11309 11309 THEN
  REALIGN_NONOV_TAC 11278
   [`sig:int64,2420`; `m:int64,mlen:num`; `pre:int64,prelen:num`;
    `rnd:int64,32`; `sk:int64,2560`; `word pc:int64,libmldsa_size`;
    `word_add stackpointer (word 11309):int64,8`;
    `word_add stackpointer (word 11317):int64,16`] THEN
  REALIGN_ALIGNED_TAC [1678; 1902; 1934; 2094; 2990; 5038; 6062; 7118; 11262] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
  MP_TAC(SPECL [`skb:num->byte`; `MU:num`; `RND:num`]
               SIGN44_DECLASS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The prologue, up to the start of the first attempt: the alignment of the  *)
(* stack pointer, with RSP the value of the AND after step 2, the saved      *)
(* registers, unpack_sk (rho, tr and the key copied, and pointers into the   *)
(* secret key stored for s1, s2 and t0), then on ext either mld_H44 for mu   *)
(* (from tr, the prefix and m) or the inlined copy of 64 bytes from m (as    *)
(* four 128-bit words), then mld_H44 for rho'' (from the key, rnd and mu)    *)
(* and the lazy expansion of the matrix (rho copied into its structure),     *)
(* from step n0 at join1.                                                    *)
(* ------------------------------------------------------------------------- *)

let SIGN44_PROL_TAIL_TAC n0 =
  let sn k = mk_var("s"^string_of_int k,`:x86state`) in
  let nh = n0 + 14 and nm = n0 + 20 in
  let kpat =
   `!j. j < 32 ==> read (memory :> bytes8
         (word_add bot (word (2062 + j)))) s = f j`
  and rgoal =
   `read (memory :> bytes (word_add bot (word 2158),64)) s =
    mld_sign_rhoprime (\j. skb(32 + j)) RND MU`
  and rpat =
   `read (memory :> bytes (word_add bot (word 2158),64)) s =
    num_of_bytelist l` in
  X86_STEPS_TAC SIGN44_EXEC (n0--(nh - 1)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] kpat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN44_MCALL_TAC "H_H"
   [`read RDI s`; `64`; `read RDX s`; `32`; `read R8 s`; `32`;
    `word_add bot (word 2094):int64`; `64`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(32 + j)) 32)`;
    `RND:num`; `MU:num`] nh THEN
  SUBGOAL_THEN (subst [sn nh,`s:x86state`] rgoal) ASSUME_TAC THENL
   [REWRITE_TAC[mld_sign_rhoprime] THEN CONV_TAC SIGN_NUM_ARITH_CONV THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE SIGN_NUM_ARITH_CONV o
      check (fun th -> can (term_match [] rpat) (concl th)));
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] rpat) (concl th))) THEN
  X86_STEPS_TAC SIGN44_EXEC ((nh + 1)--(nm - 1)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 32 ==> read (memory :> bytes8
         (word_add bot (word (1966 + j)))) s = f j`) (concl th)
    then FIRST_ASSUM(fun rth ->
           if is_eq(concl rth) && is_var(rhs(concl rth)) &&
              name_of(rhs(concl rth)) = "rh"
           then ASSUME_TAC(TRANS
                  (REWRITE_RULE[ETA_AX]
                    (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
                  (REWRITE_RULE[mld_sk_rho] rth))
           else NO_TAC)
    else NO_TAC) THEN
  SIGN44_MCALL_TAC "H_MEXP" [`read RDI s`; `read RSI s`; `rh:num`] nm THEN
  X86_STEPS_TAC SIGN44_EXEC ((nm + 1)--(nm + 13)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `0 = n <=> n = 0`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  REALIGN_UNBOT_TAC THEN SIGN_SEL_DISCHARGE_TAC;;

let SIGN44_PROL_H_TAC =
  X86_STEPS_TAC SIGN44_EXEC (40--40) THEN
  FIRST_ASSUM(fun th ->
    if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE
          [ASSUME `word_zx(ext:int64) = (word 0:int32)`] th)
    else NO_TAC) THEN
  X86_STEPS_TAC SIGN44_EXEC (41--51) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 64 ==> read (memory :> bytes8
         (word_add bot (word (1998 + j)))) s = f j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
                     (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SIGN44_MCALL_TAC "H_H"
   [`read RDI s`; `64`; `read RDX s`; `64`; `read R8 s`; `prelen:num`;
    `m:int64`; `mlen:num`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(64 + j)) 64)`;
    mk_var("PRE'",`:num`); `M:num`] 52 THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add bot (word 2094),64)) s52 = MU`
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
   `read (memory :> bytes (word_add bot (word 2094),64)) s52 =
    num_of_bytelist l`) (concl th))) THEN
  X86_STEPS_TAC SIGN44_EXEC (53--54) THEN
  SIGN44_PROL_TAIL_TAC 55;;

let SIGN44_PROL_X_TAC =
  X86_STEPS_TAC SIGN44_EXEC (40--40) THEN
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
  X86_STEPS_TAC SIGN44_EXEC (41--51) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIGN_SUBWORD_JOIN_128]) THEN
  MP_TAC(SPECL [`word_add bot (word 2094):int64`; `M:num`; `4`;
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
   `read (memory :> bytes (word_add bot (word 2094),64)) s51 = MU`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" &&
         not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
   `read (memory :> bytes (word_add bot (word 2094),64)) s51 =
    M MOD 2 EXP 512`) (concl th))) THEN
  SIGN44_PROL_TAIL_TAC 52;;

let SIGN44_PROL_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC SIGN44_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (3--21) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIGN_BYTES32_OF_BYTES64 o check (fun th ->
    can (term_match [] `read (memory :> bytes64
      (word_add stackpointer (word 11325))) s = ext`) (concl th))) THEN
  X86_STEPS_TAC SIGN44_EXEC (22--35) THEN
  SIGN44_MCALL_TAC "H_UNPACK"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `read R9 s`; `sk:int64`; `skb:num->byte`] 36 THEN
  X86_STEPS_TAC SIGN44_EXEC (37--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN
  ASM_CASES_TAC `word_zx(ext:int64) = (word 0:int32)` THENL
   [SIGN44_PROL_H_TAC; SIGN44_PROL_X_TAC];;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop over the attempts: the facts about attempt i     *)
(* (its record D i as mld_sign_attempt_declass gives it, the termination of  *)
(* its challenge, and the result and signature if it is the last), the       *)
(* attempt as one step (ATT), then the three exits: on success to join5; on  *)
(* rejection kappa += 4, then back to join2 or, after the last attempt, -4   *)
(* in RDX and the zeroing of the signature, which gcc inlines, to join5. The *)
(* equations for mld_sign_ok_44 and mld_sign_sig_44 are made conditional on  *)
(* ~(i + 1 < N) before any call, which would otherwise rewrite the           *)
(* postcondition with them.                                                  *)
(* ------------------------------------------------------------------------- *)

let SIGN44_BALLOWED = SIGN44_MALLOWED @ [`i:num`];;

let SIGN44_ATT_ILIST =
  [`sig:int64`; `sk:int64`; `skb:num->byte`; `bot:int64`; `rh:num`;
   `MU:num`; `mld_sign_rhoprime (\j. (skb:num->byte)(32 + j)) RND MU`;
   `i:num`; `FST((D:num->num#num#(num->int32)#(num->byte)) i)`;
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i))`;
   `FST(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `SND(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `pc:num`];;

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

let SIGN44_BODY_ATT_TAC =
  FULL_INIT_TAC THEN
  REMOVE_THEN "H_ATT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (SIGN44_MC,SIGN44_EXEC,0x0,SIGN44_MC,th)
      (`e:(uarch_event)list`::SIGN44_ATT_ILIST) 1 THENL
     [REPEAT(CONJ_TAC THENL
        [SIGN_NUMS_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
      FULL_EXISTS_E2_TAC (ref SIGN44_BALLOWED);
      LABEL_TAC "H_ATT" th]);;

let SIGN44_BODY_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN
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
    `read RDX s = (if b then x else y)`) (concl th))) THEN
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


(*** The update of kappa, a 16-bit word on the stack, and its test ***)

let SIGN44_KAPPA_TAC =
  SUBGOAL_THEN `4 * i + 4 < 2 EXP 16` ASSUME_TAC THENL
   [UNDISCH_TAC `i < 16382` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD; SIGN_WORD16_OF_ZX]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`4 * i + 4`; `65528`]
                                         SIGN_VAL_WORD_SUB_EQ_0_16)
                               (CONJ (ASSUME `4 * i + 4 < 2 EXP 16`)
                                     (ARITH_RULE `65528 < 2 EXP 16`))]);;

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

let SIGN44_EXH_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [SIGN_SUFFIX_UNIFY_TAC;
    SIGN_STOS_GEN_TAC `sig:int64` 2420 THEN SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN44_EXH_TAC =
  SUBGOAL_THEN `4 * i + 4 = 65528` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(i + 1 < 16382)`; `i < 16382`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIGN_PC_SIMP_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (8--18) THEN
  SIGN_STOS_PREP_TAC `sig:int64` 2420 THEN
  SIGN_STOS_STEP_TAC SIGN44_EXEC 19 THEN
  SIGN_STOS_DONE_TAC `sig:int64` 2420 19 THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIGN_BYTES8_ZERO o check (fun th ->
    can (term_match [] `read (memory :> bytes(sig,2420)) s = 0`) (concl th)))
  THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 16382 13 D)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mld_sign_natt 16382 13 D <= 16382`; `~(i + 1 < 16382)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SIGN44_LAST_TAC SIGN44_NCASE_TH THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIGN44_EXH_DISCHARGE_TAC;;

let SIGN44_FAIL_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `read RDX s = (if b then x else y)`) (concl th))) THEN
  REWRITE_TAC[SIGN44_NCASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13 ==> P`)
    (concl th))) THEN
  X86_STEPS_TAC SIGN44_EXEC (2--7) THEN
  SIGN44_KAPPA_TAC THEN
  ASM_CASES_TAC `i + 1 < 16382` THENL [SIGN44_CONT_TAC; SIGN44_EXH_TAC];;

let SIGN44_BODY_TAC =
  SIGN44_BODY_INIT_TAC THEN SIGN44_BODY_ATT_TAC THEN
  ASM_CASES_TAC
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13` THENL
   [SIGN44_SUCC_TAC; SIGN44_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The epilogue, from join5: the zeroing of the pointers into the secret key *)
(* with three stores, of the structure of the matrix (1056 bytes) and of the *)
(* 256 bytes of the seed buffer with REP STOSQ, the restoring of the         *)
(* registers and the return.                                                 *)
(* ------------------------------------------------------------------------- *)

let SIGN44_EPIL_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN
  SIGN_BETA_ALL_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SIGN44_EPIL_TAC =
  SIGN_DROP_TAC SIGN44_DANGER THEN
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC SIGN44_EXEC (1--26) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SIGN_RET_ZX] THEN
  SIGN44_EPIL_DISCHARGE_TAC;;

let SIGN44_MAIN_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mld_sign_natt 16382 13 D`
   `pc + mldsa44_signature_internal_join2`
   `pc + mldsa44_signature_internal_join5` SIGN44_INV THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC; SIGN44_PROL_TAC; SIGN44_BODY_TAC; SIGN44_EPIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  SIGN44_START_TAC THEN SIGN44_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
