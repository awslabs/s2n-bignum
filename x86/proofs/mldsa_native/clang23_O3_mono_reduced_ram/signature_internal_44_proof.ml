(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with the secret key, all the attempts (ML-DSA-44, clang 23 -O3    *)
(* mono reduced-RAM): the proof (see signature_internal_44_spec.ml).         *)
(*                                                                           *)
(* The attempt is SI44_HEAD and SI44_ATT of signature_internal_44_stages.ml, *)
(* at the frame rsp0 of the attempt. The proof of the whole function follows *)
(* the gcc reduced-RAM proof: the prologue (the six pushes, the realignment  *)
(* of the frame to 32 bytes with bot = its bottom and rsp0 = bot + 1471, the *)
(* pointers into the secret key, tr and the seeds, mu with mld_H44 or copied *)
(* from m when ext is not 0, rho''), then the loop over the attempts         *)
(* (ENSURES_EVENTS_WHILE_UP2_TAC up to mld_sign_natt 16382 13 D), each one   *)
(* SI44_ATT followed by the count of the attempts (16 bits against 16382)    *)
(* and, after the last failed one, the zeroing of the signature with memset  *)
(* and -4 in R15, and the epilogue (the zeroing of the pointers into the     *)
(* secret key, of the seed buffer with memset and of the 256 bytes of tr and *)
(* the seeds with SSE stores, the restored registers).                       *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/clang_tools.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_attempt.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hrow.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_stage.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_44_stages.ml";;

(* ------------------------------------------------------------------------- *)
(* The facts about the attempts that the main proof needs, for D =           *)
(* mld_sign_declass_44 and its number of attempts (as in the gcc proof).     *)
(* ------------------------------------------------------------------------- *)

let SI44_DECLASS_FACTS = prove
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
(* 64 bytes stored as four 128-bit chunks                                    *)
(* ------------------------------------------------------------------------- *)

let SI_BYTES64_OF_CHUNKS = prove
 (`!a:int64 (f:num->byte) s.
     read (memory :> bytes128 a) s = mld_chunk128 f 0 /\
     read (memory :> bytes128 (word_add a (word 16))) s = mld_chunk128 f 1 /\
     read (memory :> bytes128 (word_add a (word 32))) s = mld_chunk128 f 2 /\
     read (memory :> bytes128 (word_add a (word 48))) s = mld_chunk128 f 3
     ==> read (memory :> bytes(a,64)) s = num_of_bytelist(list_of_seq f 64)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mld_chunk128 (f:num->byte) 2 = mld_chunk128 (\j. f(32 + j)) 0 /\
                mld_chunk128 f 3 = mld_chunk128 (\j. f(32 + j)) 1`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mld_chunk128] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ARITH_RULE `!k. 16 * 2 + k = 32 + 16 * 0 + k`;
                ARITH_RULE `!k. 16 * 3 + k = 32 + 16 * 1 + k`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `f:num->byte`; `s:x86state`] MLD_BYTES32_OF_CHUNKS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word 32):int64`; `\j. (f:num->byte)(32 + j)`; `s:x86state`]
               MLD_BYTES32_OF_CHUNKS) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (a:int64) (word 32)) (word 16) =
                         word_add a (word 48)`] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ_ADD_GEN; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ]);;

(* ------------------------------------------------------------------------- *)
(* The main proof. The frame: after the six pushes (at stackpointer + 12030  *)
(* .. + 12077, with N = 12078 bytes of stack below the return address), the  *)
(* AND aligns RSP to 32 (REALIGN_TAC 12030: its value is bot + 11999) and    *)
(* the code subtracts 0x2920, so that the frame of the attempts rsp0 is bot  *)
(* + 1471 and the callees use the 1471 bytes below it. The events are those *)
(* of the prologue (one function for each case of ext), then attempt i for  *)
(* each i < N (one that is followed by another, the successful last one, or *)
(* the last one after which the signature is zeroed), then the epilogue,    *)
(* as in the gcc proof.                                                      *)
(* ------------------------------------------------------------------------- *)

let SI44_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let SI44_TEMPLATE =
 `\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (rnd:int64)
   (sk:int64) (ext:int32) (rh:num)
   (D:num->num#num#(num->int32)#(num->byte)) (mf:int64) (mc:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND
    (f_ev_epil sig m mlen pre prelen rnd sk ext rh D mf mc pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (mld_sign_natt 16382 13 D)
        (\i. if i + 1 < mld_sign_natt 16382 13 D
             then f_ev_cont sig m mlen pre prelen rnd sk ext rh D mf mc pc
                    stackpointer returnaddress i
             else if FST(SND(D i)) = 13
             then f_ev_succ sig m mlen pre prelen rnd sk ext rh D mf mc pc
                    stackpointer returnaddress i
             else f_ev_exh sig m mlen pre prelen rnd sk ext rh D mf mc pc
                    stackpointer returnaddress i))
      (if ext = (word 0:int32)
       then f_ev_prolh sig m mlen pre prelen rnd sk ext rh D mf mc pc
              stackpointer returnaddress
       else f_ev_prolx sig m mlen pre prelen rnd sk ext rh D mf mc pc
              stackpointer returnaddress))
   :(uarch_event)list`;;

let SI44_INV =
 `\i s.
   read RSP s = word_add bot (word 1471) /\
   read RBP s = word_add stackpointer (word 12070) /\
   read (memory :> bytes64 (word_add stackpointer (word 12030))) s = rbx_init /\
   read (memory :> bytes64 (word_add stackpointer (word 12038))) s = r12_init /\
   read (memory :> bytes64 (word_add stackpointer (word 12046))) s = r13_init /\
   read (memory :> bytes64 (word_add stackpointer (word 12054))) s = r14_init /\
   read (memory :> bytes64 (word_add stackpointer (word 12062))) s = r15_init /\
   read (memory :> bytes64 (word_add stackpointer (word 12070))) s = rbp_init /\
   read (memory :> bytes64 (word_add stackpointer (word 12078))) s = returnaddress /\
   (read DF s <=> false) /\
   read (memory :> bytes64(word(pc + got_memset))) s = mf /\
   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
   read (memory :> bytes(ea,el)) s = ev /\
   read (memory :> bytes64 (word_add bot (word 1479))) s = sig /\
   read (memory :> bytes64 (word_add bot (word 1495))) s = word_add sig (word 2336) /\
   read (memory :> bytes64 (word_add bot (word 1503))) s = word_add sk (word 512) /\
   read (memory :> bytes64 (word_add bot (word 1535))) s = word_add sk (word 896) /\
   read (memory :> bytes64 (word_add bot (word 1567))) s = word_add sk (word 128) /\
   read (memory :> bytes64 (word_add bot (word 1863))) s = word_add sig (word 39) /\
   read (memory :> bytes (word_add bot (word 6815),32)) s = rh /\
   read (memory :> bytes (word_add bot (word 2143),64)) s = MU /\
   read (memory :> bytes (word_add bot (word 2207),64)) s =
   mld_sign_rhoprime (\j. skb(32 + j)) RND MU /\
   (!j. j < 2560 ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\
   (i < mld_sign_natt 16382 13 D ==> read RCX s = word i) /\
   (i = mld_sign_natt 16382 13 D
    ==> read R15 s = (if mld_sign_ok_44 skb MU RND then word 0 else word 4294967292) /\
        (!t. t < 2420
             ==> read (memory :> bytes8 (word_add sig (word t))) s =
                 mld_sign_sig_44 skb MU RND t))`;;

let SI44_MALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `rnd:int64`; `sk:int64`; `ext:int32`; `rh:num`;
   `D:num->num#num#(num->int32)#(num->byte)`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`; `rsp0:int64`];;

let SI44_MCALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC SI44_MALLOWED;
      LABEL_TAC name th]);;

let SI44_MFCALL_TAC name ilist n =
  SI44_MCALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC THEN EXPAND_CALLEE_MEMACCESS_TAC;;

(* 128-bit chunk i of the bytes k .. k + n - 1 of the secret key at state st *)
let SI44_SKCHUNK_TAC k n i st =
  let pat = subst [st,`s:x86state`]
    `!j. j < 2560 ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j` in
  FIRST_ASSUM(fun skth ->
    if concl skth <> pat then NO_TAC else
    let kt = mk_small_numeral k and nt = mk_small_numeral n in
    let sl = MP (SPECL [`sk:int64`; `skb:num->byte`; `2560`; kt; nt; st] SIGN_SK_SLICE)
                (CONJ skth (EQT_ELIM(NUM_REDUCE_CONV (mk_binop `(<=):num->num->bool`
                                    (mk_binop `(+):num->num->num` kt nt) `2560`)))) in
    let bt = BETA_RULE(ISPECL [`sk:int64`; kt; nt;
               mk_abs(`j:num`,mk_comb(`skb:num->byte`,mk_binop `(+):num->num->num` kt `j:num`));
               st; mk_small_numeral i] BYTES128_OF_BYTES8_OFF) in
    let r = MP bt (CONJ sl (EQT_ELIM(NUM_REDUCE_CONV(rand(lhand(concl bt)))))) in
    ASSUME_TAC(CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THENC
                         REWRITE_CONV[WORD_ADD_0; ADD_CLAUSES; ETA_AX]) r));;

let SI44_RSP0 = `word_add bot (word 1471):int64`;;

(* the bytes of two or four stored chunks of f at bot + off, as one number *)
let SI44_CHUNKS_TAC lem off f st =
  let a = mk_comb(mk_comb(`word_add:int64->int64->int64`,`bot:int64`),
                  mk_comb(`word:num->int64`,mk_small_numeral off)) in
  MP_TAC(SPECL [a; f; st] lem) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC];;

(* RSP after a SUB or an ADD of the stack pointer, as bot + k *)
let SI44_RSP_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RSP s = x`) (concl th)
    then CONV_RULE(RAND_CONV(REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)))) th
    else th);;

let SI44_START_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    SI_ASSUME_CALLEE_TAILED_TAC (MP (SPEC_ALL SI44_ATT) th) "H_ATT" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MP (SPEC_ALL MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) mcs) "H_H" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC SI44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `rh = mld_sk_rho skb` THEN
  ABBREV_TAC `D = mld_sign_declass_44 skb MU RND` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SI44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `MU = (if p then a else b)`) (concl th))) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  REALIGN_TAC 12030 THEN REALIGN_FRAME_TAC 12078 12030 THEN
  REALIGN_NONOV_TAC 11999
   [`sig:int64,2420`; `m:int64,mlen:num`; `pre:int64,prelen:num`;
    `rnd:int64,32`; `sk:int64,2560`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 12030):int64,48`;
    `word_add stackpointer (word 12078):int64,8`;
    `word_add stackpointer (word 12086):int64,16`] THEN
  REALIGN_ALIGNED_TAC [1455; 2015; 2031; 2047; 2063; 2079; 2095; 2111; 2127;
                       2143; 2159; 2175; 2191; 2207; 2223; 2239; 2255; 6815; 6831] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word k))
                            (word 18446744073709551584):int64 = x`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[th] (SPEC (lhand(lhs(concl th))) REALIGN_ALIGNED_AND))
    else NO_TAC) THEN
  SUBGOAL_THEN `aligned 32 (word_add bot (word 1471):int64)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if can (term_match [] `aligned 32 (word_add bot (word n):int64)`) (concl th)
      then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[WORD_RULE `word_add bot (word 11999):int64 =
                           word_add (word_add bot (word 1471)) (word 10528)`] THEN
    MATCH_MP_TAC VI44_ALIGNED32_LEMMA THEN
    REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV DIVIDES_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
  MP_TAC(SPECL [`skb:num->byte`; `MU:num`; `RND:num`] SI44_DECLASS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(*** the prologue: the six pushes, the alignment, the frame, the copies of ***)
(*** rho, the key and tr from the secret key, the pointers into it         ***)

(* aligned 16 (word_add (word_add bot (word 1471)) (word k)), the form of the
   addresses of the aligned SSE accesses at rsp0 + k, from the bot + (1471 + k)
   facts of REALIGN_ALIGNED_TAC *)
let SI44_NESTED_ALIGNED_TAC ks =
  MAP_EVERY (fun k ->
    SUBGOAL_THEN (subst [mk_small_numeral k,`k:num`]
      `aligned 16 (word_add (word_add bot (word 1471)) (word k):int64)`)
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC]) ks;;

let SI44_PROL_A_TAC =
  MAP_EVERY (fun (n,r) -> GHOST_INTRO_TAC (mk_var(n,`:int256`)) r)
   [("ymm0_init",`read YMM0`); ("ymm1_init",`read YMM1`);
    ("ymm2_init",`read YMM2`); ("ymm3_init",`read YMM3`)] THEN
  FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  X86_STEPS_TAC SI44_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SI44_EXEC (9--13) THEN SI44_RSP_NORM_TAC THEN
  SI44_NESTED_ALIGNED_TAC [544; 560; 576; 592; 608; 624; 640; 656; 672; 688; 704; 720;
                           736; 752; 768; 784; 5344; 5360] THEN
  X86_STEPS_TAC SI44_EXEC (14--22) THEN
  MAP_EVERY (fun (k,n,i) -> SI44_SKCHUNK_TAC k n i `s22:x86state`)
   [0,32,0; 0,32,1; 32,32,0; 32,32,1; 64,64,0; 64,64,1; 64,64,2; 64,64,3] THEN
  X86_STEPS_TAC SI44_EXEC (23--38) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  SI44_CHUNKS_TAC MLD_BYTES32_OF_CHUNKS 2015 `skb:num->byte` `s38:x86state` THEN
  SI44_CHUNKS_TAC MLD_BYTES32_OF_CHUNKS 2111 `\j. (skb:num->byte)(32 + j)` `s38:x86state` THEN
  SI44_CHUNKS_TAC SI_BYTES64_OF_CHUNKS 2047 `\j. (skb:num->byte)(64 + j)` `s38:x86state` THEN
  X86_STEPS_TAC SI44_EXEC (39--46);;

(*** mu: mld_H44 of tr, pre and m (ext = 0), or the 64 bytes of m copied ***)

(* aligned 16 (stackpointer + 8) for mld_H44 called after two pushes *)
let SI44_HALIGN_TAC =
  SUBGOAL_THEN `aligned 16 (word_add (word_sub (word_sub (word_sub (word_add bot (word 1471))
                  (word 8)) (word 8)) (word 8)) (word 8):int64)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_add (word_sub (word_sub (word_sub (word_add (b:int64) (word 1471))
                  (word 8)) (word 8)) (word 8)) (word 8) = word_add b (word 1455)`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

let SI44_MU_CASE_TAC cth =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" &&
       is_cond(lhs(concl th))
    then ASSUME_TAC(REWRITE_RULE[cth] th) else NO_TAC);;

let SI44_PROL_H_TAC =
  SI44_MU_CASE_TAC (ASSUME `ext = (word 0:int32)`) THEN
  X86_STEPS_TAC SI44_EXEC (47--53) THEN
  SI44_HALIGN_TAC THEN
  SI44_MFCALL_TAC "H_H"
   [`read RDI s`; `64`; `read RDX s`; `64`; `read R8 s`; `prelen:num`;
    `m:int64`; `mlen:num`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(64 + j)) 64)`;
    mk_var("PRE'",`:num`); `M:num`] 54 THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add bot (word 2143),64)) s54 = MU` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" && not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_mu] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    FIRST_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add bot (word 2143),64)) s54 = num_of_bytelist l`) (concl th)
       then ACCEPT_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) th) else NO_TAC);
    ALL_TAC] THEN
  X86_STEPS_TAC SI44_EXEC (55--56) THEN SI44_RSP_NORM_TAC;;

let SI44_PROL_X_TAC =
  SI44_MU_CASE_TAC (ASSUME `~(ext = (word 0:int32))`) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `~(ext = (word 0:int32)) ==> 64 <= mlen`) (concl th)
    then ASSUME_TAC(MP th (ASSUME `~(ext = (word 0:int32))`)) else NO_TAC) THEN
  MAP_EVERY (fun n ->
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral n; `s46:x86state`]
                 SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [UNDISCH_TAC `64 <= mlen` THEN ARITH_TAC;
                    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC])
   [0;1;2;3] THEN
  X86_STEPS_TAC SI44_EXEC (47--55) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; SIGN_SUBWORD_JOIN_128]) THEN
  MP_TAC(SPECL [`word_add bot (word 2143):int64`; `M:num`; `4`; `s55:x86state`]
               SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    CONV_TAC(LAND_CONV(DEPTH_CONV NUM_MULT_CONV)) THEN DISCH_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add bot (word 2143),64)) s55 = MU` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" && not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC];;

(*** rho'' = mld_H44 of the key, rnd and mu, rho copied for the matrix,   ***)
(*** the pointers into the signature, the attempt count 0 (from n0)       ***)

let SI44_PROL_END_TAC =
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (word_add bot (word 6815),32)) s = x`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM mld_sk_rho; ASSUME `mld_sk_rho skb = rh`] th)
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] `read (memory :> bytes (word_add bot (word n),64)) s =
                        num_of_bytelist l`) (concl th) ||
    can (term_match [] `read (memory :> bytes (word_add (word_add bot (word n)) (word k),64)) s =
                        num_of_bytelist l`) (concl th)))) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `0 = n <=> n = 0`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  REALIGN_UNBOT_TAC THEN SIGN_SEL_DISCHARGE_TAC;;

let SI44_PROL_TAIL_TAC n0 =
  let sn k = mk_var("s"^string_of_int k,`:x86state`) in
  X86_STEPS_TAC SI44_EXEC (n0--(n0+8)) THEN SI44_HALIGN_TAC THEN
  SI44_MFCALL_TAC "H_H"
   [`read RDI s`; `64`; `read RDX s`; `32`; `read R8 s`; `32`;
    `word_add bot (word 2143):int64`; `64`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(32 + j)) 32)`;
    `RND:num`; `MU:num`] (n0+9) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes (a,64)) s = num_of_bytelist l`) (concl th)
    then CONV_RULE(LAND_CONV(REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)))) th
    else th) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (word_add bot (word 2207),64)) s = num_of_bytelist l`)
           (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  X86_STEPS_TAC SI44_EXEC ((n0+10)--(n0+10)) THEN SI44_RSP_NORM_TAC THEN
  YMM_GHOST_TAC (sn (n0+10)) ["YMM0","ymm0_t"; "YMM1","ymm1_t"] THEN
  X86_STEPS_TAC SI44_EXEC ((n0+11)--(n0+21)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  SI44_CHUNKS_TAC MLD_BYTES32_OF_CHUNKS 6815 `skb:num->byte` (sn (n0+21)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!j. j < 64 ==> read (memory :> bytes8
              (word_add (word_add bot (word 2207)) (word j))) s = f j`) (concl th)
    then ASSUME_TAC(MATCH_MP READ_BYTES_OF_BYTES8 th) else NO_TAC) THEN
  SUBGOAL_THEN (subst [sn (n0+21),`s:x86state`]
    `read (memory :> bytes (word_add bot (word 2207),64)) s =
     mld_sign_rhoprime (\j. skb(32 + j)) RND MU`) ASSUME_TAC THENL
   [REWRITE_TAC[mld_sign_rhoprime] THEN CONV_TAC SIGN_NUM_ARITH_CONV THEN
    FIRST_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add bot (word 2207),64)) s = num_of_bytelist l`) (concl th)
       then ACCEPT_TAC(CONV_RULE SIGN_NUM_ARITH_CONV th) else NO_TAC);
    ALL_TAC] THEN
  SI44_PROL_END_TAC;;

let SI44_PROL_TAC =
  SI44_PROL_A_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; WORD_SUB_0]) THEN
  ASM_CASES_TAC `ext = (word 0:int32)` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `read RIP s = x`) (concl th))) THEN
  ASM_REWRITE_TAC[VAL_WORD_0] THEN DISCH_TAC THENL
   [SI44_PROL_H_TAC THEN SI44_PROL_TAIL_TAC 57;
    SI44_PROL_X_TAC THEN SI44_PROL_TAIL_TAC 56];;

(* RUN_STRAIGHT_TAC of inline_verify.ml, stopping at the offset stop *)
let SI44_RUN_TO_TAC execth memset_name allowed stop n0 =
  let plt = layout "plt_memset" and got = layout "got_memset" in
  let rec run n (asl,w) =
    let off = cur_pc_offset (asl,w) in
    if off = stop || off < 0 then ALL_TAC (asl,w)
    else if off = plt then
      (LIBC_PLT_TAC execth plt got (n - 1) THEN
       LIBC_FULL_CALL_TAC memset_name execth
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
         `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
        allowed (n + 1) THEN RSP_NORM_TAC THEN
       run (n + 2)) (asl,w)
    else (X86_STEPS_TAC execth [n] THEN run (n + 1)) (asl,w) in
  run n0;;

(*** an iteration of the loop over the attempts (as gcc's SIGN44_BODY) ***)

let SI44_BALLOWED = SI44_MALLOWED @ [`i:num`];;

let SI44_ATT_ILIST =
  [`sig:int64`; `sk:int64`; `skb:num->byte`; SI44_RSP0; `rh:num`;
   `MU:num`; `mld_sign_rhoprime (\j. (skb:num->byte)(32 + j)) RND MU`;
   `i:num`; `FST((D:num->num#num#(num->int32)#(num->byte)) i)`;
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i))`;
   `FST(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `SND(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `pc:num`];;

let SI44_BODY_INIT_TAC =
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

let SI44_BODY_ATT_TAC =
  FULL_INIT_TAC THEN
  REMOVE_THEN "H_ATT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::SI44_ATT_ILIST) 1 THENL
     [REPEAT(CONJ_TAC THENL
        [SIGN_NUMS_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
      REPEAT CONJ_TAC THEN
      TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC SI44_BALLOWED;
      LABEL_TAC "H_ATT" th]);;

let SI44_BODY_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SI44_CASE_TH = ASSUME
  `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13`;;

let SI44_NCASE_TH = ASSUME
  `~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13)`;;

let SI44_LAST_TAC cth =
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

let SI44_SUCC_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13 ==> P`)
    (concl th))) THEN
  REWRITE_TAC[SI44_CASE_TH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 16382 13 D)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> can (term_match []
     `i + 1 < mld_sign_natt 16382 13 D ==> P`) (concl th))) THEN
    REWRITE_TAC[SI44_CASE_TH];
    ALL_TAC] THEN
  SI44_LAST_TAC SI44_CASE_TH THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI44_BODY_DISCHARGE_TAC;;

(*** the epilogue, from join28: the pointers into the secret key and the ***)
(*** buffers of the matrix and the seeds zeroed, the registers restored  ***)

let SI44_EPIL_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN
  SIGN_BETA_ALL_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SI44_DANGER =
  [`mld_sign_ok_44 skb MU RND <=> P`;
   `mld_sign_sig_44 skb MU RND = x`];;

let SI44_EPIL_TAC =
  SIGN_DROP_TAC SI44_DANGER THEN
  REWRITE_TAC[LT_REFL] THEN
  SI44_NESTED_ALIGNED_TAC [544; 560; 576; 592; 608; 624; 640; 656; 672; 688; 704; 720;
                           736; 752; 768; 784] THEN
  FULL_INIT_TAC THEN
  SI44_RUN_TO_TAC SI44_EXEC "H_MEMSET" (ref SI44_MALLOWED) (-1) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SIGN_RET_ZX] THEN
  SI44_EPIL_DISCHARGE_TAC;;

(*** after a failed attempt: the count n + 1 (16 bits) against 16382, back ***)
(*** to join2, or the signature zeroed and -4 in R15                       ***)

let SI44_CONT_TAC =
  SUBGOAL_THEN `i + 1 < mld_sign_natt 16382 13 D` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match []
           `~(i + 1 < mld_sign_natt 16382 13 D)
            ==> (mld_sign_ok_44 skb MU RND <=> P)`) (concl th)
      then ASSUME_TAC(REWRITE_RULE[SI44_NCASE_TH]
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
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI44_BODY_DISCHARGE_TAC;;

let SI44_EXH_TAC =
  SI44_RUN_TO_TAC SI44_EXEC "H_MEMSET" (ref SI44_BALLOWED)
    (layout "mldsa44_signature_internal_join28") 7 THEN
  RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ZX_0]) THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 16382 13 D)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mld_sign_natt 16382 13 D <= 16382`; `~(i + 1 < 16382)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SI44_LAST_TAC SI44_NCASE_TH THEN
  SUBGOAL_THEN `~(16382 < mld_sign_natt 16382 13 D)` ASSUME_TAC THENL
   [UNDISCH_TAC `mld_sign_natt 16382 13 D <= 16382` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

(*** the count of the attempts after a failed one: n + 1 in 32 bits, its ***)
(*** low 16 bits against 16382                                          ***)

let SI44_CNT_TAC =
  DISCH_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_ADD;
              DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `i < 18446744073709551616 /\ i < 4294967296 /\ i + 1 < 4294967296 /\
                i + 1 < 65536 /\ i + 1 < 18446744073709551616` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `i < 16382` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;;
let SI44_CNT_LEMMA c = prove(mk_imp(`i < 16382`, mk_iff(c, `~(i + 1 = 16382)`)), SI44_CNT_TAC);;
let SI44_RCX_LEMMA = prove
 (`i < 16382 ==> word_zx (word_add (word_zx (word i:int64):int32) (word 1)):int64 = word (i + 1)`,
  DISCH_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_ADD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `i < 18446744073709551616 /\ i < 4294967296 /\ i + 1 < 4294967296 /\
                i + 1 < 18446744073709551616` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `i < 16382` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let SI44_FAIL_PRE_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13 ==> P`)
    (concl th))) THEN
  X86_STEPS_TAC SI44_EXEC (2--6) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read RIP s = (if c then a else b)`) (concl th)
    then let c = rand(rator(rator(rhs(concl th)))) in
         let cth = MP (SI44_CNT_LEMMA c) (ASSUME `i < 16382`) in
         RULE_ASSUM_TAC(fun t ->
           if can (term_match [] `read RIP s = x`) (concl t) ||
              can (term_match [] `read events s = x`) (concl t)
           then REWRITE_RULE[cth] t else t)
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP SI44_RCX_LEMMA (ASSUME `i < 16382`)]);;

(* i + 1 = 16382 is used only in the PC and the events: as an assumption, *)
(* the calls of the memset would substitute 16382 for i + 1 in the goal.    *)
let SI44_EXH_PRE_TAC =
  SUBGOAL_THEN `i + 1 = 16382`
   (fun th -> RULE_ASSUM_TAC(fun t ->
      if can (term_match [] `read RIP s = x`) (concl t) ||
         can (term_match [] `read events s = x`) (concl t)
      then REWRITE_RULE[th] t else t)) THENL
   [MAP_EVERY UNDISCH_TAC [`~(i + 1 < 16382)`; `i < 16382`] THEN ARITH_TAC;
    ALL_TAC];;

let SI44_FAIL_TAC =
  SI44_FAIL_PRE_TAC THEN
  ASM_CASES_TAC `i + 1 < 16382` THENL
   [SUBGOAL_THEN `~(i + 1 = 16382)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [UNDISCH_TAC `i + 1 < 16382` THEN ARITH_TAC; ALL_TAC] THEN
    SI44_CONT_TAC;
    SI44_EXH_PRE_TAC THEN SI44_EXH_TAC];;

let SI44_BODY_TAC =
  SI44_BODY_INIT_TAC THEN SI44_BODY_ATT_TAC THEN
  ASM_CASES_TAC
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 13` THENL
   [SI44_SUCC_TAC; SI44_FAIL_TAC];;

let SI44_MAIN_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mld_sign_natt 16382 13 D`
   `pc + mldsa44_signature_internal_join2`
   `pc + mldsa44_signature_internal_join28` SI44_INV THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC; SI44_PROL_TAC; SI44_BODY_TAC; SI44_EPIL_TAC];;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  SI44_START_TAC THEN SI44_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
