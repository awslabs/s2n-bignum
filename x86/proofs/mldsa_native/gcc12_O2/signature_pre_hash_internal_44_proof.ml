(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a pre-hash (HashML-DSA): the proof (see                           *)
(* signature_pre_hash_internal_44_spec.ml).                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/signature_pre_hash_internal_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;

let SPHI44_EXEC =
  MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 49972 bytes of stack below the return address, at           *)
(* stackpointer + 49972, with sk and hashalg above it; the code first aligns *)
(* RSP to 32 bytes, at bot + 49941 (see utils/mldsa_native_realign.ml), with *)
(* R10 keeping the original RSP + 8, and then pushes a copy of the return    *)
(* address, RBP (at bot + 49925, the frame pointer), R14, R13, R12, R10 and  *)
(* RBX, and reserves the prefix, at bot + 49525 with RSP. The call of the    *)
(* prefix has its return address at bot + 49517 (its frame the 64 bytes      *)
(* below it), and that of mldsa44_signature_internal, above its two          *)
(* arguments on the stack (sk and ext = 0), at bot + 49501, its frame the    *)
(* 49501 bytes at bot. The events before a call are functions of the         *)
(* variables SPHI44_VARS, with bot, which REALIGN_UNBOT_TAC expands at the   *)
(* end. HA, PLEN and PRE are replaced by their definitions, the length       *)
(* SPHI44_PLEN and the prefix SPHI44_PRE.                                    *)
(* ------------------------------------------------------------------------- *)

let SPHI44_VARS =
  [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
   `rnd:int64`; `sk:int64`; `hashalg:int64`; `skb:num->byte`; `PH:num`;
   `C:num`; `RND:num`; `MU:num`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let SPHI44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SPHI44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   SPHI44_VARS n;;

let SPHI44_PLEN =
  `mld_domain_separation_prefix_length (val(word_zx (hashalg:int64):int32))
     ctxlen phlen`
and SPHI44_PRE =
  `num_of_bytelist(mld_domain_separation_prefix
     (val(word_zx (hashalg:int64):int32))
     (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH))`;;

let SPHI44_LE =
  SPECL [`val(word_zx (hashalg:int64):int32)`; `ctxlen:num`; `phlen:num`]
   API_PREFIX_LENGTH_LE;;

(*** From join3 at step j: the zeroing of the prefix, and the return ***)

let SPHI44_R_TAC j = X86_STEPS_TAC SPHI44_EXEC (j--(j + 14));;

(*** From join2 at step k: the zeroing of the signature (see               ***)
(*** utils/mldsa_native_signing.ml), and then join3                        ***)

let SPHI44_Z_TAC k =
  X86_STEPS_TAC SPHI44_EXEC (k--(k + 8)) THEN
  SIGN_STOS_PREP_TAC `sig:int64` 2420 THEN
  SIGN_STOS_STEP_TAC SPHI44_EXEC (k + 9) THEN
  SIGN_STOS_DONE_TAC `sig:int64` 2420 (k + 9) THEN
  SPHI44_R_TAC (k + 10);;

(*** The end of a path, and the events, with the count of the REP STOSQ    ***)
(*** that zeroes the signature generalized for the bounds of its accesses  ***)

let SPHI44_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    SIGN_STOS_GEN_TAC `sig:int64` 2420 THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SPHI44_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[API_SIGN_DISTINCT] THEN
  REPEAT CONJ_TAC THEN TRY(API_RET_TAC THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_BYTES8_ZERO THEN FIRST_ASSUM ACCEPT_TAC THEN
      NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_44 skb MU RND` THEN
  REALIGN_UNBOT_TAC THEN API_EMPTY_REGIONS_TAC THEN
  SPHI44_DISCHARGE_TAC;;

(*** hashalg, the 32-bit eighth argument, from its slot on the stack ***)

let SPHI44_HASHALG_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add stackpointer (word 49988))) s =
          (hashalg:int64)`) (concl th)
    then ASSUME_TAC(MATCH_MP SIGN_BYTES32_OF_BYTES64 th) else NO_TAC);;

(*** A prefix of PLEN bytes, apart from what is written below it before    ***)
(*** the signing: signing it as the message, pre = NULL, prelen = 0 and    ***)
(*** ext = 0, and the zeroing of the signature if that fails               ***)

let SPHI44_SIGN_TAC =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,SPHI44_PLEN),
                        `2 EXP 64`)) ASSUME_TAC THENL
   [MP_TAC SPHI44_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                       mk_comb(`word:num->int64`,SPHI44_PLEN)),
                      SPHI44_PLEN)) ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC SPHI44_LE THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun r -> API_DRIVER_TAC
    (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r),
             mk_pair(`word_add bot (word 49525):int64`,SPHI44_PLEN)))
    SPHI44_LE)
   [`word_add bot (word 49517):int64,8`; `word_add bot (word 49509):int64,8`;
    `word_add bot (word 49501):int64,8`; `bot:int64,49501`;
    `sig:int64,2420`] THEN
  X86_STEPS_TAC SPHI44_EXEC (22--32) THEN
  API_NULL_TAC [`sig:int64`,`2420`; `bot:int64`,`49501`] THEN
  API_TERMINATES_TAC THEN
  ASSUME_TAC(INST_TYPE [`:64`,`:M`; `:32`,`:N`] WORD_ZX_0) THEN
  SPHI44_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; SPHI44_PLEN; `read RCX s`; `0`;
    `read R9 s`; `sk:int64`; `word 0:int64`; `skb:num->byte`;
    SPHI44_PRE; `0`; `RND:num`; `MU:num`] 33 THEN
  API_WIDEN_TAC
   [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                          mk_pair(`word_add bot (word 49525):int64`,
                                  SPHI44_PLEN)),
                  `word_add bot (word 49525):int64,332`),
          REWRITE_TAC[contained; CONTAINED_MODULO_REFL;
                      API_PREFIX_LENGTH_LE])] THEN
  ASM_CASES_TAC `mld_sign_ok_44 skb MU RND` THEN
  API_USE_CASE_TAC `mld_sign_ok_44 skb MU RND` [] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[API_SIGN_OK_DECLASS_44] o
    check (fun th -> concl th = `mld_sign_ok_44 skb MU RND` ||
                     concl th = `~mld_sign_ok_44 skb MU RND`)) THENL
   [X86_STEPS_TAC SPHI44_EXEC (34--38) THEN SPHI44_R_TAC 39 THEN
    SPHI44_FINAL_TAC;
    ASSUME_TAC(GEN `t:num` (MP (SPECL [`skb:num->byte`; `MU:num`;
      `RND:num`; `t:num`] (CONJUNCT1 API_SIGN_SIG_FAIL))
      (ASSUME `~mld_sign_ok_44 skb MU RND`))) THEN
    X86_STEPS_TAC SPHI44_EXEC (34--39) THEN SPHI44_Z_TAC 40 THEN
    SPHI44_FINAL_TAC];;

(*** hashalg is not 0: the prefix, -9 if it is rejected ***)

let SPHI44_PREFIX_TAC =
  X86_STEPS_TAC SPHI44_EXEC (19--20) THEN
  SPHI44_CALL_TAC "H_PREFIX"
   [`read RDI s`; `read RSI s`; `phlen:num`; `read RCX s`; `ctxlen:num`;
    `read R9 s`; `C:num`; `PH:num`] 21 THEN
  API_LET_TAC [] [WORD_ZX_ZX_32_64_32] THEN
  ASM_CASES_TAC (mk_eq(SPHI44_PLEN,`0`)) THEN
  API_USE_CASE_TAC (mk_eq(SPHI44_PLEN,`0`)) [] THENL
   [X86_STEPS_TAC SPHI44_EXEC (22--24) THEN SPHI44_Z_TAC 25 THEN
    SPHI44_FINAL_TAC;
    SPHI44_SIGN_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether hashalg *)
(* is 0, whether the prefix is rejected and whether signing succeeds (which  *)
(* the events give as what it declassifies).                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       ms) "H_INTERNAL" THEN
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (ph:int64) (phlen:num) (ctx:int64) (ctxlen:num) (rnd:int64)
     (sk:int64) (hashalg:int64) (rho:num)
     (dcl:num->num#num#(num->int32)#(num->byte)) (mf:int64) (mc:int64)
     (pc:num) (stackpointer:int64) (returnaddress:int64).
     if val(word_zx hashalg:int32) = 0
     then f_ev_0 sig ph phlen ctx ctxlen rnd sk hashalg mf mc pc
           stackpointer returnaddress
     else if mld_domain_separation_prefix_length
              (val(word_zx hashalg:int32)) ctxlen phlen = 0
     then f_ev_1 sig ph phlen ctx ctxlen rnd sk hashalg mf mc pc
           stackpointer returnaddress
     else if (?n. FST(SND(dcl n)) = 13)
     then f_ev_2 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl mf mc pc
           stackpointer returnaddress
     else f_ev_3 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl mf mc pc
           stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SPHI44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`HA:num`; `PLEN:num`; mk_var("PRE'",`:num`)] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  REALIGN_TAC 49972 THEN REALIGN_FRAME_TAC 49972 49972 THEN
  REALIGN_NONOV_TAC 49941
   [`sig:int64,2420`; `ph:int64,phlen:num`; `ctx:int64,ctxlen:num`;
    `rnd:int64,32`; `sk:int64,2560`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 49972):int64,24`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC SPHI44_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SPHI44_EXEC (3--14) THEN SPHI44_HASHALG_TAC THEN
  X86_STEPS_TAC SPHI44_EXEC (15--18) THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[VAL_EQ_0]) THEN
  API_PC_TAC [`word_zx (hashalg:int64) = (word 0:int32)`] THENL
   [X86_STEPS_TAC SPHI44_EXEC (19--19) THEN SPHI44_Z_TAC 20 THEN
    SPHI44_FINAL_TAC;
    SPHI44_PREFIX_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_SIGN_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SIGN_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
