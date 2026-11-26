(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a pre-hash (HashML-DSA): the proof (see                           *)
(* signature_pre_hash_internal_87_spec.ml).                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_pre_hash_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/api_inline.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 16909 bytes of stack below the return address, at           *)
(* stackpointer + 16909, with sk and hashalg above it; the code pushes RBP   *)
(* (the frame pointer), R15, R14, R12 and RBX, from stackpointer + 16901     *)
(* down to stackpointer + 16869, aligns RSP to 32 bytes, at bot + 16838 (see *)
(* utils/mldsa_native_realign.ml), and reserves 352 bytes for the prefix,    *)
(* with RSP at bot + 16486. The call of the prefix has its return address at *)
(* bot + 16478, and that of mldsa87_signature_internal, above its two        *)
(* arguments on the stack (sk and ext = 0), at bot + 16462, its frame the    *)
(* 16462 bytes at bot. The events before a call are functions of the         *)
(* variables SPHI87_VARS, with bot, which REALIGN_UNBOT_TAC expands at the   *)
(* end. HA, PLEN and PRE are replaced by their definitions, the length       *)
(* SPHI87_PLEN and the prefix SPHI87_PRE.                                    *)
(* ------------------------------------------------------------------------- *)


let SPHI87_EXEC =
  MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let SPHI87_VARS =
  [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
   `rnd:int64`; `sk:int64`; `hashalg:int64`; `skb:num->byte`; `PH:num`;
   `C:num`; `RND:num`; `MU:num`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let SPHI87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   SPHI87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   SPHI87_VARS n;;

let SPHI87_PLEN =
  `mld_domain_separation_prefix_length (val(word_zx (hashalg:int64):int32))
     ctxlen phlen`
and SPHI87_PRE =
  `num_of_bytelist(mld_domain_separation_prefix
     (val(word_zx (hashalg:int64):int32))
     (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH))`;;

let SPHI87_LE =
  SPECL [`val(word_zx (hashalg:int64):int32)`; `ctxlen:num`; `phlen:num`]
   API_PREFIX_LENGTH_LE;;

(*** The call of memset at step c; the state after it is c + 2 ***)

let SPHI87_MEMSET_TAC c =
  LIBC_PLT_TAC SPHI87_EXEC (layout "plt_memset") (layout "got_memset") c THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" SPHI87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref SPHI87_VARS) (c + 2);;

(*** From join2 at step t: the zeroing of the prefix and the return        ***)

let SPHI87_T_STEPS_TAC t =
  X86_STEPS_TAC SPHI87_EXEC ((t + 1)--(t + 5)) THEN
  SPHI87_MEMSET_TAC (t + 5) THEN
  X86_STEPS_TAC SPHI87_EXEC ((t + 8)--(t + 21));;

(*** From join1 at step c: the zeroing of the signature, then join2        ***)

let SPHI87_Z_STEPS_TAC c =
  X86_STEPS_TAC SPHI87_EXEC ((c + 1)--(c + 4)) THEN
  SPHI87_MEMSET_TAC (c + 4) THEN
  API_MEMSET_BYTES_TAC THEN
  X86_STEPS_TAC SPHI87_EXEC ((c + 7)--(c + 7)) THEN
  SPHI87_T_STEPS_TAC (c + 7);;

(*** The end of a path, and the events ***)

let SPHI87_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[API_SIGN_DISTINCT] THEN
  REPEAT CONJ_TAC THEN TRY(API_RET_TAC THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_BYTES8_ZERO THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_87 skb MU RND` THEN
  REALIGN_UNBOT_TAC THEN API_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** hashalg, the 32-bit eighth argument, from its slot on the stack ***)

let SPHI87_HASHALG_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add stackpointer (word 16925))) s =
          (hashalg:int64)`) (concl th)
    then ASSUME_TAC(MATCH_MP SIGN_BYTES32_OF_BYTES64 th) else NO_TAC);;

(*** A prefix of PLEN bytes: signing it as the message, pre = NULL,        ***)
(*** prelen = 0 and ext = 0, and the zeroing of the signature if that fails ***)

let SPHI87_FACTS_TAC =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,SPHI87_PLEN),
                        `2 EXP 64`)) ASSUME_TAC THENL
   [MP_TAC SPHI87_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                       mk_comb(`word:num->int64`,SPHI87_PLEN)),
                      SPHI87_PLEN)) ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC SPHI87_LE THEN ARITH_TAC;
    ALL_TAC];;

let SPHI87_SIGN_TAC =
  MAP_EVERY (fun r -> API_DRIVER_TAC
    (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r),
             mk_pair(`word_add bot (word 16486):int64`,SPHI87_PLEN)))
    SPHI87_LE)
   [`word_add bot (word 16478):int64,8`; `word_add bot (word 16470):int64,8`;
    `word_add bot (word 16462):int64,8`; `bot:int64,16462`;
    `sig:int64,4627`] THEN
  X86_STEPS_TAC SPHI87_EXEC (20--29) THEN
  API_NULL_TAC [`sig:int64`,`4627`; `bot:int64`,`16462`] THEN
  API_TERMINATES_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes64 a) s29 = word 0`)
           (concl th)
    then ASSUME_TAC(CONV_RULE(RAND_CONV WORD_REDUCE_CONV)
                      (MATCH_MP SIGN_BYTES32_OF_BYTES64 th))
    else NO_TAC) THEN
  SPHI87_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; SPHI87_PLEN; `read RCX s`; `0`;
    `read R9 s`; `sk:int64`; `word 0:int32`; `skb:num->byte`;
    SPHI87_PRE; `0`; `RND:num`; `MU:num`] 30 THEN
  API_WIDEN_TAC
   [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                          mk_pair(`word_add bot (word 16486):int64`,
                                  SPHI87_PLEN)),
                  `word_add bot (word 16486):int64,332`),
          REWRITE_TAC[contained; CONTAINED_MODULO_REFL;
                      API_PREFIX_LENGTH_LE])] THEN
  X86_STEPS_TAC SPHI87_EXEC (31--33) THEN
  ASM_CASES_TAC `mld_sign_ok_87 skb MU RND` THEN
  API_USE_CASE_TAC `mld_sign_ok_87 skb MU RND` [] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[API_SIGN_OK_DECLASS_87] o
    check (fun th -> concl th = `mld_sign_ok_87 skb MU RND` ||
                     concl th = `~mld_sign_ok_87 skb MU RND`)) THENL
   [X86_STEPS_TAC SPHI87_EXEC (34--34) THEN
    SPHI87_T_STEPS_TAC 34 THEN SPHI87_FINAL_TAC;
    ASSUME_TAC(GEN `t:num` (MP (SPECL [`skb:num->byte`; `MU:num`;
      `RND:num`; `t:num`] (CONJUNCT2(CONJUNCT2 API_SIGN_SIG_FAIL)))
      (ASSUME `~mld_sign_ok_87 skb MU RND`))) THEN
    X86_STEPS_TAC SPHI87_EXEC (34--34) THEN
    SPHI87_Z_STEPS_TAC 34 THEN SPHI87_FINAL_TAC];;

(*** hashalg is not 0: the prefix, -9 if it is rejected ***)

let SPHI87_PREFIX_TAC =
  X86_STEPS_TAC SPHI87_EXEC (15--16) THEN
  SPHI87_CALL_TAC "H_PREFIX"
   [`read RDI s`; `read RSI s`; `phlen:num`; `read RCX s`; `ctxlen:num`;
    `read R9 s`; `C:num`; `PH:num`] 17 THEN
  API_LET_TAC [] [WORD_ZX_ZX_32_64_32] THEN
  ASM_CASES_TAC (mk_eq(SPHI87_PLEN,`0`)) THEN
  API_USE_CASE_TAC (mk_eq(SPHI87_PLEN,`0`)) [] THENL
   [X86_STEPS_TAC SPHI87_EXEC (18--19) THEN
    SPHI87_Z_STEPS_TAC 19 THEN SPHI87_FINAL_TAC;
    SPHI87_FACTS_TAC THEN
    X86_STEPS_TAC SPHI87_EXEC (18--19) THEN SPHI87_SIGN_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether hashalg *)
(* is 0, whether the prefix is rejected and whether signing succeeds.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_INTERNAL" THEN
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       mcb) "H_PREFIX" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms)
     "H_MEMSET") THEN
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
     else if (?n. FST(SND(dcl n)) = 24)
     then f_ev_2 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl mf mc pc
           stackpointer returnaddress
     else f_ev_3 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl mf mc pc
           stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SPHI87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`HA:num`; `PLEN:num`; mk_var("PRE'",`:num`)] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  REALIGN_TAC 16869 THEN REALIGN_FRAME_TAC 16909 16869 THEN
  REALIGN_NONOV_TAC 16838
   [`sig:int64,4627`; `ph:int64,phlen:num`; `ctx:int64,ctxlen:num`;
    `rnd:int64,32`; `sk:int64,4896`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `word(pc + oid_map_ptrs):int64,96`;
    `ea:int64,el:num`; `word_add stackpointer (word 16869):int64,40`;
    `word_add stackpointer (word 16909):int64,24`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC SPHI87_EXEC (1--7) THEN REALIGN_RSP_TAC THEN
  SPHI87_HASHALG_TAC THEN
  X86_STEPS_TAC SPHI87_EXEC (8--14) THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[VAL_EQ_0]) THEN
  API_PC_TAC [`word_zx (hashalg:int64) = (word 0:int32)`] THENL
   [SPHI87_Z_STEPS_TAC 14 THEN SPHI87_FINAL_TAC;
    SPHI87_PREFIX_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_SIGN_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SIGN_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
