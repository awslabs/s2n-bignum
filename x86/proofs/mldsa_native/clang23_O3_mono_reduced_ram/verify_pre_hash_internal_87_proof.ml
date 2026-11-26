(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a pre-hash: the proof (see                       *)
(* verify_pre_hash_internal_87_spec.ml).                                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_pre_hash_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/api_inline.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 15020 bytes of stack below the return address, at           *)
(* stackpointer + 15020, with hashalg above it; the code pushes RBP (the     *)
(* frame pointer), R15, R14 and RBX, from stackpointer + 15012 down to       *)
(* stackpointer + 14988, aligns RSP to 32 bytes, at bot + 14957 (see         *)
(* utils/mldsa_native_realign.ml), and reserves 384 bytes, with RSP at bot + *)
(* 14573, ext, the seventh argument of mldsa87_verify_internal, at RSP, and  *)
(* the prefix at bot + 14605. The call of the prefix has its return address  *)
(* at bot + 14597 and that of mldsa87_verify_internal at bot + 14565, its    *)
(* frame the 14565 bytes at bot. The events before a call are functions of   *)
(* the variables VPHI87_VARS, with bot, which REALIGN_UNBOT_TAC expands at   *)
(* the end.                                                                  *)
(* ------------------------------------------------------------------------- *)


let VPHI87_EXEC =
  MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let VPHI87_VARS =
  [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `hashalg:int64`; `sigb:num->byte`; `pkb:num->byte`;
   `PH:num`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let VPHI87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   VPHI87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   VPHI87_VARS n;;

let VPHI87_PLEN =
  `mld_domain_separation_prefix_length (val(word_zx (hashalg:int64):int32))
     ctxlen phlen`
and VPHI87_PRE =
  `num_of_bytelist(mld_domain_separation_prefix
     (val(word_zx (hashalg:int64):int32))
     (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH))`;;

let VPHI87_LE =
  SPECL [`val(word_zx (hashalg:int64):int32)`; `ctxlen:num`; `phlen:num`]
   VERIF_PREFIX_LENGTH_LE;;

let VPHI87_TEMPLATE =
  `\(sig:int64) (ph:int64) (phlen:num) (ctx:int64) (ctxlen:num) (pk:int64)
    (hashalg:int64) (sigb:num->byte) (pkb:num->byte) (PH:num) (C:num)
    (mf:int64) (mc:int64) (pc:num) (stackpointer:int64)
    (returnaddress:int64).
    if val(word_zx hashalg:int32) = 0
    then f_ev_none sig ph phlen ctx ctxlen pk hashalg mf mc pc stackpointer
          returnaddress
    else if mld_domain_separation_prefix_length (val(word_zx hashalg:int32))
             ctxlen phlen = 0
    then f_ev_rej sig ph phlen ctx ctxlen pk hashalg mf mc pc stackpointer
          returnaddress
    else f_ev_acc sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C mf mc pc
          stackpointer returnaddress
    :(uarch_event)list`;;

(*** hashalg, the 32-bit seventh argument, from its slot on the stack ***)

let VPHI87_HASHALG_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add stackpointer (word 15028))) s =
          (hashalg:int64)`) (concl th)
    then ASSUME_TAC(MATCH_MP VERIF_BYTES32_OF_BYTES64 th) else NO_TAC);;

(*** From join1 at step t: the zeroing of the prefix and the return        ***)

let VPHI87_TAIL_TAC t =
  X86_STEPS_TAC VPHI87_EXEC ((t + 1)--(t + 5)) THEN
  LIBC_PLT_TAC VPHI87_EXEC (layout "plt_memset") (layout "got_memset")
   (t + 5) THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" VPHI87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref VPHI87_VARS) (t + 7) THEN
  X86_STEPS_TAC VPHI87_EXEC ((t + 8)--(t + 20)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(VERIF_RET_TAC THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN VERIF_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** A prefix of PLEN bytes: verification, pre = NULL and mlen = PLEN ***)

let VPHI87_FACTS_TAC =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,VPHI87_PLEN),
                        `2 EXP 64`)) ASSUME_TAC THENL
   [MP_TAC VPHI87_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                       mk_comb(`word:num->int64`,VPHI87_PLEN)),
                      VPHI87_PLEN)) ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC VPHI87_LE THEN ARITH_TAC;
    ALL_TAC];;

let VPHI87_VERIFY_TAC =
  MAP_EVERY (fun b -> VERIF_DRIVER_TAC
    (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                     mk_pair(b,`8`)),
             mk_pair(`word_add bot (word 14605):int64`,VPHI87_PLEN)))
    VPHI87_LE)
   [`word_add bot (word 14573):int64`; `word_add bot (word 14565):int64`] THEN
  X86_STEPS_TAC VPHI87_EXEC (19--26) THEN
  VERIF_NULL_TAC [`bot:int64`,`14565`] THEN
  VERIF_DRIVER_TAC
   (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                    `bot:int64,14565`),
            mk_pair(`word_add bot (word 14605):int64`,VPHI87_PLEN)))
   VPHI87_LE THEN
  VERIF_TERMINATES_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes32 a) s26 = word 0`)
           (concl th)
    then ALL_TAC else NO_TAC) THEN
  VPHI87_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; VPHI87_PLEN; `read RCX s`; `0`;
    `read R9 s`; `word 0:int32`; `sigb:num->byte`; `pkb:num->byte`;
    VPHI87_PRE; `0`] 27 THEN
  VERIF_WIDEN_TAC
   [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                          mk_pair(`word_add bot (word 14605):int64`,
                                  VPHI87_PLEN)),
                  `word_add bot (word 14605):int64,332`),
          REWRITE_TAC[contained; CONTAINED_MODULO_REFL;
                      VERIF_PREFIX_LENGTH_LE])] THEN
  X86_STEPS_TAC VPHI87_EXEC (28--28) THEN
  VPHI87_TAIL_TAC 28;;

(*** hashalg is not 0: the prefix, -9 if it is rejected ***)

let VPHI87_PREFIX_TAC =
  X86_STEPS_TAC VPHI87_EXEC (13--15) THEN
  VERIF_NULL_TAC [`word_add bot (word 14605):int64`,`332`;
                  `word_add bot (word 14549):int64`,`64`] THEN
  VPHI87_CALL_TAC "H_PREFIX"
   [`read RDI s`; `read RSI s`; `phlen:num`; `read RCX s`; `ctxlen:num`;
    `read R9 s`; `C:num`; `PH:num`] 16 THEN
  VERIF_LET_TAC [] [WORD_ZX_ZX_32_64_32] THEN
  ASM_CASES_TAC (mk_eq(VPHI87_PLEN,`0`)) THEN
  VERIF_USE_CASE_TAC (mk_eq(VPHI87_PLEN,`0`)) [] THENL
   [X86_STEPS_TAC VPHI87_EXEC (17--18) THEN VPHI87_TAIL_TAC 18;
    VPHI87_FACTS_TAC THEN
    X86_STEPS_TAC VPHI87_EXEC (17--18) THEN VPHI87_VERIFY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether hashalg *)
(* is 0 and whether the prefix is rejected.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_INTERNAL" THEN
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       mcb) "H_PREFIX" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms)
     "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC VPHI87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst VPHI87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`HA:num`; `PLEN:num`; mk_var("PRE'",`:num`)] THEN
  REALIGN_TAC 14988 THEN REALIGN_FRAME_TAC 15020 14988 THEN
  REALIGN_NONOV_TAC 14957
   [`sig:int64,4627`; `ph:int64,phlen:num`; `ctx:int64,ctxlen:num`;
    `pk:int64,2592`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `word(pc + oid_map_ptrs):int64,96`;
    `ea:int64,el:num`; `word_add stackpointer (word 14988):int64,32`;
    `word_add stackpointer (word 15020):int64,16`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC VPHI87_EXEC (1--6) THEN REALIGN_RSP_TAC THEN
  VPHI87_HASHALG_TAC THEN
  X86_STEPS_TAC VPHI87_EXEC (7--12) THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[VAL_EQ_0]) THEN
  VERIF_PC_TAC [`word_zx (hashalg:int64) = (word 0:int32)`] THENL
   [VPHI87_TAIL_TAC 12;
    VPHI87_PREFIX_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
      MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
      MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
