(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a pre-hash: the proof (see                       *)
(* verify_pre_hash_internal_87_spec.ml).                                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_internal_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame is realigned to 32 bytes below the entry RSP (with   *)
(* REALIGN_TAC k = N, as the AND comes first): RBP at bot + 74773, the       *)
(* prefix and RSP at bot + 74373, and mldsa87_verify_internal called with    *)
(* RSP at bot + 74349, its frame the 74349 bytes at bot. The events before a *)
(* call are functions of the variables VPHI87_VARS, with bot, which          *)
(* REALIGN_UNBOT_TAC expands at the end. HA, PLEN and PRE are replaced by    *)
(* their definitions, the length VPHI87_PLEN and the prefix VPHI87_PRE.      *)
(* ------------------------------------------------------------------------- *)

let VPHI87_EXEC = MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_EXEC;;

let VPHI87_VARS =
  [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `hashalg:int64`; `sigb:num->byte`; `pkb:num->byte`;
   `PH:num`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let VPHI87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc VPHI87_EXEC name
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
         `read (memory :> bytes64 (word_add stackpointer (word 74828))) s =
          (hashalg:int64)`) (concl th)
    then ASSUME_TAC(MATCH_MP VERIF_BYTES32_OF_BYTES64 th) else NO_TAC);;

(*** That the pushes before the call do not overlap the prefix ***)

let VPHI87_NONOV_TAC b =
  VERIF_DRIVER_TAC
   (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                    mk_pair(b,`8`)),
            mk_pair(`word_add bot (word 74373):int64`,VPHI87_PLEN)))
   VPHI87_LE;;

(*** From join1 at step k: the zeroing of the prefix and the return ***)

let VPHI87_TAIL_TAC k =
  X86_STEPS_TAC VPHI87_EXEC (k--(k + 13)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(VERIF_RET_TAC THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN VERIF_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** A prefix of PLEN bytes: verification, pre = NULL and mlen = PLEN ***)

let VPHI87_VERIFY_TAC =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,VPHI87_PLEN),
                        `2 EXP 64`)) ASSUME_TAC THENL
   [MP_TAC VPHI87_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                       mk_comb(`word:num->int64`,VPHI87_PLEN)),
                      VPHI87_PLEN)) ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC VPHI87_LE THEN ARITH_TAC;
    ALL_TAC] THEN
  VPHI87_NONOV_TAC `word_add bot (word 74357):int64` THEN
  VPHI87_NONOV_TAC `word_add bot (word 74349):int64` THEN
  X86_STEPS_TAC VPHI87_EXEC (20--30) THEN
  VERIF_NULL_TAC [`bot:int64`,`74349`] THEN
  VERIF_DRIVER_TAC
   (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                    `bot:int64,74349`),
            mk_pair(`word_add bot (word 74373):int64`,VPHI87_PLEN)))
   VPHI87_LE THEN
  VERIF_TERMINATES_TAC THEN
  VPHI87_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; VPHI87_PLEN; `read RCX s`; `0`;
    `read R9 s`; `word 0:int64`; `sigb:num->byte`; `pkb:num->byte`;
    VPHI87_PRE; `0`] 31 THEN
  VERIF_WIDEN_TAC
   [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                          mk_pair(`word_add bot (word 74373):int64`,
                                  VPHI87_PLEN)),
                  `word_add bot (word 74373):int64,332`),
          REWRITE_TAC[contained; CONTAINED_MODULO_REFL;
                      VERIF_PREFIX_LENGTH_LE])] THEN
  X86_STEPS_TAC VPHI87_EXEC (32--34) THEN
  VPHI87_TAIL_TAC 35;;

(*** hashalg is not 0: the prefix, -9 if it is rejected ***)

let VPHI87_PREFIX_TAC =
  X86_STEPS_TAC VPHI87_EXEC (15--18) THEN
  VERIF_NULL_TAC [`word_add bot (word 74373):int64`,`332`;
                  `word_add bot (word 74301):int64`,`64`] THEN
  VPHI87_CALL_TAC "H_PREFIX"
   [`read RDI s`; `read RSI s`; `phlen:num`; `read RCX s`; `ctxlen:num`;
    `read R9 s`; `C:num`; `PH:num`] 19 THEN
  VERIF_LET_TAC [] [WORD_ZX_ZX_32_64_32] THEN
  ASM_CASES_TAC (mk_eq(VPHI87_PLEN,`0`)) THEN
  VERIF_USE_CASE_TAC (mk_eq(VPHI87_PLEN,`0`)) [] THENL
   [X86_STEPS_TAC VPHI87_EXEC (20--24) THEN VPHI87_TAIL_TAC 25;
    VPHI87_VERIFY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether hashalg *)
(* is 0 and whether the prefix is rejected.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
               ms) "H_INTERNAL" THEN
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX") THEN
  CONCRETIZE_F_EVENTS_TAC VPHI87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst VPHI87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`HA:num`; `PLEN:num`; mk_var("PRE'",`:num`)] THEN
  REALIGN_TAC 74820 THEN REALIGN_FRAME_TAC 74820 74820 THEN
  REALIGN_NONOV_TAC 74789
   [`sig:int64,4627`; `ph:int64,phlen:num`; `ctx:int64,ctxlen:num`;
    `pk:int64,2592`; `word pc:int64,51232`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 74820):int64,8`;
    `word_add stackpointer (word 74828):int64,8`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC VPHI87_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC VPHI87_EXEC (3--11) THEN VPHI87_HASHALG_TAC THEN
  X86_STEPS_TAC VPHI87_EXEC (12--14) THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[VAL_EQ_0]) THEN
  VERIF_PC_TAC [`word_zx (hashalg:int64) = (word 0:int32)`] THENL
   [X86_STEPS_TAC VPHI87_EXEC (15--17) THEN VPHI87_TAIL_TAC 18;
    VPHI87_PREFIX_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
      MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
      MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
