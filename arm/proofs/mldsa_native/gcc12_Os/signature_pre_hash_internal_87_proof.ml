(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a pre-hash (HashML-DSA): the proof (see                           *)
(* signature_pre_hash_internal_87_spec.ml).                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/signature_pre_hash_internal_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_6_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The bytes of a region that is zero (mld_zeroize leaves a number 0).       *)
(* ------------------------------------------------------------------------- *)

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
(* The calls. The frame of 416 bytes is at stackpointer + 112096, with the   *)
(* prefix in the buffer at stackpointer + kb, kb = 112160 or 112144 (aligned *)
(* to 32), and the canary at + 112504. The events before a call are          *)
(* functions of the variables MLD_SPHI87_VARS (those of the signing being    *)
(* the arguments of its events). HA, PLEN and PRE are replaced by their      *)
(* definitions, the length MLD_SPHI87_PLEN and the prefix MLD_SPHI87_PRE.    *)
(* ------------------------------------------------------------------------- *)

let MLD_SPHI87_EXEC =
  MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_EXEC;;

let MLD_SPHI87_VARS =
  [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
   `rnd:int64`; `sk:int64`; `hashalg:int64`; `skb:num->byte`; `MU:num`;
   `RND:num`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `kb:num`];;

let MLD_SPHI87_PLEN =
  `mld_domain_separation_prefix_length (val(word_zx (hashalg:int64):int32))
     ctxlen phlen`
and MLD_SPHI87_PRE =
  `num_of_bytelist(mld_domain_separation_prefix
     (val(word_zx (hashalg:int64):int32))
     (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH))`;;

let MLD_SPHI87_LE =
  SPECL [`val(word_zx (hashalg:int64):int32)`; `ctxlen:num`; `phlen:num`]
   MLD_WRAP_PREFIX_LENGTH_LE;;

(*** The call of mld_zeroize on len bytes at X0, whose arguments are set by
     the steps k, k + 1 and k + 2 (the call is at step k + 3) ***)

let MLD_SPHI87_ZERO_TAC k len =
  ARM_STEPS_TAC MLD_SPHI87_EXEC (k--(k + 2)) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MLD_SPHI87_EXEC "H_ZERO"
   [`read X0 s`; mk_small_numeral len; `pc:num`; `read SP s`; `read X30 s`]
   MLD_SPHI87_VARS (k + 3);;

(*** The end of a path ***)

let MLD_SPHI87_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT] THEN
  REPEAT CONJ_TAC THEN TRY(MLD_WRAP_RET_TAC THEN NO_TAC) THEN
  TRY((X_GEN_TAC `t:num` THEN DISCH_TAC THEN
       FIRST_ASSUM(MP_TAC o SPEC `t:num` o MATCH_MP SIGN_BYTES_ZERO o check
        (can (term_match [`sig:int64`] `read (memory :> bytes(sig,4627)) s = 0`)
         o concl)) THEN
       ASM_REWRITE_TAC[]) THEN NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_87 skb MU RND` THEN
  MLD_WRAP_DISCHARGE_TAC;;

(*** From the zeroing of the prefix (332 bytes) at step j to the return ***)

let MLD_SPHI87_R_TAC j =
  MLD_SPHI87_ZERO_TAC j 332 THEN
  ARM_STEPS_TAC MLD_SPHI87_EXEC ((j + 4)--(j + 4)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SPHI87_EXEC ((j + 5)--(j + 15)) THEN
  MLD_SPHI87_FINAL_TAC;;

(*** From the zeroing of the signature at step k to the return ***)

let MLD_SPHI87_Z_TAC k =
  MLD_SPHI87_ZERO_TAC k 4627 THEN
  ARM_STEPS_TAC MLD_SPHI87_EXEC ((k + 4)--(k + 4)) THEN MLD_SPHI87_R_TAC (k + 5);;

(*** A prefix of PLEN bytes: signing it as the message, pre = NULL ***)

let MLD_SPHI87_SIGN_TAC =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,MLD_SPHI87_PLEN),
                        `2 EXP 64`)) ASSUME_TAC THENL
   [MP_TAC MLD_SPHI87_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                       mk_comb(`word:num->int64`,MLD_SPHI87_PLEN)),
                      MLD_SPHI87_PLEN)) ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC MLD_SPHI87_LE THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLD_SPHI87_EXEC (19--28) THEN
  MLD_WRAP_GOT_TAC THEN
  MLD_WRAP_NULL_TAC [`sig:int64`,`4627`; `stackpointer:int64`,`112512`] THEN
  MLD_WRAP_TERMINATES_TAC THEN
  ASSUME_TAC(INST_TYPE [`:64`,`:M`; `:32`,`:N`] WORD_ZX_0) THEN
  MAP_EVERY (fun r -> MLD_WRAP_DRIVER_TAC
   (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r),
            mk_pair(`word_add stackpointer (word kb):int64`,
                    MLD_SPHI87_PLEN)))
   MLD_SPHI87_LE) [`sig:int64,4627`; `stackpointer:int64,112096`] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MLD_SPHI87_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; MLD_SPHI87_PLEN; `read X3 s`; `0`;
    `read X5 s`; `read X6 s`; `read X7 s`; `skb:num->byte`;
    MLD_SPHI87_PRE; `0`; `RND:num`; `MU:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] MLD_SPHI87_VARS 29 THEN
  MLD_WRAP_WIDEN_TAC
   [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                          mk_pair(`word_add stackpointer (word kb):int64`,
                                  MLD_SPHI87_PLEN)),
                  `word_add stackpointer (word kb):int64,332`),
          REWRITE_TAC[contained; CONTAINED_MODULO_REFL;
                      MLD_WRAP_PREFIX_LENGTH_LE])] THEN
  ASM_CASES_TAC `mld_sign_ok_87 skb MU RND` THEN
  MLD_WRAP_USE_CASE_TAC `mld_sign_ok_87 skb MU RND` [] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[MLD_WRAP_SIGN_OK_DECLASS_87] o
    check (fun th -> concl th = `mld_sign_ok_87 skb MU RND` ||
                     concl th = `~mld_sign_ok_87 skb MU RND`)) THENL
   [ARM_STEPS_TAC MLD_SPHI87_EXEC (30--31) THEN MLD_SPHI87_R_TAC 32;
    ASSUME_TAC(GEN `t:num` (MP (SPECL [`skb:num->byte`; `MU:num`;
      `RND:num`; `t:num`] (CONJUNCT2(CONJUNCT2 MLD_WRAP_SIGN_SIG_FAIL)))
      (ASSUME `~mld_sign_ok_87 skb MU RND`))) THEN
    ARM_STEPS_TAC MLD_SPHI87_EXEC (30--31) THEN MLD_SPHI87_Z_TAC 32];;

(*** hashalg is not 0: the prefix, -9 if it is rejected ***)

let MLD_SPHI87_PREFIX_TAC =
  ARM_STEPS_TAC MLD_SPHI87_EXEC (13--17) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MLD_SPHI87_EXEC "H_PREFIX"
   [`read X0 s`; `read X1 s`; `phlen:num`; `read X3 s`; `ctxlen:num`;
    `read X5 s`; `C:num`; `PH:num`; `pc:num`; `read SP s`; `read X30 s`]
   MLD_SPHI87_VARS 18 THEN
  MLD_WRAP_LET_TAC [] [MLD_PREFIX_ZX_ZX] THEN
  ASM_CASES_TAC (mk_eq(MLD_SPHI87_PLEN,`0`)) THEN
  MLD_WRAP_USE_CASE_TAC (mk_eq(MLD_SPHI87_PLEN,`0`)) [] THENL
   [ARM_STEPS_TAC MLD_SPHI87_EXEC (19--21) THEN MLD_SPHI87_Z_TAC 22;
    MLD_SPHI87_SIGN_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether hashalg *)
(* is 0, whether the prefix is rejected and whether signing succeeds (which  *)
(* the events give as what it declassifies), and at the end of each on       *)
(* whether the stack pointer is a multiple of 32, which gives the address of *)
(* the buffer.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_OS_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_ZEROIZE_6_GCC12_OS_IMAGE_SUBROUTINE_FULL ms)
     "H_ZERO") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (ph:int64) (phlen:num) (ctx:int64) (ctxlen:num) (rnd:int64)
     (sk:int64) (hashalg:int64) (rho:num)
     (dcl:num->num#num#(num->int32)#(num->byte)) (guard:int64) (mf:int64)
     (mc:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if val(word_zx hashalg:int32) = 0
       then f_ev_a0 sig ph phlen ctx ctxlen rnd sk hashalg guard mf mc pc sp ra
       else if mld_domain_separation_prefix_length
                (val(word_zx hashalg:int32)) ctxlen phlen = 0
       then f_ev_a1 sig ph phlen ctx ctxlen rnd sk hashalg guard mf mc pc sp ra
       else if (?n. FST(SND(dcl n)) = 24)
       then f_ev_a2 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl guard mf mc
             pc sp ra
       else f_ev_a3 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl guard mf mc
             pc sp ra
     else
       if val(word_zx hashalg:int32) = 0
       then f_ev_u0 sig ph phlen ctx ctxlen rnd sk hashalg guard mf mc pc sp ra
       else if mld_domain_separation_prefix_length
                (val(word_zx hashalg:int32)) ctxlen phlen = 0
       then f_ev_u1 sig ph phlen ctx ctxlen rnd sk hashalg guard mf mc pc sp ra
       else if (?n. FST(SND(dcl n)) = 24)
       then f_ev_u2 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl guard mf mc
             pc sp ra
       else f_ev_u3 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl guard mf mc
             pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `ph:int64`; `phlen:num`;
    `ctx:int64`; `ctxlen:num`; `rnd:int64`; `sk:int64`; `hashalg:int64`;
    `skb:num->byte`; `PH:num`; `C:num`; `RND:num`; `HA:num`; `PLEN:num`;
    mk_var("PRE",`:num`); `MU:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 112512 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_SPHI87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`HA:num`; `PLEN:num`; mk_var("PRE",`:num`)] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  MLD_WRAP_FRAME_TAC 112512 [`got_stack_chk_guard:num`]
   (19--22) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_SPHI87_EXEC (1--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SPHI87_EXEC (6--12) THEN MLD_WRAP_SYMBUF_TAC `kb:num` THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THENL
   [ARM_STEPS_TAC MLD_SPHI87_EXEC (13--14) THEN MLD_SPHI87_Z_TAC 15;
    MLD_SPHI87_PREFIX_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
