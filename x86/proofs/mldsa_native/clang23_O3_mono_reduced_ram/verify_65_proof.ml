(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a message (pure ML-DSA): the proof (see          *)
(* verify_65_spec.ml).                                                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/api_inline.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 12540 bytes of stack below the return address, at           *)
(* stackpointer + 12540; the code pushes RBP (the frame pointer), R15, R14,  *)
(* R13, R12 and RBX, from stackpointer + 12532 down to stackpointer + 12492, *)
(* aligns RSP to 32 bytes, at bot + 12461 (see                               *)
(* utils/mldsa_native_realign.ml), and reserves 416 bytes, with RSP at bot + *)
(* 12045, ext, the seventh argument of mldsa65_verify_internal, at RSP, and  *)
(* the prefix at bot + 12077. The call of mldsa65_verify_internal has its    *)
(* return address at bot + 12037, its frame the 12037 bytes at bot. The      *)
(* events before a call are functions of the variables VER65_VARS, with bot, *)
(* which REALIGN_UNBOT_TAC expands at the end.                               *)
(* ------------------------------------------------------------------------- *)


let VER65_EXEC = MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let VER65_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `C:num`;
   `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let VER65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   VER65_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   VER65_VARS n;;

let VER65_TEMPLATE =
  `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (pk:int64)
    (sigb:num->byte) (pkb:num->byte) (M:num) (C:num) (mf:int64) (mc:int64)
    (pc:num) (stackpointer:int64) (returnaddress:int64).
    if 255 < ctxlen
    then f_ev_rej sig m mlen ctx ctxlen pk mf mc pc stackpointer
          returnaddress
    else if ctxlen = 0
    then f_ev_nul sig m mlen ctx ctxlen pk sigb pkb M C mf mc pc stackpointer
          returnaddress
    else f_ev_acc sig m mlen ctx ctxlen pk sigb pkb M C mf mc pc stackpointer
          returnaddress
    :(uarch_event)list`;;

(*** The call of memset at step c, zeroing the prefix, and the return from ***)
(*** step c + 3 ***)

let VER65_TAIL_STEPS_TAC c =
  LIBC_PLT_TAC VER65_EXEC (layout "plt_memset") (layout "got_memset") c THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" VER65_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref VER65_VARS) (c + 2) THEN
  X86_STEPS_TAC VER65_EXEC ((c + 3)--(c + 17));;

let VER65_FINAL_TAC ths =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC ths THEN
  REPEAT CONJ_TAC THEN TRY(VERIF_RET_TAC THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN VERIF_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let VER65_TAIL_TAC ths c = VER65_TAIL_STEPS_TAC c THEN VER65_FINAL_TAC ths;;

let VER65_PREFIX0_TAC c =
  MP_TAC(SPECL [mk_var("s"^string_of_int c,`:x86state`);
                `word_add bot (word 12077):int64`; `0`; `0`]
               API_PREFIX_BYTES) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                     ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; API_WORD_MOD_256]; DISCH_TAC];;

let VER65_VERIFY0_TAC c =
  VER65_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `mlen:num`; `read RCX s`; `2`;
    `read R9 s`; `word 0:int32`;
    `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    `num_of_bytelist(mld_domain_separation_prefix 0
       (bytelist_of_num 0 0) [])`] (c + 1);;

let VER65_PREFIX_TAC c =
  MP_TAC(SPECL [mk_var("s"^string_of_int c,`:x86state`);
                `word_add bot (word 12077):int64`; `ctxlen:num`; `C:num`]
               API_PREFIX_BYTES) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                     ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; API_WORD_MOD_256]; DISCH_TAC];;

let VER65_VERIFY_TAC c =
  VER65_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `mlen:num`; `read RCX s`; `2 + ctxlen`;
    `read R9 s`; `word 0:int32`;
    `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    `num_of_bytelist(mld_domain_separation_prefix 0
       (bytelist_of_num ctxlen C) [])`] (c + 1);;

(*** ctxlen > 255: the result is -9 ***)

let VER65_REJ_TAC =
  X86_STEPS_TAC VER65_EXEC (13--17) THEN VER65_TAIL_TAC [] 17;;

(*** ctxlen = 0: the prefix is the two bytes 0 and 0 ***)

let VER65_ZERO_TAC =
  SUBGOAL_THEN `C = 0` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes(ctx,ctxlen)) s12 = C` THEN
    ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `C = 0`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`)) THEN
  X86_STEPS_TAC VER65_EXEC (13--20) THEN
  VER65_PREFIX0_TAC 20 THEN
  VER65_VERIFY0_TAC 20 THEN
  X86_STEPS_TAC VER65_EXEC (22--27) THEN VER65_TAIL_TAC [ADD_CLAUSES] 27;;

(*** 0 < ctxlen <= 255: the context is copied with memcpy ***)

let VER65_COPY_TAC =
  SUBGOAL_THEN `val(word ctxlen:int64) = ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X86_STEPS_TAC VER65_EXEC (13--26) THEN
  LIBC_PLT_TAC VER65_EXEC (layout "plt_memcpy") (layout "got_memcpy") 26 THEN
  LIBC_FULL_CALL_TAC "H_MEMCPY" VER65_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `C:num`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref VER65_VARS) 28 THEN
  X86_STEPS_TAC VER65_EXEC (29--37) THEN
  SUBGOAL_THEN `word_add (word ctxlen:int64) (word 2) = word (2 + ctxlen)`
  ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  VER65_PREFIX_TAC 37 THEN
  VER65_VERIFY_TAC 37 THEN
  X86_STEPS_TAC VER65_EXEC (39--44) THEN VER65_TAIL_TAC [] 44;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long and whether it is empty.                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_INTERNAL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms)
     "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] mcb)
     "H_MEMCPY") THEN
  CONCRETIZE_F_EVENTS_TAC VER65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst VER65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 12492 THEN REALIGN_FRAME_TAC 12540 12492 THEN
  REALIGN_NONOV_TAC 12461
   [`sig:int64,3309`; `m:int64,mlen:num`; `ctx:int64,ctxlen:num`;
    `pk:int64,1952`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 12492):int64,48`;
    `word_add stackpointer (word 12540):int64,8`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC VER65_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC VER65_EXEC (9--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP API_JA_255 (ASSUME `ctxlen < 2 EXP 64`);
                              NOT_LE]) THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  VERIF_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [VER65_REJ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 + ctxlen):int64) = 2 + ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  VERIF_MP_TAC `ctxlen <= 255` THEN
  ASM_CASES_TAC `ctxlen = 0` THENL [VER65_ZERO_TAC; VER65_COPY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
