(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the proof (see               *)
(* signature_87_spec.ml).                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/api_inline.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 17013 bytes of stack below the return address, at           *)
(* stackpointer + 17013; the code pushes RBP (the frame pointer), R15, R14,  *)
(* R13, R12 and RBX, from stackpointer + 12621 down to stackpointer + 16965, *)
(* aligns RSP to 32 bytes, at bot + 16934 (see                               *)
(* utils/mldsa_native_realign.ml), and reserves 448 bytes, with RSP at bot + *)
(* 16486, the saved m at RSP + 0x18, rnd at bot + 16518 and the prefix at    *)
(* bot + 16550. mldsa87_signature_internal is called with sk and ext = 0     *)
(* pushed above its return address, at bot + 16462, its frame the 16462      *)
(* bytes at bot. The events before a call are functions of the variables     *)
(* SG87_VARS, with bot, which REALIGN_UNBOT_TAC expands at the end.          *)
(* ------------------------------------------------------------------------- *)


let SG87_EXEC = MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let SG87_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `sk:int64`; `skb:num->byte`; `M:num`; `C:num`; `MU:num`; `RND:num`;
   `mf:int64`; `mc:int64`; `mr:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let SG87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   SG87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   SG87_VARS n;;

(*** The events: by the context length (too long, empty or not), and by    ***)
(*** the result (-3 if randombytes fails, 0 or -4 from signing)            ***)

let SG87_TEMPLATE =
  `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (sk:int64)
    (rho:num) (r:int64) (dcl:num->num#num#(num->int32)#(num->byte))
    (mf:int64) (mc:int64) (mr:int64) (pc:num) (stackpointer:int64)
    (returnaddress:int64).
    if 255 < ctxlen
    then f_ev_0 sig m mlen ctx ctxlen sk mf mc mr pc stackpointer
          returnaddress
    else if ctxlen = 0
    then (if r = word 4294967293
          then f_ev_1z sig m mlen ctx ctxlen sk mf mc mr pc stackpointer
                returnaddress
          else if r = word 0
          then f_ev_2z sig m mlen ctx ctxlen sk rho dcl mf mc mr pc
                stackpointer returnaddress
          else f_ev_3z sig m mlen ctx ctxlen sk rho dcl mf mc mr pc
                stackpointer returnaddress)
    else (if r = word 4294967293
          then f_ev_1 sig m mlen ctx ctxlen sk mf mc mr pc stackpointer
                returnaddress
          else if r = word 0
          then f_ev_2 sig m mlen ctx ctxlen sk rho dcl mf mc mr pc
                stackpointer returnaddress
          else f_ev_3 sig m mlen ctx ctxlen sk rho dcl mf mc mr pc
                stackpointer returnaddress)
    :(uarch_event)list`;;

(*** The call of memset at step c: the registers RDI, RSI and RDX are its  ***)
(*** arguments; the state after it is c + 2                                ***)

let SG87_MEMSET_TAC c =
  LIBC_PLT_TAC SG87_EXEC (layout "plt_memset") (layout "got_memset") c THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" SG87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref SG87_VARS) (c + 2);;

(*** From the state t at the entry of the zeroing of the prefix: memset,   ***)
(*** the result and the return (15 instructions)                           ***)

let SG87_T_STEPS_TAC t =
  X86_STEPS_TAC SG87_EXEC ((t + 1)--(t + 1)) THEN
  API_ALIGN_TAC ("s" ^ string_of_int (t + 1)) 16486 48 THEN
  API_ALIGN_TAC ("s" ^ string_of_int (t + 1)) 16486 32 THEN
  X86_STEPS_TAC SG87_EXEC ((t + 2)--(t + 9)) THEN
  SG87_MEMSET_TAC (t + 9) THEN
  X86_STEPS_TAC SG87_EXEC ((t + 12)--(t + 26));;

(*** From the state c at the entry of the zeroing of the signature         ***)

let SG87_Z_STEPS_TAC c =
  X86_STEPS_TAC SG87_EXEC ((c + 1)--(c + 4)) THEN
  SG87_MEMSET_TAC (c + 4) THEN
  API_MEMSET_BYTES_TAC THEN
  SG87_T_STEPS_TAC (c + 6);;

(*** The end of a path with the random bytes RND (any number if            ***)
(*** randombytes was not called) and the result in RAX                     ***)

let SG87_FINAL_TAC rnd =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC rnd THEN
  ASM_REWRITE_TAC[API_SIGN_DISTINCT; API_SIGN_RET; GSYM NOT_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_BYTES8_ZERO THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_87 skb MU RND` THEN
  REALIGN_UNBOT_TAC THEN API_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let SG87_PREFIX_TAC c =
  MP_TAC(SPECL [mk_var("s"^string_of_int c,`:x86state`);
                `word_add bot (word 16550):int64`; `ctxlen:num`; `C:num`]
               API_PREFIX_BYTES) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                     ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; API_WORD_MOD_256]; DISCH_TAC];;

let SG87_PREFIX0_TAC c =
  MP_TAC(SPECL [mk_var("s"^string_of_int c,`:x86state`);
                `word_add bot (word 16550):int64`; `0`; `0`]
               API_PREFIX_BYTES) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                     ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL; API_WORD_MOD_256]; DISCH_TAC];;


let SG87_J1Z_TAC =
  X86_STEPS_TAC SG87_EXEC (22--24) THEN
  LIBC_PLT_TAC SG87_EXEC (layout "plt_randombytes")
   (layout "got_randombytes") 24 THEN
  LIBC_FULL_CALL_TAC "H_RANDOMBYTES" SG87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   (ref SG87_VARS) 26 THEN
  ABBREV_TAC `rv = read RAX s26` THEN
  API_RANDOM_TAC `RND:num` `word_add bot (word 16518):int64` 32
   `s26:x86state` THEN
  X86_STEPS_TAC SG87_EXEC (27--29) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [X86_STEPS_TAC SG87_EXEC (30--39) THEN
    FIRST_ASSUM(fun th ->
      try STRIP_ASSUME_TAC
           (MP (SPEC `RND:num` th) (ASSUME `RND < 2 EXP 256`))
      with Failure _ -> NO_TAC) THEN
    SG87_PREFIX0_TAC 39 THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes64 a) s39 = word 0`)
             (concl th)
      then ASSUME_TAC(CONV_RULE(RAND_CONV WORD_REDUCE_CONV)
                        (MATCH_MP SIGN_BYTES32_OF_BYTES64 th))
      else NO_TAC) THEN
    SG87_CALL_TAC "H_INTERNAL"
     [`read RDI s`; `read RSI s`; `mlen:num`; `read RCX s`; `2`;
      `read R9 s`; `sk:int64`; `word 0:int32`; `skb:num->byte`; `M:num`;
      `num_of_bytelist(mld_domain_separation_prefix 0
         (bytelist_of_num 0 0) [])`;
      `RND:num`; `MU:num`] 40 THEN
    X86_STEPS_TAC SG87_EXEC (41--43) THEN
    ASM_CASES_TAC `mld_sign_ok_87 skb MU RND` THEN
    API_USE_CASE_TAC `mld_sign_ok_87 skb MU RND` [] THENL
     [X86_STEPS_TAC SG87_EXEC (44--46) THEN
      SG87_T_STEPS_TAC 46 THEN SG87_FINAL_TAC `RND:num`;
      X86_STEPS_TAC SG87_EXEC (44--44) THEN
      SG87_Z_STEPS_TAC 44 THEN SG87_FINAL_TAC `RND:num`];
    X86_STEPS_TAC SG87_EXEC (30--30) THEN
    SG87_Z_STEPS_TAC 30 THEN SG87_FINAL_TAC `0`];;

let SG87_J1N_TAC =
  X86_STEPS_TAC SG87_EXEC (28--30) THEN
  LIBC_PLT_TAC SG87_EXEC (layout "plt_randombytes")
   (layout "got_randombytes") 30 THEN
  LIBC_FULL_CALL_TAC "H_RANDOMBYTES" SG87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   (ref SG87_VARS) 32 THEN
  ABBREV_TAC `rv = read RAX s32` THEN
  API_RANDOM_TAC `RND:num` `word_add bot (word 16518):int64` 32
   `s32:x86state` THEN
  X86_STEPS_TAC SG87_EXEC (33--35) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [X86_STEPS_TAC SG87_EXEC (36--45) THEN
    FIRST_ASSUM(fun th ->
      try STRIP_ASSUME_TAC
           (MP (SPEC `RND:num` th) (ASSUME `RND < 2 EXP 256`))
      with Failure _ -> NO_TAC) THEN
    SG87_PREFIX_TAC 45 THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes64 a) s45 = word 0`)
             (concl th)
      then ASSUME_TAC(CONV_RULE(RAND_CONV WORD_REDUCE_CONV)
                        (MATCH_MP SIGN_BYTES32_OF_BYTES64 th))
      else NO_TAC) THEN
    SUBGOAL_THEN `word_add (word ctxlen) (word 2):int64 = word(2 + ctxlen)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SG87_CALL_TAC "H_INTERNAL"
     [`read RDI s`; `read RSI s`; `mlen:num`; `read RCX s`; `2 + ctxlen`;
      `read R9 s`; `sk:int64`; `word 0:int32`; `skb:num->byte`; `M:num`;
      `num_of_bytelist(mld_domain_separation_prefix 0
         (bytelist_of_num ctxlen C) [])`;
      `RND:num`; `MU:num`] 46 THEN
    X86_STEPS_TAC SG87_EXEC (47--49) THEN
    ASM_CASES_TAC `mld_sign_ok_87 skb MU RND` THEN
    API_USE_CASE_TAC `mld_sign_ok_87 skb MU RND` [] THENL
     [X86_STEPS_TAC SG87_EXEC (50--52) THEN
      SG87_T_STEPS_TAC 52 THEN SG87_FINAL_TAC `RND:num`;
      X86_STEPS_TAC SG87_EXEC (50--50) THEN
      SG87_Z_STEPS_TAC 50 THEN SG87_FINAL_TAC `RND:num`];
    X86_STEPS_TAC SG87_EXEC (36--36) THEN
    SG87_Z_STEPS_TAC 36 THEN SG87_FINAL_TAC `0`];;


(*** ctxlen > 255: the result is -9 ***)

let SG87_REJ_TAC =
  SG87_Z_STEPS_TAC 13 THEN SG87_FINAL_TAC `0`;;

(*** ctxlen = 0: the prefix is the two bytes 0 and 0 ***)

let SG87_ZERO_TAC =
  SUBGOAL_THEN `C = 0` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes(ctx,ctxlen)) s13 = C` THEN
    ASM_REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `C = 0`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  X86_STEPS_TAC SG87_EXEC (14--21) THEN
  SG87_J1Z_TAC;;

(*** 0 < ctxlen <= 255: the context is copied with memcpy ***)

let SG87_COPY_TAC =
  SUBGOAL_THEN `val(word ctxlen:int64) = ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X86_STEPS_TAC SG87_EXEC (14--25) THEN
  LIBC_PLT_TAC SG87_EXEC (layout "plt_memcpy") (layout "got_memcpy") 25 THEN
  LIBC_FULL_CALL_TAC "H_MEMCPY" SG87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `C:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref SG87_VARS) 27 THEN
  SG87_J1N_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long, whether randombytes succeeds and whether signing     *)
(* does.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,rest = CONJ_PAIR th in
    let mcb,mrb = CONJ_PAIR rest in
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       (CONJ ms mcb)) "H_INTERNAL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms)
     "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] mcb)
     "H_MEMCPY" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC SG87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SG87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhand(concl th) = `MU:num`)) THEN
  REALIGN_TAC 16965 THEN REALIGN_FRAME_TAC 17013 16965 THEN
  REALIGN_NONOV_TAC 16934
   [`sig:int64,4627`; `m:int64,mlen:num`; `ctx:int64,ctxlen:num`;
    `sk:int64,4896`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `word(pc + got_randombytes):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 16965):int64,48`;
    `word_add stackpointer (word 17013):int64,8`] THEN
  REALIGN_ALIGNED_TAC [16518; 16534] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC SG87_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SG87_EXEC (9--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP API_JA_255 (ASSUME `ctxlen < 2 EXP 64`);
                              NOT_LE]) THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  API_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [SG87_REJ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 + ctxlen):int64) = 2 + ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  API_MP_TAC `ctxlen <= 255` THEN
  ASM_CASES_TAC `ctxlen = 0` THENL [SG87_ZERO_TAC; SG87_COPY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_SIGN_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SIGN_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
