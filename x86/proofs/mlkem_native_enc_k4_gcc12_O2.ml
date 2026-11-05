(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-1024 (FIPS 203 Algorithm 20). This is the     *)
(* code for mlkem1024_enc from mlkem-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It gets 32      *)
(* random bytes with randombytes, through its PLT stub and GOT entry, into a *)
(* buffer on the stack, and returns -3 if that fails, and otherwise          *)
(* encapsulates with them as the message with mlkem1024_enc_derand. In both  *)
(* cases it zeroes the buffer. It is verified in the whole image (see        *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x1c20, using  *)
(* the theorem for mlkem1024_enc_derand in the image and the contract for    *)
(* randombytes (see utils/mlkem_native_libc.ml).                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_enc_derand_k4_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_libc.ml";;

(*** The code in the image:

    1010: jmp    QWORD PTR [rip+0x9fe2]
 ***)

(*** The code in the image:

    1c20: push   rbp
    1c21: mov    rbp,rsp
    1c24: push   r14
    1c26: mov    r14,rdx
    1c29: push   r13
    1c2b: mov    r13,rsi
    1c2e: mov    esi,0x20
    1c33: push   r12
    1c35: mov    r12,rdi
    1c38: push   rbx
    1c39: and    rsp,0xffffffffffffffe0
    1c3d: sub    rsp,0x20
    1c41: mov    rbx,rsp
    1c44: mov    rdi,rbx
    1c47: call   1010 <randombytes@plt>
    1c4c: test   eax,eax
    1c4e: jne    1c80 <mlkem1024_enc+0x60>
    1c50: mov    rcx,rbx
    1c53: mov    rdx,r14
    1c56: mov    rsi,r13
    1c59: mov    rdi,r12
    1c5c: call   1b30 <mlkem1024_enc_derand>
    1c61: pxor   xmm0,xmm0
    1c65: movaps XMMWORD PTR [rsp],xmm0
    1c69: movaps XMMWORD PTR [rsp+0x10],xmm0
    1c6e: lea    rsp,[rbp-0x20]
    1c72: pop    rbx
    1c73: pop    r12
    1c75: pop    r13
    1c77: pop    r14
    1c79: pop    rbp
    1c7a: ret
    1c7b: nop    DWORD PTR [rax+rax*1+0x0]
    1c80: mov    eax,0xfffffffd
    1c85: jmp    1c61 <mlkem1024_enc+0x41>
 ***)

let MLKEM_NATIVE_ENC_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1010,0x1016; 0x1c20,0x1c87];;

let KER4_EXEC = MLKEM_NATIVE_ENC_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame, with the buffer for the random bytes at the frame variable bot *)
(* of INDCPA_BOT_TAC plus 23128, the bottom of the stack of                  *)
(* mlkem1024_enc_derand, and the random bytes as the message.                *)
(* ------------------------------------------------------------------------- *)

let KER4_FRAME = (23232,40,23128,32);;

let KER4_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KER4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KER4_SETUP_TAC =
  INDCPA_BOT_TAC KER4_FRAME [23128] THEN
  INDCPA_FRAME_TAC
   ["memory :> bytes(ct:int64,1568)"; "memory :> bytes(ss:int64,32)"]
   KER4_FRAME THEN
  INDCPA_NONOV_TAC 23160
   [`ct:int64,1568`; `ss:int64,32`; `pk:int64,1568`; `word pc:int64,0x82a0`;
    `word_add stackpointer (word 23192):int64,48`;
    `word(pc + 0xaff8):int64,8`; `ea:int64,el:num`; `word 0:int64,1`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KER4_M = `bytelist_of_num 32 rnd`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for randombytes. Either          *)
(* randombytes succeeds, and then for some message m of 32 bytes (the random *)
(* bytes) the function behaves as mlkem1024_enc_derand with m: if the        *)
(* encapsulation key ek of 1568 bytes at pk passes the check of FIPS 203, it *)
(* returns 0 and the shared secret at ss and the ciphertext at ct are those  *)
(* of mlkem_encaps_internal mlkem1024 ek m, and otherwise it returns -4. Or  *)
(* randombytes fails and the function returns -3. The theorem assumes that   *)
(* SampleNTT terminates for each entry of the matrix and that the stack does *)
(* not contain address 0, as for mlkem1024_enc_derand. The stack is the      *)
(* 23232 bytes below the return address, for the five saved registers, up to *)
(* 31 bytes for the alignment, the 32 bytes of the buffer (aligned to 32     *)
(* bytes by AND with -32 after the pushes) and the 23128 used by             *)
(* mlkem1024_enc_derand below it. The proof is by cases on whether           *)
(* randombytes succeeds.                                                     *)
(* ------------------------------------------------------------------------- *)

let KER4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `ek:byte list`; `mr:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 23232 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `randombytes_contract mr ea el ev`) (concl th)
    then LABEL_TAC "H_RANDOMBYTES" (REWRITE_RULE[randombytes_contract] th)
    else NO_TAC);;

let KER4_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KER4_CALL in
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KER4_EXEC (1--11) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KER4_EXEC (12--15) THEN INDCPA_NORM_TAC THEN
  LIBC_PLT_TAC KER4_EXEC 15 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KER4_EXEC
   [`read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 17 THEN
  ABBREV_TAC `rv = read RAX s17` THEN
  ABBREV_TAC `rnd = read (memory :> bytes(word_add bot (word 23128),32))
                       s17` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [X86_STEPS_TAC KER4_EXEC (18--23) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP KEM_RANDOM_32 o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KER4_M),`32`))
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    X86_STEPS_TAC KER4_EXEC [24] THEN
    call MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
     ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
      `ek:byte list`; KER4_M] @
      post) 25 THEN
    INDCPA_YMMS_TAC "s25" [0] THEN
    MAP_EVERY (fun k -> X86_STEPS_TAC KER4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
     (26--28) THEN
    X86_STEPS_TAC KER4_EXEC (29--35) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN EXISTS_TAC KER4_M THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    X86_STEPS_TAC KER4_EXEC (18--21) THEN
    INDCPA_YMMS_TAC "s21" [0] THEN
    MAP_EVERY (fun k -> X86_STEPS_TAC KER4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
     (22--24) THEN
    X86_STEPS_TAC KER4_EXEC (25--31) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_ENC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!ct ss pk (ek:byte list) mr ea el ev pc stackpointer
    returnaddress.
    randombytes_contract mr ea el ev /\ aligned 16 (word pc:int64) /\
    LENGTH ek = 1568 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 23232),23240) /\
    PAIRWISE nonoverlapping
     [(ct,1568); (ss,32); (word_sub stackpointer (word 23232),23240)] /\
    ALLPAIRS nonoverlapping
     [(ct,1568); (ss,32); (word_sub stackpointer (word 23232),23240)]
     [(pk,1568); (word pc,0x82a0); (word(pc + 0xaff8),8);
      (ea,el)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1c20) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ct; ss; pk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes64(word(pc + 0xaff8))) s = mr /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytes(pk,1568)) s = num_of_bytelist ek)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              ((?m. LENGTH m = 32 /\
                    (mlkem_ek_check mlkem1024 ek
                     ==> read (memory :> bytes(ss,32)) s =
                         num_of_bytelist
                          (FST(mlkem_encaps_internal mlkem1024 ek m)) /\
                         read (memory :> bytes(ct,1568)) s =
                         num_of_bytelist
                          (SND(mlkem_encaps_internal mlkem1024 ek m))) /\
                    C_RETURN s =
                    (if mlkem_ek_check mlkem1024 ek then word 0
                     else word 0xfffffffc)) \/
               C_RETURN s = word 0xfffffffd))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ct,1568); memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 23232),23232)])`,
  KER4_INTRO_TAC THEN KER4_SETUP_TAC THEN KER4_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the safety contract for   *)
(* randombytes. The events depend only on the addresses (and the address of  *)
(* randombytes in the GOT), on the encapsulation key and on whether          *)
(* randombytes fails, when the result is -3, but not on the random message.  *)
(* They are given by cases on whether the result is -3, and the frame        *)
(* variables are expanded in them by INDCPA_UNBOT_TAC.                       *)
(* ------------------------------------------------------------------------- *)

let KER4_SAFE_TEMPLATE =
 `\(ct:int64) (ss:int64) (pk:int64) (mr:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64) (ek:byte list) (r:int64).
   if r = word 4294967293
   then f_ev0 ct ss pk mr pc stackpointer returnaddress
   else f_ev1 ct ss pk mr pc stackpointer returnaddress ek
   :(uarch_event)list`;;

let KER4_SAFE_ALLOWED =
  [`pc:num`; `ct:int64`; `ss:int64`; `pk:int64`; `mr:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `ek:byte list`;
   `bot:int64`];;

let KER4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KER4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KER4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KER4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `randombytes_safety_contract mr ea el ev`)
           (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[randombytes_safety_contract] th) "H_RANDOMBYTES"
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_INNER" THEN
  CONCRETIZE_F_EVENTS_TAC KER4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `ek:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 23232 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let KER4_SAFE_MAIN_TAC =
  let call = KER4_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KER4_EXEC (1--11) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KER4_EXEC (12--15) THEN INDCPA_NORM_TAC THEN
  LIBC_PLT_TAC KER4_EXEC 15 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" KER4_EXEC
   (`e:(uarch_event)list`::[`read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`])
   (ref KER4_SAFE_ALLOWED) 17 THEN
  ABBREV_TAC `rv = read RAX s17` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [X86_STEPS_TAC KER4_EXEC (18--23) THEN
    X86_STEPS_TAC KER4_EXEC [24] THEN
    call "H_INNER"
     [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
      `ek:byte list`] 25 THEN
    X86_STEPS_TAC KER4_EXEC (26--35) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~((if mlkem_ek_check mlkem1024 ek then word 0 else word 4294967292) =
        (word 4294967293:int64))`
     (fun th -> REWRITE_TAC[th]) THENL
     [COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X86_STEPS_TAC KER4_EXEC (18--31) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_ENC_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mr ea el ev.
   randombytes_safety_contract mr ea el ev
   ==> exists f_events.
        forall e ct ss pk (ek:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH ek = 1568 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 23232),23240) /\
    PAIRWISE nonoverlapping
     [(ct,1568); (ss,32); (word_sub stackpointer (word 23232),23240)] /\
    ALLPAIRS nonoverlapping
     [(ct,1568); (ss,32); (word_sub stackpointer (word 23232),23240)]
     [(pk,1568); (word pc,0x82a0); (word(pc + 0xaff8),8);
      (ea,el)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1c20) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ct; ss; pk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes64(word(pc + 0xaff8))) s = mr /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events ct ss pk mr pc
                        (word_sub stackpointer (word 23232)) returnaddress ek
                        (C_RETURN s) /\
                 memaccess_inbounds e2
                  [pk,1568; ct,1568; ss,32;
                   word_sub stackpointer (word 23232),23240;
                   word(pc + 0xaff8),8; ea,el; word(pc + 0x8008),8;
                   word(pc + 0x8018),8; word(pc + 0x8030),16;
                   word(pc + 0x8040),16; word(pc + 0x8080),48;
                   word(pc + 0x80c0),192; word(pc + 0x81a0),256]
                  [ct,1568; ss,32;
                   word_sub stackpointer (word 23232),23232]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ct,1568); memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 23232),23232)])`,
  KER4_SAFE_INTRO_TAC THEN KER4_SETUP_TAC THEN KER4_SAFE_MAIN_TAC);;
