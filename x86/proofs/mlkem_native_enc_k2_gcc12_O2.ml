(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-512 (FIPS 203 Algorithm 20). This is the code *)
(* for mlkem512_enc from mlkem-native's portable C implementation compiled   *)
(* by gcc 12 with -O2 (see mlkem_native/README.md). It gets 32 random bytes  *)
(* with randombytes, through its PLT stub and GOT entry, into a buffer on    *)
(* the stack, and returns -3 if that fails, and otherwise encapsulates with  *)
(* them as the message with mlkem512_enc_derand. In both cases it zeroes the *)
(* buffer. It is verified in the whole image (see                            *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x5280, using  *)
(* the theorem for mlkem512_enc_derand in the image and the contract for     *)
(* randombytes (see utils/mlkem_native_libc.ml).                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_enc_derand_k2_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_libc.ml";;

(*** The code in the image:

    1010: jmp    QWORD PTR [rip+0x9fe2]
 ***)

(*** The code in the image:

    5280: push   rbp
    5281: mov    rbp,rsp
    5284: push   r14
    5286: mov    r14,rdx
    5289: push   r13
    528b: mov    r13,rsi
    528e: mov    esi,0x20
    5293: push   r12
    5295: mov    r12,rdi
    5298: push   rbx
    5299: and    rsp,0xffffffffffffffe0
    529d: sub    rsp,0x20
    52a1: mov    rbx,rsp
    52a4: mov    rdi,rbx
    52a7: call   1010 <randombytes@plt>
    52ac: test   eax,eax
    52ae: jne    52e0 <mlkem512_enc+0x60>
    52b0: mov    rcx,rbx
    52b3: mov    rdx,r14
    52b6: mov    rsi,r13
    52b9: mov    rdi,r12
    52bc: call   5190 <mlkem512_enc_derand>
    52c1: pxor   xmm0,xmm0
    52c5: movaps XMMWORD PTR [rsp],xmm0
    52c9: movaps XMMWORD PTR [rsp+0x10],xmm0
    52ce: lea    rsp,[rbp-0x20]
    52d2: pop    rbx
    52d3: pop    r12
    52d5: pop    r13
    52d7: pop    r14
    52d9: pop    rbp
    52da: ret
    52db: nop    DWORD PTR [rax+rax*1+0x0]
    52e0: mov    eax,0xfffffffd
    52e5: jmp    52c1 <mlkem512_enc+0x41>
 ***)

let MLKEM_NATIVE_ENC_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1010,0x1016; 0x5280,0x52e7];;

let KER2_EXEC = MLKEM_NATIVE_ENC_K2_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame, with the buffer for the random bytes at the frame variable bot *)
(* of INDCPA_BOT_TAC plus 12344, the bottom of the stack of                  *)
(* mlkem512_enc_derand, and the random bytes as the message.                 *)
(* ------------------------------------------------------------------------- *)

let KER2_FRAME = (12448,40,12344,32);;

let KER2_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KER2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KER2_SETUP_TAC =
  INDCPA_BOT_TAC KER2_FRAME [12344] THEN
  INDCPA_FRAME_TAC
   ["memory :> bytes(ct:int64,768)"; "memory :> bytes(ss:int64,32)"]
   KER2_FRAME THEN
  INDCPA_NONOV_TAC 12376
   [`ct:int64,768`; `ss:int64,32`; `pk:int64,800`; `word pc:int64,0x82a0`;
    `word_add stackpointer (word 12408):int64,48`;
    `word(pc + 0xaff8):int64,8`; `ea:int64,el:num`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KER2_M = `bytelist_of_num 32 rnd`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for randombytes. Either          *)
(* randombytes succeeds, and then for some message m of 32 bytes (the random *)
(* bytes) the function behaves as mlkem512_enc_derand with m: if the         *)
(* encapsulation key ek of 800 bytes at pk passes the check of FIPS 203, it  *)
(* returns 0 and the shared secret at ss and the ciphertext at ct are those  *)
(* of mlkem_encaps_internal mlkem512 ek m, and otherwise it returns -4. Or   *)
(* randombytes fails and the function returns -3. The theorem assumes that   *)
(* SampleNTT terminates for each entry of the matrix, as for                 *)
(* mlkem512_enc_derand. The stack is the 12448 bytes below the return        *)
(* address, for the five saved registers, up to 31 bytes for the alignment,  *)
(* the 32 bytes of the buffer (aligned to 32 bytes by AND with -32 after the *)
(* pushes) and the 12344 used by mlkem512_enc_derand below it. The proof is  *)
(* by cases on whether randombytes succeeds.                                 *)
(* ------------------------------------------------------------------------- *)

let KER2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `ek:byte list`; `mr:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 12448 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `randombytes_contract mr ea el ev`) (concl th)
    then LABEL_TAC "H_RANDOMBYTES" (REWRITE_RULE[randombytes_contract] th)
    else NO_TAC);;

let KER2_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KER2_CALL in
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KER2_EXEC (1--11) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KER2_EXEC (12--15) THEN INDCPA_NORM_TAC THEN
  LIBC_PLT_TAC KER2_EXEC 15 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KER2_EXEC
   [`read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 17 THEN
  ABBREV_TAC `rv = read RAX s17` THEN
  ABBREV_TAC `rnd = read (memory :> bytes(word_add bot (word 12344),32))
                       s17` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [X86_STEPS_TAC KER2_EXEC (18--23) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP KEM_RANDOM_32 o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KER2_M),`32`))
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    X86_STEPS_TAC KER2_EXEC [24] THEN
    call MLKEM_NATIVE_ENC_DERAND_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
     ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
      `ek:byte list`; KER2_M] @
      post) 25 THEN
    INDCPA_YMMS_TAC "s25" [0] THEN
    MAP_EVERY (fun k -> X86_STEPS_TAC KER2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
     (26--28) THEN
    X86_STEPS_TAC KER2_EXEC (29--35) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN EXISTS_TAC KER2_M THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    X86_STEPS_TAC KER2_EXEC (18--21) THEN
    INDCPA_YMMS_TAC "s21" [0] THEN
    MAP_EVERY (fun k -> X86_STEPS_TAC KER2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
     (22--24) THEN
    X86_STEPS_TAC KER2_EXEC (25--31) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_ENC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!ct ss pk (ek:byte list) mr ea el ev pc stackpointer
    returnaddress.
    randombytes_contract mr ea el ev /\ aligned 16 (word pc:int64) /\
    LENGTH ek = 800 /\
    (!i j. i < 2 /\ j < 2
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
    PAIRWISE nonoverlapping
     [(ct,768); (ss,32); (word_sub stackpointer (word 12448),12456)] /\
    ALLPAIRS nonoverlapping
     [(ct,768); (ss,32); (word_sub stackpointer (word 12448),12456)]
     [(pk,800); (word pc,0x82a0); (word(pc + 0xaff8),8);
      (ea,el)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x5280) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ct; ss; pk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes64(word(pc + 0xaff8))) s = mr /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytes(pk,800)) s = num_of_bytelist ek)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              ((?m. LENGTH m = 32 /\
                    (mlkem_ek_check mlkem512 ek
                     ==> read (memory :> bytes(ss,32)) s =
                         num_of_bytelist
                          (FST(mlkem_encaps_internal mlkem512 ek m)) /\
                         read (memory :> bytes(ct,768)) s =
                         num_of_bytelist
                          (SND(mlkem_encaps_internal mlkem512 ek m))) /\
                    C_RETURN s =
                    (if mlkem_ek_check mlkem512 ek then word 0
                     else word 0xfffffffc)) \/
               C_RETURN s = word 0xfffffffd))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ct,768); memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 12448),12448)])`,
  KER2_INTRO_TAC THEN KER2_SETUP_TAC THEN KER2_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the safety contract for   *)
(* randombytes. The events depend only on the addresses (and the address of  *)
(* randombytes in the GOT), on the encapsulation key and on whether          *)
(* randombytes fails, when the result is -3, but not on the random message.  *)
(* They are given by cases on whether the result is -3, and the frame        *)
(* variables are expanded in them by INDCPA_UNBOT_TAC.                       *)
(* ------------------------------------------------------------------------- *)

let KER2_SAFE_TEMPLATE =
 `\(ct:int64) (ss:int64) (pk:int64) (mr:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64) (ek:byte list) (r:int64).
   if r = word 4294967293
   then f_ev0 ct ss pk mr pc stackpointer returnaddress
   else f_ev1 ct ss pk mr pc stackpointer returnaddress ek
   :(uarch_event)list`;;

let KER2_SAFE_ALLOWED =
  [`pc:num`; `ct:int64`; `ss:int64`; `pk:int64`; `mr:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `ek:byte list`;
   `bot:int64`];;

let KER2_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KER2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KER2_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KER2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `randombytes_safety_contract mr ea el ev`)
           (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[randombytes_safety_contract] th) "H_RANDOMBYTES"
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLKEM_NATIVE_ENC_DERAND_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_INNER" THEN
  CONCRETIZE_F_EVENTS_TAC KER2_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `ek:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 12448 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let KER2_SAFE_MAIN_TAC =
  let call = KER2_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KER2_EXEC (1--11) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KER2_EXEC (12--15) THEN INDCPA_NORM_TAC THEN
  LIBC_PLT_TAC KER2_EXEC 15 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" KER2_EXEC
   (`e:(uarch_event)list`::[`read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`])
   (ref KER2_SAFE_ALLOWED) 17 THEN
  ABBREV_TAC `rv = read RAX s17` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [X86_STEPS_TAC KER2_EXEC (18--23) THEN
    X86_STEPS_TAC KER2_EXEC [24] THEN
    call "H_INNER"
     [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
      `ek:byte list`] 25 THEN
    X86_STEPS_TAC KER2_EXEC (26--35) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~((if mlkem_ek_check mlkem512 ek then word 0 else word 4294967292) =
        (word 4294967293:int64))`
     (fun th -> REWRITE_TAC[th]) THENL
     [COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X86_STEPS_TAC KER2_EXEC (18--31) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_ENC_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mr ea el ev.
   randombytes_safety_contract mr ea el ev
   ==> exists f_events.
        forall e ct ss pk (ek:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH ek = 800 /\
    (!i j. i < 2 /\ j < 2
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
    PAIRWISE nonoverlapping
     [(ct,768); (ss,32); (word_sub stackpointer (word 12448),12456)] /\
    ALLPAIRS nonoverlapping
     [(ct,768); (ss,32); (word_sub stackpointer (word 12448),12456)]
     [(pk,800); (word pc,0x82a0); (word(pc + 0xaff8),8);
      (ea,el)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x5280) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ct; ss; pk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes64(word(pc + 0xaff8))) s = mr /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events ct ss pk mr pc
                        (word_sub stackpointer (word 12448)) returnaddress ek
                        (C_RETURN s) /\
                 memaccess_inbounds e2
                  [pk,800; ct,768; ss,32;
                   word_sub stackpointer (word 12448),12456;
                   word(pc + 0xaff8),8; ea,el; word(pc + 0x8000),8;
                   word(pc + 0x8008),8; word(pc + 0x8080),48;
                   word(pc + 0x80c0),192; word(pc + 0x8180),2;
                   word(pc + 0x81a0),256]
                  [ct,768; ss,32;
                   word_sub stackpointer (word 12448),12448]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ct,768); memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 12448),12448)])`,
  KER2_SAFE_INTRO_TAC THEN KER2_SETUP_TAC THEN KER2_SAFE_MAIN_TAC);;
