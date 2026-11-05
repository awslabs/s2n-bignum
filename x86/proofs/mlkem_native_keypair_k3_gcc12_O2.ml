(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of ML-KEM-768 (FIPS 203 Algorithm 19). This is the     *)
(* code for mlkem768_keypair from mlkem-native's portable C implementation   *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It gets 64      *)
(* random bytes with randombytes, through its PLT stub and GOT entry, into a *)
(* buffer on the stack, and returns -3 if that fails, and otherwise          *)
(* generates the keys from them with mlkem768_keypair_derand. In both cases  *)
(* it zeroes the buffer. It is verified in the whole image (see              *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x6ff0, using  *)
(* the theorem for mlkem768_keypair_derand in the image and the contract for *)
(* randombytes (see utils/mlkem_native_libc.ml).                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keypair_derand_k3_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_libc.ml";;

(*** The code in the image:

    1010: jmp    QWORD PTR [rip+0x9fe2]
 ***)

(*** The code in the image:

    6ff0: push   rbp
    6ff1: mov    rbp,rsp
    6ff4: push   r13
    6ff6: mov    r13,rsi
    6ff9: mov    esi,0x40
    6ffe: push   r12
    7000: mov    r12,rdi
    7003: push   rbx
    7004: and    rsp,0xffffffffffffffe0
    7008: sub    rsp,0x40
    700c: mov    rbx,rsp
    700f: mov    rdi,rbx
    7012: call   1010 <randombytes@plt>
    7017: test   eax,eax
    7019: jne    7050 <mlkem768_keypair+0x60>
    701b: mov    rdx,rbx
    701e: mov    rsi,r13
    7021: mov    rdi,r12
    7024: call   6ed0 <mlkem768_keypair_derand>
    7029: pxor   xmm0,xmm0
    702d: movaps XMMWORD PTR [rsp],xmm0
    7031: movaps XMMWORD PTR [rsp+0x10],xmm0
    7036: movaps XMMWORD PTR [rsp+0x20],xmm0
    703b: movaps XMMWORD PTR [rsp+0x30],xmm0
    7040: lea    rsp,[rbp-0x18]
    7044: pop    rbx
    7045: pop    r12
    7047: pop    r13
    7049: pop    rbp
    704a: ret
    704b: nop    DWORD PTR [rax+rax*1+0x0]
    7050: mov    eax,0xfffffffd
    7055: jmp    7029 <mlkem768_keypair+0x39>
 ***)

let MLKEM_NATIVE_KEYPAIR_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1010,0x1016; 0x6ff0,0x7057];;

let KR3_EXEC = MLKEM_NATIVE_KEYPAIR_K3_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame, with the buffer for the random bytes at the frame variable bot *)
(* of INDCPA_BOT_TAC plus 14072, the bottom of the stack of                  *)
(* mlkem768_keypair_derand, and the random bytes as the seeds d and z.       *)
(* ------------------------------------------------------------------------- *)

let KR3_FRAME = (14200,32,14072,64);;

let KR3_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KR3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KR3_SETUP_TAC =
  INDCPA_BOT_TAC KR3_FRAME [14072] THEN
  INDCPA_FRAME_TAC
   ["memory :> bytes(pk:int64,1184)"; "memory :> bytes(sk:int64,2400)"]
   KR3_FRAME THEN
  INDCPA_NONOV_TAC 14136
   [`pk:int64,1184`; `sk:int64,2400`; `word pc:int64,0x82a0`;
    `word_add stackpointer (word 14168):int64,40`;
    `word(pc + 0xaff8):int64,8`; `ea:int64,el:num`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KR3_D = `bytelist_of_num 32 (rnd MOD 2 EXP 256)`;;

let KR3_Z = `bytelist_of_num 32 (rnd DIV 2 EXP 256)`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for randombytes. Either          *)
(* randombytes succeeds and the function returns 0, and then the             *)
(* encapsulation key of 1184 bytes at pk and the decapsulation key of 2400   *)
(* bytes at sk are those of mlkem_keygen mlkem768 d z in common/fips203.ml   *)
(* for some d and z of 32 bytes (the random bytes), or it fails and the      *)
(* function returns -3. The theorem assumes that SampleNTT terminates for    *)
(* each entry of the matrix for any seed d, as for mlkem768_keypair_derand.  *)
(* The stack is the 14200 bytes below the return address, for the four saved *)
(* registers, up to 31 bytes for the alignment, the 64 bytes of the buffer   *)
(* (aligned to 32 bytes by AND with -32 after the pushes) and the 14072 used *)
(* by mlkem768_keypair_derand below it. The proof is by cases on whether     *)
(* randombytes succeeds.                                                     *)
(* ------------------------------------------------------------------------- *)

let KR3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `mr:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 14200 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `randombytes_contract mr ea el ev`) (concl th)
    then LABEL_TAC "H_RANDOMBYTES" (REWRITE_RULE[randombytes_contract] th)
    else NO_TAC);;

let KR3_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KR3_CALL in
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KR3_EXEC (1--9) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KR3_EXEC (10--13) THEN INDCPA_NORM_TAC THEN
  LIBC_PLT_TAC KR3_EXEC 13 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KR3_EXEC
   [`read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 15 THEN
  ABBREV_TAC `rv = read RAX s15` THEN
  ABBREV_TAC `rnd = read (memory :> bytes(word_add bot (word 14072),64))
                       s15` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [X86_STEPS_TAC KR3_EXEC (16--20) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                ONCE_DEPTH_CONV NUM_ADD_CONV) o
      MATCH_MP KEM_RANDOM_SPLIT o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KR3_D),`32`),
                          mk_eq(mk_comb(`LENGTH:byte list->num`,KR3_Z),`32`)))
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC KR3_D o check (is_forall o concl)) THEN
    REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN DISCH_TAC THEN
    X86_STEPS_TAC KR3_EXEC [21] THEN
    call MLKEM_NATIVE_KEYPAIR_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
     ([`read RDI s`; `read RSI s`; `read RDX s`; KR3_D; KR3_Z] @
      post) 22 THEN
    INDCPA_YMMS_TAC "s22" [0] THEN
    MAP_EVERY (fun k -> X86_STEPS_TAC KR3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
     (23--27) THEN
    X86_STEPS_TAC KR3_EXEC (28--33) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [KR3_D; KR3_Z] THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    X86_STEPS_TAC KR3_EXEC (16--19) THEN
    INDCPA_YMMS_TAC "s19" [0] THEN
    MAP_EVERY (fun k -> X86_STEPS_TAC KR3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
     (20--24) THEN
    X86_STEPS_TAC KR3_EXEC (25--30) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_KEYPAIR_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!pk sk mr ea el ev pc stackpointer returnaddress.
    randombytes_contract mr ea el ev /\ aligned 16 (word pc:int64) /\
    (!d. LENGTH d = 32
         ==> !i j. i < 3 /\ j < 3
                   ==> mlkem_samplentt_terminates
                        (APPEND (FST(mlkem_g(APPEND d [word 3])))
                                [word j; word i])) /\
    PAIRWISE nonoverlapping
     [(pk,1184); (sk,2400); (word_sub stackpointer (word 14200),14208)] /\
    ALLPAIRS nonoverlapping
     [(pk,1184); (sk,2400); (word_sub stackpointer (word 14200),14208)]
     [(word pc,0x82a0); (word(pc + 0xaff8),8); (ea,el)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x6ff0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes64(word(pc + 0xaff8))) s = mr /\
              read (memory :> bytes(ea,el)) s = ev)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (C_RETURN s = word 0 /\
               (?d z. LENGTH d = 32 /\ LENGTH z = 32 /\
                      read (memory :> bytes(pk,1184)) s =
                      num_of_bytelist(FST(mlkem_keygen mlkem768 d z)) /\
                      read (memory :> bytes(sk,2400)) s =
                      num_of_bytelist(SND(mlkem_keygen mlkem768 d z))) \/
               C_RETURN s = word 0xfffffffd))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
            memory :> bytes(word_sub stackpointer (word 14200),14200)])`,
  KR3_INTRO_TAC THEN KR3_SETUP_TAC THEN KR3_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the safety contract for   *)
(* randombytes. The events depend only on the addresses (and the address of  *)
(* randombytes in the GOT), on whether randombytes fails and, if it does     *)
(* not, on rho, which is the end of the public key by the theorem for        *)
(* mlkem768_keypair_derand. So they are given in terms of the result and of  *)
(* the last 32 bytes of the public key, by cases on whether the result is 0, *)
(* and the frame variables are expanded in them by INDCPA_UNBOT_TAC.         *)
(* ------------------------------------------------------------------------- *)

let KR3_SAFE_TEMPLATE =
 `\(pk:int64) (sk:int64) (mr:int64) (pc:num) (stackpointer:int64)
   (returnaddress:int64) (r:int64) (n:num).
   if r = word 0
   then f_ev1 pk sk mr pc stackpointer returnaddress (bytelist_of_num 32 n)
   else f_ev0 pk sk mr pc stackpointer returnaddress
   :(uarch_event)list`;;

let KR3_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `mr:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `d:byte list`; `bot:int64`];;

let KR3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KR3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KR3_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KR3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `randombytes_safety_contract mr ea el ev`)
           (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[randombytes_safety_contract] th) "H_RANDOMBYTES"
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLKEM_NATIVE_KEYPAIR_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_INNER" THEN
  CONCRETIZE_F_EVENTS_TAC KR3_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`pk:int64`; `sk:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 14200 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let KR3_SAFE_MAIN_TAC =
  let call = KR3_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KR3_EXEC (1--9) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KR3_EXEC (10--13) THEN INDCPA_NORM_TAC THEN
  LIBC_PLT_TAC KR3_EXEC 13 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" KR3_EXEC
   (`e:(uarch_event)list`::[`read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`])
   (ref KR3_SAFE_ALLOWED) 15 THEN
  ABBREV_TAC `rv = read RAX s15` THEN
  ABBREV_TAC `rnd = read (memory :> bytes(word_add bot (word 14072),64))
                       s15` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [X86_STEPS_TAC KR3_EXEC (16--20) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                ONCE_DEPTH_CONV NUM_ADD_CONV) o
      MATCH_MP KEM_RANDOM_SPLIT o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    FIRST_ASSUM(MP_TAC o SPEC KR3_D o check (is_forall o concl)) THEN
    REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN DISCH_TAC THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KR3_D),`32`))
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    ABBREV_TAC(mk_eq(`d:byte list`,KR3_D)) THEN
    X86_STEPS_TAC KR3_EXEC [21] THEN
    call "H_INNER"
     [`read RDI s`; `read RSI s`; `read RDX s`; `d:byte list`] 22 THEN
    X86_STEPS_TAC KR3_EXEC (23--33) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    SIMP_TAC[KEM_BYTELIST_32; LENGTH_MLKEM_G] THEN
    REWRITE_TAC[APPEND_NIL] THEN
    ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 3]))` THEN
    INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X86_STEPS_TAC KR3_EXEC (16--30) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_KEYPAIR_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mr ea el ev.
   randombytes_safety_contract mr ea el ev
   ==> exists f_events.
        forall e pk sk pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    (!d. LENGTH d = 32
         ==> !i j. i < 3 /\ j < 3
                   ==> mlkem_samplentt_terminates
                        (APPEND (FST(mlkem_g(APPEND d [word 3])))
                                [word j; word i])) /\
    PAIRWISE nonoverlapping
     [(pk,1184); (sk,2400); (word_sub stackpointer (word 14200),14208)] /\
    ALLPAIRS nonoverlapping
     [(pk,1184); (sk,2400); (word_sub stackpointer (word 14200),14208)]
     [(word pc,0x82a0); (word(pc + 0xaff8),8); (ea,el)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x6ff0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes64(word(pc + 0xaff8))) s = mr /\
              read (memory :> bytes(ea,el)) s = ev /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk sk mr pc
                        (word_sub stackpointer (word 14200)) returnaddress
                        (C_RETURN s)
                        (read (memory :> bytes(word_add pk (word 1152),32))
                              s) /\
                 memaccess_inbounds e2
                  [pk,1184; sk,2400; word_sub stackpointer (word 14200),14208;
                   word(pc + 0xaff8),8; ea,el; word(pc + 0x8070),48;
                   word(pc + 0x80c0),192; word(pc + 0x8180),4;
                   word(pc + 0x81a0),256]
                  [pk,1184; sk,2400;
                   word_sub stackpointer (word 14200),14200]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
            memory :> bytes(word_sub stackpointer (word 14200),14200)])`,
  KR3_SAFE_INTRO_TAC THEN KR3_SETUP_TAC THEN KR3_SAFE_MAIN_TAC);;
