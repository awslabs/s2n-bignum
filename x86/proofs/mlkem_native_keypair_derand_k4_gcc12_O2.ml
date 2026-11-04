(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of ML-KEM-1024 (FIPS 203 Algorithm 16, which is        *)
(* Algorithm 19 with its random seeds as arguments). This is the code for    *)
(* mlkem1024_keypair_derand from mlkem-native's portable C implementation    *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It generates    *)
(* the K-PKE keys from the first 32 bytes d of its argument coins with       *)
(* mlkem1024_indcpa_keypair_derand, and writes the decapsulation key as the  *)
(* K-PKE decryption key followed by the encapsulation key, copied by an      *)
(* inline memcpy, its hash H by mlkem_sha3_256 and the last 32 bytes z of    *)
(* coins. If mlkem1024_indcpa_keypair_derand returned an error, which it     *)
(* never does, the function would zero the keys. It is verified in the whole *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x19a0, using the theorems for mlkem1024_indcpa_keypair_derand and        *)
(* mlkem_sha3_256 in the image.                                              *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_indcpa_keypair_derand_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_sha3_256_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    19a0: push   r13
    19a2: push   r12
    19a4: mov    r12,rdx
    19a7: push   rbp
    19a8: mov    rbp,rdi
    19ab: push   rbx
    19ac: mov    rbx,rsi
    19af: sub    rsp,0x8
    19b3: call   1110 <mlkem1024_indcpa_keypair_derand>
    19b8: mov    r13d,eax
    19bb: test   eax,eax
    19bd: jne    1a48 <mlkem1024_keypair_derand+0xa8>
    19c3: mov    rax,QWORD PTR [rbp+0x0]
    19c7: lea    rdi,[rbx+0x608]
    19ce: lea    rcx,[rbx+0x600]
    19d5: mov    rsi,rbp
    19d8: and    rdi,0xfffffffffffffff8
    19dc: mov    QWORD PTR [rbx+0x600],rax
    19e3: sub    rcx,rdi
    19e6: mov    rdx,QWORD PTR [rbp+0x618]
    19ed: lea    rax,[rbx+0xc20]
    19f4: sub    rsi,rcx
    19f7: add    ecx,0x620
    19fd: mov    QWORD PTR [rbx+0xc18],rdx
    1a04: shr    ecx,0x3
    1a07: mov    edx,0x620
    1a0c: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
    1a0f: mov    rsi,rbp
    1a12: mov    rdi,rax
    1a15: call   3510 <mlkem_sha3_256>
    1a1a: movdqu xmm0,XMMWORD PTR [r12+0x20]
    1a21: mov    eax,r13d
    1a24: movups XMMWORD PTR [rbx+0xc40],xmm0
    1a2b: movdqu xmm1,XMMWORD PTR [r12+0x30]
    1a32: movups XMMWORD PTR [rbx+0xc50],xmm1
    1a39: add    rsp,0x8
    1a3d: pop    rbx
    1a3e: pop    rbp
    1a3f: pop    r12
    1a41: pop    r13
    1a43: ret
 ***)

let MLKEM_NATIVE_KEYPAIR_DERAND_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x19a0,0x1a44];;

let KK4_EXEC = MLKEM_NATIVE_KEYPAIR_DERAND_K4_GCC12_O2_EXEC;;

let KPKE_KEYGEN_LENGTHS_1024 = prove
 (`!d. LENGTH(FST(kpke_keygen mlkem1024 d)) = 1568 /\
       LENGTH(SND(kpke_keygen mlkem1024 d)) = 1536`,
  REWRITE_TAC[mlkem1024; KPKE_KEYGEN_LENGTHS] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The copy of z into the decapsulation key, from its two 128-bit halves,    *)
(* and the final combination of the parts of the keys, as for AArch64. The   *)
(* copy of the encapsulation key is by KEM_MEMCPY_TAC (see                   *)
(* mlkem_native_kem.ml), and z is copied by legacy SSE moves through XMM0    *)
(* and XMM1, so the values of YMM0 and YMM1 after the hash are named.        *)
(* ------------------------------------------------------------------------- *)

let KK4_Z_TAC s =
  MP_TAC(SPECL [`word_add sk (word 3136):int64`; `num_of_bytelist z`;
                mk_var(s,`:x86state`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `z:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

let KK4_FINAL_TAC =
  REWRITE_TAC[mlkem1024; MLKEM_KEYGEN_PAIR] THEN
  REWRITE_TAC[GSYM mlkem1024] THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_KEYGEN_LENGTHS_1024;
              mlkem_h; LENGTH_SHA3_256] THEN
  REWRITE_TAC[ARITH_RULE `3168 = 1536 + 1632`; ARITH_RULE `1632 = 1568 + 64`;
              ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is d followed by z, 32 bytes each, at coins,  *)
(* and the encapsulation key of 1568 bytes at pk and the decapsulation key   *)
(* of 3168 bytes at sk are those of mlkem_keygen mlkem1024 d z in            *)
(* common/fips203.ml. The theorem assumes that SampleNTT terminates for each *)
(* entry of the matrix and that the stack does not contain address 0, as for *)
(* mlkem1024_indcpa_keypair_derand. The stack is the 40 bytes of the four    *)
(* pushes and the alignment of the stack for the calls, the return address   *)
(* of the call and the 19416 bytes used by mlkem1024_indcpa_keypair_derand   *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let KK4_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KK4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KK4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `z:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19464 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`] THEN
  MP_TAC(SPEC `d:byte list` KPKE_KEYGEN_LENGTHS_1024) THEN STRIP_TAC;;

let KK4_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KK4_CALL in
  ENSURES_INIT_TAC "s0" THEN
  KEM_HALVES_TAC `word_add coins (word 32):int64` THEN

  (*** The K-PKE keys ***)

  X86_STEPS_TAC KK4_EXEC (1--9) THEN
  call MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `d:byte list`] @ post) 10 THEN

  (*** The copy of the encapsulation key into the decapsulation key ***)

  X86_STEPS_TAC KK4_EXEC (11--13) THEN
  KEM_MEMCPY_TAC KK4_EXEC 14 28 1536 1568 `stackpointer:int64,19472` THEN

  (*** Its hash and z ***)

  X86_STEPS_TAC KK4_EXEC (29--31) THEN
  call MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `FST(kpke_keygen mlkem1024 d)`] @ post)
   32 THEN
  INDCPA_YMMS_TAC "s32" [0; 1] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KK4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (33--37) THEN
  KK4_Z_TAC "s37" THEN
  X86_STEPS_TAC KK4_EXEC (38--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KK4_FINAL_TAC;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!pk sk coins (d:byte list) (z:byte list) pc stackpointer
    returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH d = 32 /\ LENGTH z = 32 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (FST(mlkem_g(APPEND d [word 4])))
                        [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 19464),19472) /\
    PAIRWISE nonoverlapping
     [(pk,1568); (sk,3168); (word_sub stackpointer (word 19464),19472)] /\
    ALLPAIRS nonoverlapping
     [(pk,1568); (sk,3168); (word_sub stackpointer (word 19464),19472)]
     [(coins,64); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x19a0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
              read (memory :> bytes(word_add coins (word 32),32)) s =
              num_of_bytelist z)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(pk,1568)) s =
              num_of_bytelist(FST(mlkem_keygen mlkem1024 d z)) /\
              read (memory :> bytes(sk,3168)) s =
              num_of_bytelist(SND(mlkem_keygen mlkem1024 d z)) /\
              C_RETURN s = word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,1568); memory :> bytes(sk,3168);
            memory :> bytes(word_sub stackpointer (word 19464),19464)])`,
  KK4_INTRO_TAC THEN KK4_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for                             *)
(* mlkem1024_indcpa_keypair_derand, the events depend only on the addresses  *)
(* and on rho, and the theorem also states that rho is the end of the public *)
(* key, which the copy into the secret key and its hash do not change. The   *)
(* events of the REP MOVSQ depend on the address of the secret key modulo 8, *)
(* through lo, which is expanded in them.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let KK4_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `coins:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `d:byte list`; `rho:byte list`];;

let KK4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KK4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KK4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KK4_SAFE_INTRO_TAC =
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_INDCPA";
    MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHA3_256"] THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `coins:int64`;
    `d:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19464 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KK4_SAFE_MAIN_TAC =
  let call = KK4_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KK4_EXEC (1--9) THEN
  call "H_INDCPA"
   [`read RDI s`; `read RSI s`; `read RDX s`; `d:byte list`] 10 THEN
  X86_STEPS_TAC KK4_EXEC (11--26) THEN KEM_MEMCPY_REGS_TAC 1536 1568 THEN
  MAP_EVERY (fun r ->
    SUBGOAL_THEN
     (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                      `word_add sk (word (1536 + lo)):int64,1560`),r))
     ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC])
   [`word_add pk (word 1536):int64,32`; `stackpointer:int64,19472`;
    `word pc:int64,0x82a0`] THEN
  X86_STEPS_TAC KK4_EXEC (27--28) THEN KEM_UNLO_TAC THEN
  X86_STEPS_TAC KK4_EXEC (29--31) THEN
  call "H_SHA3_256" [`read RDI s`; `read RSI s`; `1568`] 32 THEN
  X86_STEPS_TAC KK4_EXEC (33--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND_NIL] THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 4]))` THEN
  KEM_MEMCPY_DISCHARGE_TAC `word_add sk (word 1536):int64`;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e pk sk coins (d:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH d = 32 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (FST(mlkem_g(APPEND d [word 4])))
                        [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 19464),19472) /\
    PAIRWISE nonoverlapping
     [(pk,1568); (sk,3168); (word_sub stackpointer (word 19464),19472)] /\
    ALLPAIRS nonoverlapping
     [(pk,1568); (sk,3168); (word_sub stackpointer (word 19464),19472)]
     [(coins,64); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x19a0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word 0 /\
              read (memory :> bytes(word_add pk (word 1536),32)) s =
              num_of_bytelist(FST(mlkem_g(APPEND d [word 4]))) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk sk coins pc
                        (word_sub stackpointer (word 19464)) returnaddress
                        (FST(mlkem_g(APPEND d [word 4]))) /\
                 memaccess_inbounds e2
                  [coins,64; pk,1568; sk,3168;
                   word_sub stackpointer (word 19464),19472;
                   word(pc + 0x8070),48; word(pc + 0x80c0),192;
                   word(pc + 0x81a0),256]
                  [pk,1568; sk,3168;
                   word_sub stackpointer (word 19464),19464]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,1568); memory :> bytes(sk,3168);
            memory :> bytes(word_sub stackpointer (word 19464),19464)])`,
  KK4_SAFE_INTRO_TAC THEN KK4_SAFE_MAIN_TAC);;
