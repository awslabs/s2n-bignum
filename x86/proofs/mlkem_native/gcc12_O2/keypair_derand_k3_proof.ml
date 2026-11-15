(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of ML-KEM-768 (FIPS 203 Algorithm 16, which is         *)
(* Algorithm 19 with its random seeds as arguments). This is the code for    *)
(* mlkem768_keypair_derand from mlkem-native's portable C implementation     *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It generates    *)
(* the K-PKE keys from the first 32 bytes d of its argument coins with       *)
(* mlkem768_indcpa_keypair_derand, and writes the decapsulation key as the   *)
(* K-PKE decryption key followed by the encapsulation key, copied by an      *)
(* inline memcpy, its hash H by mlkem_sha3_256 and the last 32 bytes z of    *)
(* coins. If mlkem768_indcpa_keypair_derand returned an error, which it      *)
(* never does, the function would zero the keys. It is verified in the whole *)
(* image (see libmlkem.ml), using the theorems for                           *)
(* mlkem768_indcpa_keypair_derand and mlkem_sha3_256 in the image.           *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/gcc12_O2/indcpa_keypair_derand_k3_proof.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/sha3_256_proof.ml";;
needs "x86/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    mlkem768_keypair_derand:
       +0x0: push   r13
       +0x2: push   r12
       +0x4: mov    r12,rdx
       +0x7: push   rbp
       +0x8: mov    rbp,rdi
       +0xb: push   rbx
       +0xc: mov    rbx,rsi
       +0xf: sub    rsp,0x8
      +0x13: call   <mlkem768_indcpa_keypair_derand>
      +0x18: mov    r13d,eax
      +0x1b: test   eax,eax
      +0x1d: jne    <mlkem768_keypair_derand+0xa8>
      +0x23: mov    rax,QWORD PTR [rbp+0x0]
      +0x27: lea    rdi,[rbx+0x488]
      +0x2e: lea    rcx,[rbx+0x480]
      +0x35: mov    rsi,rbp
      +0x38: and    rdi,0xfffffffffffffff8
      +0x3c: mov    QWORD PTR [rbx+0x480],rax
      +0x43: sub    rcx,rdi
      +0x46: mov    rdx,QWORD PTR [rbp+0x498]
      +0x4d: lea    rax,[rbx+0x920]
      +0x54: sub    rsi,rcx
      +0x57: add    ecx,0x4a0
      +0x5d: mov    QWORD PTR [rbx+0x918],rdx
      +0x64: shr    ecx,0x3
      +0x67: mov    edx,0x4a0
      +0x6c: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
      +0x6f: mov    rsi,rbp
      +0x72: mov    rdi,rax
      +0x75: call   <mlkem_sha3_256>
      +0x7a: movdqu xmm0,XMMWORD PTR [r12+0x20]
      +0x81: mov    eax,r13d
      +0x84: movups XMMWORD PTR [rbx+0x940],xmm0
      +0x8b: movdqu xmm1,XMMWORD PTR [r12+0x30]
      +0x92: movups XMMWORD PTR [rbx+0x950],xmm1
      +0x99: add    rsp,0x8
      +0x9d: pop    rbx
      +0x9e: pop    rbp
      +0x9f: pop    r12
      +0xa1: pop    r13
      +0xa3: ret
 ***)

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [(layout "mlkem768_keypair_derand",layout "mlkem768_keypair_derand" + 0xa4)];;

let KK3_EXEC = MLKEM_NATIVE_KEYPAIR_DERAND_K3_GCC12_O2_EXEC;;

let KPKE_KEYGEN_LENGTHS_768 = prove
 (`!d. LENGTH(FST(kpke_keygen mlkem768 d)) = 1184 /\
       LENGTH(SND(kpke_keygen mlkem768 d)) = 1152`,
  REWRITE_TAC[mlkem768; KPKE_KEYGEN_LENGTHS] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The copy of z into the decapsulation key, from its two 128-bit halves,    *)
(* and the final combination of the parts of the keys, as for AArch64. The   *)
(* copy of the encapsulation key is by KEM_MEMCPY_TAC (see                   *)
(* mlkem_native_kem.ml), and z is copied by legacy SSE moves through XMM0    *)
(* and XMM1, so the values of YMM0 and YMM1 after the hash are named.        *)
(* ------------------------------------------------------------------------- *)

let KK3_Z_TAC s =
  MP_TAC(SPECL [`word_add sk (word 2368):int64`; `num_of_bytelist z`;
                mk_var(s,`:x86state`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `z:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

let KK3_FINAL_TAC =
  REWRITE_TAC[mlkem768; MLKEM_KEYGEN_PAIR] THEN REWRITE_TAC[GSYM mlkem768] THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_KEYGEN_LENGTHS_768;
              mlkem_h; LENGTH_SHA3_256] THEN
  REWRITE_TAC[ARITH_RULE `2400 = 1152 + 1248`; ARITH_RULE `1248 = 1184 + 64`;
              ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is d followed by z, 32 bytes each, at coins,  *)
(* and the encapsulation key of 1184 bytes at pk and the decapsulation key   *)
(* of 2400 bytes at sk are those of mlkem_keygen_internal mlkem768 d z in    *)
(* common/fips203/fips203.ml. The theorem assumes that SampleNTT terminates  *)
(* for each entry of the matrix, as for mlkem768_indcpa_keypair_derand. The  *)
(* stack is the 40 bytes of the four pushes and the alignment of the stack   *)
(* for the calls, the return address of the call and the 14016 bytes used by *)
(* mlkem768_indcpa_keypair_derand below them.                                *)
(* ------------------------------------------------------------------------- *)

let KK3_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KK3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KK3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `z:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 14064 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`] THEN
  MP_TAC(SPEC `d:byte list` KPKE_KEYGEN_LENGTHS_768) THEN STRIP_TAC;;

let KK3_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KK3_CALL in
  ENSURES_INIT_TAC "s0" THEN
  KEM_HALVES_TAC `word_add coins (word 32):int64` THEN

  (*** The K-PKE keys ***)

  X86_STEPS_TAC KK3_EXEC (1--9) THEN
  call MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `d:byte list`] @ post) 10 THEN

  (*** The copy of the encapsulation key into the decapsulation key ***)

  X86_STEPS_TAC KK3_EXEC (11--13) THEN
  KEM_MEMCPY_TAC KK3_EXEC 14 28 1152 1184 `stackpointer:int64,14072` THEN

  (*** Its hash and z ***)

  X86_STEPS_TAC KK3_EXEC (29--31) THEN
  call MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `FST(kpke_keygen mlkem768 d)`] @ post) 32 THEN
  INDCPA_YMMS_TAC "s32" [0; 1] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KK3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (33--37) THEN
  KK3_Z_TAC "s37" THEN
  X86_STEPS_TAC KK3_EXEC (38--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KK3_FINAL_TAC;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!pk sk coins (d:byte list) (z:byte list) pc stackpointer
    returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH d = 32 /\ LENGTH z = 32 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (FST(mlkem_g(APPEND d [word 3])))
                        [word j; word i])) /\
    PAIRWISE nonoverlapping
     [(pk,1184); (sk,2400); (word_sub stackpointer (word 14064),14072)] /\
    ALLPAIRS nonoverlapping
     [(pk,1184); (sk,2400); (word_sub stackpointer (word 14064),14072)]
     [(coins,64); (word pc,libmlkem_size)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem768_keypair_derand) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
              read (memory :> bytes(word_add coins (word 32),32)) s =
              num_of_bytelist z)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(pk,1184)) s =
              num_of_bytelist(FST(mlkem_keygen_internal mlkem768 d z)) /\
              read (memory :> bytes(sk,2400)) s =
              num_of_bytelist(SND(mlkem_keygen_internal mlkem768 d z)) /\
              C_RETURN s = word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
            memory :> bytes(word_sub stackpointer (word 14064),14064)])`,
  KK3_INTRO_TAC THEN KK3_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for                             *)
(* mlkem768_indcpa_keypair_derand, the events depend only on the addresses   *)
(* and on rho, and the theorem also states that rho is the end of the public *)
(* key, which the copy into the secret key and its hash do not change. The   *)
(* events of the REP MOVSQ depend on the address of the secret key modulo 8, *)
(* through lo, which is expanded in them.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let KK3_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `coins:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `d:byte list`; `rho:byte list`];;

let KK3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KK3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KK3_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KK3_SAFE_INTRO_TAC =
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_INDCPA";
    MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHA3_256"] THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `coins:int64`;
    `d:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 14064 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KK3_SAFE_MAIN_TAC =
  let call = KK3_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KK3_EXEC (1--9) THEN
  call "H_INDCPA"
   [`read RDI s`; `read RSI s`; `read RDX s`; `d:byte list`] 10 THEN
  X86_STEPS_TAC KK3_EXEC (11--26) THEN KEM_MEMCPY_REGS_TAC 1152 1184 THEN
  MAP_EVERY (fun r ->
    SUBGOAL_THEN
     (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                      `word_add sk (word (1152 + lo)):int64,1176`),r))
     ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC])
   [`word_add pk (word 1152):int64,32`; `stackpointer:int64,14072`;
    `word pc:int64,libmlkem_size`] THEN
  X86_STEPS_TAC KK3_EXEC (27--28) THEN KEM_UNLO_TAC THEN
  X86_STEPS_TAC KK3_EXEC (29--31) THEN
  call "H_SHA3_256" [`read RDI s`; `read RSI s`; `1184`] 32 THEN
  X86_STEPS_TAC KK3_EXEC (33--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND_NIL] THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 3]))` THEN
  KEM_MEMCPY_DISCHARGE_TAC `word_add sk (word 1152):int64`;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e pk sk coins (d:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH d = 32 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (FST(mlkem_g(APPEND d [word 3])))
                        [word j; word i])) /\
    PAIRWISE nonoverlapping
     [(pk,1184); (sk,2400); (word_sub stackpointer (word 14064),14072)] /\
    ALLPAIRS nonoverlapping
     [(pk,1184); (sk,2400); (word_sub stackpointer (word 14064),14072)]
     [(coins,64); (word pc,libmlkem_size)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem768_keypair_derand) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word 0 /\
              read (memory :> bytes(word_add pk (word 1152),32)) s =
              num_of_bytelist(FST(mlkem_g(APPEND d [word 3]))) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk sk coins pc
                        (word_sub stackpointer (word 14064)) returnaddress
                        (FST(mlkem_g(APPEND d [word 3]))) /\
                 memaccess_inbounds e2
                  [coins,64; pk,1184; sk,2400;
                   word_sub stackpointer (word 14064),14072;
                   word(pc + mlkem_poly_tomont_consts),48; word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                   word(pc + mlkem768_gen_matrix_consts),4; word(pc + rodata_mlk_zetas),256]
                  [pk,1184; sk,2400;
                   word_sub stackpointer (word 14064),14064]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
            memory :> bytes(word_sub stackpointer (word 14064),14064)])`,
  KK3_SAFE_INTRO_TAC THEN KK3_SAFE_MAIN_TAC);;
