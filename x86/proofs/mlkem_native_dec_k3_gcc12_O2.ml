(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-768 (FIPS 203 Algorithm 18, with the input    *)
(* check of Algorithm 21). This is the code for mlkem768_dec from            *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md). It checks the decapsulation key with             *)
(* mlkem768_check_sk, and returns -5 if the check fails. Otherwise it        *)
(* decrypts the ciphertext into m' with mlkem768_indcpa_dec, computes K' and *)
(* r' as G of m' followed by the hash h in the key with mlkem_sha3_512,      *)
(* encrypts m' with r' again by mlkem768_indcpa_enc, compares the result     *)
(* with the ciphertext in constant time, computes J of z (in the key)        *)
(* followed by the ciphertext into the shared secret with mlkem_shake256,    *)
(* and replaces it by K' if the ciphertexts are equal, again in constant     *)
(* time. In both cases it zeroes its buffers. It is verified in the whole    *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x71c0, using the theorems for mlkem768_check_sk, mlkem768_indcpa_dec,    *)
(* mlkem_sha3_512, mlkem768_indcpa_enc and mlkem_shake256 in the image.      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_check_sk_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_indcpa_dec_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_indcpa_enc_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake256_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    71c0: push   rbp
    71c1: mov    rbp,rsp
    71c4: push   r15
    71c6: mov    r15,rsi
    71c9: push   r14
    71cb: mov    r14,rdi
    71ce: mov    rdi,rdx
    71d1: push   r13
    71d3: mov    r13,rdx
    71d6: push   r12
    71d8: push   rbx
    71d9: and    rsp,0xffffffffffffffe0
    71dd: sub    rsp,0x500
    71e4: call   6de0 <mlkem768_check_sk>
    71e9: test   eax,eax
    71eb: je     7258 <mlkem768_dec+0x98>
    71ed: mov    ebx,eax
    71ef: lea    r10,[rsp+0x20]
    71f4: lea    r9,[rsp+0x60]
    71f9: lea    r8,[rsp+0xa0]
    7201: xor    eax,eax
    7203: mov    rdi,r8
    7206: mov    ecx,0x8c
    720b: rep    stos QWORD PTR es:[rdi],rax
    720e: pxor   xmm0,xmm0
    7212: movaps XMMWORD PTR [rsp+0x60],xmm0
    7217: movaps XMMWORD PTR [rsp+0x70],xmm0
    721c: movaps XMMWORD PTR [rsp+0x80],xmm0
    7224: movaps XMMWORD PTR [rsp+0x90],xmm0
    722c: movaps XMMWORD PTR [rsp+0x20],xmm0
    7231: movaps XMMWORD PTR [rsp+0x30],xmm0
    7236: movaps XMMWORD PTR [rsp+0x40],xmm0
    723b: movaps XMMWORD PTR [rsp+0x50],xmm0
    7240: lea    rsp,[rbp-0x28]
    7244: mov    eax,ebx
    7246: pop    rbx
    7247: pop    r12
    7249: pop    r13
    724b: pop    r14
    724d: pop    r15
    724f: pop    rbp
    7250: ret
    7251: nop    DWORD PTR [rax+0x0]
    7258: lea    r10,[rsp+0x20]
    725d: mov    rdx,r13
    7260: mov    rsi,r15
    7263: mov    rdi,r10
    7266: mov    QWORD PTR [rsp+0x18],r10
    726b: call   6bc0 <mlkem768_indcpa_dec>
    7270: mov    r10,QWORD PTR [rsp+0x18]
    7275: test   eax,eax
    7277: mov    ebx,eax
    7279: je     7290 <mlkem768_dec+0xd0>
    727b: lea    r9,[rsp+0x60]
    7280: lea    r8,[rsp+0xa0]
    7288: jmp    7201 <mlkem768_dec+0x41>
    728d: nop    DWORD PTR [rax]
    7290: lea    r9,[rsp+0x60]
    7295: mov    rsi,r10
    7298: mov    edx,0x40
    729d: mov    QWORD PTR [rsp+0x18],r10
    72a2: movdqu xmm3,XMMWORD PTR [r13+0x920]
    72ab: mov    rdi,r9
    72ae: mov    QWORD PTR [rsp+0x8],r9
    72b3: movdqu xmm4,XMMWORD PTR [r13+0x930]
    72bc: movaps XMMWORD PTR [rsp+0x40],xmm3
    72c1: movaps XMMWORD PTR [rsp+0x50],xmm4
    72c6: call   3570 <mlkem_sha3_512>
    72cb: mov    r10,QWORD PTR [rsp+0x18]
    72d0: lea    r8,[rsp+0xa0]
    72d8: lea    rcx,[rsp+0x80]
    72e0: mov    rdi,r8
    72e3: lea    rdx,[r13+0x480]
    72ea: mov    QWORD PTR [rsp+0x18],r8
    72ef: mov    rsi,r10
    72f2: mov    QWORD PTR [rsp+0x10],r10
    72f7: call   68d0 <mlkem768_indcpa_enc>
    72fc: mov    r8,QWORD PTR [rsp+0x18]
    7301: mov    r10,QWORD PTR [rsp+0x10]
    7306: test   eax,eax
    7308: mov    r9,QWORD PTR [rsp+0x8]
    730d: mov    ebx,eax
    730f: jne    7201 <mlkem768_dec+0x41>
    7315: pxor   xmm2,xmm2
    7319: xor    eax,eax
    731b: movdqa xmm0,xmm2
    731f: nop
    7320: movdqu xmm1,XMMWORD PTR [r15+rax*1]
    7326: pxor   xmm1,XMMWORD PTR [r8+rax*1]
    732c: add    rax,0x10
    7330: por    xmm0,xmm1
    7334: pxor   xmm2,xmm1
    7338: cmp    rax,0x440
    733e: jne    7320 <mlkem768_dec+0x160>
    7340: movdqa xmm1,xmm2
    7344: mov    QWORD PTR [rsp+0x8],r10
    7349: psrldq xmm1,0x8
    734e: mov    QWORD PTR [rsp+0x10],r9
    7353: pxor   xmm2,xmm1
    7357: movdqa xmm1,xmm2
    735b: psrldq xmm1,0x4
    7360: pxor   xmm2,xmm1
    7364: movdqa xmm1,xmm2
    7368: psrldq xmm1,0x2
    736d: pxor   xmm2,xmm1
    7371: movdqa xmm1,xmm2
    7375: psrldq xmm1,0x1
    737a: pxor   xmm2,xmm1
    737e: movdqa xmm1,xmm0
    7382: psrldq xmm1,0x8
    7387: movd   eax,xmm2
    738b: por    xmm0,xmm1
    738f: movdqa xmm1,xmm0
    7393: psrldq xmm1,0x4
    7398: por    xmm0,xmm1
    739c: movdqa xmm1,xmm0
    73a0: psrldq xmm1,0x2
    73a5: por    xmm0,xmm1
    73a9: movdqa xmm1,xmm0
    73ad: psrldq xmm1,0x1
    73b2: por    xmm0,xmm1
    73b6: movd   r12d,xmm0
    73bb: movzx  r12d,r12b
    73bf: neg    r12d
    73c2: sar    r12d,0x10
    73c6: xor    r12d,eax
    73c9: xor    r12d,eax
    73cc: mov    rdx,r8
    73cf: mov    ecx,0x88
    73d4: mov    rsi,r15
    73d7: movdqu xmm6,XMMWORD PTR [r13+0x950]
    73e0: mov    QWORD PTR [rsp+0x18],r8
    73e5: movzx  r12d,r12b
    73e9: lea    rax,[rsp+0xc0]
    73f1: movdqu xmm5,XMMWORD PTR [r13+0x940]
    73fa: mov    rdi,rax
    73fd: neg    r12d
    7400: movaps XMMWORD PTR [rsp+0xb0],xmm6
    7408: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
    740b: mov    ecx,0x460
    7410: mov    esi,0x20
    7415: mov    rdi,r14
    7418: movaps XMMWORD PTR [rsp+0xa0],xmm5
    7420: call   3480 <mlkem_shake256>
    7425: mov    r10,QWORD PTR [rsp+0x8]
    742a: mov    r9,QWORD PTR [rsp+0x10]
    742f: xor    eax,eax
    7431: mov    r8,QWORD PTR [rsp+0x18]
    7436: cs     nop WORD PTR [rax+rax*1+0x0]
    7440: movzx  esi,BYTE PTR [r9+rax*1]
    7445: mov    ecx,r12d
    7448: movzx  edx,BYTE PTR [r14+rax*1]
    744d: sar    ecx,0x10
    7450: xor    edx,esi
    7452: and    edx,ecx
    7454: xor    edx,esi
    7456: mov    BYTE PTR [r14+rax*1],dl
    745a: add    rax,0x1
    745e: cmp    rax,0x20
    7462: jne    7440 <mlkem768_dec+0x280>
    7464: jmp    7201 <mlkem768_dec+0x41>
 ***)

let MLKEM_NATIVE_DEC_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x71c0,0x7469];;

let KD3_EXEC = MLKEM_NATIVE_DEC_K3_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-768, and the input check   *)
(* of FIPS 203 in terms of the result of mlkem768_check_sk.                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_768 = prove
 (`!ek m r. LENGTH(kpke_encrypt mlkem768 ek m r) = 1088`,
  REWRITE_TAC[mlkem768; KPKE_ENCRYPT_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let KPKE_DECRYPT_LENGTH_768 = prove
 (`!dk c. LENGTH(kpke_decrypt mlkem768 dk c) = 32`,
  REWRITE_TAC[mlkem768; KPKE_DECRYPT_LENGTH]);;

let KD3_CHECK = prove
 (`!dk c. LENGTH dk = 2400 /\ LENGTH c = 1088
          ==> (mlkem_decaps_check mlkem768 dk c <=>
               num_of_bytelist(mlkem_slice 2336 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 1152 1184 dk)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem768; mlkem_decaps_check] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[mlkem_h] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ; LENGTH_SHA3_256]);;

(* ------------------------------------------------------------------------- *)
(* The frame, the slices of the decapsulation key, and the values computed:  *)
(* m', G of m' and h, K' and r', the reencryption c' of m', z, the result of *)
(* J, and whether c' is the ciphertext. The buffers are aligned to 32 bytes  *)
(* within the stack frame, by AND with -32 after the pushes, as in           *)
(* mlkem768_indcpa_dec, and their addresses are offsets from the frame       *)
(* variable bot of INDCPA_BOT_TAC, the bottom of the stacks of the callees   *)
(* 17000 bytes below them: m' and h at bot + 17032, K' and r' at bot + 17096 *)
(* and c', and then z and the copy of the ciphertext, at bot + 17160.        *)
(* ------------------------------------------------------------------------- *)

let KD3_FRAME = (18360,48,17000,1280);;

let KD3_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KD3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KD3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 18360 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SIMP_TAC[KD3_CHECK; ASSUME `LENGTH(dk:byte list) = 2400`;
           ASSUME `LENGTH(c:byte list) = 1088`] THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1152 (dk:byte list)) = 1152 /\
    LENGTH(mlkem_slice 1152 1184 (dk:byte list)) = 1184 /\
    LENGTH(mlkem_slice 2336 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 2368 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1152`; `32`; `1152`; `1184`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1152 + 32 <= 1184`)))] o
   check (fun th -> is_forall(concl th) &&
                    INDCPA_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD3_SETUP_TAC =
  INDCPA_BOT_TAC KD3_FRAME [17000] THEN
  INDCPA_FRAME_TAC ["memory :> bytes(ss:int64,32)"] KD3_FRAME THEN
  INDCPA_NONOV_TAC 18280
   [`ss:int64,32`; `ct:int64,1088`; `sk:int64,2400`;
    `word pc:int64,0x82a0`; `word_add stackpointer (word 18312):int64,56`;
    `word 0:int64,1`]
  THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KD3_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,2400)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,1152; 1152,1184; 2336,32; 2368,32]
    else NO_TAC);;

let KD3_MP = `kpke_decrypt mlkem768 (mlkem_slice 0 1152 dk) c`;;

let KD3_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem768 (mlkem_slice 0 1152 dk) c)
                  (mlkem_slice 2336 32 dk))`;;

let KD3_KP = mk_comb(`mlkem_slice 0 32`,KD3_GG);;

let KD3_RR = mk_comb(`mlkem_slice 32 32`,KD3_GG);;

let KD3_CP = list_mk_comb(`kpke_encrypt mlkem768`,
  [`mlkem_slice 1152 1184 (dk:byte list)`; KD3_MP; KD3_RR]);;

let KD3_ZZ = `mlkem_slice 2368 32 (dk:byte list)`;;

let KD3_KB =
 `list_of_seq (shake256 (APPEND (mlkem_slice 2368 32 dk) c)) 32`;;

let KD3_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD3_CP));;

let KD3_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD3_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD3_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD3_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD3_ZZ),`ZZ:num`;
         KD3_EQ,`EQ:bool`] tm;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the comparison loop at iteration i states that the OR    *)
(* accumulator in XMM0 is zero if and only if the first 16 * i bytes of the  *)
(* ciphertext and of c' are equal, and the invariant of the conditional move *)
(* at iteration i that the first i bytes at ss are those of K' if the        *)
(* ciphertexts are equal and those of the result of J otherwise, and the     *)
(* others still those of the result of J. Both keep the registers, the       *)
(* pushes and K' (KEEP).                                                     *)
(* ------------------------------------------------------------------------- *)

let KD3_SAFE_KEEP =
 `read RSP s = word_add bot (word 17000) /\
  read RBP s = word_add stackpointer (word 18352) /\
  read RBX s = word 0 /\
  read R13 s = sk /\ read R14 s = ss /\ read R15 s = ct /\
  read R8 s = word_add bot (word 17160) /\
  read R9 s = word_add bot (word 17096) /\
  (read DF s <=> false) /\
  read (memory :> bytes64 (word_add stackpointer (word 18360))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 18352))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18344))) s =
  r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18336))) s =
  r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18328))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18320))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18312))) s =
  rbx_init`;;

let KD3_KEEP = KD3_SUBST
 `read RSP s = word_add bot (word 17000) /\
  read RBP s = word_add stackpointer (word 18352) /\
  read RBX s = word 0 /\
  read R13 s = sk /\ read R14 s = ss /\ read R15 s = ct /\
  read R8 s = word_add bot (word 17160) /\
  read R9 s = word_add bot (word 17096) /\
  (read DF s <=> false) /\
  read (memory :> bytes64 (word_add stackpointer (word 18360))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 18352))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18344))) s =
  r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18336))) s =
  r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18328))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18320))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 18312))) s =
  rbx_init /\
  read (memory :> bytes(word_add bot (word 17096),32)) s = KP`;;

let KD3_WITH_KEEP keep inv =
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [keep,`KEEP:bool`] bod);;

let KD3_INV = KD3_WITH_KEEP KD3_KEEP (KD3_SUBST
 `\i s. read RAX s = word(16 * i) /\
        read R10 s = word_add bot (word 17032) /\
        read R12 s = r12_init /\
        (word_subword (read YMM0 s) (0,128):int128 = word 0 <=>
         num_of_bytelist c MOD 2 EXP (128 * i) = CP MOD 2 EXP (128 * i)) /\
        read (memory :> bytes(ct,1088)) s = num_of_bytelist c /\
        read (memory :> bytes(word_add bot (word 17160),1088)) s = CP /\
        read (memory :> bytes128 (word_add sk (word 2368))) s =
        word(ZZ MOD 2 EXP 128) /\
        read (memory :> bytes128 (word_add sk (word 2384))) s =
        word(ZZ DIV 2 EXP 128) /\ KEEP`);;

let KD3_CMOV_INV = KD3_WITH_KEEP KD3_KEEP (KD3_SUBST
 `\i s. read RAX s = word i /\
        read R12 s = (if EQ then word 0 else word 4294967041) /\
        read (memory :> bytes(ss,i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\
        read (memory :> bytes(word_add ss (word i),32 - i)) s =
        KB DIV 2 EXP (8 * i) /\ KEEP`);;

(* ------------------------------------------------------------------------- *)
(* From the start to the comparison loop: the check of the key, the          *)
(* decryption, G of m' and h and the reencryption. The hash h is copied      *)
(* after m' and the comparison starts with legacy SSE moves, so the values   *)
(* of the YMM registers that they use are named.                             *)
(* ------------------------------------------------------------------------- *)

let KD3_G_INPUT_TAC s =
  let st = mk_var(s,`:x86state`) in
  SUBGOAL_THEN
   (subst [st,`s:x86state`; INDCPA_SP 17032,`a:int64`;
           KD3_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 2336 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND;
                    KPKE_DECRYPT_LENGTH_768];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD3_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 2336 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_768] THEN
    ARITH_TAC;
    ALL_TAC];;

let KD3_KR_TAC s =
  let st = mk_var(s,`:x86state`) and a = INDCPA_SP 17096 in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:x86state`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD3_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD3_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD3_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD3_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KD3_PART1_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD3_CALL in
  ENSURES_INIT_TAC "s0" THEN KD3_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 2336):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 2368):int64` THEN

  (*** The check of the key ***)

  X86_STEPS_TAC KD3_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD3_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `mlkem_slice 1152 1184 (dk:byte list)`;
     `num_of_bytelist(mlkem_slice 2336 32 (dk:byte list))`] @ post) 15 THEN
  INDCPA_NORM_TAC THEN

  (*** The decryption, G and the reencryption ***)

  X86_STEPS_TAC KD3_EXEC (16--23) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`;
     `mlkem_slice 0 1152 (dk:byte list)`; `c:byte list`] @ post) 24 THEN
  INDCPA_NORM_TAC THEN INDCPA_YMMS_TAC "s24" [3; 4] THEN
  X86_STEPS_TAC KD3_EXEC (25--32) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (33--38) THEN
  INDCPA_NORM_TAC THEN
  KEM_JOIN_TAC (INDCPA_SP 17064) `mlkem_slice 2336 32 (dk:byte list)` "s38"
  THEN KD3_G_INPUT_TAC "s38" THEN
  X86_STEPS_TAC KD3_EXEC [39] THEN
  call MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`;
     mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD3_MP),
             `mlkem_slice 2336 32 (dk:byte list)`)] @ post) 40 THEN
  INDCPA_NORM_TAC THEN KD3_KR_TAC "s40" THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD3_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_768]; ALL_TAC] THEN
  X86_STEPS_TAC KD3_EXEC (41--49) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
     `mlkem_slice 1152 1184 (dk:byte list)`; KD3_MP; KD3_RR] @ post) 50 THEN
  INDCPA_NORM_TAC THEN

  (*** The start of the comparison ***)

  X86_STEPS_TAC KD3_EXEC (51--56) THEN INDCPA_YMMS_TAC "s56" [0; 2] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (57--60) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[KEM_SUBWORD_JOIN_128; MOD_1] THEN CONV_TAC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the comparison, with the loop test. The two 128-bit      *)
(* words loaded are given in the form of the address computed for the base   *)
(* and index registers (KEM_INDEX_TAC), and the values of the YMM registers  *)
(* at the start of the iteration are introduced as ghosts.                   *)
(* ------------------------------------------------------------------------- *)

let KD3_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 68 ==> 16 * i + 16 <= 1088`)
               (ASSUME `i < 68`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`1088`) && vv = v ->
          let lth = SPECL [a; `1088`; `i:num`; v; s] KEM_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (MP lth (CONJ th bth)))
    | _ -> NO_TAC);;

let KD3_TEST = prove
 (`!i. i < 68
       ==> (val(word_add (word(16 * i)) (word 18446744073709550544):int64) =
            0 <=> ~(i + 1 < 68))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 68 ==> 16 * i < 18446744073709551616`] THEN
  ASM_CASES_TAC `i + 1 < 68` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i + 1 < 68 ==> 16 * i + 18446744073709550544 < 18446744073709551616`]
    THEN ARITH_TAC;
    SUBGOAL_THEN `i = 67` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]]);;

let KD3_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  ENSURES_INIT_TAC "s0" THEN
  KD3_CHUNK_TAC `ct:int64` `num_of_bytelist c` THEN
  KD3_CHUNK_TAC (INDCPA_SP 17160) (mk_comb(`num_of_bytelist`,KD3_CP)) THEN
  VAL_INT64_TAC `16 * i` THEN KEM_INDEX_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD3_TEST) (ASSUME `i < 68`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 68` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[KEM_SUBWORD_JOIN_128; KEM_OR_STEP; KEM_MOD_STEP] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[CONJ_ACI; EQ_SYM_EQ];
    CONV_TAC NUM_REDUCE_CONV];;

(* ------------------------------------------------------------------------- *)
(* From the comparison loop to the conditional move: the result of the       *)
(* comparison as a mask of 0 or 4294967041 (the XOR accumulator, which is    *)
(* also reduced and cancels out, does not matter), by BITBLAST, z and the    *)
(* ciphertext copied after it (by REP MOVSQ, see KEM_MOVSQ_STEP_TAC) and J   *)
(* of them.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KD3_Q = `word_subword (y0:int256) (0,128):int128`;;

let KD3_DONE_TAC =
  SUBGOAL_THEN (mk_iff(mk_eq(KD3_Q,`word 0:int128`),KD3_EQ)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = mk_eq(KD3_Q,`word 0:int128`)
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(ISPEC `c:byte list` NUM_OF_BYTELIST_BOUND) THEN
    MP_TAC(ISPEC KD3_CP NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_768] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let KD3_MASK_TAC s =
  let r12 = mk_comb(`read R12`,mk_var(s,`:x86state`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = r12 then
      let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[KEM_MOD256])) th in
      let eth = BITBLAST_RULE
        (mk_eq(rand(concl th1),
               mk_cond(mk_eq(KD3_Q,`word 0:int128`),
                       `word 0:int64`,`word 4294967041:int64`))) in
      ASSUME_TAC(TRANS th1 eth)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = r12 then
      FIRST_ASSUM(fun th' ->
        if is_iff(concl th') &&
           lhand(concl th') = mk_eq(KD3_Q,`word 0:int128`)
        then ASSUME_TAC(REWRITE_RULE[th'] th) else NO_TAC)
    else NO_TAC);;

let KD3_J_INPUT_TAC s =
  let st = mk_var(s,`:x86state`) in
  SUBGOAL_THEN
   (subst [st,`s:x86state`; INDCPA_SP 17160,`a:int64`]
     `read (memory :> bytes(a,1120)) s =
      num_of_bytelist(APPEND (mlkem_slice 2368 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1120 = 32 + 1088`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 2368 32 (dk:byte list)) c) = 1120`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

let KD3_EXIT_A_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD3_CALL in
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `y5:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `y6:int256` `read YMM6` THEN
  ENSURES_INIT_TAC "s0" THEN KD3_DONE_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (1--44) THEN
  KD3_MASK_TAC "s44" THEN KEM_MOVSQ_STEP_TAC KD3_EXEC 45 136 THEN
  X86_STEPS_TAC KD3_EXEC (46--48) THEN
  X86_STEPS_TAC KD3_EXEC [49] THEN SIMD_SIMPLIFY_TAC[] THEN
  KEM_JOIN_TAC (INDCPA_SP 17160) KD3_ZZ "s49" THEN KD3_J_INPUT_TAC "s49" THEN
  X86_STEPS_TAC KD3_EXEC [50] THEN
  call MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `32`; `read RDX s`;
     `APPEND (mlkem_slice 2368 32 (dk:byte list)) c`] @ post) 51 THEN
  X86_STEPS_TAC KD3_EXEC (52--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers by REP STOSQ and SSE stores, and the result in terms of FIPS 203, *)
(* and the case where the check of the key fails.                            *)
(* ------------------------------------------------------------------------- *)

let KD3_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [INDCPA_SP 17096; `32`; mk_comb(`num_of_bytelist`,KD3_KP);
                `i:num`; `s0:x86state`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   (KD3_SUBST `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC th1 THEN ASSUME_TAC th2)] THEN
  VAL_INT64_TAC `i:num` THEN KEM_INDEX1_TAC THEN
  X86_STEPS_TAC KD3_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD];
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC KD3_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN REWRITE_TAC[KEM_MOD256] THEN
    SPEC_TAC(KD3_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD3_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; WORD_ADD; WORD_ADD_ASSOC;
                KEM_DIV_BYTE] THEN
    ASM_REWRITE_TAC[]];;

let KD3_FINAL_TAC =
  REWRITE_TAC[mlkem768; MLKEM_DECAPS_ALT] THEN
  REWRITE_TAC[GSYM mlkem768] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD3_CP,`c:byte list`),KD3_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_768];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let KD3_EXIT_B_TAC =
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KD3_EXEC (1--5) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (6--14) THEN
  X86_STEPS_TAC KD3_EXEC (15--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD3_FINAL_TAC;;

let KD3_BAD_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD3_CALL in
  ENSURES_INIT_TAC "s0" THEN KD3_SK_TAC THEN
  X86_STEPS_TAC KD3_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD3_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `mlkem_slice 1152 1184 (dk:byte list)`;
     `num_of_bytelist(mlkem_slice 2336 32 (dk:byte list))`] @ post) 15 THEN
  INDCPA_NORM_TAC THEN INDCPA_YMMS_TAC "s15" [0] THEN
  X86_STEPS_TAC KD3_EXEC (16--25) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (26--34) THEN
  X86_STEPS_TAC KD3_EXEC (35--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The decapsulation key dk of 2400 bytes is at sk and    *)
(* the ciphertext c of 1088 bytes at ct, and if they pass the check of FIPS  *)
(* 203, the shared secret of 32 bytes written at ss is that of               *)
(* mlkem_decaps_internal mlkem768 dk c in common/fips203.ml and the function *)
(* returns 0, and otherwise it returns -5. The theorem assumes that          *)
(* SampleNTT terminates for each entry of the matrix from the seed in the    *)
(* key and that the stack does not contain address 0, as for                 *)
(* mlkem768_indcpa_enc. The stack is the 18360 bytes below the return        *)
(* address, for the six saved registers, up to 31 bytes for the alignment,   *)
(* the 1280 bytes of the buffers and the 17000 used by the callees below     *)
(* them. The proof is by cases on the check of the key, with the two loops   *)
(* for the comparison and the conditional move.                              *)
(* ------------------------------------------------------------------------- *)

let KD3_OK_TAC =
  ENSURES_WHILE_UP2_TAC `68` `pc + 0x7320` `pc + 0x7340`
   KD3_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD3_PART1_TAC; KD3_BODY_TAC;
    ENSURES_WHILE_UP2_TAC `32` `pc + 0x7440` `pc + 0x7464`
     KD3_CMOV_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD3_EXIT_A_TAC; KD3_CMOV_BODY_TAC; KD3_EXIT_B_TAC]];;

let MLKEM_NATIVE_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!ss ct sk (dk:byte list) (c:byte list) pc stackpointer
    returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH dk = 2400 /\ LENGTH c = 1088 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 2304 32 dk) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 18360),18368) /\
    nonoverlapping (ss,32) (word_sub stackpointer (word 18360),18368) /\
    ALLPAIRS nonoverlapping
     [(ss,32); (word_sub stackpointer (word 18360),18368)]
     [(ct,1088); (sk,2400); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x71c0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ss; ct; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(ct,1088)) s = num_of_bytelist c /\
              read (memory :> bytes(sk,2400)) s = num_of_bytelist dk)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (mlkem_decaps_check mlkem768 dk c
               ==> read (memory :> bytes(ss,32)) s =
                   num_of_bytelist(mlkem_decaps_internal mlkem768 dk c)) /\
              C_RETURN s =
              (if mlkem_decaps_check mlkem768 dk c then word 0
               else word 0xfffffffb))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 18360),18360)])`,
  KD3_INTRO_TAC THEN KD3_SETUP_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 2336 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 1152 1184 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD3_OK_TAC; KD3_BAD_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses and on the encapsulation key ek in the decapsulation key and    *)
(* the hash h stored with it, through the check of the hash, given by the    *)
(* combined theorem for mlkem768_check_sk, and the reencryption, but not on  *)
(* the secret key, z or the ciphertext: the comparison of the ciphertexts    *)
(* and the selection of the shared secret are loops in constant time. The    *)
(* events are given by a template with cases on the check, with the events   *)
(* of the loops as ENUMERATEL, whose invariants have only the pointers and   *)
(* the frame, and the frame variables are expanded in them by                *)
(* INDCPA_UNBOT_TAC.                                                         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let KD3_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (pc:num) (stackpointer:int64)
   (returnaddress:int64) (ek:byte list) (h:byte list).
   if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
   then APPEND
         (APPEND (f_ev_exitb ss ct sk pc stackpointer returnaddress)
           (APPEND (ENUMERATEL 32
                     (\i. f_ev_cmov ss ct sk pc stackpointer returnaddress i))
                   (f_ev_exita ss ct sk pc stackpointer returnaddress)))
         (APPEND (ENUMERATEL 68
                   (\i. f_ev_cmp ss ct sk pc stackpointer returnaddress i))
                 (f_ev_prol ss ct sk pc stackpointer returnaddress ek h))
   else f_ev_bad ss ct sk pc stackpointer returnaddress ek h
   :(uarch_event)list`;;

let KD3_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `ekk:byte list`; `hh:byte list`; `i:num`;
   `bot:int64`;
   `f_ev_cmp:int64->int64->int64->num->int64->int64->num->
              (uarch_event)list`;
   `f_ev_cmov:int64->int64->int64->num->int64->int64->num->
              (uarch_event)list`];;

let KD3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KD3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KD3_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD3_SAFE_INV = KD3_WITH_KEEP KD3_SAFE_KEEP
 `\i s. read RAX s = word(16 * i) /\
        read R10 s = word_add bot (word 17032) /\ KEEP`;;

let KD3_SAFE_CMOV_INV = KD3_WITH_KEEP KD3_SAFE_KEEP
 `\i s. read RAX s = word i /\ KEEP`;;

let KD3_SAFE_INTRO_TAC =
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_IMAGE_SUBROUTINE_FULL, "H_CHECK";
    MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_DEC";
    MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHA3_512";
    MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_ENC";
    MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHAKE256"] THEN
  CONCRETIZE_F_EVENTS_TAC KD3_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 18360 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1152 (dk:byte list)) = 1152 /\
    LENGTH(mlkem_slice 1152 1184 (dk:byte list)) = 1184 /\
    LENGTH(mlkem_slice 2336 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 2368 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1152`; `32`; `1152`; `1184`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1152 + 32 <= 1184`)))] o
   check (fun th -> is_forall(concl th) &&
                    INDCPA_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD3_SAFE_START_TAC =
  let call = KD3_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN KD3_SK_TAC THEN
  X86_STEPS_TAC KD3_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD3_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call "H_CHECK"
   [`read RDI s`; `ekk:byte list`; `num_of_bytelist(hh:byte list)`] 15 THEN
  INDCPA_NORM_TAC;;

let KD3_SAFE_PART1_TAC =
  let call = KD3_SAFE_CALL_TAC in
  KD3_SAFE_START_TAC THEN
  X86_STEPS_TAC KD3_EXEC (16--23) THEN INDCPA_NORM_TAC THEN
  call "H_DEC" [`read RDI s`; `read RSI s`; `read RDX s`] 24 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KD3_EXEC (25--39) THEN INDCPA_NORM_TAC THEN
  call "H_SHA3_512" [`read RDI s`; `read RSI s`; `64`] 40 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KD3_EXEC (41--49) THEN INDCPA_NORM_TAC THEN
  call "H_ENC"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `ekk:byte list`]
   50 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC KD3_EXEC (51--60) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `16 * i` THEN
  X86_STEPS_TAC KD3_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD3_TEST) (ASSUME `i < 68`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_EXIT_A_TAC =
  let call = KD3_SAFE_CALL_TAC in
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC KD3_EXEC (1--50) THEN
  call "H_SHAKE256" [`read RDI s`; `32`; `read RDX s`; `1120`] 51 THEN
  X86_STEPS_TAC KD3_EXEC (52--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; APPEND_NIL; ENUMERATEL_APPEND_ZERO] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC KD3_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD]; ALL_TAC] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_EXIT_B_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC KD3_EXEC (1--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_BAD_TAC =
  KD3_SAFE_START_TAC THEN
  X86_STEPS_TAC KD3_EXEC (16--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH dk = 2400 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 2304 32 dk) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 18360),18368) /\
    nonoverlapping (ss,32) (word_sub stackpointer (word 18360),18368) /\
    ALLPAIRS nonoverlapping
     [(ss,32); (word_sub stackpointer (word 18360),18368)]
     [(ct,1088); (sk,2400); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x71c0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ss; ct; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(sk,2400)) s = num_of_bytelist dk /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events ss ct sk pc
                        (word_sub stackpointer (word 18360)) returnaddress
                        (mlkem_slice 1152 1184 dk) (mlkem_slice 2336 32 dk) /\
                 memaccess_inbounds e2
                  [ct,1088; sk,2400; ss,32;
                   word_sub stackpointer (word 18360),18368;
                   word(pc + 0x8000),8; word(pc + 0x8008),8;
                   word(pc + 0x8010),8; word(pc + 0x8080),48;
                   word(pc + 0x80c0),192; word(pc + 0x8180),4;
                   word(pc + 0x81a0),256]
                  [ss,32; word_sub stackpointer (word 18360),18360]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 18360),18360)])`,
  KD3_SAFE_INTRO_TAC THEN KD3_SETUP_TAC THEN
  ABBREV_TAC `ekk = mlkem_slice 1152 1184 (dk:byte list)` THEN
  ABBREV_TAC `hh = mlkem_slice 2336 32 (dk:byte list)` THEN
  ASM_CASES_TAC
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)` THEN
  ASM_REWRITE_TAC[] THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `68` `pc + 0x7320` `pc + 0x7340`
     KD3_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD3_SAFE_PART1_TAC; KD3_SAFE_BODY_TAC;
      ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x7440` `pc + 0x7464`
       KD3_SAFE_CMOV_INV THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; KD3_SAFE_EXIT_A_TAC; KD3_SAFE_CMOV_BODY_TAC;
        KD3_SAFE_EXIT_B_TAC]];
    KD3_SAFE_BAD_TAC]);;
