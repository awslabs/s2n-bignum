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
(* followed by the ciphertext into a buffer on the stack with                *)
(* mlkem_shake256, replaces it by K' if the ciphertexts are equal, again in  *)
(* constant time, and copies the 32 bytes to ss, which it writes only there. *)
(* In both cases it zeroes its buffers. It is verified in the whole image    *)
(* (see libmlkem.ml), using the theorems for mlkem768_check_sk,              *)
(* mlkem768_indcpa_dec, mlkem_sha3_512, mlkem768_indcpa_enc and              *)
(* mlkem_shake256 in the image.                                              *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/check_sk_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/indcpa_dec_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/sha3_512_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/indcpa_enc_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    mlkem768_dec:
       +0x0: push   rbp
       +0x1: mov    rbp,rsp
       +0x4: push   r15
       +0x6: push   r14
       +0x8: mov    r14,rsi
       +0xb: push   r13
       +0xd: mov    r13,rdx
      +0x10: push   r12
      +0x12: push   rbx
      +0x13: and    rsp,0xffffffffffffffe0
      +0x17: sub    rsp,0x500
      +0x1e: mov    QWORD PTR [rsp+0x18],rdi
      +0x23: mov    rdi,rdx
      +0x26: call   <mlkem768_check_sk>
      +0x2b: test   eax,eax
      +0x2d: je     <mlkem768_dec+0x98>
      +0x2f: mov    ebx,eax
      +0x31: lea    r15,[rsp+0x20]
      +0x36: lea    r10,[rsp+0x60]
      +0x3b: lea    r8,[rsp+0xa0]
      +0x43: xor    eax,eax
      +0x45: mov    rdi,r8
      +0x48: mov    ecx,0x8c
      +0x4d: rep    stos QWORD PTR es:[rdi],rax
      +0x50: pxor   xmm0,xmm0
      +0x54: movaps XMMWORD PTR [rsp+0x60],xmm0
      +0x59: movaps XMMWORD PTR [rsp+0x70],xmm0
      +0x5e: movaps XMMWORD PTR [rsp+0x80],xmm0
      +0x66: movaps XMMWORD PTR [rsp+0x90],xmm0
      +0x6e: movaps XMMWORD PTR [rsp+0x20],xmm0
      +0x73: movaps XMMWORD PTR [rsp+0x30],xmm0
      +0x78: movaps XMMWORD PTR [rsp+0x40],xmm0
      +0x7d: movaps XMMWORD PTR [rsp+0x50],xmm0
      +0x82: lea    rsp,[rbp-0x28]
      +0x86: mov    eax,ebx
      +0x88: pop    rbx
      +0x89: pop    r12
      +0x8b: pop    r13
      +0x8d: pop    r14
      +0x8f: pop    r15
      +0x91: pop    rbp
      +0x92: ret
      +0x93: nop    DWORD PTR [rax+rax*1+0x0]
      +0x98: lea    r15,[rsp+0x20]
      +0x9d: mov    rdx,r13
      +0xa0: mov    rsi,r14
      +0xa3: mov    rdi,r15
      +0xa6: call   <mlkem768_indcpa_dec>
      +0xab: mov    ebx,eax
      +0xad: test   eax,eax
      +0xaf: je     <mlkem768_dec+0xc0>
      +0xb1: lea    r10,[rsp+0x60]
      +0xb6: lea    r8,[rsp+0xa0]
      +0xbe: jmp    <mlkem768_dec+0x43>
      +0xc0: lea    r10,[rsp+0x60]
      +0xc5: mov    edx,0x40
      +0xca: mov    rsi,r15
      +0xcd: movdqu xmm3,XMMWORD PTR [r13+0x920]
      +0xd6: movdqu xmm4,XMMWORD PTR [r13+0x930]
      +0xdf: mov    rdi,r10
      +0xe2: mov    QWORD PTR [rsp+0x8],r10
      +0xe7: movaps XMMWORD PTR [rsp+0x40],xmm3
      +0xec: movaps XMMWORD PTR [rsp+0x50],xmm4
      +0xf1: call   <mlkem_sha3_512>
      +0xf6: lea    r8,[rsp+0xa0]
      +0xfe: lea    r11,[rsp+0x80]
     +0x106: mov    rsi,r15
     +0x109: mov    rdi,r8
     +0x10c: lea    rdx,[r13+0x480]
     +0x113: mov    rcx,r11
     +0x116: mov    QWORD PTR [rsp],r11
     +0x11a: mov    QWORD PTR [rsp+0x10],r8
     +0x11f: call   <mlkem768_indcpa_enc>
     +0x124: mov    r8,QWORD PTR [rsp+0x10]
     +0x129: mov    r10,QWORD PTR [rsp+0x8]
     +0x12e: test   eax,eax
     +0x130: mov    ebx,eax
     +0x132: jne    <mlkem768_dec+0x43>
     +0x138: pxor   xmm2,xmm2
     +0x13c: mov    r11,QWORD PTR [rsp]
     +0x140: xor    eax,eax
     +0x142: movdqa xmm0,xmm2
     +0x146: cs     nop WORD PTR [rax+rax*1+0x0]
     +0x150: movdqu xmm1,XMMWORD PTR [r14+rax*1]
     +0x156: pxor   xmm1,XMMWORD PTR [r8+rax*1]
     +0x15c: add    rax,0x10
     +0x160: por    xmm0,xmm1
     +0x164: pxor   xmm2,xmm1
     +0x168: cmp    rax,0x440
     +0x16e: jne    <mlkem768_dec+0x150>
     +0x170: movdqa xmm1,xmm2
     +0x174: mov    QWORD PTR [rsp],r11
     +0x178: psrldq xmm1,0x8
     +0x17d: mov    QWORD PTR [rsp+0x8],r10
     +0x182: pxor   xmm2,xmm1
     +0x186: movdqa xmm1,xmm2
     +0x18a: psrldq xmm1,0x4
     +0x18f: pxor   xmm2,xmm1
     +0x193: movdqa xmm1,xmm2
     +0x197: psrldq xmm1,0x2
     +0x19c: pxor   xmm2,xmm1
     +0x1a0: movdqa xmm1,xmm2
     +0x1a4: psrldq xmm1,0x1
     +0x1a9: pxor   xmm2,xmm1
     +0x1ad: movdqa xmm1,xmm0
     +0x1b1: psrldq xmm1,0x8
     +0x1b6: movd   eax,xmm2
     +0x1ba: por    xmm0,xmm1
     +0x1be: movdqa xmm1,xmm0
     +0x1c2: psrldq xmm1,0x4
     +0x1c7: por    xmm0,xmm1
     +0x1cb: movdqa xmm1,xmm0
     +0x1cf: psrldq xmm1,0x2
     +0x1d4: por    xmm0,xmm1
     +0x1d8: movdqa xmm1,xmm0
     +0x1dc: psrldq xmm1,0x1
     +0x1e1: por    xmm0,xmm1
     +0x1e5: movd   r12d,xmm0
     +0x1ea: movzx  r12d,r12b
     +0x1ee: neg    r12d
     +0x1f1: sar    r12d,0x10
     +0x1f5: xor    r12d,eax
     +0x1f8: xor    r12d,eax
     +0x1fb: mov    rdx,r8
     +0x1fe: mov    ecx,0x88
     +0x203: mov    rsi,r14
     +0x206: movdqu xmm6,XMMWORD PTR [r13+0x950]
     +0x20f: mov    QWORD PTR [rsp+0x10],r8
     +0x214: movzx  r12d,r12b
     +0x218: lea    rax,[rsp+0xc0]
     +0x220: movdqu xmm5,XMMWORD PTR [r13+0x940]
     +0x229: mov    rdi,rax
     +0x22c: neg    r12d
     +0x22f: movaps XMMWORD PTR [rsp+0xb0],xmm6
     +0x237: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
     +0x23a: mov    ecx,0x460
     +0x23f: mov    esi,0x20
     +0x244: mov    rdi,r15
     +0x247: movaps XMMWORD PTR [rsp+0xa0],xmm5
     +0x24f: call   <mlkem_shake256>
     +0x254: mov    r10,QWORD PTR [rsp+0x8]
     +0x259: mov    r11,QWORD PTR [rsp]
     +0x25d: mov    rcx,r15
     +0x260: mov    r8,QWORD PTR [rsp+0x10]
     +0x265: mov    rsi,r10
     +0x268: nop    DWORD PTR [rax+rax*1+0x0]
     +0x270: movzx  edi,BYTE PTR [rsi]
     +0x273: mov    edx,r12d
     +0x276: movzx  eax,BYTE PTR [rcx]
     +0x279: sar    edx,0x10
     +0x27c: add    rsi,0x1
     +0x280: add    rcx,0x1
     +0x284: xor    eax,edi
     +0x286: and    eax,edx
     +0x288: xor    eax,edi
     +0x28a: mov    BYTE PTR [rcx-0x1],al
     +0x28d: cmp    r11,rsi
     +0x290: jne    <mlkem768_dec+0x270>
     +0x292: mov    rax,QWORD PTR [rsp+0x18]
     +0x297: movdqa xmm7,XMMWORD PTR [rsp+0x20]
     +0x29d: movdqa xmm5,XMMWORD PTR [rsp+0x30]
     +0x2a3: movups XMMWORD PTR [rax],xmm7
     +0x2a6: movups XMMWORD PTR [rax+0x10],xmm5
     +0x2aa: jmp    <mlkem768_dec+0x43>
 ***)

let MLKEM_NATIVE_DEC_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem768_dec"];;

let KD3_EXEC = MLKEM_NATIVE_DEC_K3_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-768, and the input check   *)
(* of FIPS 203 in terms of the result of mlkem768_check_sk.                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_768_STMT =
  `!ek m r. LENGTH(kpke_encrypt mlkem768 ek m r) = 1088`;;

let KPKE_ENCRYPT_LENGTH_768 =
  assume_spec KPKE_ENCRYPT_LENGTH_768_STMT;;

let KPKE_DECRYPT_LENGTH_768_STMT =
  `!dk c. LENGTH(kpke_decrypt mlkem768 dk c) = 32`;;

let KPKE_DECRYPT_LENGTH_768 =
  assume_spec KPKE_DECRYPT_LENGTH_768_STMT;;

let KD3_CHECK_STMT =
  `!dk c. LENGTH dk = 2400 /\ LENGTH c = 1088
          ==> (mlkem_decaps_check mlkem768 dk c <=>
               num_of_bytelist(mlkem_slice 2336 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 1152 1184 dk)))`;;

let KD3_CHECK =
  assume_spec KD3_CHECK_STMT;;

(* ------------------------------------------------------------------------- *)
(* The frame, the slices of the decapsulation key, and the values computed:  *)
(* m', G of m' and h, K' and r', the reencryption c' of m', z, the result of *)
(* J, and whether c' is the ciphertext. The buffers are aligned to 32 bytes  *)
(* within the stack frame, by AND with -32 after the pushes, as in           *)
(* mlkem768_indcpa_dec, and their addresses are offsets from the frame       *)
(* variable bot of INDCPA_BOT_TAC, the bottom of the stacks of the callees   *)
(* 17000 bytes below them: m' and h at bot + 17032, K' and r' at bot + 17096 *)
(* and c', and then z and the copy of the ciphertext, at bot + 17160. The    *)
(* result of J is written to bot + 17032, over m', and K' is selected into   *)
(* it there, so ss is written once, at the end, from that buffer, whose      *)
(* address is kept in the stack slot at bot + 17024. In the loop that        *)
(* compares c' with the ciphertext, PXOR reads c' from memory, which needs   *)
(* 16-byte alignment, so that of bot + 17160 is given too; the aligned moves *)
(* at the end read the buffer at bot + 17032.                                *)
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
  INDCPA_BOT_TAC KD3_FRAME [17000; 17032; 17160] THEN
  INDCPA_FRAME_TAC ["memory :> bytes(ss:int64,32)"] KD3_FRAME THEN
  INDCPA_NONOV_TAC 18280
   [`ss:int64,32`; `ct:int64,1088`; `sk:int64,2400`;
    `word pc:int64,libmlkem_size`; `word_add stackpointer (word 18312):int64,56`;
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
(* at iteration i that the first i bytes of the buffer for the result of J,  *)
(* at bot + 17032, are those of K' if the ciphertexts are equal and those of *)
(* the result of J otherwise, and the others still those of the result of J, *)
(* with the pointers into the buffer and K' at offset i. Both keep the       *)
(* registers, the pushes, K' and the slot with ss (KEEP).                    *)
(* ------------------------------------------------------------------------- *)

let KD3_SAFE_KEEP =
 `read RSP s = word_add bot (word 17000) /\
  read RBP s = word_add stackpointer (word 18352) /\
  read RBX s = word 0 /\
  read R13 s = sk /\ read R14 s = ct /\
  read R15 s = word_add bot (word 17032) /\
  read R8 s = word_add bot (word 17160) /\
  read R10 s = word_add bot (word 17096) /\
  read R11 s = word_add bot (word 17128) /\
  (read DF s <=> false) /\
  read (memory :> bytes64 (word_add bot (word 17024))) s = ss /\
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
  read R13 s = sk /\ read R14 s = ct /\
  read R15 s = word_add bot (word 17032) /\
  read R8 s = word_add bot (word 17160) /\
  read R10 s = word_add bot (word 17096) /\
  read R11 s = word_add bot (word 17128) /\
  (read DF s <=> false) /\
  read (memory :> bytes64 (word_add bot (word 17024))) s = ss /\
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
 `\i s. read RSI s = word_add bot (word (17096 + i)) /\
        read RCX s = word_add bot (word (17032 + i)) /\
        read R12 s = (if EQ then word 0 else word 4294967041) /\
        read (memory :> bytes(word_add bot (word 17032),i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\
        read (memory :> bytes(word_add bot (word (17032 + i)),32 - i)) s =
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

  X86_STEPS_TAC KD3_EXEC (1--10) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD3_EXEC (11--14) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `mlkem_slice 1152 1184 (dk:byte list)`;
     `num_of_bytelist(mlkem_slice 2336 32 (dk:byte list))`] @ post) 15 THEN
  INDCPA_NORM_TAC THEN

  (*** The decryption, G and the reencryption ***)

  X86_STEPS_TAC KD3_EXEC (16--22) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`;
     `mlkem_slice 0 1152 (dk:byte list)`; `c:byte list`] @ post) 23 THEN
  INDCPA_NORM_TAC THEN INDCPA_YMMS_TAC "s23" [3; 4] THEN
  X86_STEPS_TAC KD3_EXEC (24--29) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (30--35) THEN
  INDCPA_NORM_TAC THEN
  KEM_JOIN_TAC (INDCPA_SP 17064) `mlkem_slice 2336 32 (dk:byte list)` "s35"
  THEN KD3_G_INPUT_TAC "s35" THEN
  X86_STEPS_TAC KD3_EXEC [36] THEN
  call MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`;
     mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD3_MP),
             `mlkem_slice 2336 32 (dk:byte list)`)] @ post) 37 THEN
  INDCPA_NORM_TAC THEN KD3_KR_TAC "s37" THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD3_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_768]; ALL_TAC] THEN
  X86_STEPS_TAC KD3_EXEC (38--46) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
     `mlkem_slice 1152 1184 (dk:byte list)`; KD3_MP; KD3_RR] @ post) 47 THEN
  INDCPA_NORM_TAC THEN

  (*** The start of the comparison ***)

  X86_STEPS_TAC KD3_EXEC (48--52) THEN INDCPA_YMMS_TAC "s52" [0; 2] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (53--57) THEN
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

let KD3_TEST_STMT =
  `!i. i < 68
       ==> (val(word_add (word(16 * i)) (word 18446744073709550544):int64) =
            0 <=> ~(i + 1 < 68))`;;

let KD3_TEST =
  assume_spec KD3_TEST_STMT;;

let KD3_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  ENSURES_INIT_TAC "s0" THEN
  KD3_CHUNK_TAC `ct:int64` `num_of_bytelist c` THEN
  KD3_CHUNK_TAC (INDCPA_SP 17160) (mk_comb(`num_of_bytelist`,KD3_CP)) THEN
  VAL_INT64_TAC `16 * i` THEN KEM_INDEX_TAC THEN
  SUBGOAL_THEN
   `aligned 16 (word_add (word_add bot (word 17160)) (word (1 * 16 * i)):int64)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
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
  X86_STEPS_TAC KD3_EXEC (52--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0; ADD_CLAUSES;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the copy of the       *)
(* buffer to ss by two 128-bit moves, the zeroing of the buffers by REP      *)
(* STOSQ and SSE stores, and the result in terms of FIPS 203, and the case   *)
(* where the check of the key fails.                                         *)
(* ------------------------------------------------------------------------- *)

let KD3_CMOV_TEST_TAC =
  SUBGOAL_THEN
   `val(word_sub (word_add bot (word 17128))
                 (word_add (word_add bot (word (17096 + i))) (word 1)):int64) = 0
    <=> ~(i + 1 < 32)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SUBGOAL_THEN
     `word_sub (word_add bot (word 17128))
               (word_add (word_add bot (word (17096 + i))) (word 1)):int64 =
      word_neg(word_add (word i) (word 18446744073709551585))`
     SUBST1_TAC THENL
     [SUBGOAL_THEN `word 18446744073709551585:int64 = word_neg(word 31)`
       SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0] THEN
    REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_SIMP_TAC[KEM_CMOV_TEST];
    ALL_TAC];;

let KD3_CMOV_BODY_TAC =
  let nrm = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [INDCPA_SP 17096; `32`; mk_comb(`num_of_bytelist`,KD3_KP);
                `i:num`; `s0:x86state`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   (KD3_SUBST `read (memory :> bytes(word_add bot (word (17032 + i)),
                                      (31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC(nrm th1) THEN ASSUME_TAC(nrm th2))] THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC KD3_EXEC (1--12) THEN
  KD3_CMOV_TEST_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC];
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC KD3_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN REWRITE_TAC[KEM_MOD256] THEN
    SPEC_TAC(KD3_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD3_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; KEM_DIV_BYTE; ADD_ASSOC] THEN
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
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y5:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `y7:int256` `read YMM7` THEN ENSURES_INIT_TAC "s0" THEN
  KEM_HALVES_TAC (INDCPA_SP 17032) THEN
  X86_STEPS_TAC KD3_EXEC [1] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (2--5) THEN
  MP_TAC(SPECL [`ss:int64`;
                KD3_SUBST `(if EQ then KP else KB) MOD 2 EXP (8 * 32)`;
                `s5:x86state`] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  X86_STEPS_TAC KD3_EXEC (6--10) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (11--19) THEN
  X86_STEPS_TAC KD3_EXEC (20--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD3_FINAL_TAC;;

let KD3_BAD_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD3_CALL in
  ENSURES_INIT_TAC "s0" THEN KD3_SK_TAC THEN
  X86_STEPS_TAC KD3_EXEC (1--10) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD3_EXEC (11--14) THEN INDCPA_NORM_TAC THEN
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
(* mlkem_decaps_internal mlkem768 dk c in common/fips203/fips203.ml and the  *)
(* function returns 0, and otherwise it returns -5. The theorem assumes that *)
(* SampleNTT terminates for each entry of the matrix from the seed in the    *)
(* key and that the stack does not contain address 0, as for                 *)
(* mlkem768_indcpa_enc. The stack is the 18360 bytes below the return        *)
(* address, for the six saved registers, up to 31 bytes for the alignment,   *)
(* the 1280 bytes of the buffers and the 17000 used by the callees below     *)
(* them. The proof is by cases on the check of the key, with the two loops   *)
(* for the comparison and the conditional move.                              *)
(* ------------------------------------------------------------------------- *)

let KD3_OK_TAC =
  ENSURES_WHILE_UP2_TAC `68` `pc + mlkem768_dec_loop1` `pc + mlkem768_dec_loop1_exit`
   KD3_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD3_PART1_TAC; KD3_BODY_TAC;
    ENSURES_WHILE_UP2_TAC `32` `pc + mlkem768_dec_loop2` `pc + mlkem768_dec_loop2_exit`
     KD3_CMOV_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD3_EXIT_A_TAC; KD3_CMOV_BODY_TAC; KD3_EXIT_B_TAC]];;

let MLKEM_NATIVE_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ss ct sk (dk:byte list) (c:byte list) pc stackpointer
    returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH dk = 2400 /\ LENGTH c = 1088 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 2304 32 dk) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 18360),18368) /\
    nonoverlapping (ss,32) (word_sub stackpointer (word 18360),18368) /\
    ALLPAIRS nonoverlapping
     [(ss,32); (word_sub stackpointer (word 18360),18368)]
     [(ct,1088); (sk,2400); (word pc,libmlkem_size)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem768_dec) /\
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
            memory :> bytes(word_sub stackpointer (word 18360),18360)])`;;

let MLKEM_NATIVE_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

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
        KEEP`;;

let KD3_SAFE_CMOV_INV = KD3_WITH_KEEP KD3_SAFE_KEEP
 `\i s. read RSI s = word_add bot (word (17096 + i)) /\
        read RCX s = word_add bot (word (17032 + i)) /\ KEEP`;;

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
  X86_STEPS_TAC KD3_EXEC (1--10) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD3_EXEC (11--14) THEN INDCPA_NORM_TAC THEN
  call "H_CHECK"
   [`read RDI s`; `ekk:byte list`; `num_of_bytelist(hh:byte list)`] 15 THEN
  INDCPA_NORM_TAC;;

let KD3_SAFE_PART1_TAC =
  let call = KD3_SAFE_CALL_TAC in
  KD3_SAFE_START_TAC THEN
  X86_STEPS_TAC KD3_EXEC (16--22) THEN INDCPA_NORM_TAC THEN
  call "H_DEC" [`read RDI s`; `read RSI s`; `read RDX s`] 23 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KD3_EXEC (24--36) THEN INDCPA_NORM_TAC THEN
  call "H_SHA3_512" [`read RDI s`; `read RSI s`; `64`] 37 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KD3_EXEC (38--46) THEN INDCPA_NORM_TAC THEN
  call "H_ENC"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `ekk:byte list`]
   47 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC KD3_EXEC (48--57) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `16 * i` THEN
  SUBGOAL_THEN
   `aligned 16 (word_add (word_add bot (word 17160)) (word (1 * 16 * i)):int64)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
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
  X86_STEPS_TAC KD3_EXEC (52--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 + 1 = 1`; APPEND_NIL; ENUMERATEL_APPEND_ZERO] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC KD3_EXEC (1--12) THEN
  KD3_CMOV_TEST_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC]; ALL_TAC] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;


let KD3_SAFE_EXIT_B_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC KD3_EXEC (1--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD3_SAFE_BAD_TAC =
  KD3_SAFE_START_TAC THEN
  X86_STEPS_TAC KD3_EXEC (16--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
   forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH dk = 2400 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 2304 32 dk) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 18360),18368) /\
    nonoverlapping (ss,32) (word_sub stackpointer (word 18360),18368) /\
    ALLPAIRS nonoverlapping
     [(ss,32); (word_sub stackpointer (word 18360),18368)]
     [(ct,1088); (sk,2400); (word pc,libmlkem_size)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem768_dec) /\
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
                   word(pc + mlkem_poly_compress_d4_const1),8; word(pc + mlkem_poly_compress_d4_const2),8;
                   word(pc + mlkem_poly_decompress_d10_consts),8; word(pc + mlkem_poly_invntt_tomont_consts),48;
                   word(pc + rodata_mlk_KeccakF_RoundConstants),192; word(pc + mlkem768_gen_matrix_consts),4;
                   word(pc + rodata_mlk_zetas),256]
                  [ss,32; word_sub stackpointer (word 18360),18360]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 18360),18360)])`;;

let MLKEM_NATIVE_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_DEC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
