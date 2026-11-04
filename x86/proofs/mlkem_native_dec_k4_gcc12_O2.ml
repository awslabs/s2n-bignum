(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-1024 (FIPS 203 Algorithm 18, with the input   *)
(* check of Algorithm 21). This is the code for mlkem1024_dec from           *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md). It checks the decapsulation key with             *)
(* mlkem1024_check_sk, and returns -5 if the check fails. Otherwise it       *)
(* decrypts the ciphertext into m' with mlkem1024_indcpa_dec, computes K'    *)
(* and r' as G of m' followed by the hash h in the key with mlkem_sha3_512,  *)
(* encrypts m' with r' again by mlkem1024_indcpa_enc, compares the result    *)
(* with the ciphertext in constant time, computes J of z (in the key)        *)
(* followed by the ciphertext into the shared secret with mlkem_shake256,    *)
(* and replaces it by K' if the ciphertexts are equal, again in constant     *)
(* time. In both cases it zeroes its buffers. It is verified in the whole    *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x1c90, using the theorems for mlkem1024_check_sk, mlkem1024_indcpa_dec,  *)
(* mlkem_sha3_512, mlkem1024_indcpa_enc and mlkem_shake256 in the image.     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_check_sk_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_indcpa_dec_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_indcpa_enc_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake256_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    1c90: push   rbp
    1c91: mov    rbp,rsp
    1c94: push   r15
    1c96: mov    r15,rsi
    1c99: push   r14
    1c9b: mov    r14,rdi
    1c9e: mov    rdi,rdx
    1ca1: push   r13
    1ca3: mov    r13,rdx
    1ca6: push   r12
    1ca8: push   rbx
    1ca9: and    rsp,0xffffffffffffffe0
    1cad: sub    rsp,0x6e0
    1cb4: call   18b0 <mlkem1024_check_sk>
    1cb9: test   eax,eax
    1cbb: je     1d28 <mlkem1024_dec+0x98>
    1cbd: mov    ebx,eax
    1cbf: lea    r10,[rsp+0x20]
    1cc4: lea    r9,[rsp+0x60]
    1cc9: lea    r8,[rsp+0xa0]
    1cd1: xor    eax,eax
    1cd3: mov    rdi,r8
    1cd6: mov    ecx,0xc8
    1cdb: rep    stos QWORD PTR es:[rdi],rax
    1cde: pxor   xmm0,xmm0
    1ce2: movaps XMMWORD PTR [rsp+0x60],xmm0
    1ce7: movaps XMMWORD PTR [rsp+0x70],xmm0
    1cec: movaps XMMWORD PTR [rsp+0x80],xmm0
    1cf4: movaps XMMWORD PTR [rsp+0x90],xmm0
    1cfc: movaps XMMWORD PTR [rsp+0x20],xmm0
    1d01: movaps XMMWORD PTR [rsp+0x30],xmm0
    1d06: movaps XMMWORD PTR [rsp+0x40],xmm0
    1d0b: movaps XMMWORD PTR [rsp+0x50],xmm0
    1d10: lea    rsp,[rbp-0x28]
    1d14: mov    eax,ebx
    1d16: pop    rbx
    1d17: pop    r12
    1d19: pop    r13
    1d1b: pop    r14
    1d1d: pop    r15
    1d1f: pop    rbp
    1d20: ret
    1d21: nop    DWORD PTR [rax+0x0]
    1d28: lea    r10,[rsp+0x20]
    1d2d: mov    rdx,r13
    1d30: mov    rsi,r15
    1d33: mov    rdi,r10
    1d36: mov    QWORD PTR [rsp+0x18],r10
    1d3b: call   1690 <mlkem1024_indcpa_dec>
    1d40: mov    r10,QWORD PTR [rsp+0x18]
    1d45: test   eax,eax
    1d47: mov    ebx,eax
    1d49: je     1d60 <mlkem1024_dec+0xd0>
    1d4b: lea    r9,[rsp+0x60]
    1d50: lea    r8,[rsp+0xa0]
    1d58: jmp    1cd1 <mlkem1024_dec+0x41>
    1d5d: nop    DWORD PTR [rax]
    1d60: lea    r9,[rsp+0x60]
    1d65: mov    rsi,r10
    1d68: mov    edx,0x40
    1d6d: mov    QWORD PTR [rsp+0x18],r10
    1d72: movdqu xmm3,XMMWORD PTR [r13+0xc20]
    1d7b: mov    rdi,r9
    1d7e: mov    QWORD PTR [rsp+0x8],r9
    1d83: movdqu xmm4,XMMWORD PTR [r13+0xc30]
    1d8c: movaps XMMWORD PTR [rsp+0x40],xmm3
    1d91: movaps XMMWORD PTR [rsp+0x50],xmm4
    1d96: call   3570 <mlkem_sha3_512>
    1d9b: mov    r10,QWORD PTR [rsp+0x18]
    1da0: lea    r8,[rsp+0xa0]
    1da8: lea    rcx,[rsp+0x80]
    1db0: mov    rdi,r8
    1db3: lea    rdx,[r13+0x600]
    1dba: mov    QWORD PTR [rsp+0x18],r8
    1dbf: mov    rsi,r10
    1dc2: mov    QWORD PTR [rsp+0x10],r10
    1dc7: call   1390 <mlkem1024_indcpa_enc>
    1dcc: mov    r8,QWORD PTR [rsp+0x18]
    1dd1: mov    r10,QWORD PTR [rsp+0x10]
    1dd6: test   eax,eax
    1dd8: mov    r9,QWORD PTR [rsp+0x8]
    1ddd: mov    ebx,eax
    1ddf: jne    1cd1 <mlkem1024_dec+0x41>
    1de5: pxor   xmm2,xmm2
    1de9: xor    eax,eax
    1deb: movdqa xmm0,xmm2
    1def: nop
    1df0: movdqu xmm1,XMMWORD PTR [r15+rax*1]
    1df6: pxor   xmm1,XMMWORD PTR [r8+rax*1]
    1dfc: add    rax,0x10
    1e00: por    xmm0,xmm1
    1e04: pxor   xmm2,xmm1
    1e08: cmp    rax,0x620
    1e0e: jne    1df0 <mlkem1024_dec+0x160>
    1e10: movdqa xmm1,xmm2
    1e14: mov    QWORD PTR [rsp+0x8],r9
    1e19: psrldq xmm1,0x8
    1e1e: mov    QWORD PTR [rsp+0x10],r10
    1e23: pxor   xmm2,xmm1
    1e27: movdqa xmm1,xmm2
    1e2b: psrldq xmm1,0x4
    1e30: pxor   xmm2,xmm1
    1e34: movdqa xmm1,xmm2
    1e38: psrldq xmm1,0x2
    1e3d: pxor   xmm2,xmm1
    1e41: movdqa xmm1,xmm2
    1e45: psrldq xmm1,0x1
    1e4a: pxor   xmm2,xmm1
    1e4e: movdqa xmm1,xmm0
    1e52: psrldq xmm1,0x8
    1e57: movd   eax,xmm2
    1e5b: por    xmm0,xmm1
    1e5f: movdqa xmm1,xmm0
    1e63: psrldq xmm1,0x4
    1e68: por    xmm0,xmm1
    1e6c: movdqa xmm1,xmm0
    1e70: psrldq xmm1,0x2
    1e75: por    xmm0,xmm1
    1e79: movdqa xmm1,xmm0
    1e7d: psrldq xmm1,0x1
    1e82: por    xmm0,xmm1
    1e86: movd   r12d,xmm0
    1e8b: movzx  r12d,r12b
    1e8f: neg    r12d
    1e92: sar    r12d,0x10
    1e96: xor    r12d,eax
    1e99: xor    r12d,eax
    1e9c: mov    rdx,r8
    1e9f: mov    ecx,0xc4
    1ea4: mov    rsi,r15
    1ea7: movdqu xmm6,XMMWORD PTR [r13+0xc50]
    1eb0: mov    QWORD PTR [rsp+0x18],r8
    1eb5: movzx  r12d,r12b
    1eb9: lea    rax,[rsp+0xc0]
    1ec1: movdqu xmm5,XMMWORD PTR [r13+0xc40]
    1eca: mov    rdi,rax
    1ecd: neg    r12d
    1ed0: movaps XMMWORD PTR [rsp+0xb0],xmm6
    1ed8: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
    1edb: mov    ecx,0x640
    1ee0: mov    esi,0x20
    1ee5: mov    rdi,r14
    1ee8: movaps XMMWORD PTR [rsp+0xa0],xmm5
    1ef0: call   3480 <mlkem_shake256>
    1ef5: mov    r9,QWORD PTR [rsp+0x8]
    1efa: mov    r10,QWORD PTR [rsp+0x10]
    1eff: xor    eax,eax
    1f01: mov    r8,QWORD PTR [rsp+0x18]
    1f06: cs     nop WORD PTR [rax+rax*1+0x0]
    1f10: movzx  esi,BYTE PTR [r9+rax*1]
    1f15: mov    ecx,r12d
    1f18: movzx  edx,BYTE PTR [r14+rax*1]
    1f1d: sar    ecx,0x10
    1f20: xor    edx,esi
    1f22: and    edx,ecx
    1f24: xor    edx,esi
    1f26: mov    BYTE PTR [r14+rax*1],dl
    1f2a: add    rax,0x1
    1f2e: cmp    rax,0x20
    1f32: jne    1f10 <mlkem1024_dec+0x280>
    1f34: jmp    1cd1 <mlkem1024_dec+0x41>
 ***)

let MLKEM_NATIVE_DEC_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1c90,0x1f39];;

let KD4_EXEC = MLKEM_NATIVE_DEC_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-1024, and the input check  *)
(* of FIPS 203 in terms of the result of mlkem1024_check_sk.                 *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_1024 = prove
 (`!ek m r. LENGTH(kpke_encrypt mlkem1024 ek m r) = 1568`,
  REWRITE_TAC[mlkem1024; KPKE_ENCRYPT_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let KPKE_DECRYPT_LENGTH_1024 = prove
 (`!dk c. LENGTH(kpke_decrypt mlkem1024 dk c) = 32`,
  REWRITE_TAC[mlkem1024; KPKE_DECRYPT_LENGTH]);;

let KD4_CHECK = prove
 (`!dk c. LENGTH dk = 3168 /\ LENGTH c = 1568
          ==> (mlkem_decaps_check mlkem1024 dk c <=>
               num_of_bytelist(mlkem_slice 3104 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 1536 1568 dk)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem1024; mlkem_decaps_check] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[mlkem_h] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ; LENGTH_SHA3_256]);;

(* ------------------------------------------------------------------------- *)
(* The frame, the slices of the decapsulation key, and the values computed:  *)
(* m', G of m' and h, K' and r', the reencryption c' of m', z, the result of *)
(* J, and whether c' is the ciphertext. The buffers are aligned to 32 bytes  *)
(* within the stack frame, by AND with -32 after the pushes, as in           *)
(* mlkem1024_indcpa_dec, and their addresses are offsets from the frame      *)
(* variable bot of INDCPA_BOT_TAC, the bottom of the stacks of the callees   *)
(* 22912 bytes below them: m' and h at bot + 22944, K' and r' at bot + 23008 *)
(* and c', and then z and the copy of the ciphertext, at bot + 23072.        *)
(* ------------------------------------------------------------------------- *)

let KD4_FRAME = (24752,48,22912,1760);;

let KD4_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KD4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 24752 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SIMP_TAC[KD4_CHECK; ASSUME `LENGTH(dk:byte list) = 3168`;
           ASSUME `LENGTH(c:byte list) = 1568`] THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1536 (dk:byte list)) = 1536 /\
    LENGTH(mlkem_slice 1536 1568 (dk:byte list)) = 1568 /\
    LENGTH(mlkem_slice 3104 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 3136 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1536`; `32`; `1536`; `1568`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1536 + 32 <= 1568`)))] o
   check (fun th -> is_forall(concl th) &&
                    INDCPA_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD4_SETUP_TAC =
  INDCPA_BOT_TAC KD4_FRAME [22912] THEN
  INDCPA_FRAME_TAC ["memory :> bytes(ss:int64,32)"] KD4_FRAME THEN
  INDCPA_NONOV_TAC 24672
   [`ss:int64,32`; `ct:int64,1568`; `sk:int64,3168`;
    `word pc:int64,0x82a0`; `word_add stackpointer (word 24704):int64,56`;
    `word 0:int64,1`]
  THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KD4_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,3168)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,1536; 1536,1568; 3104,32; 3136,32]
    else NO_TAC);;

let KD4_MP = `kpke_decrypt mlkem1024 (mlkem_slice 0 1536 dk) c`;;

let KD4_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem1024 (mlkem_slice 0 1536 dk) c)
                  (mlkem_slice 3104 32 dk))`;;

let KD4_KP = mk_comb(`mlkem_slice 0 32`,KD4_GG);;

let KD4_RR = mk_comb(`mlkem_slice 32 32`,KD4_GG);;

let KD4_CP = list_mk_comb(`kpke_encrypt mlkem1024`,
  [`mlkem_slice 1536 1568 (dk:byte list)`; KD4_MP; KD4_RR]);;

let KD4_ZZ = `mlkem_slice 3136 32 (dk:byte list)`;;

let KD4_KB =
 `list_of_seq (shake256 (APPEND (mlkem_slice 3136 32 dk) c)) 32`;;

let KD4_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD4_CP));;

let KD4_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD4_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD4_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD4_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD4_ZZ),`ZZ:num`;
         KD4_EQ,`EQ:bool`] tm;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the comparison loop at iteration i states that the OR    *)
(* accumulator in XMM0 is zero if and only if the first 16 * i bytes of the  *)
(* ciphertext and of c' are equal, and the invariant of the conditional move *)
(* at iteration i that the first i bytes at ss are those of K' if the        *)
(* ciphertexts are equal and those of the result of J otherwise, and the     *)
(* others still those of the result of J. Both keep the registers, the       *)
(* pushes and K' (KEEP).                                                     *)
(* ------------------------------------------------------------------------- *)

let KD4_SAFE_KEEP =
 `read RSP s = word_add bot (word 22912) /\
  read RBP s = word_add stackpointer (word 24744) /\
  read RBX s = word 0 /\
  read R13 s = sk /\ read R14 s = ss /\ read R15 s = ct /\
  read R8 s = word_add bot (word 23072) /\
  read R9 s = word_add bot (word 23008) /\
  (read DF s <=> false) /\
  read (memory :> bytes64 (word_add stackpointer (word 24752))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 24744))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24736))) s =
  r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24728))) s =
  r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24720))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24712))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24704))) s =
  rbx_init`;;

let KD4_KEEP = KD4_SUBST
 `read RSP s = word_add bot (word 22912) /\
  read RBP s = word_add stackpointer (word 24744) /\
  read RBX s = word 0 /\
  read R13 s = sk /\ read R14 s = ss /\ read R15 s = ct /\
  read R8 s = word_add bot (word 23072) /\
  read R9 s = word_add bot (word 23008) /\
  (read DF s <=> false) /\
  read (memory :> bytes64 (word_add stackpointer (word 24752))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 24744))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24736))) s =
  r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24728))) s =
  r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24720))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24712))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24704))) s =
  rbx_init /\
  read (memory :> bytes(word_add bot (word 23008),32)) s = KP`;;

let KD4_WITH_KEEP keep inv =
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [keep,`KEEP:bool`] bod);;

let KD4_INV = KD4_WITH_KEEP KD4_KEEP (KD4_SUBST
 `\i s. read RAX s = word(16 * i) /\
        read R10 s = word_add bot (word 22944) /\
        read R12 s = r12_init /\
        (word_subword (read YMM0 s) (0,128):int128 = word 0 <=>
         num_of_bytelist c MOD 2 EXP (128 * i) = CP MOD 2 EXP (128 * i)) /\
        read (memory :> bytes(ct,1568)) s = num_of_bytelist c /\
        read (memory :> bytes(word_add bot (word 23072),1568)) s = CP /\
        read (memory :> bytes128 (word_add sk (word 3136))) s =
        word(ZZ MOD 2 EXP 128) /\
        read (memory :> bytes128 (word_add sk (word 3152))) s =
        word(ZZ DIV 2 EXP 128) /\ KEEP`);;

let KD4_CMOV_INV = KD4_WITH_KEEP KD4_KEEP (KD4_SUBST
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

let KD4_G_INPUT_TAC s =
  let st = mk_var(s,`:x86state`) in
  SUBGOAL_THEN
   (subst [st,`s:x86state`; INDCPA_SP 22944,`a:int64`;
           KD4_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 3104 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND;
                    KPKE_DECRYPT_LENGTH_1024];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD4_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 3104 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_1024] THEN
    ARITH_TAC;
    ALL_TAC];;

let KD4_KR_TAC s =
  let st = mk_var(s,`:x86state`) and a = INDCPA_SP 23008 in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:x86state`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD4_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD4_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KD4_PART1_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD4_CALL in
  ENSURES_INIT_TAC "s0" THEN KD4_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 3104):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 3136):int64` THEN

  (*** The check of the key ***)

  X86_STEPS_TAC KD4_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD4_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_CHECK_SK_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `mlkem_slice 1536 1568 (dk:byte list)`;
     `num_of_bytelist(mlkem_slice 3104 32 (dk:byte list))`] @ post) 15 THEN
  INDCPA_NORM_TAC THEN

  (*** The decryption, G and the reencryption ***)

  X86_STEPS_TAC KD4_EXEC (16--23) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`;
     `mlkem_slice 0 1536 (dk:byte list)`; `c:byte list`] @ post) 24 THEN
  INDCPA_NORM_TAC THEN INDCPA_YMMS_TAC "s24" [3; 4] THEN
  X86_STEPS_TAC KD4_EXEC (25--32) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (33--38) THEN
  INDCPA_NORM_TAC THEN
  KEM_JOIN_TAC (INDCPA_SP 22976) `mlkem_slice 3104 32 (dk:byte list)` "s38"
  THEN KD4_G_INPUT_TAC "s38" THEN
  X86_STEPS_TAC KD4_EXEC [39] THEN
  call MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`;
     mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD4_MP),
             `mlkem_slice 3104 32 (dk:byte list)`)] @ post) 40 THEN
  INDCPA_NORM_TAC THEN KD4_KR_TAC "s40" THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_1024]; ALL_TAC] THEN
  X86_STEPS_TAC KD4_EXEC (41--49) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
     `mlkem_slice 1536 1568 (dk:byte list)`; KD4_MP; KD4_RR] @ post) 50 THEN
  INDCPA_NORM_TAC THEN

  (*** The start of the comparison ***)

  X86_STEPS_TAC KD4_EXEC (51--56) THEN INDCPA_YMMS_TAC "s56" [0; 2] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (57--60) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[KEM_SUBWORD_JOIN_128; MOD_1] THEN CONV_TAC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the comparison, with the loop test. The two 128-bit      *)
(* words loaded are given in the form of the address computed for the base   *)
(* and index registers (KEM_INDEX_TAC), and the values of the YMM registers  *)
(* at the start of the iteration are introduced as ghosts.                   *)
(* ------------------------------------------------------------------------- *)

let KD4_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 98 ==> 16 * i + 16 <= 1568`)
               (ASSUME `i < 98`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`1568`) && vv = v ->
          let lth = SPECL [a; `1568`; `i:num`; v; s] KEM_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (MP lth (CONJ th bth)))
    | _ -> NO_TAC);;

let KD4_TEST = prove
 (`!i. i < 98
       ==> (val(word_add (word(16 * i)) (word 18446744073709550064):int64) =
            0 <=> ~(i + 1 < 98))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 98 ==> 16 * i < 18446744073709551616`] THEN
  ASM_CASES_TAC `i + 1 < 98` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i + 1 < 98 ==> 16 * i + 18446744073709550064 < 18446744073709551616`]
    THEN ARITH_TAC;
    SUBGOAL_THEN `i = 97` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]]);;

let KD4_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  ENSURES_INIT_TAC "s0" THEN
  KD4_CHUNK_TAC `ct:int64` `num_of_bytelist c` THEN
  KD4_CHUNK_TAC (INDCPA_SP 23072) (mk_comb(`num_of_bytelist`,KD4_CP)) THEN
  VAL_INT64_TAC `16 * i` THEN KEM_INDEX_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD4_TEST) (ASSUME `i < 98`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 98` THEN ASM_REWRITE_TAC[];
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

let KD4_Q = `word_subword (y0:int256) (0,128):int128`;;

let KD4_DONE_TAC =
  SUBGOAL_THEN (mk_iff(mk_eq(KD4_Q,`word 0:int128`),KD4_EQ)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = mk_eq(KD4_Q,`word 0:int128`)
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(ISPEC `c:byte list` NUM_OF_BYTELIST_BOUND) THEN
    MP_TAC(ISPEC KD4_CP NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_1024] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let KD4_MASK_TAC s =
  let r12 = mk_comb(`read R12`,mk_var(s,`:x86state`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = r12 then
      let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[KEM_MOD256])) th in
      let eth = BITBLAST_RULE
        (mk_eq(rand(concl th1),
               mk_cond(mk_eq(KD4_Q,`word 0:int128`),
                       `word 0:int64`,`word 4294967041:int64`))) in
      ASSUME_TAC(TRANS th1 eth)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = r12 then
      FIRST_ASSUM(fun th' ->
        if is_iff(concl th') &&
           lhand(concl th') = mk_eq(KD4_Q,`word 0:int128`)
        then ASSUME_TAC(REWRITE_RULE[th'] th) else NO_TAC)
    else NO_TAC);;

let KD4_J_INPUT_TAC s =
  let st = mk_var(s,`:x86state`) in
  SUBGOAL_THEN
   (subst [st,`s:x86state`; INDCPA_SP 23072,`a:int64`]
     `read (memory :> bytes(a,1600)) s =
      num_of_bytelist(APPEND (mlkem_slice 3136 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1600 = 32 + 1568`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 3136 32 (dk:byte list)) c) = 1600`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

let KD4_EXIT_A_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD4_CALL in
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `y5:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `y6:int256` `read YMM6` THEN
  ENSURES_INIT_TAC "s0" THEN KD4_DONE_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (1--44) THEN
  KD4_MASK_TAC "s44" THEN KEM_MOVSQ_STEP_TAC KD4_EXEC 45 196 THEN
  X86_STEPS_TAC KD4_EXEC (46--48) THEN
  X86_STEPS_TAC KD4_EXEC [49] THEN SIMD_SIMPLIFY_TAC[] THEN
  KEM_JOIN_TAC (INDCPA_SP 23072) KD4_ZZ "s49" THEN KD4_J_INPUT_TAC "s49" THEN
  X86_STEPS_TAC KD4_EXEC [50] THEN
  call MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `32`; `read RDX s`;
     `APPEND (mlkem_slice 3136 32 (dk:byte list)) c`] @ post) 51 THEN
  X86_STEPS_TAC KD4_EXEC (52--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers by REP STOSQ and SSE stores, and the result in terms of FIPS 203, *)
(* and the case where the check of the key fails.                            *)
(* ------------------------------------------------------------------------- *)

let KD4_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [INDCPA_SP 23008; `32`; mk_comb(`num_of_bytelist`,KD4_KP);
                `i:num`; `s0:x86state`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   (KD4_SUBST `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC th1 THEN ASSUME_TAC th2)] THEN
  VAL_INT64_TAC `i:num` THEN KEM_INDEX1_TAC THEN
  X86_STEPS_TAC KD4_EXEC (1--11) THEN
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
    ASM_CASES_TAC KD4_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN REWRITE_TAC[KEM_MOD256] THEN
    SPEC_TAC(KD4_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD4_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; WORD_ADD; WORD_ADD_ASSOC;
                KEM_DIV_BYTE] THEN
    ASM_REWRITE_TAC[]];;

let KD4_FINAL_TAC =
  REWRITE_TAC[mlkem1024; MLKEM_DECAPS_ALT] THEN
  REWRITE_TAC[GSYM mlkem1024] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD4_CP,`c:byte list`),KD4_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_1024];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let KD4_EXIT_B_TAC =
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KD4_EXEC (1--5) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (6--14) THEN
  X86_STEPS_TAC KD4_EXEC (15--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD4_FINAL_TAC;;

let KD4_BAD_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD4_CALL in
  ENSURES_INIT_TAC "s0" THEN KD4_SK_TAC THEN
  X86_STEPS_TAC KD4_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD4_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_CHECK_SK_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `mlkem_slice 1536 1568 (dk:byte list)`;
     `num_of_bytelist(mlkem_slice 3104 32 (dk:byte list))`] @ post) 15 THEN
  INDCPA_NORM_TAC THEN INDCPA_YMMS_TAC "s15" [0] THEN
  X86_STEPS_TAC KD4_EXEC (16--25) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (26--34) THEN
  X86_STEPS_TAC KD4_EXEC (35--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The decapsulation key dk of 3168 bytes is at sk and    *)
(* the ciphertext c of 1568 bytes at ct, and if they pass the check of FIPS  *)
(* 203, the shared secret of 32 bytes written at ss is that of               *)
(* mlkem_decaps_internal mlkem1024 dk c in common/fips203.ml and the         *)
(* function returns 0, and otherwise it returns -5. The theorem assumes that *)
(* SampleNTT terminates for each entry of the matrix from the seed in the    *)
(* key and that the stack does not contain address 0, as for                 *)
(* mlkem1024_indcpa_enc. The stack is the 24752 bytes below the return       *)
(* address, for the six saved registers, up to 31 bytes for the alignment,   *)
(* the 1760 bytes of the buffers and the 22912 used by the callees below     *)
(* them. The proof is by cases on the check of the key, with the two loops   *)
(* for the comparison and the conditional move.                              *)
(* ------------------------------------------------------------------------- *)

let KD4_OK_TAC =
  ENSURES_WHILE_UP2_TAC `98` `pc + 0x1df0` `pc + 0x1e10`
   KD4_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD4_PART1_TAC; KD4_BODY_TAC;
    ENSURES_WHILE_UP2_TAC `32` `pc + 0x1f10` `pc + 0x1f34`
     KD4_CMOV_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD4_EXIT_A_TAC; KD4_CMOV_BODY_TAC; KD4_EXIT_B_TAC]];;

let MLKEM_NATIVE_DEC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!ss ct sk (dk:byte list) (c:byte list) pc stackpointer
    returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH dk = 3168 /\ LENGTH c = 1568 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 3072 32 dk) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 24752),24760) /\
    nonoverlapping (ss,32) (word_sub stackpointer (word 24752),24760) /\
    ALLPAIRS nonoverlapping
     [(ss,32); (word_sub stackpointer (word 24752),24760)]
     [(ct,1568); (sk,3168); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1c90) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ss; ct; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(ct,1568)) s = num_of_bytelist c /\
              read (memory :> bytes(sk,3168)) s = num_of_bytelist dk)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (mlkem_decaps_check mlkem1024 dk c
               ==> read (memory :> bytes(ss,32)) s =
                   num_of_bytelist(mlkem_decaps_internal mlkem1024 dk c)) /\
              C_RETURN s =
              (if mlkem_decaps_check mlkem1024 dk c then word 0
               else word 0xfffffffb))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 24752),24752)])`,
  KD4_INTRO_TAC THEN KD4_SETUP_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 3104 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 1536 1568 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD4_OK_TAC; KD4_BAD_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses and on the encapsulation key ek in the decapsulation key and    *)
(* the hash h stored with it, through the check of the hash, given by the    *)
(* combined theorem for mlkem1024_check_sk, and the reencryption, but not on *)
(* the secret key, z or the ciphertext: the comparison of the ciphertexts    *)
(* and the selection of the shared secret are loops in constant time. The    *)
(* events are given by a template with cases on the check, with the events   *)
(* of the loops as ENUMERATEL, whose invariants have only the pointers and   *)
(* the frame, and the frame variables are expanded in them by                *)
(* INDCPA_UNBOT_TAC.                                                         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let KD4_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (pc:num) (stackpointer:int64)
   (returnaddress:int64) (ek:byte list) (h:byte list).
   if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
   then APPEND
         (APPEND (f_ev_exitb ss ct sk pc stackpointer returnaddress)
           (APPEND (ENUMERATEL 32
                     (\i. f_ev_cmov ss ct sk pc stackpointer returnaddress i))
                   (f_ev_exita ss ct sk pc stackpointer returnaddress)))
         (APPEND (ENUMERATEL 98
                   (\i. f_ev_cmp ss ct sk pc stackpointer returnaddress i))
                 (f_ev_prol ss ct sk pc stackpointer returnaddress ek h))
   else f_ev_bad ss ct sk pc stackpointer returnaddress ek h
   :(uarch_event)list`;;

let KD4_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `ekk:byte list`; `hh:byte list`; `i:num`;
   `bot:int64`;
   `f_ev_cmp:int64->int64->int64->num->int64->int64->num->
              (uarch_event)list`;
   `f_ev_cmov:int64->int64->int64->num->int64->int64->num->
              (uarch_event)list`];;

let KD4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KD4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KD4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD4_SAFE_INV = KD4_WITH_KEEP KD4_SAFE_KEEP
 `\i s. read RAX s = word(16 * i) /\
        read R10 s = word_add bot (word 22944) /\ KEEP`;;

let KD4_SAFE_CMOV_INV = KD4_WITH_KEEP KD4_SAFE_KEEP
 `\i s. read RAX s = word i /\ KEEP`;;

let KD4_SAFE_INTRO_TAC =
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_CHECK_SK_K4_GCC12_O2_IMAGE_SUBROUTINE_FULL, "H_CHECK";
    MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_DEC";
    MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHA3_512";
    MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_ENC";
    MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHAKE256"] THEN
  CONCRETIZE_F_EVENTS_TAC KD4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 24752 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1536 (dk:byte list)) = 1536 /\
    LENGTH(mlkem_slice 1536 1568 (dk:byte list)) = 1568 /\
    LENGTH(mlkem_slice 3104 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 3136 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1536`; `32`; `1536`; `1568`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1536 + 32 <= 1568`)))] o
   check (fun th -> is_forall(concl th) &&
                    INDCPA_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD4_SAFE_START_TAC =
  let call = KD4_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN KD4_SK_TAC THEN
  X86_STEPS_TAC KD4_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD4_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call "H_CHECK"
   [`read RDI s`; `ekk:byte list`; `num_of_bytelist(hh:byte list)`] 15 THEN
  INDCPA_NORM_TAC;;

let KD4_SAFE_PART1_TAC =
  let call = KD4_SAFE_CALL_TAC in
  KD4_SAFE_START_TAC THEN
  X86_STEPS_TAC KD4_EXEC (16--23) THEN INDCPA_NORM_TAC THEN
  call "H_DEC" [`read RDI s`; `read RSI s`; `read RDX s`] 24 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KD4_EXEC (25--39) THEN INDCPA_NORM_TAC THEN
  call "H_SHA3_512" [`read RDI s`; `read RSI s`; `64`] 40 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KD4_EXEC (41--49) THEN INDCPA_NORM_TAC THEN
  call "H_ENC"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `ekk:byte list`]
   50 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC KD4_EXEC (51--60) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `16 * i` THEN
  X86_STEPS_TAC KD4_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD4_TEST) (ASSUME `i < 98`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_EXIT_A_TAC =
  let call = KD4_SAFE_CALL_TAC in
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC KD4_EXEC (1--50) THEN
  call "H_SHAKE256" [`read RDI s`; `32`; `read RDX s`; `1600`] 51 THEN
  X86_STEPS_TAC KD4_EXEC (52--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; APPEND_NIL; ENUMERATEL_APPEND_ZERO] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC KD4_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD]; ALL_TAC] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_EXIT_B_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC KD4_EXEC (1--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_BAD_TAC =
  KD4_SAFE_START_TAC THEN
  X86_STEPS_TAC KD4_EXEC (16--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_DEC_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH dk = 3168 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 3072 32 dk) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 24752),24760) /\
    nonoverlapping (ss,32) (word_sub stackpointer (word 24752),24760) /\
    ALLPAIRS nonoverlapping
     [(ss,32); (word_sub stackpointer (word 24752),24760)]
     [(ct,1568); (sk,3168); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1c90) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ss; ct; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(sk,3168)) s = num_of_bytelist dk /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events ss ct sk pc
                        (word_sub stackpointer (word 24752)) returnaddress
                        (mlkem_slice 1536 1568 dk) (mlkem_slice 3104 32 dk) /\
                 memaccess_inbounds e2
                  [ct,1568; sk,3168; ss,32;
                   word_sub stackpointer (word 24752),24760;
                   word(pc + 0x8008),8; word(pc + 0x8018),8;
                   word(pc + 0x8020),8; word(pc + 0x8030),16;
                   word(pc + 0x8040),16; word(pc + 0x8050),16;
                   word(pc + 0x8060),16; word(pc + 0x8080),48;
                   word(pc + 0x80c0),192; word(pc + 0x81a0),256]
                  [ss,32; word_sub stackpointer (word 24752),24752]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 24752),24752)])`,
  KD4_SAFE_INTRO_TAC THEN KD4_SETUP_TAC THEN
  ABBREV_TAC `ekk = mlkem_slice 1536 1568 (dk:byte list)` THEN
  ABBREV_TAC `hh = mlkem_slice 3104 32 (dk:byte list)` THEN
  ASM_CASES_TAC
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)` THEN
  ASM_REWRITE_TAC[] THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `98` `pc + 0x1df0` `pc + 0x1e10`
     KD4_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD4_SAFE_PART1_TAC; KD4_SAFE_BODY_TAC;
      ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x1f10` `pc + 0x1f34`
       KD4_SAFE_CMOV_INV THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; KD4_SAFE_EXIT_A_TAC; KD4_SAFE_CMOV_BODY_TAC;
        KD4_SAFE_EXIT_B_TAC]];
    KD4_SAFE_BAD_TAC]);;
