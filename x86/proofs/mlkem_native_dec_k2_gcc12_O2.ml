(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-512 (FIPS 203 Algorithm 18, with the input    *)
(* check of Algorithm 21). This is the code for mlkem512_dec from            *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md). It checks the decapsulation key with             *)
(* mlkem512_check_sk, and returns -5 if the check fails. Otherwise it        *)
(* decrypts the ciphertext into m' with mlkem512_indcpa_dec, computes K' and *)
(* r' as G of m' followed by the hash h in the key with mlkem_sha3_512,      *)
(* encrypts m' with r' again by mlkem512_indcpa_enc, compares the result     *)
(* with the ciphertext in constant time, computes J of z (in the key)        *)
(* followed by the ciphertext into the shared secret with mlkem_shake256,    *)
(* and replaces it by K' if the ciphertexts are equal, again in constant     *)
(* time. In both cases it zeroes its buffers. It is verified in the whole    *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x52f0, using the theorems for mlkem512_check_sk, mlkem512_indcpa_dec,    *)
(* mlkem_sha3_512, mlkem512_indcpa_enc and mlkem_shake256 in the image.      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_check_sk_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_indcpa_dec_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_indcpa_enc_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake256_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    52f0: push   rbp
    52f1: mov    rbp,rsp
    52f4: push   r15
    52f6: mov    r15,rsi
    52f9: push   r14
    52fb: mov    r14,rdi
    52fe: mov    rdi,rdx
    5301: push   r13
    5303: mov    r13,rdx
    5306: push   r12
    5308: push   rbx
    5309: and    rsp,0xffffffffffffffe0
    530d: sub    rsp,0x3c0
    5314: call   4f10 <mlkem512_check_sk>
    5319: test   eax,eax
    531b: je     5388 <mlkem512_dec+0x98>
    531d: mov    ebx,eax
    531f: lea    r10,[rsp+0x20]
    5324: lea    r9,[rsp+0x60]
    5329: lea    r8,[rsp+0xa0]
    5331: xor    eax,eax
    5333: mov    rdi,r8
    5336: mov    ecx,0x64
    533b: rep    stos QWORD PTR es:[rdi],rax
    533e: pxor   xmm0,xmm0
    5342: movaps XMMWORD PTR [rsp+0x60],xmm0
    5347: movaps XMMWORD PTR [rsp+0x70],xmm0
    534c: movaps XMMWORD PTR [rsp+0x80],xmm0
    5354: movaps XMMWORD PTR [rsp+0x90],xmm0
    535c: movaps XMMWORD PTR [rsp+0x20],xmm0
    5361: movaps XMMWORD PTR [rsp+0x30],xmm0
    5366: movaps XMMWORD PTR [rsp+0x40],xmm0
    536b: movaps XMMWORD PTR [rsp+0x50],xmm0
    5370: lea    rsp,[rbp-0x28]
    5374: mov    eax,ebx
    5376: pop    rbx
    5377: pop    r12
    5379: pop    r13
    537b: pop    r14
    537d: pop    r15
    537f: pop    rbp
    5380: ret
    5381: nop    DWORD PTR [rax+0x0]
    5388: lea    r10,[rsp+0x20]
    538d: mov    rdx,r13
    5390: mov    rsi,r15
    5393: mov    rdi,r10
    5396: mov    QWORD PTR [rsp+0x18],r10
    539b: call   4cf0 <mlkem512_indcpa_dec>
    53a0: mov    r10,QWORD PTR [rsp+0x18]
    53a5: test   eax,eax
    53a7: mov    ebx,eax
    53a9: je     53c0 <mlkem512_dec+0xd0>
    53ab: lea    r9,[rsp+0x60]
    53b0: lea    r8,[rsp+0xa0]
    53b8: jmp    5331 <mlkem512_dec+0x41>
    53bd: nop    DWORD PTR [rax]
    53c0: lea    r9,[rsp+0x60]
    53c5: mov    rsi,r10
    53c8: mov    edx,0x40
    53cd: mov    QWORD PTR [rsp+0x18],r10
    53d2: movdqu xmm3,XMMWORD PTR [r13+0x620]
    53db: mov    rdi,r9
    53de: mov    QWORD PTR [rsp+0x8],r9
    53e3: movdqu xmm4,XMMWORD PTR [r13+0x630]
    53ec: movaps XMMWORD PTR [rsp+0x40],xmm3
    53f1: movaps XMMWORD PTR [rsp+0x50],xmm4
    53f6: call   3570 <mlkem_sha3_512>
    53fb: mov    r10,QWORD PTR [rsp+0x18]
    5400: lea    r8,[rsp+0xa0]
    5408: lea    rcx,[rsp+0x80]
    5410: mov    rdi,r8
    5413: lea    rdx,[r13+0x300]
    541a: mov    QWORD PTR [rsp+0x18],r8
    541f: mov    rsi,r10
    5422: mov    QWORD PTR [rsp+0x10],r10
    5427: call   4a40 <mlkem512_indcpa_enc>
    542c: mov    r8,QWORD PTR [rsp+0x18]
    5431: mov    r10,QWORD PTR [rsp+0x10]
    5436: test   eax,eax
    5438: mov    r9,QWORD PTR [rsp+0x8]
    543d: mov    ebx,eax
    543f: jne    5331 <mlkem512_dec+0x41>
    5445: pxor   xmm2,xmm2
    5449: xor    eax,eax
    544b: movdqa xmm0,xmm2
    544f: nop
    5450: movdqu xmm1,XMMWORD PTR [r15+rax*1]
    5456: pxor   xmm1,XMMWORD PTR [r8+rax*1]
    545c: add    rax,0x10
    5460: por    xmm0,xmm1
    5464: pxor   xmm2,xmm1
    5468: cmp    rax,0x300
    546e: jne    5450 <mlkem512_dec+0x160>
    5470: movdqa xmm1,xmm2
    5474: mov    QWORD PTR [rsp+0x8],r10
    5479: psrldq xmm1,0x8
    547e: mov    QWORD PTR [rsp+0x10],r9
    5483: pxor   xmm2,xmm1
    5487: movdqa xmm1,xmm2
    548b: psrldq xmm1,0x4
    5490: pxor   xmm2,xmm1
    5494: movdqa xmm1,xmm2
    5498: psrldq xmm1,0x2
    549d: pxor   xmm2,xmm1
    54a1: movdqa xmm1,xmm2
    54a5: psrldq xmm1,0x1
    54aa: pxor   xmm2,xmm1
    54ae: movdqa xmm1,xmm0
    54b2: psrldq xmm1,0x8
    54b7: movd   eax,xmm2
    54bb: por    xmm0,xmm1
    54bf: movdqa xmm1,xmm0
    54c3: psrldq xmm1,0x4
    54c8: por    xmm0,xmm1
    54cc: movdqa xmm1,xmm0
    54d0: psrldq xmm1,0x2
    54d5: por    xmm0,xmm1
    54d9: movdqa xmm1,xmm0
    54dd: psrldq xmm1,0x1
    54e2: por    xmm0,xmm1
    54e6: movd   r12d,xmm0
    54eb: movzx  r12d,r12b
    54ef: neg    r12d
    54f2: sar    r12d,0x10
    54f6: xor    r12d,eax
    54f9: xor    r12d,eax
    54fc: mov    rdx,r8
    54ff: mov    ecx,0x60
    5504: mov    rsi,r15
    5507: movdqu xmm6,XMMWORD PTR [r13+0x650]
    5510: mov    QWORD PTR [rsp+0x18],r8
    5515: movzx  r12d,r12b
    5519: lea    rax,[rsp+0xc0]
    5521: movdqu xmm5,XMMWORD PTR [r13+0x640]
    552a: mov    rdi,rax
    552d: neg    r12d
    5530: movaps XMMWORD PTR [rsp+0xb0],xmm6
    5538: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
    553b: mov    ecx,0x320
    5540: mov    esi,0x20
    5545: mov    rdi,r14
    5548: movaps XMMWORD PTR [rsp+0xa0],xmm5
    5550: call   3480 <mlkem_shake256>
    5555: mov    r10,QWORD PTR [rsp+0x8]
    555a: mov    r9,QWORD PTR [rsp+0x10]
    555f: xor    eax,eax
    5561: mov    r8,QWORD PTR [rsp+0x18]
    5566: cs     nop WORD PTR [rax+rax*1+0x0]
    5570: movzx  esi,BYTE PTR [r9+rax*1]
    5575: mov    ecx,r12d
    5578: movzx  edx,BYTE PTR [r14+rax*1]
    557d: sar    ecx,0x10
    5580: xor    edx,esi
    5582: and    edx,ecx
    5584: xor    edx,esi
    5586: mov    BYTE PTR [r14+rax*1],dl
    558a: add    rax,0x1
    558e: cmp    rax,0x20
    5592: jne    5570 <mlkem512_dec+0x280>
    5594: jmp    5331 <mlkem512_dec+0x41>
 ***)

let MLKEM_NATIVE_DEC_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x52f0,0x5599];;

let KD2_EXEC = MLKEM_NATIVE_DEC_K2_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-512, and the input check   *)
(* of FIPS 203 in terms of the result of mlkem512_check_sk.                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_512 = prove
 (`!ek m r. LENGTH(kpke_encrypt mlkem512 ek m r) = 768`,
  REWRITE_TAC[mlkem512; KPKE_ENCRYPT_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let KPKE_DECRYPT_LENGTH_512 = prove
 (`!dk c. LENGTH(kpke_decrypt mlkem512 dk c) = 32`,
  REWRITE_TAC[mlkem512; KPKE_DECRYPT_LENGTH]);;

let KD2_CHECK = prove
 (`!dk c. LENGTH dk = 1632 /\ LENGTH c = 768
          ==> (mlkem_decaps_check mlkem512 dk c <=>
               num_of_bytelist(mlkem_slice 1568 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 768 800 dk)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem512; mlkem_decaps_check] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[mlkem_h] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ; LENGTH_SHA3_256]);;

(* ------------------------------------------------------------------------- *)
(* The frame, the slices of the decapsulation key, and the values computed:  *)
(* m', G of m' and h, K' and r', the reencryption c' of m', z, the result of *)
(* J, and whether c' is the ciphertext. The buffers are aligned to 32 bytes  *)
(* within the stack frame, by AND with -32 after the pushes, as in           *)
(* mlkem512_indcpa_dec, and their addresses are offsets from the frame       *)
(* variable bot of INDCPA_BOT_TAC, the bottom of the stacks of the callees   *)
(* 12128 bytes below them: m' and h at bot + 12160, K' and r' at bot + 12224 *)
(* and c', and then z and the copy of the ciphertext, at bot + 12288.        *)
(* ------------------------------------------------------------------------- *)

let KD2_FRAME = (13168,48,12128,960);;

let KD2_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KD2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13168 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SIMP_TAC[KD2_CHECK; ASSUME `LENGTH(dk:byte list) = 1632`;
           ASSUME `LENGTH(c:byte list) = 768`] THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 768 (dk:byte list)) = 768 /\
    LENGTH(mlkem_slice 768 800 (dk:byte list)) = 800 /\
    LENGTH(mlkem_slice 1568 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 1600 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`768`; `32`; `768`; `800`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `768 + 32 <= 800`)))] o
   check (fun th -> is_forall(concl th) &&
                    INDCPA_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD2_SETUP_TAC =
  INDCPA_BOT_TAC KD2_FRAME [12128] THEN
  INDCPA_FRAME_TAC ["memory :> bytes(ss:int64,32)"] KD2_FRAME THEN
  INDCPA_NONOV_TAC 13088
   [`ss:int64,32`; `ct:int64,768`; `sk:int64,1632`;
    `word pc:int64,0x82a0`; `word_add stackpointer (word 13120):int64,56`]
  THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KD2_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,1632)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,768; 768,800; 1568,32; 1600,32]
    else NO_TAC);;

let KD2_MP = `kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c`;;

let KD2_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c)
                  (mlkem_slice 1568 32 dk))`;;

let KD2_KP = mk_comb(`mlkem_slice 0 32`,KD2_GG);;

let KD2_RR = mk_comb(`mlkem_slice 32 32`,KD2_GG);;

let KD2_CP = list_mk_comb(`kpke_encrypt mlkem512`,
  [`mlkem_slice 768 800 (dk:byte list)`; KD2_MP; KD2_RR]);;

let KD2_ZZ = `mlkem_slice 1600 32 (dk:byte list)`;;

let KD2_KB =
 `list_of_seq (shake256 (APPEND (mlkem_slice 1600 32 dk) c)) 32`;;

let KD2_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD2_CP));;

let KD2_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD2_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD2_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD2_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD2_ZZ),`ZZ:num`;
         KD2_EQ,`EQ:bool`] tm;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the comparison loop at iteration i states that the OR    *)
(* accumulator in XMM0 is zero if and only if the first 16 * i bytes of the  *)
(* ciphertext and of c' are equal, and the invariant of the conditional move *)
(* at iteration i that the first i bytes at ss are those of K' if the        *)
(* ciphertexts are equal and those of the result of J otherwise, and the     *)
(* others still those of the result of J. Both keep the registers, the       *)
(* pushes and K' (KEEP).                                                     *)
(* ------------------------------------------------------------------------- *)

let KD2_SAFE_KEEP =
 `read RSP s = word_add bot (word 12128) /\
  read RBP s = word_add stackpointer (word 13160) /\
  read RBX s = word 0 /\
  read R13 s = sk /\ read R14 s = ss /\ read R15 s = ct /\
  read R8 s = word_add bot (word 12288) /\
  read R9 s = word_add bot (word 12224) /\
  (read DF s <=> false) /\
  read (memory :> bytes64 (word_add stackpointer (word 13168))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 13160))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13152))) s =
  r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13144))) s =
  r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13136))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13128))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13120))) s =
  rbx_init`;;

let KD2_KEEP = KD2_SUBST
 `read RSP s = word_add bot (word 12128) /\
  read RBP s = word_add stackpointer (word 13160) /\
  read RBX s = word 0 /\
  read R13 s = sk /\ read R14 s = ss /\ read R15 s = ct /\
  read R8 s = word_add bot (word 12288) /\
  read R9 s = word_add bot (word 12224) /\
  (read DF s <=> false) /\
  read (memory :> bytes64 (word_add stackpointer (word 13168))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 13160))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13152))) s =
  r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13144))) s =
  r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13136))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13128))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 13120))) s =
  rbx_init /\
  read (memory :> bytes(word_add bot (word 12224),32)) s = KP`;;

let KD2_WITH_KEEP keep inv =
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [keep,`KEEP:bool`] bod);;

let KD2_INV = KD2_WITH_KEEP KD2_KEEP (KD2_SUBST
 `\i s. read RAX s = word(16 * i) /\
        read R10 s = word_add bot (word 12160) /\
        read R12 s = r12_init /\
        (word_subword (read YMM0 s) (0,128):int128 = word 0 <=>
         num_of_bytelist c MOD 2 EXP (128 * i) = CP MOD 2 EXP (128 * i)) /\
        read (memory :> bytes(ct,768)) s = num_of_bytelist c /\
        read (memory :> bytes(word_add bot (word 12288),768)) s = CP /\
        read (memory :> bytes128 (word_add sk (word 1600))) s =
        word(ZZ MOD 2 EXP 128) /\
        read (memory :> bytes128 (word_add sk (word 1616))) s =
        word(ZZ DIV 2 EXP 128) /\ KEEP`);;

let KD2_CMOV_INV = KD2_WITH_KEEP KD2_KEEP (KD2_SUBST
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

let KD2_G_INPUT_TAC s =
  let st = mk_var(s,`:x86state`) in
  SUBGOAL_THEN
   (subst [st,`s:x86state`; INDCPA_SP 12160,`a:int64`;
           KD2_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 1568 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND;
                    KPKE_DECRYPT_LENGTH_512];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD2_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 1568 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_512] THEN
    ARITH_TAC;
    ALL_TAC];;

let KD2_KR_TAC s =
  let st = mk_var(s,`:x86state`) and a = INDCPA_SP 12224 in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:x86state`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD2_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD2_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KD2_PART1_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD2_CALL in
  ENSURES_INIT_TAC "s0" THEN KD2_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 1568):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 1600):int64` THEN

  (*** The check of the key ***)

  X86_STEPS_TAC KD2_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD2_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `mlkem_slice 768 800 (dk:byte list)`;
     `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list))`] @ post) 15 THEN
  INDCPA_NORM_TAC THEN

  (*** The decryption, G and the reencryption ***)

  X86_STEPS_TAC KD2_EXEC (16--23) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_DEC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`;
     `mlkem_slice 0 768 (dk:byte list)`; `c:byte list`] @ post) 24 THEN
  INDCPA_NORM_TAC THEN INDCPA_YMMS_TAC "s24" [3; 4] THEN
  X86_STEPS_TAC KD2_EXEC (25--32) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (33--38) THEN
  INDCPA_NORM_TAC THEN
  KEM_JOIN_TAC (INDCPA_SP 12192) `mlkem_slice 1568 32 (dk:byte list)` "s38"
  THEN KD2_G_INPUT_TAC "s38" THEN
  X86_STEPS_TAC KD2_EXEC [39] THEN
  call MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`;
     mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD2_MP),
             `mlkem_slice 1568 32 (dk:byte list)`)] @ post) 40 THEN
  INDCPA_NORM_TAC THEN KD2_KR_TAC "s40" THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_512]; ALL_TAC] THEN
  X86_STEPS_TAC KD2_EXEC (41--49) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
     `mlkem_slice 768 800 (dk:byte list)`; KD2_MP; KD2_RR] @ post) 50 THEN
  INDCPA_NORM_TAC THEN

  (*** The start of the comparison ***)

  X86_STEPS_TAC KD2_EXEC (51--56) THEN INDCPA_YMMS_TAC "s56" [0; 2] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (57--60) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[KEM_SUBWORD_JOIN_128; MOD_1] THEN CONV_TAC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the comparison, with the loop test. The two 128-bit      *)
(* words loaded are given in the form of the address computed for the base   *)
(* and index registers (KEM_INDEX_TAC), and the values of the YMM registers  *)
(* at the start of the iteration are introduced as ghosts.                   *)
(* ------------------------------------------------------------------------- *)

let KD2_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 48 ==> 16 * i + 16 <= 768`)
               (ASSUME `i < 48`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`768`) && vv = v ->
          let lth = SPECL [a; `768`; `i:num`; v; s] KEM_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (MP lth (CONJ th bth)))
    | _ -> NO_TAC);;

let KD2_TEST = prove
 (`!i. i < 48
       ==> (val(word_add (word(16 * i)) (word 18446744073709550864):int64) =
            0 <=> ~(i + 1 < 48))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 48 ==> 16 * i < 18446744073709551616`] THEN
  ASM_CASES_TAC `i + 1 < 48` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i + 1 < 48 ==> 16 * i + 18446744073709550864 < 18446744073709551616`]
    THEN ARITH_TAC;
    SUBGOAL_THEN `i = 47` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]]);;

let KD2_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  ENSURES_INIT_TAC "s0" THEN
  KD2_CHUNK_TAC `ct:int64` `num_of_bytelist c` THEN
  KD2_CHUNK_TAC (INDCPA_SP 12288) (mk_comb(`num_of_bytelist`,KD2_CP)) THEN
  VAL_INT64_TAC `16 * i` THEN KEM_INDEX_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD2_TEST) (ASSUME `i < 48`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 48` THEN ASM_REWRITE_TAC[];
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

let KD2_Q = `word_subword (y0:int256) (0,128):int128`;;

let KD2_DONE_TAC =
  SUBGOAL_THEN (mk_iff(mk_eq(KD2_Q,`word 0:int128`),KD2_EQ)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = mk_eq(KD2_Q,`word 0:int128`)
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(ISPEC `c:byte list` NUM_OF_BYTELIST_BOUND) THEN
    MP_TAC(ISPEC KD2_CP NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_512] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let KD2_MASK_TAC s =
  let r12 = mk_comb(`read R12`,mk_var(s,`:x86state`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = r12 then
      let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[KEM_MOD256])) th in
      let eth = BITBLAST_RULE
        (mk_eq(rand(concl th1),
               mk_cond(mk_eq(KD2_Q,`word 0:int128`),
                       `word 0:int64`,`word 4294967041:int64`))) in
      ASSUME_TAC(TRANS th1 eth)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = r12 then
      FIRST_ASSUM(fun th' ->
        if is_iff(concl th') &&
           lhand(concl th') = mk_eq(KD2_Q,`word 0:int128`)
        then ASSUME_TAC(REWRITE_RULE[th'] th) else NO_TAC)
    else NO_TAC);;

let KD2_J_INPUT_TAC s =
  let st = mk_var(s,`:x86state`) in
  SUBGOAL_THEN
   (subst [st,`s:x86state`; INDCPA_SP 12288,`a:int64`]
     `read (memory :> bytes(a,800)) s =
      num_of_bytelist(APPEND (mlkem_slice 1600 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `800 = 32 + 768`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 1600 32 (dk:byte list)) c) = 800`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

let KD2_EXIT_A_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD2_CALL in
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `y5:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `y6:int256` `read YMM6` THEN
  ENSURES_INIT_TAC "s0" THEN KD2_DONE_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (1--44) THEN
  KD2_MASK_TAC "s44" THEN KEM_MOVSQ_STEP_TAC KD2_EXEC 45 96 THEN
  X86_STEPS_TAC KD2_EXEC (46--48) THEN
  X86_STEPS_TAC KD2_EXEC [49] THEN SIMD_SIMPLIFY_TAC[] THEN
  KEM_JOIN_TAC (INDCPA_SP 12288) KD2_ZZ "s49" THEN KD2_J_INPUT_TAC "s49" THEN
  X86_STEPS_TAC KD2_EXEC [50] THEN
  call MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `32`; `read RDX s`;
     `APPEND (mlkem_slice 1600 32 (dk:byte list)) c`] @ post) 51 THEN
  X86_STEPS_TAC KD2_EXEC (52--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers by REP STOSQ and SSE stores, and the result in terms of FIPS 203, *)
(* and the case where the check of the key fails.                            *)
(* ------------------------------------------------------------------------- *)

let KD2_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [INDCPA_SP 12224; `32`; mk_comb(`num_of_bytelist`,KD2_KP);
                `i:num`; `s0:x86state`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   (KD2_SUBST `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC th1 THEN ASSUME_TAC th2)] THEN
  VAL_INT64_TAC `i:num` THEN KEM_INDEX1_TAC THEN
  X86_STEPS_TAC KD2_EXEC (1--11) THEN
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
    ASM_CASES_TAC KD2_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN REWRITE_TAC[KEM_MOD256] THEN
    SPEC_TAC(KD2_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD2_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; WORD_ADD; WORD_ADD_ASSOC;
                KEM_DIV_BYTE] THEN
    ASM_REWRITE_TAC[]];;

let KD2_FINAL_TAC =
  REWRITE_TAC[mlkem512; MLKEM_DECAPS_ALT] THEN
  REWRITE_TAC[GSYM mlkem512] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD2_CP,`c:byte list`),KD2_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_512];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let KD2_EXIT_B_TAC =
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KD2_EXEC (1--5) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (6--14) THEN
  X86_STEPS_TAC KD2_EXEC (15--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD2_FINAL_TAC;;

let KD2_BAD_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KD2_CALL in
  ENSURES_INIT_TAC "s0" THEN KD2_SK_TAC THEN
  X86_STEPS_TAC KD2_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD2_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `mlkem_slice 768 800 (dk:byte list)`;
     `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list))`] @ post) 15 THEN
  INDCPA_NORM_TAC THEN INDCPA_YMMS_TAC "s15" [0] THEN
  X86_STEPS_TAC KD2_EXEC (16--25) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (26--34) THEN
  X86_STEPS_TAC KD2_EXEC (35--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The decapsulation key dk of 1632 bytes is at sk and    *)
(* the ciphertext c of 768 bytes at ct, and if they pass the check of FIPS   *)
(* 203, the shared secret of 32 bytes written at ss is that of               *)
(* mlkem_decaps_internal mlkem512 dk c in common/fips203.ml and the function *)
(* returns 0, and otherwise it returns -5. The theorem assumes that          *)
(* SampleNTT terminates for each entry of the matrix from the seed in the    *)
(* key, as for mlkem512_indcpa_enc. The stack is the 13168 bytes below the   *)
(* return address, for the six saved registers, up to 31 bytes for the       *)
(* alignment, the 960 bytes of the buffers and the 12128 used by the callees *)
(* below them. The proof is by cases on the check of the key, with the two   *)
(* loops for the comparison and the conditional move.                        *)
(* ------------------------------------------------------------------------- *)

let KD2_OK_TAC =
  ENSURES_WHILE_UP2_TAC `48` `pc + 0x5450` `pc + 0x5470`
   KD2_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD2_PART1_TAC; KD2_BODY_TAC;
    ENSURES_WHILE_UP2_TAC `32` `pc + 0x5570` `pc + 0x5594`
     KD2_CMOV_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD2_EXIT_A_TAC; KD2_CMOV_BODY_TAC; KD2_EXIT_B_TAC]];;

let MLKEM_NATIVE_DEC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!ss ct sk (dk:byte list) (c:byte list) pc stackpointer
    returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH dk = 1632 /\ LENGTH c = 768 /\
    (!i j. i < 2 /\ j < 2
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1536 32 dk) [word j; word i])) /\
    nonoverlapping (ss,32) (word_sub stackpointer (word 13168),13176) /\
    ALLPAIRS nonoverlapping
     [(ss,32); (word_sub stackpointer (word 13168),13176)]
     [(ct,768); (sk,1632); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x52f0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ss; ct; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(ct,768)) s = num_of_bytelist c /\
              read (memory :> bytes(sk,1632)) s = num_of_bytelist dk)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (mlkem_decaps_check mlkem512 dk c
               ==> read (memory :> bytes(ss,32)) s =
                   num_of_bytelist(mlkem_decaps_internal mlkem512 dk c)) /\
              C_RETURN s =
              (if mlkem_decaps_check mlkem512 dk c then word 0
               else word 0xfffffffb))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 13168),13168)])`,
  KD2_INTRO_TAC THEN KD2_SETUP_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 768 800 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD2_OK_TAC; KD2_BAD_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses and on the encapsulation key ek in the decapsulation key and    *)
(* the hash h stored with it, through the check of the hash, given by the    *)
(* combined theorem for mlkem512_check_sk, and the reencryption, but not on  *)
(* the secret key, z or the ciphertext: the comparison of the ciphertexts    *)
(* and the selection of the shared secret are loops in constant time. The    *)
(* events are given by a template with cases on the check, with the events   *)
(* of the loops as ENUMERATEL, whose invariants have only the pointers and   *)
(* the frame, and the frame variables are expanded in them by                *)
(* INDCPA_UNBOT_TAC.                                                         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let KD2_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (pc:num) (stackpointer:int64)
   (returnaddress:int64) (ek:byte list) (h:byte list).
   if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
   then APPEND
         (APPEND (f_ev_exitb ss ct sk pc stackpointer returnaddress)
           (APPEND (ENUMERATEL 32
                     (\i. f_ev_cmov ss ct sk pc stackpointer returnaddress i))
                   (f_ev_exita ss ct sk pc stackpointer returnaddress)))
         (APPEND (ENUMERATEL 48
                   (\i. f_ev_cmp ss ct sk pc stackpointer returnaddress i))
                 (f_ev_prol ss ct sk pc stackpointer returnaddress ek h))
   else f_ev_bad ss ct sk pc stackpointer returnaddress ek h
   :(uarch_event)list`;;

let KD2_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `ekk:byte list`; `hh:byte list`; `i:num`;
   `bot:int64`;
   `f_ev_cmp:int64->int64->int64->num->int64->int64->num->
              (uarch_event)list`;
   `f_ev_cmov:int64->int64->int64->num->int64->int64->num->
              (uarch_event)list`];;

let KD2_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KD2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KD2_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD2_SAFE_INV = KD2_WITH_KEEP KD2_SAFE_KEEP
 `\i s. read RAX s = word(16 * i) /\
        read R10 s = word_add bot (word 12160) /\ KEEP`;;

let KD2_SAFE_CMOV_INV = KD2_WITH_KEEP KD2_SAFE_KEEP
 `\i s. read RAX s = word i /\ KEEP`;;

let KD2_SAFE_INTRO_TAC =
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL, "H_CHECK";
    MLKEM_NATIVE_INDCPA_DEC_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_DEC";
    MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHA3_512";
    MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_ENC";
    MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHAKE256"] THEN
  CONCRETIZE_F_EVENTS_TAC KD2_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13168 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 768 (dk:byte list)) = 768 /\
    LENGTH(mlkem_slice 768 800 (dk:byte list)) = 800 /\
    LENGTH(mlkem_slice 1568 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 1600 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`768`; `32`; `768`; `800`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `768 + 32 <= 800`)))] o
   check (fun th -> is_forall(concl th) &&
                    INDCPA_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD2_SAFE_START_TAC =
  let call = KD2_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN KD2_SK_TAC THEN
  X86_STEPS_TAC KD2_EXEC (1--12) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KD2_EXEC (13--14) THEN INDCPA_NORM_TAC THEN
  call "H_CHECK"
   [`read RDI s`; `ekk:byte list`; `num_of_bytelist(hh:byte list)`] 15 THEN
  INDCPA_NORM_TAC;;

let KD2_SAFE_PART1_TAC =
  let call = KD2_SAFE_CALL_TAC in
  KD2_SAFE_START_TAC THEN
  X86_STEPS_TAC KD2_EXEC (16--23) THEN INDCPA_NORM_TAC THEN
  call "H_DEC" [`read RDI s`; `read RSI s`; `read RDX s`] 24 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KD2_EXEC (25--39) THEN INDCPA_NORM_TAC THEN
  call "H_SHA3_512" [`read RDI s`; `read RSI s`; `64`] 40 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KD2_EXEC (41--49) THEN INDCPA_NORM_TAC THEN
  call "H_ENC"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `ekk:byte list`]
   50 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC KD2_EXEC (51--60) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `16 * i` THEN
  X86_STEPS_TAC KD2_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD2_TEST) (ASSUME `i < 48`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_EXIT_A_TAC =
  let call = KD2_SAFE_CALL_TAC in
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC KD2_EXEC (1--50) THEN
  call "H_SHAKE256" [`read RDI s`; `32`; `read RDX s`; `800`] 51 THEN
  X86_STEPS_TAC KD2_EXEC (52--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; APPEND_NIL; ENUMERATEL_APPEND_ZERO] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC KD2_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD]; ALL_TAC] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_EXIT_B_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC KD2_EXEC (1--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_BAD_TAC =
  KD2_SAFE_START_TAC THEN
  X86_STEPS_TAC KD2_EXEC (16--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_DEC_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH dk = 1632 /\
    (!i j. i < 2 /\ j < 2
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1536 32 dk) [word j; word i])) /\
    nonoverlapping (ss,32) (word_sub stackpointer (word 13168),13176) /\
    ALLPAIRS nonoverlapping
     [(ss,32); (word_sub stackpointer (word 13168),13176)]
     [(ct,768); (sk,1632); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x52f0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ss; ct; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(sk,1632)) s = num_of_bytelist dk /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events ss ct sk pc
                        (word_sub stackpointer (word 13168)) returnaddress
                        (mlkem_slice 768 800 dk) (mlkem_slice 1568 32 dk) /\
                 memaccess_inbounds e2
                  [ct,768; sk,1632; ss,32;
                   word_sub stackpointer (word 13168),13176;
                   word(pc + 0x8000),8; word(pc + 0x8008),8;
                   word(pc + 0x8010),8; word(pc + 0x8080),48;
                   word(pc + 0x80c0),192; word(pc + 0x8180),2;
                   word(pc + 0x81a0),256]
                  [ss,32; word_sub stackpointer (word 13168),13168]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 13168),13168)])`,
  KD2_SAFE_INTRO_TAC THEN KD2_SETUP_TAC THEN
  ABBREV_TAC `ekk = mlkem_slice 768 800 (dk:byte list)` THEN
  ABBREV_TAC `hh = mlkem_slice 1568 32 (dk:byte list)` THEN
  ASM_CASES_TAC
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)` THEN
  ASM_REWRITE_TAC[] THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `48` `pc + 0x5450` `pc + 0x5470`
     KD2_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD2_SAFE_PART1_TAC; KD2_SAFE_BODY_TAC;
      ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x5570` `pc + 0x5594`
       KD2_SAFE_CMOV_INV THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; KD2_SAFE_EXIT_A_TAC; KD2_SAFE_CMOV_BODY_TAC;
        KD2_SAFE_EXIT_B_TAC]];
    KD2_SAFE_BAD_TAC]);;
