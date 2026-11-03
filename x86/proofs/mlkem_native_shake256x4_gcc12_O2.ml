(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of four inputs of the same length, with four outputs of any      *)
(* length. This is the code for mlkem_shake256x4 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which realigns the stack to 32 bytes, zeroes a   *)
(* context of four states on it with an inline memset, absorbs the inputs    *)
(* into it with mlk_keccak_absorb_once_x4, squeezes the whole blocks of 136  *)
(* bytes, the rate of SHAKE256, directly into the outputs, and the rest of   *)
(* the outputs through four buffers on the stack with inline copies, before  *)
(* zeroing the context and the buffers with REP STOSQ. It is verified in the *)
(* whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at       *)
(* address 0x3870, using the theorems for mlk_keccak_absorb_once_x4 at       *)
(* 0x35d0, mlkem_keccakf1600x4_permute at 0x4740 and                         *)
(* mlkem_keccakf1600x4_extract_bytes at 0x3d70 in the image. The result is   *)
(* shake256 of common/fips202.ml for each input.                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccak_absorb_once_x4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_keccakf1600x4_permute_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_keccakf1600x4_extract_bytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;
needs "x86/proofs/consttime.ml";;

(*** The code in the image:

    3870: lea    r10,[rsp+0x8]
    3875: and    rsp,0xffffffffffffffe0
    3879: mov    r11,r8
    387c: push   QWORD PTR [r10-0x8]
    3880: mov    rax,r11
    3883: push   rbp
    3884: mov    rbp,rsp
    3887: push   r15
    3889: mov    r15,rdi
    388c: push   r14
    388e: mov    r14,rsi
    3891: push   r13
    3893: mov    r13,rdx
    3896: push   r12
    3898: mov    r12,rcx
    389b: push   r10
    389d: push   rbx
    389e: sub    rsp,0x5a8
    38a5: mov    QWORD PTR [rbp-0x5c0],rdx
    38ac: movabs rdx,0xf0f0f0f0f0f0f0f1
    38b6: mov    rbx,QWORD PTR [r10]
    38b9: mul    rdx
    38bc: mov    QWORD PTR [rbp-0x5a8],r11
    38c3: lea    r11,[rbp-0x350]
    38ca: mov    r8,QWORD PTR [r10+0x8]
    38ce: mov    QWORD PTR [rbp-0x5b0],rdi
    38d5: mov    rdi,r11
    38d8: mov    QWORD PTR [rbp-0x5c8],rcx
    38df: mov    ecx,0x64
    38e4: mov    rax,rdx
    38e7: mov    QWORD PTR [rbp-0x5b8],rsi
    38ee: mov    rsi,r9
    38f1: mov    r9,QWORD PTR [r10+0x10]
    38f5: shr    rax,0x7
    38f9: mov    QWORD PTR [rbp-0x598],r11
    3900: mov    rdx,rsi
    3903: mov    esi,0x88
    3908: mov    QWORD PTR [rbp-0x5a0],rax
    390f: xor    eax,eax
    3911: rep    stos QWORD PTR es:[rdi],rax
    3914: push   QWORD PTR [r10+0x18]
    3918: mov    rdi,r11
    391b: mov    rcx,rbx
    391e: call   35d0 <mlk_keccak_absorb_once_x4.constprop.0>
    3923: mov    r11,QWORD PTR [rbp-0x5a8]
    392a: pop    rdi
    392b: pop    r8
    392d: cmp    r11,0x87
    3934: jbe    399b <mlkem_shake256x4+0x12b>
    3936: mov    rbx,QWORD PTR [rbp-0x5a0]
    393d: nop    DWORD PTR [rax]
    3940: mov    rdi,QWORD PTR [rbp-0x598]
    3947: call   4740 <mlkem_keccakf1600x4_permute>
    394c: sub    rsp,0x8
    3950: mov    rcx,r13
    3953: mov    rsi,r15
    3956: push   0x88
    395b: mov    r8,r12
    395e: mov    rdx,r14
    3961: xor    r9d,r9d
    3964: mov    rdi,QWORD PTR [rbp-0x598]
    396b: add    r15,0x88
    3972: add    r14,0x88
    3979: add    r13,0x88
    3980: add    r12,0x88
    3987: call   3d70 <mlkem_keccakf1600x4_extract_bytes>
    398c: pop    rcx
    398d: pop    rsi
    398e: sub    rbx,0x1
    3992: jne    3940 <mlkem_shake256x4+0xd0>
    3994: mov    r11,QWORD PTR [rbp-0x5a8]
    399b: movabs rax,0xf0f0f0f0f0f0f0f1
    39a5: mul    r11
    39a8: mov    rbx,rdx
    39ab: shr    rbx,0x7
    39af: mov    rax,rbx
    39b2: shl    rax,0x4
    39b6: add    rax,rbx
    39b9: mov    rbx,r11
    39bc: shl    rax,0x3
    39c0: sub    rbx,rax
    39c3: jne    3a40 <mlkem_shake256x4+0x1d0>
    39c5: lea    r12,[rbp-0x3e0]
    39cc: lea    r13,[rbp-0x470]
    39d3: lea    r14,[rbp-0x500]
    39da: lea    r15,[rbp-0x590]
    39e1: mov    rdi,QWORD PTR [rbp-0x598]
    39e8: xor    eax,eax
    39ea: mov    ecx,0x64
    39ef: rep    stos QWORD PTR es:[rdi],rax
    39f2: mov    rdi,QWORD PTR [rbp-0x598]
    39f9: mov    ecx,0x11
    39fe: mov    rdi,r15
    3a01: rep    stos QWORD PTR es:[rdi],rax
    3a04: mov    ecx,0x11
    3a09: mov    rdi,r14
    3a0c: rep    stos QWORD PTR es:[rdi],rax
    3a0f: mov    ecx,0x11
    3a14: mov    rdi,r13
    3a17: rep    stos QWORD PTR es:[rdi],rax
    3a1a: mov    ecx,0x11
    3a1f: mov    rdi,r12
    3a22: rep    stos QWORD PTR es:[rdi],rax
    3a25: lea    rsp,[rbp-0x30]
    3a29: pop    rbx
    3a2a: pop    r10
    3a2c: pop    r12
    3a2e: pop    r13
    3a30: pop    r14
    3a32: pop    r15
    3a34: pop    rbp
    3a35: lea    rsp,[r10-0x8]
    3a39: ret
    3a3a: nop    WORD PTR [rax+rax*1+0x0]
    3a40: mov    rsi,QWORD PTR [rbp-0x5a0]
    3a47: mov    rdi,QWORD PTR [rbp-0x598]
    3a4e: lea    r12,[rbp-0x3e0]
    3a55: lea    r13,[rbp-0x470]
    3a5c: lea    r14,[rbp-0x500]
    3a63: lea    r15,[rbp-0x590]
    3a6a: mov    rax,rsi
    3a6d: shl    rax,0x4
    3a71: add    rax,rsi
    3a74: shl    rax,0x3
    3a78: mov    QWORD PTR [rbp-0x5a0],rax
    3a7f: call   4740 <mlkem_keccakf1600x4_permute>
    3a84: sub    rsp,0x8
    3a88: mov    rcx,r13
    3a8b: mov    rdx,r14
    3a8e: push   0x88
    3a93: xor    r9d,r9d
    3a96: mov    r8,r12
    3a99: mov    rsi,r15
    3a9c: mov    rdi,QWORD PTR [rbp-0x598]
    3aa3: call   3d70 <mlkem_keccakf1600x4_extract_bytes>
    3aa8: mov    rdx,QWORD PTR [rbp-0x5b0]
    3aaf: mov    rax,QWORD PTR [rbp-0x5a0]
    3ab6: mov    ecx,ebx
    3ab8: add    rdx,rax
    3abb: cmp    ebx,0x8
    3abe: jae    3b90 <mlkem_shake256x4+0x320>
    3ac4: test   bl,0x4
    3ac7: jne    3cc3 <mlkem_shake256x4+0x453>
    3acd: test   ecx,ecx
    3acf: je     3ae4 <mlkem_shake256x4+0x274>
    3ad1: movzx  esi,BYTE PTR [rbp-0x590]
    3ad8: mov    BYTE PTR [rdx],sil
    3adb: test   cl,0x2
    3ade: jne    3cd9 <mlkem_shake256x4+0x469>
    3ae4: mov    rdx,QWORD PTR [rbp-0x5b8]
    3aeb: mov    ecx,ebx
    3aed: add    rdx,rax
    3af0: cmp    ebx,0x8
    3af3: jae    3c38 <mlkem_shake256x4+0x3c8>
    3af9: test   bl,0x4
    3afc: jne    3cad <mlkem_shake256x4+0x43d>
    3b02: test   ecx,ecx
    3b04: je     3b19 <mlkem_shake256x4+0x2a9>
    3b06: movzx  esi,BYTE PTR [rbp-0x500]
    3b0d: mov    BYTE PTR [rdx],sil
    3b10: test   cl,0x2
    3b13: jne    3cf9 <mlkem_shake256x4+0x489>
    3b19: mov    rdx,QWORD PTR [rbp-0x5c0]
    3b20: mov    ecx,ebx
    3b22: add    rdx,rax
    3b25: cmp    ebx,0x8
    3b28: jae    3c00 <mlkem_shake256x4+0x390>
    3b2e: test   bl,0x4
    3b31: jne    3c97 <mlkem_shake256x4+0x427>
    3b37: test   ecx,ecx
    3b39: je     3b4e <mlkem_shake256x4+0x2de>
    3b3b: movzx  esi,BYTE PTR [rbp-0x470]
    3b42: mov    BYTE PTR [rdx],sil
    3b45: test   cl,0x2
    3b48: jne    3ce9 <mlkem_shake256x4+0x479>
    3b4e: mov    rsi,QWORD PTR [rbp-0x5c8]
    3b55: mov    ecx,ebx
    3b57: add    rsi,rax
    3b5a: mov    rax,rsi
    3b5d: cmp    ebx,0x8
    3b60: jae    3bc8 <mlkem_shake256x4+0x358>
    3b62: and    ebx,0x4
    3b65: jne    3c7f <mlkem_shake256x4+0x40f>
    3b6b: test   ecx,ecx
    3b6d: je     3b81 <mlkem_shake256x4+0x311>
    3b6f: movzx  edx,BYTE PTR [rbp-0x3e0]
    3b76: mov    BYTE PTR [rsi],dl
    3b78: test   cl,0x2
    3b7b: jne    3c6d <mlkem_shake256x4+0x3fd>
    3b81: pop    rax
    3b82: pop    rdx
    3b83: jmp    39e1 <mlkem_shake256x4+0x171>
    3b88: nop    DWORD PTR [rax+rax*1+0x0]
    3b90: mov    rcx,QWORD PTR [rbp-0x590]
    3b97: lea    rdi,[rdx+0x8]
    3b9b: and    rdi,0xfffffffffffffff8
    3b9f: mov    QWORD PTR [rdx],rcx
    3ba2: mov    ecx,ebx
    3ba4: mov    rsi,QWORD PTR [r15+rcx*1-0x8]
    3ba9: mov    QWORD PTR [rdx+rcx*1-0x8],rsi
    3bae: sub    rdx,rdi
    3bb1: mov    rsi,r15
    3bb4: lea    ecx,[rbx+rdx*1]
    3bb7: sub    rsi,rdx
    3bba: shr    ecx,0x3
    3bbd: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
    3bc0: jmp    3ae4 <mlkem_shake256x4+0x274>
    3bc5: nop    DWORD PTR [rax]
    3bc8: mov    rdx,QWORD PTR [rbp-0x3e0]
    3bcf: lea    rdi,[rsi+0x8]
    3bd3: and    rdi,0xfffffffffffffff8
    3bd7: mov    QWORD PTR [rsi],rdx
    3bda: mov    edx,ebx
    3bdc: sub    rax,rdi
    3bdf: mov    rcx,QWORD PTR [r12+rdx*1-0x8]
    3be4: mov    QWORD PTR [rsi+rdx*1-0x8],rcx
    3be9: lea    ecx,[rbx+rax*1]
    3bec: mov    rsi,r12
    3bef: sub    rsi,rax
    3bf2: shr    ecx,0x3
    3bf5: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
    3bf8: pop    rax
    3bf9: pop    rdx
    3bfa: jmp    39e1 <mlkem_shake256x4+0x171>
    3bff: nop
    3c00: mov    rcx,QWORD PTR [rbp-0x470]
    3c07: lea    rdi,[rdx+0x8]
    3c0b: and    rdi,0xfffffffffffffff8
    3c0f: mov    QWORD PTR [rdx],rcx
    3c12: mov    ecx,ebx
    3c14: mov    rsi,QWORD PTR [r13+rcx*1-0x8]
    3c19: mov    QWORD PTR [rdx+rcx*1-0x8],rsi
    3c1e: sub    rdx,rdi
    3c21: mov    rsi,r13
    3c24: lea    ecx,[rbx+rdx*1]
    3c27: sub    rsi,rdx
    3c2a: shr    ecx,0x3
    3c2d: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
    3c30: jmp    3b4e <mlkem_shake256x4+0x2de>
    3c35: nop    DWORD PTR [rax]
    3c38: mov    rcx,QWORD PTR [rbp-0x500]
    3c3f: lea    rdi,[rdx+0x8]
    3c43: and    rdi,0xfffffffffffffff8
    3c47: mov    QWORD PTR [rdx],rcx
    3c4a: mov    ecx,ebx
    3c4c: mov    rsi,QWORD PTR [r14+rcx*1-0x8]
    3c51: mov    QWORD PTR [rdx+rcx*1-0x8],rsi
    3c56: sub    rdx,rdi
    3c59: mov    rsi,r14
    3c5c: lea    ecx,[rbx+rdx*1]
    3c5f: sub    rsi,rdx
    3c62: shr    ecx,0x3
    3c65: rep    movs QWORD PTR es:[rdi],QWORD PTR ds:[rsi]
    3c68: jmp    3b19 <mlkem_shake256x4+0x2a9>
    3c6d: movzx  edx,WORD PTR [r12+rcx*1-0x2]
    3c73: mov    WORD PTR [rsi+rcx*1-0x2],dx
    3c78: pop    rax
    3c79: pop    rdx
    3c7a: jmp    39e1 <mlkem_shake256x4+0x171>
    3c7f: mov    edx,DWORD PTR [rbp-0x3e0]
    3c85: mov    DWORD PTR [rsi],edx
    3c87: mov    edx,DWORD PTR [r12+rcx*1-0x4]
    3c8c: mov    DWORD PTR [rsi+rcx*1-0x4],edx
    3c90: pop    rax
    3c91: pop    rdx
    3c92: jmp    39e1 <mlkem_shake256x4+0x171>
    3c97: mov    esi,DWORD PTR [rbp-0x470]
    3c9d: mov    DWORD PTR [rdx],esi
    3c9f: mov    esi,DWORD PTR [r13+rcx*1-0x4]
    3ca4: mov    DWORD PTR [rdx+rcx*1-0x4],esi
    3ca8: jmp    3b4e <mlkem_shake256x4+0x2de>
    3cad: mov    esi,DWORD PTR [rbp-0x500]
    3cb3: mov    DWORD PTR [rdx],esi
    3cb5: mov    esi,DWORD PTR [r14+rcx*1-0x4]
    3cba: mov    DWORD PTR [rdx+rcx*1-0x4],esi
    3cbe: jmp    3b19 <mlkem_shake256x4+0x2a9>
    3cc3: mov    esi,DWORD PTR [rbp-0x590]
    3cc9: mov    DWORD PTR [rdx],esi
    3ccb: mov    esi,DWORD PTR [r15+rcx*1-0x4]
    3cd0: mov    DWORD PTR [rdx+rcx*1-0x4],esi
    3cd4: jmp    3ae4 <mlkem_shake256x4+0x274>
    3cd9: movzx  esi,WORD PTR [r15+rcx*1-0x2]
    3cdf: mov    WORD PTR [rdx+rcx*1-0x2],si
    3ce4: jmp    3ae4 <mlkem_shake256x4+0x274>
    3ce9: movzx  esi,WORD PTR [r13+rcx*1-0x2]
    3cef: mov    WORD PTR [rdx+rcx*1-0x2],si
    3cf4: jmp    3b4e <mlkem_shake256x4+0x2de>
    3cf9: movzx  esi,WORD PTR [r14+rcx*1-0x2]
    3cff: mov    WORD PTR [rdx+rcx*1-0x2],si
    3d04: jmp    3b19 <mlkem_shake256x4+0x2a9>
 ***)

let MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x3870,0x3d09];;

(* ------------------------------------------------------------------------- *)
(* The number of whole blocks, outlen DIV 136, is computed by multiplying by *)
(* 0xf0f0f0f0f0f0f0f1 and shifting, as on AArch64, and 136 times it by       *)
(* shifts and an addition. Comparisons with an immediate set CF as a         *)
(* comparison of the values.                                                 *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_NBLOCKS = prove
 (`!x. x < 2 EXP 64
       ==> (x * 17361641481138401521) DIV 2 EXP 64 DIV 2 EXP 7 = x DIV 136`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`x:num`; `136`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`x MOD 136`,`r:num`) THEN SPEC_TAC(`x DIV 136`,`q:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `8 * q + r * 17361641481138401521` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

let SHAKE256X4_NBLOCKS_WORD = prove
 (`!n. n < 2 EXP 64
       ==> word_ushr
            (word_zx (word_ushr (word (n * 17361641481138401521):int128) 64)
             :int64) 7 =
           word(n DIV 136)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64;
              DIMINDEX_128] THEN
  SUBGOAL_THEN `n * 17361641481138401521 < 2 EXP 128` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 64 * 17361641481138401521` THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `(n * 17361641481138401521) DIV 2 EXP 64 < 2 EXP 64`
  ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    UNDISCH_TAC `n * 17361641481138401521 < 2 EXP 128` THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ASM_SIMP_TAC[SHAKE256X4_NBLOCKS] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LET_TRANS `n:num` THEN ASM_REWRITE_TAC[DIV_LE]);;

let SHAKE256X4_NBLOCKS_TAC =
  let th = REWRITE_RULE[ASSUME `outlen DIV 136 = nb`]
            (MP (SPEC `outlen:num` SHAKE256X4_NBLOCKS_WORD)
                (ASSUME `outlen < 2 EXP 64`)) in
  let th' = ONCE_REWRITE_RULE[MULT_SYM] th in
  RULE_ASSUM_TAC(REWRITE_RULE[th; th']);;

let SHAKE256X4_MUL136 = prove
 (`!n. word_shl (word_add (word_shl (word n) 4) (word n)) 3:int64 =
       word(136 * n)`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; DIMINDEX_64; GSYM WORD_ADD] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let CMP_CF_LT = prove
 (`!a b:N word.
        ~(&(val a) - &(val b):int = &(val(word_sub a b))) <=> val a < val b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[INT_OF_NUM_SUB; NOT_LT] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB] THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN
  MP_TAC(ISPEC `b:N word` VAL_BOUND) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LE; GSYM INT_OF_NUM_LT] THEN
  INT_ARITH_TAC);;

let CMP_CF_IMM = prove
 (`!a:N word n.
        n < 2 EXP dimindex(:N)
        ==> (~(&(val a) - &n:int = &(val(word_sub a (word n)))) <=>
             val a < n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:N word`; `word n:N word`] CMP_CF_LT) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ]);;

let CMP_CF_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read CF s <=> ~(&(val (a:N word)) - &n:int = b)`)
           (concl th)
    then SIMP_RULE[CMP_CF_IMM; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
                   DIMINDEX_64; ARITH] th
    else th);;

(* ------------------------------------------------------------------------- *)
(* The output of SHAKE256 in blocks, as on AArch64, in terms of the states   *)
(* S0, ..., S3 after the absorption, given as abbreviations with the facts   *)
(* for each block by SHAKE256X4_ABSORBED_TAC.                                *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SPONGE = prove
 (`!(m:byte list) k n.
        n <= 136
        ==> num_of_bytelist(list_of_seq (\j. shake256 m (136 * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor
                   (keccak_absorb 136
                     (num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad 136 0x1F (LENGTH m)))
                     (LENGTH m DIV 136))
                   (word((num_of_bytelist m +
                          2 EXP (8 * LENGTH m) *
                          num_of_bytelist(keccak_pad 136 0x1F (LENGTH m))) DIV
                         2 EXP (8 * 136 * LENGTH m DIV 136) MOD
                         2 EXP (8 * 136))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake256] THEN
  MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SHAKE256X4_ABSORBED =
 `\M. word_xor
       (keccak_absorb 136
         (M + 2 EXP (8 * inlen) * num_of_bytelist(keccak_pad 136 0x1F inlen))
         (inlen DIV 136))
       (word((M + 2 EXP (8 * inlen) *
                  num_of_bytelist(keccak_pad 136 0x1F inlen)) DIV
             2 EXP (8 * 136 * inlen DIV 136) MOD 2 EXP (8 * 136))):1600 word`;;

let SHAKE256X4_ABSORBED_TAC =
  MAP_EVERY (fun (inp,sv) ->
    let t = rhs(concl(BETA_CONV
             (mk_comb(SHAKE256X4_ABSORBED,
                      mk_comb(`num_of_bytelist:byte list->num`,inp))))) in
    let len = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,inp),
                           `inlen:num`)) in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp SHAKE256X4_SPONGE)))
   (zip [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`;
         `inp3:byte list`]
        [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`]);;

(* ------------------------------------------------------------------------- *)
(* The stack frame is realigned to 32 bytes: with r10 = stackpointer + 8 for *)
(* the stackpointer at the entry, rsp is ANDed with -32, the return address  *)
(* is pushed again and the frame is set up below it. For the 1944 bytes of   *)
(* stack below the return address, the frame is then the 1912 bytes from fpl *)
(* = (stackpointer + 1944 AND -32) - 1912 for the stackpointer below them,   *)
(* in which all the addresses are fpl + c, and fpl = stackpointer + (32 - k) *)
(* for k = val(stackpointer + 1944) MOD 32. The setup tactic makes the frame *)
(* of the specification that of (fpl,1912) and the abbreviations nb and rest *)
(* for outlen DIV 136 and outlen MOD 136.                                    *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_ALIGN32 = prove
 (`!a:int64 n.
        32 <= n
        ==> word_and (word_add a (word n)) (word 18446744073709551584) =
            word_add a (word(n - val(word_add a (word n)) MOD 32))`,
  let lemma = prove
   (`!x:int64. word_and x (word 18446744073709551584) =
               word_sub x (word(val x MOD 32))`,
    GEN_TAC THEN
    SUBGOAL_THEN `val(x:int64) MOD 32 = val(word_and x (word 31):int64)`
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 5 = 32`];
      REWRITE_TAC[WORD_VAL] THEN
      W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[lemma] THEN
  MP_TAC(SPECL [`val(word_add a (word n):int64)`; `32`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`val(word_add a (word n):int64) MOD 32`,`k:num`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`n:num`,`x:num`; `k:num`,`y:num`]
    (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k < 32` THEN UNDISCH_TAC `32 <= n` THEN
                  ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

(*** The aligned frame, as fpl + 1912 for the lowest address fpl used ***)

let SHAKE256X4_FPL_TAC =
  ABBREV_TAC
   `fpl = word_sub (word_and (word_add stackpointer (word 1944))
                             (word 18446744073709551584))
                   (word 1912):int64` THEN
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 1944))
             (word 18446744073709551584):int64 =
    word_add fpl (word 1912)`
  ASSUME_TAC THENL
   [EXPAND_TAC "fpl" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `fpl:int64 =
    word_add stackpointer
     (word(32 - val(word_add stackpointer (word 1944)) MOD 32))`
  ASSUME_TAC THENL
   [EXPAND_TAC "fpl" THEN
    SIMP_TAC[SHAKE256X4_ALIGN32; ARITH_RULE `32 <= 1944`] THEN
    MP_TAC(SPECL [`val(word_add stackpointer (word 1944):int64)`; `32`]
      MOD_LT_EQ) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SPEC_TAC(`val(word_add stackpointer (word 1944):int64) MOD 32`,
             `k:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `1944 - k = (32 - k) + 1912` SUBST1_TAC THENL
     [UNDISCH_TAC `k < 32` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    ALL_TAC];;

(*** The facts about the region (fpl,1912) used by the code, its bound ***)

let SHAKE256X4_FPL_NONOV_TAC =
  SUBGOAL_THEN `val(word_add stackpointer (word 1944):int64) MOD 32 < 32`
   ASSUME_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = `fpl:int64`
    then
      let fplth = th in
      MAP_EVERY (fun r ->
        SUBGOAL_THEN
         (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                          `fpl:int64,1912`),r)) ASSUME_TAC THENL
         [REWRITE_TAC[fplth] THEN NONOVERLAPPING_TAC; ALL_TAC])
       [`out0:int64,outlen:num`; `out1:int64,outlen:num`;
        `out2:int64,outlen:num`; `out3:int64,outlen:num`;
        `in0:int64,inlen:num`; `in1:int64,inlen:num`;
        `in2:int64,inlen:num`; `in3:int64,inlen:num`;
        `word pc:int64,0x82a0`; `word_add stackpointer (word 1944):int64,40`]
    else NO_TAC);;

let SHAKE256X4_FRAME_TAC =
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [RSP] ,,
    (MAYCHANGE [RIP] ,,
     MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
     MAYCHANGE
      [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10;
       ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20;
       ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30;
       ZMM31] ,,
     MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
     MAYCHANGE [events]) ,,
    MAYCHANGE
     [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
      memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
      memory :> bytes(fpl:int64,1912)]` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `fpl:int64`
      then REWRITE_TAC[th] else NO_TAC) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC];;

(*** The bound on outlen, nb whole blocks and rest remaining bytes ***)

let SHAKE256X4_BOUND_TAC =
  SUBGOAL_THEN `outlen < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1984 + n <= 2 EXP 64 ==> n < 2 EXP 64`) THEN
    MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(out0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word outlen:int64) = outlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN
   `136 * outlen DIV 136 + outlen MOD 136 = outlen /\ outlen MOD 136 < 136`
  MP_TAC THENL
   [MP_TAC(SPECL [`outlen:num`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `nb = outlen DIV 136` THEN ABBREV_TAC `rest = outlen MOD 136` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rest <= 136 /\ val(word rest:int64) = rest` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC VAL_WORD_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `rest < 136` THEN ARITH_TAC;
    ALL_TAC];;

let SHAKE256X4_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
    `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`; `inlen:num`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1944 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256X4_FPL_TAC THEN SHAKE256X4_FRAME_TAC THEN
  SHAKE256X4_FPL_NONOV_TAC THEN SHAKE256X4_BOUND_TAC THEN
  SHAKE256X4_ABSORBED_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(* ------------------------------------------------------------------------- *)
(* The assertions at the intermediate points of the correctness proof, with  *)
(* the frame, and the tactics for the absorption, the whole blocks and the   *)
(* last block into the buffers.                                              *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_FRAME =
 `read RBP s = word_add fpl (word 1896) /\
  read (memory :> bytes64 (word_add fpl (word 1904))) s = returnaddress /\
  read (memory :> bytes64 (word_add fpl (word 1896))) s = rbp_init /\
  read (memory :> bytes64 (word_add fpl (word 1888))) s = r15_init /\
  read (memory :> bytes64 (word_add fpl (word 1880))) s = r14_init /\
  read (memory :> bytes64 (word_add fpl (word 1872))) s = r13_init /\
  read (memory :> bytes64 (word_add fpl (word 1864))) s = r12_init /\
  read (memory :> bytes64 (word_add fpl (word 1856))) s =
  word_add stackpointer (word 1952) /\
  read (memory :> bytes64 (word_add fpl (word 1848))) s = rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1944))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add fpl (word 416))) s = out3 /\
  read (memory :> bytes64 (word_add fpl (word 424))) s = out2 /\
  read (memory :> bytes64 (word_add fpl (word 432))) s = out1 /\
  read (memory :> bytes64 (word_add fpl (word 440))) s = out0 /\
  read (memory :> bytes64 (word_add fpl (word 448))) s = word outlen /\
  read (memory :> bytes64 (word_add fpl (word 464))) s =
  word_add fpl (word 1048) /\
  (read DF s <=> false)`;;

let SHAKE256X4_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,SHAKE256X4_FRAME));;

let SHAKE256X4_A1 = SHAKE256X4_AT
 `\s. read RSP s = word_add fpl (word 408) /\
      read R11 s = word outlen /\
      read R15 s = out0 /\ read R14 s = out1 /\
      read R13 s = out2 /\ read R12 s = out3 /\
      read (memory :> bytes64 (word_add fpl (word 456))) s = word nb /\
      read (memory :> bytes(word_add fpl (word 1048),200)) s =
      val(S0:1600 word) /\
      read (memory :> bytes(word_add fpl (word 1248),200)) s =
      val(S1:1600 word) /\
      read (memory :> bytes(word_add fpl (word 1448),200)) s =
      val(S2:1600 word) /\
      read (memory :> bytes(word_add fpl (word 1648),200)) s =
      val(S3:1600 word)`;;

let SHAKE256X4_INV = SHAKE256X4_AT
 `\i s. read RSP s = word_add fpl (word 408) /\
        read RBX s = word(nb - i) /\
        read R15 s = word_add out0 (word(136 * i)) /\
        read R14 s = word_add out1 (word(136 * i)) /\
        read R13 s = word_add out2 (word(136 * i)) /\
        read R12 s = word_add out3 (word(136 * i)) /\
        read (memory :> bytes64 (word_add fpl (word 456))) s = word nb /\
        read (memory :> bytes(out0,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp0) (136 * i)) /\
        read (memory :> bytes(out1,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp1) (136 * i)) /\
        read (memory :> bytes(out2,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp2) (136 * i)) /\
        read (memory :> bytes(out3,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp3) (136 * i)) /\
        read (memory :> bytes(word_add fpl (word 1048),200)) s =
        val(keccak_squeeze i (S0:1600 word)) /\
        read (memory :> bytes(word_add fpl (word 1248),200)) s =
        val(keccak_squeeze i (S1:1600 word)) /\
        read (memory :> bytes(word_add fpl (word 1448),200)) s =
        val(keccak_squeeze i (S2:1600 word)) /\
        read (memory :> bytes(word_add fpl (word 1648),200)) s =
        val(keccak_squeeze i (S3:1600 word))`;;

let SHAKE256X4_A2 = SHAKE256X4_AT
 `\s. read RSP s = word_add fpl (word 408) /\
      read R11 s = word outlen /\
      read (memory :> bytes64 (word_add fpl (word 456))) s = word nb /\
      read (memory :> bytes(out0,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) (136 * nb)) /\
      read (memory :> bytes(out1,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) (136 * nb)) /\
      read (memory :> bytes(out2,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) (136 * nb)) /\
      read (memory :> bytes(out3,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) (136 * nb)) /\
      read (memory :> bytes(word_add fpl (word 1048),200)) s =
      val(keccak_squeeze nb (S0:1600 word)) /\
      read (memory :> bytes(word_add fpl (word 1248),200)) s =
      val(keccak_squeeze nb (S1:1600 word)) /\
      read (memory :> bytes(word_add fpl (word 1448),200)) s =
      val(keccak_squeeze nb (S2:1600 word)) /\
      read (memory :> bytes(word_add fpl (word 1648),200)) s =
      val(keccak_squeeze nb (S3:1600 word))`;;

let SHAKE256X4_A3 = SHAKE256X4_AT
 `\s. read RSP s = word_add fpl (word 408) /\
      read R15 s = word_add fpl (word 472) /\
      read R14 s = word_add fpl (word 616) /\
      read R13 s = word_add fpl (word 760) /\
      read R12 s = word_add fpl (word 904) /\
      read (memory :> bytes(out0,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) outlen) /\
      read (memory :> bytes(out1,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) outlen) /\
      read (memory :> bytes(out2,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) outlen) /\
      read (memory :> bytes(out3,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) outlen)`;;

(*** The absorption, up to the reload of outlen after the call ***)

let SHAKE256X4_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `word_and (word_add stackpointer (word 1944))
             (word 18446744073709551584):int64 =
    word_add fpl (word 1912)`]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (3--39) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  MEMSET_STEP_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC 40 THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (41--44) THEN
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
   [`read RDI s`; `136`; `read RDX s`; `read RCX s`; `read R8 s`;
    `read R9 s`; `inlen:num`; `num_of_bytelist inp0`;
    `num_of_bytelist inp1`; `num_of_bytelist inp2`; `num_of_bytelist inp3`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 45 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (46--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The flags of the comparison of outlen with 135, for the branch round
 *** the loop if there are no whole blocks
 ***)

let SHAKE256X4_NB0_TAC =
  CMP_CF_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word outlen:int64) = outlen`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[prove(`val(word 135:int64) = 135`,
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV)]) THEN
  SUBGOAL_THEN `outlen < 135 \/ outlen = 135 <=> nb = 0` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `outlen DIV 136 = nb`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC];;

let SHAKE256X4_PART2_TAC =
  ASM_CASES_TAC `nb = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--1) THEN
    SHAKE256X4_NB0_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL; LIST_OF_SEQ;
                num_of_bytelist; keccak_squeeze];
    ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `nb:num` `pc + 0x3940` `pc + 0x3994`
    SHAKE256X4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--1) THEN
    SHAKE256X4_NB0_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                LIST_OF_SEQ; num_of_bytelist; keccak_squeeze];
    ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let SHAKE256X4_STATES =
  [`word_add fpl (word 1048):int64`; `word_add fpl (word 1248):int64`;
   `word_add fpl (word 1448):int64`; `word_add fpl (word 1648):int64`];;

let SHAKE256X4_STATES_TAC = MAP_EVERY KECCAK_STATE_AT_TAC SHAKE256X4_STATES;;

let LOCAL_PERMUTE_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
  MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600);;

let LOCAL_EXTRACT_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
  MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let SHAKE256X4_COUNTER_TAC =
  SUBGOAL_THEN `word_sub (word (nb - i)) (word 1):int64 = word(nb - (i + 1))`
  SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < nb` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(nb - (i + 1)):int64) = nb - (i + 1)`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`outlen < 2 EXP 64`; `136 * nb + rest = outlen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(nb - (i + 1) = 0) <=> i + 1 < nb`
  SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC];;

let SHAKE256X4_LOOP_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `136 * i + 136 <= outlen` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i < nb`; `136 * nb + rest = outlen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
  SHAKE256X4_STATES_TAC THEN
  LOCAL_PERMUTE_X4_TAC
   [`read RDI s`; `keccak_squeeze i (S0:1600 word)`;
    `keccak_squeeze i (S1:1600 word)`; `keccak_squeeze i (S2:1600 word)`;
    `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 3 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (4--16) THEN
  STACK_ARG32_TAC `word_add fpl (word 392):int64` THEN
  SHAKE256X4_STATES_TAC THEN
  LOCAL_EXTRACT_X4_TAC
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `0`; `136`; `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
    `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
    `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
    `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
    `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 17 THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (18--20) THEN
  SHAKE256X4_COUNTER_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (21--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
      NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[LE_REFL] THEN
  REWRITE_TAC[GSYM ADD1; keccak_squeeze; MULT_CLAUSES; EXP; DIV_1];;

let SHAKE256X4_REST_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
  SUBGOAL_THEN `word_sub (word outlen) (word(136 * nb)):int64 = word rest`
   (fun th ->
      let t = `val(word rest:int64) = rest` in
      RULE_ASSUM_TAC(fun th' ->
        if concl th' = t then th' else REWRITE_RULE[th; ASSUME t] th')) THENL
   [FIRST_ASSUM(fun th ->
      if concl th = `136 * nb + rest = outlen` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

let SHAKE256X4_B = fun k ->
  let outs = [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`]
  and inps = [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`;
              `inp3:byte list`]
  and sts = [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`]
  and tmps = [472; 616; 760; 904] in
  let outfact j =
    let ov = el j outs and iv = el j inps in
    if j < k then
      subst [ov,`ov:int64`; iv,`iv:byte list`]
       `read (memory :> bytes(ov,outlen)) s =
        num_of_bytelist(list_of_seq (shake256 iv) outlen)`
    else
      subst [ov,`ov:int64`; iv,`iv:byte list`]
       `read (memory :> bytes(ov,136 * nb)) s =
        num_of_bytelist(list_of_seq (shake256 iv) (136 * nb))` in
  let tmpfact j =
    subst [mk_small_numeral(el j tmps),`t:num`; el j sts,`S:1600 word`]
     `read (memory :> bytes(word_add fpl (word t),136)) s =
      (val(keccak_f1600(keccak_squeeze nb (S:1600 word))) DIV 2 EXP (8 * 0))
      MOD 2 EXP (8 * 136)` in
  let regs =
   [`read RSP s = word_add fpl (word 392)`; `read RBX s = word rest`;
    `read R15 s = word_add fpl (word 472)`;
    `read R14 s = word_add fpl (word 616)`;
    `read R13 s = word_add fpl (word 760)`;
    `read R12 s = word_add fpl (word 904)`;
    `read (memory :> bytes64 (word_add fpl (word 456))) s =
     word (136 * nb)`] @
   (if k > 0 then [`read RAX s = word (136 * nb)`] else []) in
  let body = list_mk_conj
   (regs @ map outfact (0--3) @ map tmpfact (filter (fun j -> j >= k) (0--3)) @
    [SHAKE256X4_FRAME]) in
  mk_abs(`s:x86state`,body);;

(*** From the end of the whole blocks: no remaining bytes, or one more
 *** block of each state into the buffers on the stack
 ***)

let SHAKE256X4_REST0_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--4) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (5--10) THEN
  SHAKE256X4_REST_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if is_iff(concl th) && free_in `ZF` (concl th)
    then REWRITE_RULE[ASSUME `rest = 0`] th else th) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (11--15) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `outlen = 136 * nb` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`rest = 0`; `136 * nb + rest = outlen`] THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[]];;

let SHAKE256X4_TAILBLOCK_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--4) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (5--10) THEN
  SHAKE256X4_REST_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if is_iff(concl th) && free_in `ZF` (concl th)
    then REWRITE_RULE[ASSUME `~(rest = 0)`] th else th) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (11--23) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
  SHAKE256X4_STATES_TAC THEN
  LOCAL_PERMUTE_X4_TAC
   [`read RDI s`; `keccak_squeeze nb (S0:1600 word)`;
    `keccak_squeeze nb (S1:1600 word)`; `keccak_squeeze nb (S2:1600 word)`;
    `keccak_squeeze nb (S3:1600 word)`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 24 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (25--33) THEN
  STACK_ARG32_TAC `word_add fpl (word 392):int64` THEN
  SHAKE256X4_STATES_TAC THEN
  LOCAL_EXTRACT_X4_TAC
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `0`; `136`; `keccak_f1600(keccak_squeeze nb (S0:1600 word))`;
    `keccak_f1600(keccak_squeeze nb (S1:1600 word))`;
    `keccak_f1600(keccak_squeeze nb (S2:1600 word))`;
    `keccak_f1600(keccak_squeeze nb (S3:1600 word))`; `pc:num`;
    `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 34 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The inline copies of the rest bytes of each output from its buffer, with  *)
(* the same code for each with different registers: for 8 or more bytes the  *)
(* first and the last 8 bytes, then by REP MOVSQ the quadwords from the      *)
(* first aligned address after the start, none if there are fewer than 8     *)
(* bytes from it to the last 8; for 4 to 7 bytes the first and the last 4;   *)
(* and for 1 to 3 the first byte and (for 2 or 3) the last 2. The cases with *)
(* fewer than 8 bytes are proved separately for each number of bytes. The    *)
(* results of the loads and stores are kept as facts for bytes(a,n) = x MOD  *)
(* 2 EXP (8 * n) and parts of x, and the simulation does not keep the result *)
(* of a REP MOVSQ of a symbolic number of quadwords, so                      *)
(* MEMCPY_MOVSQ_STEP_TAC derives it.                                         *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_SEG_SUB = prove
 (`!a:int64 x k l k1 l1 s:x86state.
        read (memory :> bytes(word_add a (word k),l)) s =
        (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l) /\
        k <= k1 /\ k1 + l1 <= k + l
        ==> read (memory :> bytes(word_add a (word k1),l1)) s =
            (x DIV 2 EXP (8 * k1)) MOD 2 EXP (8 * l1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word_add a (word k):int64`; `l:num`;
                `(x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`; `k1 - k:num`;
                `l1:num`; `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= k1 ==> k + k1 - k = k1`] THEN
  DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIV_MOD_EXP_LOW o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= k1 ==> 8 * k + 8 * (k1 - k) = 8 * k1`]);;

let READ_MEMORY_BYTES64_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 18446744073709551616)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let WORD_INDEX_SUB8 = prove
 (`!n. 8 <= n /\ n < 2 EXP 64
       ==> word (1 * val (word n:int64) + 18446744073709551608):int64 =
           word (n - 8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SUBGOAL_THEN `1 * n + 18446744073709551608 = (n - 8) + 2 EXP 64`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE `x + 2 EXP 64 = x + 1 * 2 EXP 64`]);;

let READ_MEMORY_BYTES64_SEG = prove
 (`!a:int64 x m k s:x86state.
        read (memory :> bytes(a,m)) s = x MOD 2 EXP (8 * m) /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((x DIV 2 EXP (8 * k)) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `m:num`; `x MOD 2 EXP (8 * m)`; `k:num`;
                `s:x86state`] READ_MEMORY_BYTES64_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
  MATCH_MP_TAC DIV_MOD_EXP_LOW THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES64_TO_SEG = prove
 (`!a:int64 y s:x86state.
        read (memory :> bytes64 a) s = word(y MOD 2 EXP 64)
        ==> read (memory :> bytes(a,8)) s = y MOD 2 EXP (8 * 8)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let READ_MEMORY_BYTES_PREFIX = prove
 (`!a:int64 x n k s:x86state.
        read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n) /\ k <= n
        ==> read (memory :> bytes(a,k)) s = x MOD 2 EXP (8 * k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `k:num`; `read memory s`]
    READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `k <= n ==> MIN n k = k /\ MIN (8 * n) (8 * k) = 8 * k`]);;

let WORD_INDEX_SUB8_C = prove
 (`!c n. 8 <= n /\ n < 2 EXP 64
         ==> word (c + 1 * val (word n:int64) + 18446744073709551608):int64 =
             word (c + (n - 8))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  SUBGOAL_THEN `c + 1 * n + 18446744073709551608 = (c + (n - 8)) + 2 EXP 64`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE `x + 2 EXP 64 = x + 1 * 2 EXP 64`]);;

let READ_MEMORY_SEG0_JOIN = prove
 (`!a:int64 x k l s:x86state.
        read (memory :> bytes(a,k)) s = x MOD 2 EXP (8 * k) /\
        read (memory :> bytes(word_add a (word k),l)) s =
        (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)
        ==> read (memory :> bytes(a,k + l)) s = x MOD 2 EXP (8 * (k + l))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  MATCH_ACCEPT_TAC ADD_SYM);;

let NONOVERLAPPING_EMPTY_RIGHT = prove
 (`!(a:int64) (b:int64) m. nonoverlapping (a,m) (b,0)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo] THEN ARITH_TAC);;

let NONOVERLAPPING_EMPTY_LEFT = prove
 (`!(a:int64) (b:int64) m. nonoverlapping (b,0) (a,m)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo] THEN ARITH_TAC);;

let WORD_INDEX_SUB8_N = prove
 (`!c n. 8 <= n
         ==> word (c + 1 * n + 18446744073709551608):int64 =
             word (c + (n - 8)) /\
             word (1 * n + 18446744073709551608):int64 = word (n - 8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THENL
   [SUBGOAL_THEN `c + 1 * n + 18446744073709551608 = (c + (n - 8)) + 2 EXP 64`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `1 * n + 18446744073709551608 = (n - 8) + 2 EXP 64`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
  REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE `x + 2 EXP 64 = x + 1 * 2 EXP 64`]);;

let READ_MEMORY_BYTES_SUBSEG = prove
 (`!a:int64 x n k l s:x86state.
        read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n) /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `x MOD 2 EXP (8 * n)`; `k:num`; `l:num`;
                `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `k + l <= n` THEN ARITH_TAC);;

let READ_MEMORY_BYTES32_SEG = prove
 (`!a:int64 x m k s:x86state.
        read (memory :> bytes(a,m)) s = x MOD 2 EXP (8 * m) /\ k + 4 <= m
        ==> read (memory :> bytes32(word_add a (word k))) s =
            word((x DIV 2 EXP (8 * k)) MOD 2 EXP 32)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_32; MOD_MOD_REFL] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `x:num`; `m:num`; `k:num`; `4`; `s:x86state`]
         READ_MEMORY_BYTES_SUBSEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let READ_MEMORY_BYTES16_SEG = prove
 (`!a:int64 x m k s:x86state.
        read (memory :> bytes(a,m)) s = x MOD 2 EXP (8 * m) /\ k + 2 <= m
        ==> read (memory :> bytes16(word_add a (word k))) s =
            word((x DIV 2 EXP (8 * k)) MOD 2 EXP 16)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_16; MOD_MOD_REFL] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `x:num`; `m:num`; `k:num`; `2`; `s:x86state`]
         READ_MEMORY_BYTES_SUBSEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let READ_MEMORY_BYTES8_SEG = prove
 (`!a:int64 x m k s:x86state.
        read (memory :> bytes(a,m)) s = x MOD 2 EXP (8 * m) /\ k + 1 <= m
        ==> read (memory :> bytes8(word_add a (word k))) s =
            word((x DIV 2 EXP (8 * k)) MOD 2 EXP 8)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8; MOD_MOD_REFL] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `x:num`; `m:num`; `k:num`; `1`; `s:x86state`]
         READ_MEMORY_BYTES_SUBSEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MEMCPY_COUNT = prove
 (`!n e. e <= n /\ n < 2 EXP 32
   ==> (word_zx:int32->int64)
        (word_ushr ((word_zx:int64->int32) ((word_zx:int32->int64)
          ((word_sx:int64->int32)
           (word_add (word n)
             (word (1 * val (word_neg (word e:int64)))))))) 3) =
       word((n - e) DIV 8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES; WORD_VAL] THEN
  REWRITE_TAC[WORD_RULE `word_add x (word_neg y):N word = word_sub x y`] THEN
  REWRITE_TAC[WORD_SX_64_32] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(word_sub (word n) (word e):int64) = n - e` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `n MOD 2 EXP 64 = n /\ e MOD 2 EXP 64 = e`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `n < 2 EXP 32` THEN UNDISCH_TAC `e <= n` THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `n - e < 4294967296` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 4294967296 ==> n < 18446744073709551616`]);;

(*** From the fact for the 136 bytes of the buffer at a holding x, the fact
 *** for the load by lemma (bytes8/16/32/64 _SEG) at offset k
 ***)

let SHAKE256X4_TMPSEG_TAC lemma a k =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),s)),v)
        when aa = mk_pair(a,`136`) && is_binary "MOD" v ->
          let x = lhand v in
          MP_TAC(SPECL [a; x; `136`; k; s] lemma) THEN
          ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
           [TRY(UNDISCH_TAC `rest < 136`) THEN ARITH_TAC;
            DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV) o
              REWRITE_RULE[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1;
                           GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])]
    | _ -> NO_TAC);;

(*** A store fact for bytesN at a holding word(y MOD 2 EXP N) as a fact
 *** for bytes(a,N/8)
 ***)

let SHAKE256X4_TOSEG_TAC lemma a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(_,aa))),_)),_) when aa = a ->
        (try ASSUME_TAC(MATCH_MP lemma th) with Failure _ -> NO_TAC)
    | _ -> NO_TAC);;

(*** The equations for the indexed addresses with rest - 8, and if cs the
 *** fact for the load of the last 8 bytes from the buffer at fpl + t
 ***)

let SHAKE256X4_IDX8_TAC cs t =
  let tt = mk_small_numeral t in
  let bnd = MAP_EVERY UNDISCH_TAC [`8 <= rest`; `rest < 136`] THEN
            CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC in
  MP_TAC(SPECL [tt; `rest:num`] WORD_INDEX_SUB8_C) THEN
  ANTS_TAC THENL [bnd; DISCH_TAC] THEN
  MP_TAC(SPEC `rest:num` WORD_INDEX_SUB8) THEN
  ANTS_TAC THENL [bnd; DISCH_TAC] THEN
  MP_TAC(SPECL [tt; `rest:num`] WORD_INDEX_SUB8_N) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  let a = subst [tt,`t:num`] `word_add fpl (word t):int64` in
  if not cs then ALL_TAC else
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),s)),v)
        when aa = mk_pair(a,`136`) && is_binary "MOD" v ->
          let x = lhand v in
          MP_TAC(SPECL [a; x; `136`; `rest - 8`; s]
                       READ_MEMORY_BYTES64_SEG) THEN
          ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
           [UNDISCH_TAC `rest < 136` THEN ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN DISCH_TAC]
    | _ -> NO_TAC);;

(*** The region of the 8-byte store at dst + rest - 8, in all forms of its
 *** address, does not overlap the code, the frame or the region r
 ***)

let SHAKE256X4_W2_NONOV_TAC r =
  let regs = [`word pc:int64,0x82a0`; `fpl:int64,1912`; r] in
  MAP_EVERY (fun w ->
    MAP_EVERY (fun r ->
      SUBGOAL_THEN
       (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                        mk_pair(w,`8`)),r)) ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC; ALL_TAC]) regs)
   [`word_add dst (word (rest - 8)):int64`;
    `word_add dst (word (1 * val (word rest:int64) + 18446744073709551608))
     :int64`;
    `word_add dst (word (1 * rest + 18446744073709551608)):int64`];;

(*** The fact for the quadwords copied by a REP MOVSQ of a symbolic count,
 *** from the one that the simulation leaves, when the regions do not
 *** overlap
 ***)

let READ_MEMORY_MOVSQ_RESULT = prove
 (`!df a b n x s s' t.
        read (memory :> bytes(b,8 * n)) s' =
        read (memory :> bytes(b,8 * n))
         (write (memory :> bytes(b,8 * n))
           (x86_qstringcopy df a b n x (read (memory :> bytes(b,8 * n)) s))
           t)
        ==> nonoverlapping (a,8 * n) (b,8 * n) /\
            read (memory :> bytes(a,8 * n)) s = x /\
            8 * n <= 2 EXP 64
            ==> read (memory :> bytes(b,8 * n)) s' = x`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[X86_QSTRINGCOPY_NONOVERLAPPING] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[REWRITE_RULE[valid_component]
    (VALID_COMPONENT_CONV `valid_component memory`)] THEN
  ASM_SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[READ_BYTES_BOUND]);;

(*** Step the REP MOVSQ instruction n, keeping the fact for the memory it
 *** writes, given the facts that the source and destination do not
 *** overlap and for the source, and the arithmetic tactic btac for the
 *** bound on the size
 ***)

let MEMCPY_MOVSQ_STEP_TAC execth n btac =
  let sname = "s" ^ string_of_int n in
  let sv = mk_var(sname,`:x86state`) in
  let is_qsc t = match strip_comb t with
                   Const("x86_qstringcopy",_),_ -> true | _ -> false in
  X86_VSTEPS_TAC execth [n] THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (term_match [] `read (memory :> bytes(a,k)) s`) (lhand c) &&
       rand(lhand c) = sv && can (find_term is_qsc) (rand c)
    then MP_TAC(MATCH_MP READ_MEMORY_MOVSQ_RESULT th) else NO_TAC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; btac];
    DISCH_TAC] THEN
  DISCARD_OLDSTATE_TAC sname;;

(*** The join of the facts for bytes(a,k) and bytes(a + k,l) ***)

let MEMCPY_JOIN_TAC a k l =
  let pat1 = subst [a,`a:int64`; k,`k:num`]
               `read (memory :> bytes(a,k)) s = y`
  and pat2 = subst [a,`a:int64`; k,`k:num`; l,`l:num`]
               `read (memory :> bytes(word_add a (word k),l)) s = y` in
  let fvs = frees a @ frees k @ frees l in
  FIRST_ASSUM(fun th1 ->
    if can (term_match fvs pat1) (concl th1) then
      FIRST_ASSUM(fun th2 ->
        if can (term_match fvs pat2) (concl th2) then
          ASSUME_TAC(MATCH_MP READ_MEMORY_SEG0_JOIN (CONJ th1 th2))
        else NO_TAC)
    else NO_TAC);;

(*** The prefix of k bytes of the fact for bytes(a,n) ***)

let MEMCPY_PREFIX_TAC a n k =
  let pat = subst [a,`a:int64`; n,`n:num`] `read (memory :> bytes(a,n)) s = y`
  and fvs = frees a @ frees n in
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` k n) MP_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC ORELSE CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(fun le ->
    FIRST_ASSUM(fun th ->
      if can (term_match fvs pat) (concl th)
      then ASSUME_TAC(MATCH_MP READ_MEMORY_BYTES_PREFIX (CONJ th le))
      else NO_TAC));;

(*** Store facts for bytes32/16/8 with any word value, as facts for bytes,
 *** with the numerals 256^k that the simulation leaves in the values put
 *** back as 2 EXP (8 * k)
 ***)

let READ_MEMORY_BYTES32_WORD_SEG = prove
 (`!a:int64 y s:x86state.
        read (memory :> bytes32 a) s = word y
        ==> read (memory :> bytes(a,4)) s = y MOD 2 EXP (8 * 4)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let READ_MEMORY_BYTES16_WORD_SEG = prove
 (`!a:int64 y s:x86state.
        read (memory :> bytes16 a) s = word y
        ==> read (memory :> bytes(a,2)) s = y MOD 2 EXP (8 * 2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:int16->num`) THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let READ_MEMORY_BYTES8_WORD_SEG = prove
 (`!a:int64 y s:x86state.
        read (memory :> bytes8 a) s = word y
        ==> read (memory :> bytes(a,1)) s = y MOD 2 EXP (8 * 1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:byte->num`) THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MEMCPY_POW256_CONV tm =
  let pow8 k = mk_binop `EXP` `2`
                 (mk_binop `( * ):num->num->num` `8` (mk_small_numeral k)) in
  if is_numeral tm then
    let n = dest_numeral tm in
    let rec lg k m = if m =/ Num.num_of_int 1 then k
                     else if mod_num m (Num.num_of_int 256) =/ Num.num_of_int 0
                     then lg (k + 1) (quo_num m (Num.num_of_int 256))
                     else failwith "MEMCPY_POW256_CONV" in
    let k = lg 0 n in
    if k = 0 then failwith "MEMCPY_POW256_CONV"
    else SYM(NUM_REDUCE_CONV(pow8 k))
  else if is_binary "EXP" tm && lhand tm = `2` && is_numeral(rand tm) then
    let n = dest_small_numeral(rand tm) in
    if n > 0 && n mod 8 = 0
    then SYM(LAND_CONV(RAND_CONV NUM_MULT_CONV) (pow8 (n / 8)))
    else failwith "MEMCPY_POW256_CONV"
  else failwith "MEMCPY_POW256_CONV";;

(*** The value v of a store fact, made from the word w of the same size
 *** loaded from the buffer (which has X free) by zero extensions and the
 *** like, as w
 ***)

let MEMCPY_STORE_VALUE_RULE th =
  let v = rand(concl th) in
  let ty = type_of v in
  let is_w t = is_comb t && is_const(rator t) &&
               fst(dest_const(rator t)) = "word" && type_of t = ty &&
               free_in `X:num` t in
  let cands = find_terms is_w v in
  let w = find (fun t -> not(exists (fun u -> u <> t && free_in u t) cands))
               cands in
  if w = v then th else
  let gv = genvar ty in
  TRANS th (INST [w,gv] (WORD_BLAST(mk_eq(subst [gv,w] v,gv))));;

let MEMCPY_STORE_TAC a =
  let lemmas = [READ_MEMORY_BYTES32_WORD_SEG; READ_MEMORY_BYTES16_WORD_SEG;
                READ_MEMORY_BYTES8_WORD_SEG] in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const(("bytes32"|"bytes16"|"bytes8"),_),
                                    aa))),_)),_) when aa = a ->
        let th' = tryfind (fun l -> MATCH_MP l (MEMCPY_STORE_VALUE_RULE th))
                          lemmas in
        ASSUME_TAC(REWRITE_RULE[MOD_MOD_REFL]
          (CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV MEMCPY_POW256_CONV)) th'))
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The copy for each output j as a block lemma, from the load of the output  *)
(* pointer to the next copy, or for the last one to the zeroing at the end,  *)
(* for any bytes x in the buffer, and the same for the events, which depend  *)
(* only on the addresses and rest (and not even on rest when it is less than *)
(* 8, when the cases are separate). The tactic SHAKE256X4_COPY_TAC proves    *)
(* both, doing only the steps of the simulation for the events.              *)
(* ------------------------------------------------------------------------- *)

(*** The copy of the rest bytes of output j from its buffer on the stack,
 *** from the load of the output pointer to the next copy or (for j = 3)
 *** to the zeroing at the end, as a block lemma
 ***)

let SHAKE256X4_COPY_GOAL j =
  let start = el j [0x3aa8; 0x3ae4; 0x3b19; 0x3b4e]
  and finish = el j [0x3ae4; 0x3b19; 0x3b4e; 0x39e1]
  and ooff = el j [440; 432; 424; 416]
  and toff = el j [472; 616; 760; 904]
  and treg = el j [`R15`; `R14`; `R13`; `R12`] in
  let sub = subst [mk_small_numeral start,`start:num`;
                   mk_small_numeral finish,`finish:num`;
                   mk_small_numeral ooff,`oo:num`;
                   mk_small_numeral toff,`t:num`;
                   treg,`treg:(x86state,int64)component`] in
  let pre = map sub
   ([`bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc`;
     `read RIP s = word (pc + start)`;
     `read RBX s = word rest`;
     `read RBP s = word_add fpl (word 1896)`;
     `read (treg:(x86state,int64)component) s = word_add fpl (word t)`;
     `read (memory :> bytes64 (word_add fpl (word oo))) s = out`] @
    (if j = 0
     then [`read (memory :> bytes64 (word_add fpl (word 456))) s = word m`]
     else [`read RAX s = word m`]) @
    (if j = 3 then [`read RSP s = word_add fpl (word 392)`] else []) @
    [`read (memory :> bytes(word_add fpl (word t),136)) s =
      (X DIV 2 EXP (8 * 0)) MOD 2 EXP (8 * 136)`;
     `read DF s <=> false`])
  and post = map sub
   ([`read RIP s = word (pc + finish)`] @
    (if j = 3 then [`read RSP s = word_add fpl (word 408)`]
     else [`read RAX s = word m`]) @
    [`read (memory :> bytes(word_add out (word m),rest)) s =
      X MOD 2 EXP (8 * rest)`])
  and regs =
    if j = 3 then `MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI]`
    else `MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI]` in
  let mc = subst [regs,`rr:x86state->x86state->bool`]
   `(rr:x86state->x86state->bool) ,, MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
    MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add out (word m),rest)]` in
  let s = `s:x86state` in
  let ens = list_mk_icomb "ensures"
   [`x86`; mk_abs(s,list_mk_conj pre); mk_abs(s,list_mk_conj post); mc] in
  let hyps =
   `rest < 136 /\ ~(rest = 0) /\
    nonoverlapping (word_add out (word m):int64,rest) (word pc:int64,0x82a0) /\
    nonoverlapping (word_add out (word m):int64,rest) (fpl:int64,1912)` in
  list_mk_forall([`pc:num`; `fpl:int64`; `out:int64`; `m:num`; `rest:num`;
                  `X:num`],
                 mk_imp(hyps,ens));;

(*** The same for the events, which depend only on the addresses and rest
 *** (and not at all on rest when it is less than 8, when the cases of rest
 *** are separate)
 ***)

let SHAKE256X4_COPY_SAFE_GOAL j =
  let start = el j [0x3aa8; 0x3ae4; 0x3b19; 0x3b4e]
  and finish = el j [0x3ae4; 0x3b19; 0x3b4e; 0x39e1]
  and ooff = el j [440; 432; 424; 416]
  and toff = el j [472; 616; 760; 904]
  and treg = el j [`R15`; `R14`; `R13`; `R12`] in
  let sub = subst [mk_small_numeral start,`start:num`;
                   mk_small_numeral finish,`finish:num`;
                   mk_small_numeral ooff,`oo:num`;
                   mk_small_numeral toff,`t:num`;
                   treg,`treg:(x86state,int64)component`] in
  let pre = map sub
   ([`bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc`;
     `read RIP s = word (pc + start)`;
     `read RBX s = word rest`;
     `read RBP s = word_add fpl (word 1896)`;
     `read (treg:(x86state,int64)component) s = word_add fpl (word t)`;
     `read (memory :> bytes64 (word_add fpl (word oo))) s = out`] @
    (if j = 0
     then [`read (memory :> bytes64 (word_add fpl (word 456))) s = word m`]
     else [`read RAX s = word m`]) @
    (if j = 3 then [`read RSP s = word_add fpl (word 392)`] else []) @
    [`read DF s <=> false`; `read events s = e`])
  and post = map sub
   ([`read RIP s = word (pc + finish)`] @
    (if j = 3 then [`read RSP s = word_add fpl (word 408)`]
     else [`read RAX s = word m`]) @
    [`exists e2.
        read events s = APPEND e2 e /\
        e2 = (f_events:num->int64->int64->num->num->(uarch_event)list)
              pc fpl out m rest /\
        memaccess_inbounds e2
         [word_add out (word m),rest; fpl,1912]
         [word_add out (word m),rest]`])
  and regs =
    if j = 3 then `MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI]`
    else `MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI]` in
  let mc = subst [regs,`rr:x86state->x86state->bool`]
   `(rr:x86state->x86state->bool) ,, MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
    MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add out (word m),rest)]` in
  let s = `s:x86state` in
  let ens = list_mk_icomb "ensures"
   [`x86`; mk_abs(s,list_mk_conj pre); mk_abs(s,list_mk_conj post); mc] in
  let hyps =
   `rest < 136 /\ ~(rest = 0) /\
    nonoverlapping (word_add out (word m):int64,rest) (word pc:int64,0x82a0) /\
    nonoverlapping (word_add out (word m):int64,rest) (fpl:int64,1912)` in
  mk_exists(`f_events:num->int64->int64->num->num->(uarch_event)list`,
    list_mk_forall([`e:(uarch_event)list`; `pc:num`; `fpl:int64`;
                    `out:int64`; `m:num`; `rest:num`],
                   mk_imp(hyps,ens)));;

let SHAKE256X4_COPY_TEMPLATE =
 `\(pc:num) (fpl:int64) (out:int64) (m:num) (rest:num).
    if 8 <= rest then
      if rest < (8 - val(word_add out (word m)) MOD 8) + 8
      then f_ev_big0 pc fpl out m rest
      else f_ev_big1 pc fpl out m rest
    else if rest = 1 then f_ev_r1 pc fpl out m
    else if rest = 2 then f_ev_r2 pc fpl out m
    else if rest = 3 then f_ev_r3 pc fpl out m
    else if rest = 4 then f_ev_r4 pc fpl out m
    else if rest = 5 then f_ev_r5 pc fpl out m
    else if rest = 6 then f_ev_r6 pc fpl out m
    else f_ev_r7 pc fpl out m:(uarch_event)list`;;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, with val dst MOD 8 for the events of a
 *** copy as a variable d after the unification, so that the arithmetic of
 *** the bounds of the accesses can use the facts about it
 ***)

let SHAKE256X4_COPY_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
    else ALL_TAC) THEN
  ABBREV_TAC `d = val(word_add out (word m):int64) MOD 8` THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `val(word_add out (word m):int64) MOD 8 = d`]) THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** The end of a copy: for correctness, the postcondition from the facts
 *** (with the equation eq for the length when given), and otherwise the
 *** events, with dst and the abbreviations lo and c expanded
 ***)

let SHAKE256X4_COPY_FIN_TAC cs eqth =
  ENSURES_FINAL_STATE_TAC THEN
  if cs then
    ASM_REWRITE_TAC[] THEN
    (match eqth with
       Some(eq,tac) -> SUBGOAL_THEN eq SUBST1_TAC THENL
                        [tac; ASM_REWRITE_TAC[]]
     | None -> ALL_TAC)
  else
    MAP_EVERY (fun pat ->
      TRY(FIRST_X_ASSUM(fun th ->
        if is_eq(concl th) && can (term_match [] pat) (lhs(concl th)) &&
           is_var(rhs(concl th))
        then SUBST_ALL_TAC(SYM th) else NO_TAC)))
     [`(rest - lo) DIV 8`; `8 - val(dst:int64) MOD 8`;
      `word_add out (word m):int64`] THEN
    ASM_REWRITE_TAC[ARITH_EQ; ARITH_LE; ARITH_LT] THEN
    SHAKE256X4_COPY_DISCHARGE_TAC;;

(*** The copies of 1 to 7 bytes, for each concrete rest n: p is the number
 *** of steps up to the branch for 8 or more bytes, t the offset of the
 *** buffer from fpl, tail the number of steps after the last store
 *** besides the jump (2 for the pops of the last copy) and tail1 that
 *** after the branch for rest = 1 (3 for the last copy). Only steps are
 *** made unless cs.
 ***)

let SHAKE256X4_SMALL_TAC cs p tail tail1 t =
  W(fun (_,w) ->
    let n = dest_small_numeral(snd(dest_pair(find_term (fun tm ->
              is_pair tm && fst(dest_pair tm) = `dst:int64` &&
              is_numeral(snd(dest_pair tm))) w))) in
    let tmp = subst [mk_small_numeral t,`t:num`] `word_add fpl (word t):int64`
    and num = mk_small_numeral
    and ifcs tac = if cs then tac else ALL_TAC in
    let steps a b = X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (a--b)
    and tmpseg lemma k = ifcs(SHAKE256X4_TMPSEG_TAC lemma tmp (num k))
    and store k = ifcs(MEMCPY_STORE_TAC
       (if k = 0 then `dst:int64`
        else subst [num k,`k:num`] `word_add dst (word k):int64`)) in
    let join k l = ifcs
     (MEMCPY_JOIN_TAC `dst:int64` (num k) (num l) THEN
      RULE_ASSUM_TAC(fun th ->
        if can (term_match [`dst:int64`]
                 `read (memory :> bytes(dst,k + l)) s = y`) (concl th)
        then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV) th else th))
    and fin = SHAKE256X4_COPY_FIN_TAC cs None in
    if n >= 5 then
      tmpseg READ_MEMORY_BYTES32_SEG 0 THEN
      tmpseg READ_MEMORY_BYTES32_SEG (n - 4) THEN
      steps (p + 1) (p + 4) THEN store 0 THEN
      ifcs(MEMCPY_PREFIX_TAC `dst:int64` `4` (num(n - 4))) THEN
      steps (p + 5) (p + 7 + tail) THEN store (n - 4) THEN
      join (n - 4) 4 THEN fin
    else if n = 4 then
      tmpseg READ_MEMORY_BYTES32_SEG 0 THEN
      steps (p + 1) (p + 7 + tail) THEN store 0 THEN fin
    else if n = 1 then
      tmpseg READ_MEMORY_BYTES8_SEG 0 THEN
      steps (p + 1) (p + 8 + tail1) THEN store 0 THEN fin
    else if n = 2 then
      tmpseg READ_MEMORY_BYTES8_SEG 0 THEN
      tmpseg READ_MEMORY_BYTES16_SEG 0 THEN
      steps (p + 1) (p + 11 + tail) THEN store 0 THEN fin
    else
      tmpseg READ_MEMORY_BYTES8_SEG 0 THEN
      tmpseg READ_MEMORY_BYTES16_SEG 1 THEN
      steps (p + 1) (p + 6) THEN store 0 THEN
      steps (p + 7) (p + 11 + tail) THEN store 1 THEN
      join 1 2 THEN fin);;

(*** The copy of 8 or more bytes: the first and the last 8 bytes, then
 *** the quadwords from the first aligned address by REP MOVSQ, none if
 *** rest < lo + 8 for lo = 8 - val dst MOD 8. The steps are numbered from
 *** p, the branch, with w2 for the store of the last 8 bytes and last for
 *** the last step. Only steps are made unless cs.
 ***)

let SHAKE256X4_BIG_TAC cs p w2 last t =
  let tt = mk_small_numeral t in
  let tmp = subst [tt,`t:num`] `word_add fpl (word t):int64` in
  let steps a b = X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (a--b)
  and mv = p + 13
  and ifcs tac = if cs then tac else ALL_TAC in
  let count_tac =
    MP_TAC(SPECL [`rest:num`; `lo:num`] MEMCPY_COUNT) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`8 <= rest`; `lo <= 8`; `rest < 136`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] in
  let src_norm =
    SUBGOAL_THEN
     (subst [tt,`t:num`]
       `word_sub (word_add fpl (word t)) (word_neg (word lo)):int64 =
        word_add fpl (word (t + lo))`)
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] in
  let nonov regs =
    MAP_EVERY (fun (a,b) ->
      SUBGOAL_THEN
       (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,a),b))
       ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC]) regs in
  ifcs(SHAKE256X4_TMPSEG_TAC READ_MEMORY_BYTES64_SEG tmp `0`) THEN
  steps (p + 1) (p + 4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEMSET_ALIGN_ADDR]) THEN
  ifcs(SHAKE256X4_TOSEG_TAC READ_MEMORY_BYTES64_TO_SEG `dst:int64`) THEN
  ABBREV_TAC `lo = 8 - val(dst:int64) MOD 8` THEN
  SUBGOAL_THEN `1 <= lo /\ lo <= 8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lo" THEN MP_TAC(SPECL [`val(dst:int64)`; `8`] MOD_LT_EQ) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `rest < lo + 8` THENL
   [SUBGOAL_THEN `rest - 8 <= 8` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`rest < lo + 8`; `lo <= 8`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ifcs(MEMCPY_PREFIX_TAC `dst:int64` `8` `rest - 8`) THEN
    steps (p + 5) (w2 - 2) THEN
    ARGS_32_TAC [`rest:num`] THEN SHAKE256X4_IDX8_TAC cs t THEN
    SHAKE256X4_W2_NONOV_TAC `dst:int64,rest - 8` THEN
    steps (w2 - 1) (mv - 1) THEN count_tac THEN
    SUBGOAL_THEN `(rest - lo) DIV 8 = 0` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[DIV_EQ_0] THEN UNDISCH_TAC `rest < lo + 8` THEN ARITH_TAC;
      ALL_TAC] THEN
    src_norm THEN
    ASSUME_TAC(SPECL [`word_add dst (word (rest - 8)):int64`;
                      `word_add dst (word lo):int64`; `8`]
               NONOVERLAPPING_EMPTY_RIGHT) THEN
    ASSUME_TAC(SPECL [`word_add dst (word (rest - 8)):int64`;
                      `word_add dst (word lo):int64`; `8`]
               NONOVERLAPPING_EMPTY_LEFT) THEN
    steps mv last THEN
    ifcs(SHAKE256X4_TOSEG_TAC READ_MEMORY_BYTES64_TO_SEG
          `word_add dst (word (rest - 8)):int64` THEN
         MEMCPY_JOIN_TAC `dst:int64` `rest - 8` `8`) THEN
    SHAKE256X4_COPY_FIN_TAC cs
     (Some(`rest = rest - 8 + 8`,
           UNDISCH_TAC `8 <= rest` THEN ARITH_TAC));
    SUBGOAL_THEN `lo + 8 <= rest` ASSUME_TAC THENL
     [UNDISCH_TAC `~(rest < lo + 8)` THEN ARITH_TAC; ALL_TAC] THEN
    ifcs(MEMCPY_PREFIX_TAC `dst:int64` `8` `lo:num`) THEN
    steps (p + 5) (w2 - 2) THEN
    ARGS_32_TAC [`rest:num`] THEN SHAKE256X4_IDX8_TAC cs t THEN
    SHAKE256X4_W2_NONOV_TAC `dst:int64,lo:num` THEN
    steps (w2 - 1) (mv - 1) THEN count_tac THEN
    ABBREV_TAC `c = (rest - lo) DIV 8` THEN
    SUBGOAL_THEN `8 * c <= rest - lo /\ rest - lo < 8 * c + 8`
     STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MP_TAC(SPECL [`rest - lo`; `8`] DIVISION) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word c:int64) = c` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`8 * c <= rest - lo`; `rest < 136`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ifcs
     (SHAKE256X4_TOSEG_TAC READ_MEMORY_BYTES64_TO_SEG
       `word_add dst (word (rest - 8)):int64` THEN
      FIRST_ASSUM(fun th ->
        if can (term_match [`dst:int64`; `rest:num`]
                 `read (memory :> bytes(word_add dst (word (rest - 8)),8)) s =
                  y`) (concl th)
        then MP_TAC(SPECL [`dst:int64`; `X:num`; `rest - 8`; `8`;
                           `lo + 8 * c`; `rest - (lo + 8 * c)`;
                           rand(lhand(concl th))]
                    READ_MEMORY_SEG_SUB) THEN
             ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
              [MAP_EVERY UNDISCH_TAC
                [`8 * c <= rest - lo`; `rest - lo < 8 * c + 8`;
                 `lo + 8 <= rest`] THEN ARITH_TAC;
               DISCH_TAC]
        else NO_TAC) THEN
      FIRST_ASSUM(fun th ->
        if can (term_match [`fpl:int64`]
                 (subst [tt,`t:num`]
                   `read (memory :> bytes(word_add fpl (word t),136)) s = y`))
               (concl th)
        then MP_TAC(SPECL [tmp; `X:num`; `136`; `lo:num`; `8 * c`;
                           rand(lhand(concl th))]
                    READ_MEMORY_BYTES_SUBSEG) THEN
             ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
              [MAP_EVERY UNDISCH_TAC [`8 * c <= rest - lo`; `rest < 136`;
                                      `lo + 8 <= rest`] THEN ARITH_TAC;
               REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
               DISCH_TAC]
        else NO_TAC)) THEN
    src_norm THEN
    nonov
     ([`word_add dst (word lo):int64,8 * c`,`word pc:int64,0x82a0`] @
      (if cs then
        [`word_add dst (word lo):int64,8 * c`,`dst:int64,lo:num`;
         `word_add dst (word lo):int64,8 * c`,
         `word_add dst (word (lo + 8 * c)):int64,rest - (lo + 8 * c)`;
         subst [tt,`t:num`] `word_add fpl (word (t + lo)):int64,8 * c`,
         `word_add dst (word lo):int64,8 * c`]
       else [])) THEN
    (if cs then
       MEMCPY_MOVSQ_STEP_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC mv
        (MAP_EVERY UNDISCH_TAC [`8 * c <= rest - lo`; `rest < 136`] THEN
         ARITH_TAC)
     else steps mv mv) THEN
    steps (mv + 1) last THEN
    ifcs(MEMCPY_JOIN_TAC `dst:int64` `lo:num` `8 * c` THEN
         MEMCPY_JOIN_TAC `dst:int64` `lo + 8 * c` `rest - (lo + 8 * c)`) THEN
    SHAKE256X4_COPY_FIN_TAC cs
     (Some(`rest = (lo + 8 * c) + (rest - (lo + 8 * c))`,
           MAP_EVERY UNDISCH_TAC [`8 * c <= rest - lo`; `lo + 8 <= rest`] THEN
           ARITH_TAC))];;

(*** The copy of output j as a whole, for correctness if cs, otherwise for
 *** the events
 ***)

let SHAKE256X4_COPY_TAC cs j =
  let p = if j = 1 || j = 2 then 5 else 6
  and t = el j [472; 616; 760; 904] in
  let w2 = if j = 3 then p + 8 else p + 7
  and last = if j = 3 then p + 16 else p + 14
  and tail = if j = 3 then 2 else 0
  and tail1 = if j = 3 then 3 else 0 in
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `dst = word_add out (word m):int64` THEN
  (if cs then ALL_TAC else REWRITE_TAC(!simulation_precanon_thms)) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--(p-1)) THEN
  CMP_CF_TAC THEN ARGS_32_TAC [`rest:num`] THEN
  (if cs then
     FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `read (memory :> bytes(a,136)) s =
       (x DIV 2 EXP (8 * 0)) MOD 2 EXP (8 * 136)`) o concl)) THEN
     DISCH_THEN(ASSUME_TAC o REWRITE_RULE[MULT_CLAUSES; EXP; DIV_1])
   else ALL_TAC) THEN
  ASM_CASES_TAC `8 <= rest` THENL
   [X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC [p] THEN
    SHAKE256X4_BIG_TAC cs p w2 last t;
    SUBGOAL_THEN
     `rest = 1 \/ rest = 2 \/ rest = 3 \/ rest = 4 \/ rest = 5 \/
      rest = 6 \/ rest = 7`
     MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(8 <= rest)`; `~(rest = 0)`] THEN ARITH_TAC;
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC [p] THEN
    SHAKE256X4_SMALL_TAC cs p tail tail1 t];;

let SHAKE256X4_COPY_CORRECT =
  map (fun j -> prove(SHAKE256X4_COPY_GOAL j,SHAKE256X4_COPY_TAC true j))
      (0--3);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, with the copies by their lemmas and their results      *)
(* combined with the whole blocks before them. The specification is that of  *)
(* AArch64 apart from the stack: in1, in2, in3 and inlen are on the stack as *)
(* the seventh to tenth arguments, the stack is 1944 bytes below the return  *)
(* address and the arguments above it are read, and DF must be clear as the  *)
(* ABI requires (for REP STOSQ and REP MOVSQ).                               *)
(* ------------------------------------------------------------------------- *)

(*** The copies of the rest bytes, by the block lemmas, and the combination
 *** of the result with the whole blocks before it
 ***)

let SHAKE256X4_COPYB_TAC copyth j =
  let outs = [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`]
  and sts = [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`] in
  let x = mk_comb(`val:1600 word->num`,
                  mk_comb(`keccak_f1600`,
                          mk_comb(mk_comb(`keccak_squeeze`,`nb:num`),
                                  el j sts))) in
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`pc:num`; `fpl:int64`; el j outs; `136 * nb`; `rest:num`; x]
               copyth) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  X86_BIGSTEP_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC "s1" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `outlen = 136 * nb + rest` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      if concl th = `136 * nb + rest = outlen` then ACCEPT_TAC(SYM th)
      else NO_TAC);
    ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; keccak_squeeze];;

(*** Zeroing the context and the buffers, and the return ***)

let SHAKE256X4_END_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = time prove
 (`!out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen
   (inp0:byte list) (inp1:byte list) (inp2:byte list) (inp3:byte list)
   pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        LENGTH inp0 = inlen /\ LENGTH inp1 = inlen /\
        LENGTH inp2 = inlen /\ LENGTH inp3 = inlen /\
        PAIRWISE nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1944),1984)] /\
        ALLPAIRS nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1944),1984)]
         [(in0,inlen); (in1,inlen); (in2,inlen); (in3,inlen);
          (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3870) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word outlen; in0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  in1 /\
                  read (memory :> bytes64(word_add stackpointer (word 16))) s =
                  in2 /\
                  read (memory :> bytes64(word_add stackpointer (word 24))) s =
                  in3 /\
                  read (memory :> bytes64(word_add stackpointer (word 32))) s =
                  word inlen /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(in0,inlen)) s = num_of_bytelist inp0 /\
                  read (memory :> bytes(in1,inlen)) s = num_of_bytelist inp1 /\
                  read (memory :> bytes(in2,inlen)) s = num_of_bytelist inp2 /\
                  read (memory :> bytes(in3,inlen)) s = num_of_bytelist inp3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out0,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp0) outlen) /\
                  read (memory :> bytes(out1,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp1) outlen) /\
                  read (memory :> bytes(out2,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp2) outlen) /\
                  read (memory :> bytes(out3,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp3) outlen))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
                memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
                memory :> bytes(word_sub stackpointer (word 1944),1944)])`,
  SHAKE256X4_SETUP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x392d` SHAKE256X4_A1 THEN CONJ_TAC THENL
   [SHAKE256X4_PART1_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x399b` SHAKE256X4_A2 THEN CONJ_TAC THENL
   [SHAKE256X4_PART2_TAC THEN SHAKE256X4_LOOP_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x39e1` SHAKE256X4_A3 THEN CONJ_TAC THENL
   [ASM_CASES_TAC `rest = 0` THENL [SHAKE256X4_REST0_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x3aa8` (SHAKE256X4_B 0) THEN CONJ_TAC THENL
     [SHAKE256X4_TAILBLOCK_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x3ae4` (SHAKE256X4_B 1) THEN CONJ_TAC THENL
     [SHAKE256X4_COPYB_TAC (el 0 SHAKE256X4_COPY_CORRECT) 0; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x3b19` (SHAKE256X4_B 2) THEN CONJ_TAC THENL
     [SHAKE256X4_COPYB_TAC (el 1 SHAKE256X4_COPY_CORRECT) 1; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x3b4e` (SHAKE256X4_B 3) THEN CONJ_TAC THENL
     [SHAKE256X4_COPYB_TAC (el 2 SHAKE256X4_COPY_CORRECT) 2;
      SHAKE256X4_COPYB_TAC (el 3 SHAKE256X4_COPY_CORRECT) 3];
    SHAKE256X4_END_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend on the addresses *)
(* and on outlen and inlen, and as on AArch64 they are given in parts, split *)
(* at the intermediate points of the correctness proof from the end, with    *)
(* the public parts of the same assertions, and those of the copies by their *)
(* lemmas, as the functions x86_shake256x4_gcc12_O2_copy_events_j of the     *)
(* address fpl = stackpointer + (32 - k) of the frame as above.              *)
(* ------------------------------------------------------------------------- *)

(*** The events of the copies, as functions of the addresses and rest ***)

let SHAKE256X4_COPY_SAFE_TAC j =
  CONCRETIZE_F_EVENTS_TAC SHAKE256X4_COPY_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `fpl:int64`; `out:int64`; `m:num`; `rest:num`] THEN
  SHAKE256X4_COPY_TAC false j;;

let SHAKE256X4_COPY_EVENTS =
  map (fun j ->
        new_specification
         ["x86_shake256x4_gcc12_O2_copy_events_" ^ string_of_int j]
         (prove(SHAKE256X4_COPY_SAFE_GOAL j,SHAKE256X4_COPY_SAFE_TAC j)))
      (0--3);;

(*** The events of the whole function, in parts as for the AArch64 code,
 *** with those of the copies as above for the address fpl of the frame
 ***)

let SHAKE256X4_F_EVENTS =
  let cp j oj =
    subst [mk_const("x86_shake256x4_gcc12_O2_copy_events_" ^
                    string_of_int j,[]),
           `cev:num->int64->int64->num->num->(uarch_event)list`;
           oj,`oj:int64`]
     `(cev:num->int64->int64->num->num->(uarch_event)list) pc
       (word_add stackpointer
         (word(32 - val(word_add stackpointer (word 1944)) MOD 32)))
       oj (136 * outlen DIV 136) (outlen MOD 136)` in
  let vs,body = strip_abs
   `\(in0:int64) (in1:int64) (in2:int64) (in3:int64)
     (out0:int64) (out1:int64) (out2:int64) (out3:int64) (outlen:num)
     (inlen:num) (pc:num) (stackpointer:int64) (returnaddress:int64).
    APPEND
     (f_ev_end in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen pc
               stackpointer returnaddress)
     (APPEND
       (if outlen MOD 136 = 0
        then f_ev_rest0 in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen pc
                        stackpointer returnaddress
        else APPEND (c3:(uarch_event)list)
              (APPEND (c2:(uarch_event)list)
                (APPEND (c1:(uarch_event)list)
                  (APPEND (c0:(uarch_event)list)
                    (f_ev_tail in0 in1 in2 in3 out0 out1 out2 out3 outlen
                               inlen pc stackpointer returnaddress)))))
       (APPEND
         (if outlen DIV 136 = 0
          then f_ev_skip in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                         pc stackpointer returnaddress
          else APPEND
                (f_ev_epil in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                           pc stackpointer returnaddress)
                (APPEND
                  (ENUMERATEL (outlen DIV 136)
                    (\i. f_ev_loop in0 in1 in2 in3 out0 out1 out2 out3 outlen
                                   inlen pc stackpointer returnaddress i))
                  (f_ev_prol in0 in1 in2 in3 out0 out1 out2 out3 outlen
                             inlen pc stackpointer returnaddress)))
         (f_ev_absorb in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen pc
                      stackpointer returnaddress)))
    :(uarch_event)list` in
  list_mk_abs
   (vs,
    subst [cp 0 `out0:int64`,`c0:(uarch_event)list`;
           cp 1 `out1:int64`,`c1:(uarch_event)list`;
           cp 2 `out2:int64`,`c2:(uarch_event)list`;
           cp 3 `out3:int64`,`c3:(uarch_event)list`] body);;

let SHAKE256X4_PUBLIC t =
  let vs,bod = strip_abs t
  and priv = [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
              `S3:1600 word`; `inp0:byte list`; `inp1:byte list`;
              `inp2:byte list`; `inp3:byte list`] in
  list_mk_abs(vs,list_mk_conj
   (filter (fun c -> not(exists (fun v -> vfree_in v c) priv))
           (conjuncts bod)));;

let SHAKE256X4_ALLOWED =
  [`pc:num`; `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`;
   `out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
   `inlen:num`; `stackpointer:int64`; `returnaddress:int64`; `i:num`;
   `e2:(uarch_event)list`];;

(*** nb, rest and fpl expanded in the events ***)

let SHAKE256X4_UNABBREV_TAC =
  MAP_EVERY (fun t ->
    TRY(FIRST_X_ASSUM(fun th ->
      if concl th = t then SUBST_ALL_TAC(SYM th) else NO_TAC)))
   [`outlen DIV 136 = nb`; `outlen MOD 136 = rest`] THEN
  TRY(FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `fpl:int64` &&
       is_binary "word_add" (lhs(concl th))
    then SUBST_ALL_TAC(SYM th) else NO_TAC));;

let SHAKE256X4_DISCHARGE_TAC =
  SHAKE256X4_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let SHAKE256X4_EXISTS_E2_TAC =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `outlen DIV 136 = nb` || c = `outlen MOD 136 = rest`
      then SYM th
      else if is_eq c && rhs c = `fpl:int64` && is_binary "word_add" (lhs c)
      then SYM th else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths) THEN
  ((MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL
     [REFL_TAC; SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx]) ORELSE
   (CONV_TAC(TRY_CONV(LAND_CONV CONS_TO_APPEND_CONV)) THEN
    TRY(GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx) ORELSE
   (CONV_TAC(TRY_CONV(LAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
    CONV_TAC(TRY_CONV(LAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
    GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx));;

let SHAKE256X4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [SHAKE256X4_EXISTS_E2_TAC; LABEL_TAC name safety_th]);;

(*** The start of a part, where the events e2 so far may be given ***)

let SHAKE256X4_SAFE_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC;;

let SHAKE256X4_SAFE_INIT_OPAQUE_TAC =
  SHAKE256X4_SAFE_INIT_TAC THEN
  TRY(FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l && name_of l = "e2" && not(is_var r)
    then ASSUME_TAC(SYM th) THEN PURE_REWRITE_TAC[SYM th]
    else NO_TAC));;

(*** The absorption ***)

let SHAKE256X4_SAFE_ABSORB_TAC =
  SHAKE256X4_SAFE_INIT_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `word_and (word_add stackpointer (word 1944))
             (word 18446744073709551584):int64 =
    word_add fpl (word 1912)`]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (3--39) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (40--44) THEN
  SHAKE256X4_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read RDI s`; `136`; `read RDX s`; `read RCX s`;
    `read R8 s`; `read R9 s`; `inlen:num`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 45 THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (46--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

(*** The whole blocks ***)

let SHAKE256X4_SAFE_BLOCKS_TAC =
  ASM_CASES_TAC `nb = 0` THEN ASM_REWRITE_TAC[] THENL
   [SHAKE256X4_SAFE_INIT_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--1) THEN
    SHAKE256X4_NB0_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nb:num` `pc + 0x3940` `pc + 0x3994`
    (SHAKE256X4_PUBLIC SHAKE256X4_INV) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    SHAKE256X4_SAFE_INIT_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--1) THEN
    SHAKE256X4_NB0_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    SHAKE256X4_DISCHARGE_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SHAKE256X4_SAFE_INIT_TAC THEN
    SUBGOAL_THEN `136 * i + 136 <= outlen` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < nb`; `136 * nb + rest = outlen`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
    SHAKE256X4_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`] 3 THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (4--16) THEN
    STACK_ARG32_TAC `word_add fpl (word 392):int64` THEN
    SHAKE256X4_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
      `read RCX s`; `read R8 s`; `0`; `136`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`] 17 THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (18--20) THEN
    SHAKE256X4_COUNTER_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (21--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
        NO_TAC) THEN
    SHAKE256X4_DISCHARGE_TAC;

    REWRITE_TAC[] THEN SHAKE256X4_SAFE_INIT_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC];;

(*** A copy, by the lemma for its events, at step n ***)

let SHAKE256X4_SAFE_COPY_STEP_TAC j n =
  let outs = [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`] in
  W(fun (asl,w) ->
    let ev = rhs(concl(snd(find (fun (_,th) ->
               let c = concl th in
               is_eq c && can (term_match [] `read events s`) (lhs c))
               asl))) in
    MP_TAC(SPECL [ev; `pc:num`; `fpl:int64`; el j outs; `136 * nb`;
                  `rest:num`] (el j SHAKE256X4_COPY_EVENTS)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    X86_BIGSTEP_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC
      ("s" ^ string_of_int n));;

(*** The discharge after the copies, matching the events of the copies
 *** in turn and those of the last block as f_ev_tail, and the bounds of
 *** the accesses part by part
 ***)

let rec SHAKE256X4_MEMACCESS_TAC g =
  W(fun (asl,w) ->
    if is_binary "APPEND" (rand(rator(rator w))) then
      GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
       [DISCHARGE_MEMACCESS_INBOUNDS_TAC; SHAKE256X4_MEMACCESS_TAC]
    else DISCHARGE_MEMACCESS_INBOUNDS_TAC) g;;

let SHAKE256X4_REST_DISCHARGE_TAC =
  SHAKE256X4_UNABBREV_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [GSYM APPEND_ASSOC] THEN
    MAP_EVERY (fun _ -> AP_TERM_TAC) (1--4) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [APPEND_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC allowed_vars_e (ref ["f_events_callee"; "f_ev_"]);
    SHAKE256X4_MEMACCESS_TAC];;

(*** The remaining bytes: none, or one more block and the copies ***)

let SHAKE256X4_SAFE_REST_TAC =
  ASM_CASES_TAC `rest = 0` THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--4) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (5--10) THEN
  SHAKE256X4_REST_TAC THENL
   [RULE_ASSUM_TAC(fun th ->
      if is_iff(concl th) && free_in `ZF` (concl th)
      then REWRITE_RULE[ASSUME `rest = 0`] th else th) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (11--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    RULE_ASSUM_TAC(fun th ->
      if is_iff(concl th) && free_in `ZF` (concl th)
      then REWRITE_RULE[ASSUME `~(rest = 0)`] th else th) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (11--23) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
    SHAKE256X4_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`] 24 THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (25--33) THEN
    STACK_ARG32_TAC `word_add fpl (word 392):int64` THEN
    SHAKE256X4_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
      `read RCX s`; `read R8 s`; `0`; `136`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`] 34 THEN
    MAP_EVERY (fun j -> SHAKE256X4_SAFE_COPY_STEP_TAC j (35 + j)) (0--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_REST_DISCHARGE_TAC];;

(*** Zeroing the context and the buffers, and the return ***)

let SHAKE256X4_SAFE_END_TAC =
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

let SHAKE256X4_SAFE_SETUP_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC SHAKE256X4_F_EVENTS THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
    `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`; `inlen:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1944 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256X4_FPL_TAC THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = `fpl:int64` &&
       is_binary "word_add" (rhs(concl th))
    then ASSUME_TAC(SYM th) else NO_TAC) THEN
  SHAKE256X4_FRAME_TAC THEN SHAKE256X4_FPL_NONOV_TAC THEN
  SHAKE256X4_BOUND_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
   forall e out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen
          pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1944),1984)] /\
        ALLPAIRS nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1944),1984)]
         [(in0,inlen); (in1,inlen); (in2,inlen); (in3,inlen);
          (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3870) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word outlen; in0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  in1 /\
                  read (memory :> bytes64(word_add stackpointer (word 16))) s =
                  in2 /\
                  read (memory :> bytes64(word_add stackpointer (word 24))) s =
                  in3 /\
                  read (memory :> bytes64(word_add stackpointer (word 32))) s =
                  word inlen /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events in0 in1 in2 in3 out0 out1 out2 out3
                            outlen inlen pc (word_sub stackpointer (word 1944))
                            returnaddress /\
                     memaccess_inbounds e2
                      [in0,inlen; in1,inlen; in2,inlen; in3,inlen;
                       out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                       word_sub stackpointer (word 1944),1984;
                       word(pc + 0x80c0),192]
                      [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                       word_sub stackpointer (word 1944),1944]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
                memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
                memory :> bytes(word_sub stackpointer (word 1944),1944)])`,
  SHAKE256X4_SAFE_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x39e1`
   (SHAKE256X4_PUBLIC SHAKE256X4_A3) THEN
  CONJ_TAC THENL [ALL_TAC; SHAKE256X4_SAFE_END_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x399b`
   (SHAKE256X4_PUBLIC SHAKE256X4_A2) THEN
  CONJ_TAC THENL [ALL_TAC; SHAKE256X4_SAFE_REST_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x392d`
   (SHAKE256X4_PUBLIC SHAKE256X4_A1) THEN
  CONJ_TAC THENL [SHAKE256X4_SAFE_ABSORB_TAC; SHAKE256X4_SAFE_BLOCKS_TAC]);;
