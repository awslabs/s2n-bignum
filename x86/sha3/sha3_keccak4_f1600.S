// Copyright (c) 2017-2024 The OpenSSL Project Authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Written by Andy Polyakov, @dot-asm, initially for use in the OpenSSL
// project.

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3
// Input a[25], rc[24]; output a[25]
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE 
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
//    extern void sha3_keccak4_f1600(uint64_t a[25], const uint64_t rc[24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak4_f1600)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak4_f1600)
        .text    
        .align 32

S2N_BN_SYMBOL(sha3_keccak4_f1600):
        _CET_ENDBR

#if WINDOWS_ABI
    push    rdi
    push    rsi
    mov     rdi, rcx
    mov     rsi, rdx
#endif

    push   rbp
    mov    rbp,rsp
    and    rsp,0xffffffffffffffe0
    sub    rsp,0x360
    vmovdqu ymm0,YMMWORD PTR [rdi]
    vmovdqu ymm1,YMMWORD PTR [rdi+0xc8]
    vmovdqu ymm2,YMMWORD PTR [rdi+0x190]
    vmovdqu ymm3,YMMWORD PTR [rdi+0x258]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpckhqdq ymm5,ymm0,ymm1
    vpunpcklqdq ymm6,ymm2,ymm3
    vpunpcklqdq ymm7,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm6,0x20
    vperm2i128 ymm2,ymm4,ymm6,0x31
    vperm2i128 ymm1,ymm5,ymm7,0x20
    vperm2i128 ymm3,ymm5,ymm7,0x31
    vmovdqa ymm5,ymm0
    vmovdqa YMMWORD PTR [rsp],ymm1
    vmovdqa YMMWORD PTR [rsp+0x20],ymm2
    vmovdqa YMMWORD PTR [rsp+0x40],ymm3
    vmovdqu ymm0,YMMWORD PTR [rdi+0x20]
    vmovdqu ymm1,YMMWORD PTR [rdi+0xe8]
    vmovdqu ymm2,YMMWORD PTR [rdi+0x1b0]
    vmovdqu ymm3,YMMWORD PTR [rdi+0x278]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqa YMMWORD PTR [rsp+0x60],ymm0
    vmovdqa YMMWORD PTR [rsp+0x80],ymm1
    vmovdqa YMMWORD PTR [rsp+0xa0],ymm2
    vmovdqa YMMWORD PTR [rsp+0xc0],ymm3
    vmovdqu ymm0,YMMWORD PTR [rdi+0x40]
    vmovdqu ymm1,YMMWORD PTR [rdi+0x108]
    vmovdqu ymm2,YMMWORD PTR [rdi+0x1d0]
    vmovdqu ymm3,YMMWORD PTR [rdi+0x298]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqa YMMWORD PTR [rsp+0xe0],ymm0
    vmovdqa YMMWORD PTR [rsp+0x100],ymm1
    vmovdqa YMMWORD PTR [rsp+0x120],ymm2
    vmovdqa YMMWORD PTR [rsp+0x140],ymm3
    vmovdqu ymm0,YMMWORD PTR [rdi+0x60]
    vmovdqu ymm1,YMMWORD PTR [rdi+0x128]
    vmovdqu ymm2,YMMWORD PTR [rdi+0x1f0]
    vmovdqu ymm3,YMMWORD PTR [rdi+0x2b8]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqa YMMWORD PTR [rsp+0x160],ymm0
    vmovdqa YMMWORD PTR [rsp+0x180],ymm1
    vmovdqa YMMWORD PTR [rsp+0x1a0],ymm2
    vmovdqa YMMWORD PTR [rsp+0x1c0],ymm3
    vmovdqu ymm0,YMMWORD PTR [rdi+0x80]
    vmovdqu ymm1,YMMWORD PTR [rdi+0x148]
    vmovdqu ymm2,YMMWORD PTR [rdi+0x210]
    vmovdqu ymm3,YMMWORD PTR [rdi+0x2d8]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqa YMMWORD PTR [rsp+0x1e0],ymm0
    vmovdqa YMMWORD PTR [rsp+0x200],ymm1
    vmovdqa YMMWORD PTR [rsp+0x220],ymm2
    vmovdqa YMMWORD PTR [rsp+0x240],ymm3
    vmovdqu ymm0,YMMWORD PTR [rdi+0xa0]
    vmovdqu ymm1,YMMWORD PTR [rdi+0x168]
    vmovdqu ymm2,YMMWORD PTR [rdi+0x230]
    vmovdqu ymm3,YMMWORD PTR [rdi+0x2f8]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqa YMMWORD PTR [rsp+0x260],ymm0
    vmovdqa YMMWORD PTR [rsp+0x280],ymm1
    vmovdqa YMMWORD PTR [rsp+0x2a0],ymm2
    vmovdqa YMMWORD PTR [rsp+0x2c0],ymm3
    // vmovq  xmm1,QWORD PTR [rdi+0xc0]
    vpinsrq xmm1,xmm1,QWORD PTR [rdi+0x188],0x1
    // vmovq  xmm2,QWORD PTR [rdi+0x250]
    // vpinsrq xmm2,xmm2,QWORD PTR [rdi+0x318],0x1
    // vinserti128 ymm3,ymm1,xmm2,0x1
    vmovdqa YMMWORD PTR [rsp+0x2e0],ymm3
    mov    rax,0x0

    .keccak_loop:
    vmovdqa ymm12,YMMWORD PTR [rsp+0x80]
    vmovdqa ymm13,YMMWORD PTR [rsp+0x120]
    vmovdqa ymm11,YMMWORD PTR [rsp+0x1c0]
    vmovdqa ymm10,YMMWORD PTR [rsp+0x260]
    vpxor  ymm1,ymm5,ymm12
    vpxor  ymm0,ymm11,ymm13
    vpxor  ymm1,ymm1,ymm0
    vpxor  ymm1,ymm1,ymm10
    vmovdqa ymm4,YMMWORD PTR [rsp]
    vmovdqa ymm6,YMMWORD PTR [rsp+0x1e0]
    vpxor  ymm8,ymm4,YMMWORD PTR [rsp+0xa0]
    vpxor  ymm0,ymm6,YMMWORD PTR [rsp+0x140]
    vpxor  ymm8,ymm8,ymm0
    vpxor  ymm8,ymm8,YMMWORD PTR [rsp+0x280]
    vmovdqa ymm0,YMMWORD PTR [rsp+0x20]
    vpxor  ymm7,ymm0,YMMWORD PTR [rsp+0xc0]
    vmovdqa ymm14,YMMWORD PTR [rsp+0x200]
    vpxor  ymm0,ymm14,YMMWORD PTR [rsp+0x160]
    vpxor  ymm7,ymm7,ymm0
    vpxor  ymm7,ymm7,YMMWORD PTR [rsp+0x2a0]
    vmovdqa ymm3,YMMWORD PTR [rsp+0x40]
    vpxor  ymm6,ymm3,YMMWORD PTR [rsp+0xe0]
    vmovdqa ymm0,YMMWORD PTR [rsp+0x220]
    vpxor  ymm0,ymm0,YMMWORD PTR [rsp+0x180]
    vpxor  ymm6,ymm6,ymm0
    vpxor  ymm6,ymm6,YMMWORD PTR [rsp+0x2c0]
    vmovdqa ymm4,YMMWORD PTR [rsp+0x60]
    vpxor  ymm2,ymm4,YMMWORD PTR [rsp+0x100]
    vmovdqa ymm0,YMMWORD PTR [rsp+0x240]
    vpxor  ymm0,ymm0,YMMWORD PTR [rsp+0x1a0]
    vpxor  ymm2,ymm2,ymm0
    vpxor  ymm2,ymm2,YMMWORD PTR [rsp+0x2e0]
    vpsllq ymm4,ymm8,0x1
    vpsrlq ymm0,ymm8,0x3f
    vpor   ymm4,ymm4,ymm0
    vpsllq ymm3,ymm7,0x1
    vpsrlq ymm0,ymm7,0x3f
    vpor   ymm3,ymm3,ymm0
    vpsllq ymm0,ymm6,0x1
    vpsrlq ymm9,ymm6,0x3f
    vpor   ymm0,ymm0,ymm9
    vpxor  ymm4,ymm4,ymm2
    vpxor  ymm3,ymm3,ymm1
    vpxor  ymm0,ymm0,ymm8
    vpsllq ymm8,ymm2,0x1
    vpsrlq ymm2,ymm2,0x3f
    vpor   ymm2,ymm2,ymm8
    vpxor  ymm14,ymm4,ymm5
    vpxor  ymm9,ymm0,YMMWORD PTR [rsp+0xc0]
    vmovdqa YMMWORD PTR [rsp+0x320],ymm9
    vpxor  ymm15,ymm4,ymm12
    vpxor  ymm12,ymm3,YMMWORD PTR [rsp]
    vpxor  ymm8,ymm3,YMMWORD PTR [rsp+0x140]
    vmovdqa YMMWORD PTR [rsp+0x340],ymm14
    vpxor  ymm14,ymm4,ymm13
    vpxor  ymm13,ymm4,ymm11
    vpxor  ymm11,ymm3,YMMWORD PTR [rsp+0xa0]
    vpxor  ymm4,ymm4,ymm10
    vpxor  ymm10,ymm0,YMMWORD PTR [rsp+0x20]
    vpxor  ymm2,ymm2,ymm7
    vpsllq ymm7,ymm1,0x1
    vpsrlq ymm1,ymm1,0x3f
    vpor   ymm1,ymm1,ymm7
    vpxor  ymm1,ymm1,ymm6
    vpxor  ymm7,ymm3,YMMWORD PTR [rsp+0x1e0]
    vpxor  ymm3,ymm3,YMMWORD PTR [rsp+0x280]
    vpxor  ymm5,ymm2,YMMWORD PTR [rsp+0x40]
    vpxor  ymm9,ymm0,YMMWORD PTR [rsp+0x160]
    vpxor  ymm6,ymm0,YMMWORD PTR [rsp+0x200]
    vpxor  ymm0,ymm0,YMMWORD PTR [rsp+0x2a0]
    vmovdqa YMMWORD PTR [rsp],ymm5
    vpxor  ymm5,ymm2,YMMWORD PTR [rsp+0xe0]
    vmovdqa YMMWORD PTR [rsp+0xa0],ymm5
    vpxor  ymm5,ymm2,YMMWORD PTR [rsp+0x180]
    vmovdqa YMMWORD PTR [rsp+0x140],ymm5
    vpxor  ymm5,ymm2,YMMWORD PTR [rsp+0x220]
    vpxor  ymm2,ymm2,YMMWORD PTR [rsp+0x2c0]
    vmovdqa YMMWORD PTR [rsp+0x1e0],ymm5
    vpxor  ymm5,ymm1,YMMWORD PTR [rsp+0x60]
    vmovdqa YMMWORD PTR [rsp+0x280],ymm5
    vpxor  ymm5,ymm1,YMMWORD PTR [rsp+0x100]
    vmovdqa YMMWORD PTR [rsp+0x20],ymm5
    vpxor  ymm5,ymm1,YMMWORD PTR [rsp+0x1a0]
    vmovdqa YMMWORD PTR [rsp+0x160],ymm5
    vpxor  ymm5,ymm1,YMMWORD PTR [rsp+0x240]
    vmovdqa YMMWORD PTR [rsp+0x200],ymm5
    vpxor  ymm1,ymm1,YMMWORD PTR [rsp+0x2e0]
    vmovdqa YMMWORD PTR [rsp+0x40],ymm1
    vpsrlq ymm1,ymm15,0x1c
    vpsllq ymm15,ymm15,0x24
    vpor   ymm1,ymm15,ymm1
    vmovdqa YMMWORD PTR [rsp+0x240],ymm1
    vpsrlq ymm1,ymm14,0x3d
    vpsllq ymm14,ymm14,0x3
    vpor   ymm15,ymm14,ymm1
    vmovdqa YMMWORD PTR [rsp+0x2c0],ymm15
    vpsrlq ymm1,ymm13,0x17
    vpsllq ymm13,ymm13,0x29
    vpor   ymm13,ymm13,ymm1
    vmovdqa YMMWORD PTR [rsp+0x2a0],ymm13
    vpsrlq ymm1,ymm4,0x2e
    vpsllq ymm4,ymm4,0x12
    vpor   ymm4,ymm4,ymm1
    vmovdqa YMMWORD PTR [rsp+0x180],ymm4
    vpsrlq ymm1,ymm12,0x3f
    vpsllq ymm12,ymm12,0x1
    vpor   ymm12,ymm12,ymm1
    vmovdqa YMMWORD PTR [rsp+0x1a0],ymm12
    vpsrlq ymm1,ymm11,0x14
    vpsllq ymm11,ymm11,0x2c
    vpor   ymm11,ymm11,ymm1
    vmovdqa YMMWORD PTR [rsp+0x100],ymm11
    vpsrlq ymm1,ymm8,0x36
    vpsllq ymm8,ymm8,0xa
    vpor   ymm8,ymm8,ymm1
    vpsrlq ymm1,ymm7,0x13
    vpsllq ymm7,ymm7,0x2d
    vpor   ymm7,ymm7,ymm1
    vpsrlq ymm1,ymm3,0x3e
    vpsllq ymm3,ymm3,0x2
    vpor   ymm3,ymm3,ymm1
    vmovdqa YMMWORD PTR [rsp+0x2e0],ymm3
    vpsrlq ymm1,ymm10,0x2
    vpsllq ymm10,ymm10,0x3e
    vpor   ymm10,ymm10,ymm1
    vmovdqa YMMWORD PTR [rsp+0x60],ymm10
    vmovdqa ymm3,YMMWORD PTR [rsp+0x320]
    vpsllq ymm5,ymm3,0x6
    vpsrlq ymm1,ymm3,0x3a
    vpor   ymm5,ymm5,ymm1
    vpsrlq ymm1,ymm9,0x15
    vpsllq ymm9,ymm9,0x2b
    vpor   ymm9,ymm9,ymm1
    vmovdqa YMMWORD PTR [rsp+0x320],ymm9
    vpsrlq ymm1,ymm6,0x31
    vpsllq ymm6,ymm6,0xf
    vpor   ymm6,ymm6,ymm1
    vmovdqa ymm4,YMMWORD PTR [rsp]
    vpsllq ymm3,ymm4,0x1c
    vpsrlq ymm1,ymm4,0x24
    vpor   ymm3,ymm3,ymm1
    vmovdqa ymm9,YMMWORD PTR [rsp+0x140]
    vpsllq ymm10,ymm9,0x19
    vpsrlq ymm1,ymm9,0x27
    vpor   ymm10,ymm10,ymm1
    vpsrlq ymm1,ymm0,0x3
    vpsllq ymm0,ymm0,0x3d
    vpor   ymm0,ymm0,ymm1
    vmovdqa ymm13,YMMWORD PTR [rsp+0x160]
    vpsllq ymm14,ymm13,0x27
    vpsrlq ymm12,ymm13,0x19
    vpor   ymm14,ymm14,ymm12
    vmovdqa ymm4,YMMWORD PTR [rsp+0xa0]
    vpsrlq ymm1,ymm4,0x9
    vpsllq ymm4,ymm4,0x37
    vpor   ymm4,ymm4,ymm1
    vmovdqa ymm12,YMMWORD PTR [rsp+0x1e0]
    vpsllq ymm11,ymm12,0x15
    vpsrlq ymm1,ymm12,0x2b
    vpor   ymm11,ymm11,ymm1
    vpsrlq ymm1,ymm2,0x8
    vpsllq ymm2,ymm2,0x38
    vpor   ymm2,ymm2,ymm1
    vmovdqa ymm1,YMMWORD PTR [rsp+0x280]
    vpsrlq ymm9,ymm1,0x25
    vpsllq ymm1,ymm1,0x1b
    vpor   ymm1,ymm1,ymm9
    vmovdqa ymm9,YMMWORD PTR [rsp+0x20]
    vpsrlq ymm12,ymm9,0x2c
    vpsllq ymm9,ymm9,0x14
    vpor   ymm9,ymm9,ymm12
    vmovdqa ymm13,YMMWORD PTR [rsp+0x200]
    vpsrlq ymm12,ymm13,0x38
    vpsllq ymm13,ymm13,0x8
    vpor   ymm13,ymm13,ymm12
    vmovdqa ymm12,YMMWORD PTR [rsp+0x40]
    vpsrlq ymm15,ymm12,0x32
    vpsllq ymm12,ymm12,0xe
    vpor   ymm12,ymm12,ymm15
    vpandn ymm15,ymm9,YMMWORD PTR [rsp+0x2c0]
    vpxor  ymm15,ymm15,ymm3
    vmovdqa YMMWORD PTR [rsp+0x80],ymm15
    vpandn ymm15,ymm5,ymm10
    vpxor  ymm15,ymm15,YMMWORD PTR [rsp+0x1a0]
    vmovdqa YMMWORD PTR [rsp+0x120],ymm15
    vmovdqa ymm15,YMMWORD PTR [rsp+0x240]
    vpandn ymm15,ymm15,ymm8
    vpxor  ymm15,ymm15,ymm1
    vmovdqa YMMWORD PTR [rsp+0x1c0],ymm15
    vpandn ymm15,ymm4,ymm14
    vpxor  ymm15,ymm15,YMMWORD PTR [rsp+0x60]
    vmovdqa YMMWORD PTR [rsp+0x260],ymm15
    vmovdqa ymm15,YMMWORD PTR [rsp+0x320]
    vpandn ymm15,ymm15,ymm11
    vpxor  ymm15,ymm15,YMMWORD PTR [rsp+0x100]
    vmovdqa YMMWORD PTR [rsp],ymm15
    vmovdqa ymm15,YMMWORD PTR [rsp+0x2c0]
    vpandn ymm15,ymm15,ymm7
    vpxor  ymm15,ymm15,ymm9
    vmovdqa YMMWORD PTR [rsp+0xa0],ymm15
    vpandn ymm15,ymm10,ymm13
    vpxor  ymm15,ymm15,ymm5
    vmovdqa YMMWORD PTR [rsp+0x140],ymm15
    vpandn ymm15,ymm8,ymm6
    vpxor  ymm15,ymm15,YMMWORD PTR [rsp+0x240]
    vmovdqa YMMWORD PTR [rsp+0x1e0],ymm15
    vpandn ymm15,ymm14,YMMWORD PTR [rsp+0x2a0]
    vpxor  ymm15,ymm15,ymm4
    vmovdqa YMMWORD PTR [rsp+0x280],ymm15
    vpandn ymm15,ymm11,ymm12
    vpxor  ymm15,ymm15,YMMWORD PTR [rsp+0x320]
    vmovdqa YMMWORD PTR [rsp+0x20],ymm15
    vpandn ymm15,ymm7,ymm0
    vpxor  ymm15,ymm15,YMMWORD PTR [rsp+0x2c0]
    vmovdqa YMMWORD PTR [rsp+0xc0],ymm15
    vpandn ymm15,ymm13,YMMWORD PTR [rsp+0x180]
    vpxor  ymm10,ymm15,ymm10
    vmovdqa YMMWORD PTR [rsp+0x160],ymm10
    vpandn ymm10,ymm6,ymm2
    vpxor  ymm8,ymm10,ymm8
    vmovdqa YMMWORD PTR [rsp+0x200],ymm8
    vmovdqa ymm10,YMMWORD PTR [rsp+0x2a0]
    vmovdqa ymm15,YMMWORD PTR [rsp+0x2e0]
    vpandn ymm8,ymm10,ymm15
    vpxor  ymm8,ymm8,ymm14
    vmovdqa YMMWORD PTR [rsp+0x2a0],ymm8
    vmovdqa ymm14,YMMWORD PTR [rsp+0x340]
    vpandn ymm8,ymm12,ymm14
    vpxor  ymm8,ymm8,ymm11
    vmovdqa YMMWORD PTR [rsp+0x40],ymm8
    vpandn ymm8,ymm0,ymm3
    vpxor  ymm7,ymm8,ymm7
    vmovdqa YMMWORD PTR [rsp+0xe0],ymm7
    vmovdqa ymm11,YMMWORD PTR [rsp+0x180]
    vmovdqa ymm8,YMMWORD PTR [rsp+0x1a0]
    vpandn ymm7,ymm11,ymm8
    vpxor  ymm7,ymm7,ymm13
    vmovdqa YMMWORD PTR [rsp+0x180],ymm7
    vmovdqa ymm13,YMMWORD PTR [rsp+0x100]
    vpandn ymm3,ymm3,ymm9
    vpxor  ymm3,ymm3,ymm0
    vmovdqa YMMWORD PTR [rsp+0x100],ymm3
    vpandn ymm0,ymm8,ymm5
    vpxor  ymm3,ymm0,ymm11
    vmovdqa YMMWORD PTR [rsp+0x1a0],ymm3
    vpandn ymm7,ymm2,ymm1
    vpxor  ymm6,ymm7,ymm6
    vmovdqa YMMWORD PTR [rsp+0x220],ymm6
    vmovdqa ymm6,ymm15
    vmovdqa ymm15,YMMWORD PTR [rsp+0x60]
    vpandn ymm6,ymm6,ymm15
    vpxor  ymm7,ymm6,ymm10
    vmovdqa YMMWORD PTR [rsp+0x2c0],ymm7
    vpandn ymm1,ymm1,YMMWORD PTR [rsp+0x240]
    vpxor  ymm2,ymm1,ymm2
    vmovdqa YMMWORD PTR [rsp+0x240],ymm2
    vpandn ymm5,ymm13,YMMWORD PTR [rsp+0x320]
    vpxor  ymm5,ymm5,ymm14
    vpbroadcastq ymm0,QWORD PTR [rsi]
    vpxor  ymm5,ymm5,ymm0
    vpandn ymm6,ymm14,ymm13
    vpxor  ymm14,ymm6,ymm12
    vmovdqa YMMWORD PTR [rsp+0x60],ymm14
    vpandn ymm0,ymm15,ymm4
    vpxor  ymm6,ymm0,YMMWORD PTR [rsp+0x2e0]
    vmovdqa YMMWORD PTR [rsp+0x2e0],ymm6
    add    rsi,0x8
    add    rax,0x1
    cmp    rax,0x18
    jne    .keccak_loop

    vmovdqa ymm1,YMMWORD PTR [rsp]
    vmovdqa ymm2,YMMWORD PTR [rsp+0x20]
    vmovdqa ymm3,YMMWORD PTR [rsp+0x40]
    vpunpcklqdq ymm4,ymm5,ymm1
    vpunpcklqdq ymm6,ymm5,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm5,ymm4,ymm7,0x20
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqu YMMWORD PTR [rdi],ymm5
    vmovdqu YMMWORD PTR [rdi+0xc8],ymm1
    vmovdqu YMMWORD PTR [rdi+0x190],ymm2
    vmovdqu YMMWORD PTR [rdi+0x258],ymm3
    vmovdqa ymm0,YMMWORD PTR [rsp+0x60]
    vmovdqa ymm1,YMMWORD PTR [rsp+0x80]
    vmovdqa ymm2,YMMWORD PTR [rsp+0xa0]
    vmovdqa ymm3,YMMWORD PTR [rsp+0xc0]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqu YMMWORD PTR [rdi+0x20],ymm0
    vmovdqu YMMWORD PTR [rdi+0xe8],ymm1
    vmovdqu YMMWORD PTR [rdi+0x1b0],ymm2
    vmovdqu YMMWORD PTR [rdi+0x278],ymm3
    vmovdqa ymm0,YMMWORD PTR [rsp+0xe0]
    vmovdqa ymm1,YMMWORD PTR [rsp+0x100]
    vmovdqa ymm2,YMMWORD PTR [rsp+0x120]
    vmovdqa ymm3,YMMWORD PTR [rsp+0x140]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqu YMMWORD PTR [rdi+0x40],ymm0
    vmovdqu YMMWORD PTR [rdi+0x108],ymm1
    vmovdqu YMMWORD PTR [rdi+0x1d0],ymm2
    vmovdqu YMMWORD PTR [rdi+0x298],ymm3
    vmovdqa ymm0,YMMWORD PTR [rsp+0x160]
    vmovdqa ymm1,YMMWORD PTR [rsp+0x180]
    vmovdqa ymm2,YMMWORD PTR [rsp+0x1a0]
    vmovdqa ymm3,YMMWORD PTR [rsp+0x1c0]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqu YMMWORD PTR [rdi+0x60],ymm0
    vmovdqu YMMWORD PTR [rdi+0x128],ymm1
    vmovdqu YMMWORD PTR [rdi+0x1f0],ymm2
    vmovdqu YMMWORD PTR [rdi+0x2b8],ymm3
    vmovdqa ymm0,YMMWORD PTR [rsp+0x1e0]
    vmovdqa ymm1,YMMWORD PTR [rsp+0x200]
    vmovdqa ymm2,YMMWORD PTR [rsp+0x220]
    vmovdqa ymm3,YMMWORD PTR [rsp+0x240]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqu YMMWORD PTR [rdi+0x80],ymm0
    vmovdqu YMMWORD PTR [rdi+0x148],ymm1
    vmovdqu YMMWORD PTR [rdi+0x210],ymm2
    vmovdqu YMMWORD PTR [rdi+0x2d8],ymm3
    vmovdqa ymm0,YMMWORD PTR [rsp+0x260]
    vmovdqa ymm1,YMMWORD PTR [rsp+0x280]
    vmovdqa ymm2,YMMWORD PTR [rsp+0x2a0]
    vmovdqa ymm3,YMMWORD PTR [rsp+0x2c0]
    vpunpcklqdq ymm4,ymm0,ymm1
    vpunpcklqdq ymm6,ymm0,ymm1
    vpunpcklqdq ymm7,ymm2,ymm3
    vpunpcklqdq ymm8,ymm2,ymm3
    vperm2i128 ymm0,ymm4,ymm7,0x20
    vperm2i128 ymm1,ymm6,ymm8,0x20
    vperm2i128 ymm2,ymm4,ymm7,0x31
    vperm2i128 ymm3,ymm6,ymm8,0x31
    vmovdqu YMMWORD PTR [rdi+0xa0],ymm0
    vmovdqu YMMWORD PTR [rdi+0x168],ymm1
    vmovdqu YMMWORD PTR [rdi+0x230],ymm2
    vmovdqu YMMWORD PTR [rdi+0x2f8],ymm3
    vmovdqa ymm3,YMMWORD PTR [rsp+0x2e0]
    // vextracti128 xmm0,ymm3,0x0
    // vextracti128 xmm1,ymm3,0x1
    // vmovq  QWORD PTR [rdi+0xc0],xmm0
    // vpextrq QWORD PTR [rdi+0x188],xmm0,0x1
    // vmovq  QWORD PTR [rdi+0x250],xmm1
    // vpextrq QWORD PTR [rdi+0x318],xmm1,0x1
   mov    rsp,rbp
   pop    rbp

#if WINDOWS_ABI
    pop    rsi
    pop    rdi
#endif

    ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif