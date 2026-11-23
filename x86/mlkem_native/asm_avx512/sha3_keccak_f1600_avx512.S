// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, with AVX-512VL
// Input a[25], rc[24]; output a[25]
//
// The input/output argument is a 25-element Keccak array, replaced by its
// Keccak-f1600 permutation with the round constants rc, as by
// sha3_keccak_f1600 (this is the same function, for processors with
// AVX-512F and AVX-512VL). Lane i of the state is in quadword 0 of xmm
// register i, permuted there with vprolq and vpternlogq and no spills.
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
// extern void sha3_keccak_f1600_avx512
//   (uint64_t a[S2N_BIGNUM_STATIC 25],
//    const uint64_t rc[S2N_BIGNUM_STATIC 24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak_f1600_avx512)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak_f1600_avx512)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak_f1600_avx512)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak_f1600_avx512):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(176)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVEU(xmm11,80)
        CFI_STACKSAVEU(xmm12,96)
        CFI_STACKSAVEU(xmm13,112)
        CFI_STACKSAVEU(xmm14,128)
        CFI_STACKSAVEU(xmm15,144)
        CFI_STACKSAVE(rdi,160)
        CFI_STACKSAVE(rsi,168)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load lane i into xmm i

        vmovq   xmm0, QWORD PTR [rdi+0]
        vmovq   xmm1, QWORD PTR [rdi+8]
        vmovq   xmm2, QWORD PTR [rdi+16]
        vmovq   xmm3, QWORD PTR [rdi+24]
        vmovq   xmm4, QWORD PTR [rdi+32]
        vmovq   xmm5, QWORD PTR [rdi+40]
        vmovq   xmm6, QWORD PTR [rdi+48]
        vmovq   xmm7, QWORD PTR [rdi+56]
        vmovq   xmm8, QWORD PTR [rdi+64]
        vmovq   xmm9, QWORD PTR [rdi+72]
        vmovq   xmm10, QWORD PTR [rdi+80]
        vmovq   xmm11, QWORD PTR [rdi+88]
        vmovq   xmm12, QWORD PTR [rdi+96]
        vmovq   xmm13, QWORD PTR [rdi+104]
        vmovq   xmm14, QWORD PTR [rdi+112]
        vmovq   xmm15, QWORD PTR [rdi+120]
        // The loads and stores of the lanes in xmm16 and up are written as bytes:
        // for vmovq with an EVEX-only register, GNU as and clang choose different
        // (equivalent) opcodes, 66 0F 6E/7E and F3 0F 7E/66 0F D6, and no syntax
        // selects one. These are the bytes that GNU as assembles.
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x47, 0x10  // vmovq xmm16, QWORD PTR [rdi+128]
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x4f, 0x11  // vmovq xmm17, QWORD PTR [rdi+136]
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x57, 0x12  // vmovq xmm18, QWORD PTR [rdi+144]
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x5f, 0x13  // vmovq xmm19, QWORD PTR [rdi+152]
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x67, 0x14  // vmovq xmm20, QWORD PTR [rdi+160]
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x6f, 0x15  // vmovq xmm21, QWORD PTR [rdi+168]
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x77, 0x16  // vmovq xmm22, QWORD PTR [rdi+176]
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x7f, 0x17  // vmovq xmm23, QWORD PTR [rdi+184]
        .byte   0x62, 0x61, 0xfd, 0x08, 0x6e, 0x47, 0x18  // vmovq xmm24, QWORD PTR [rdi+192]

// The 24 rounds, four at a time

        lea     rax, [rsi+192]
Lsha3_keccak_f1600_avx512_loop:

// Round 1 of 4: theta

        vmovdqa64 xmm25, xmm0
        vpternlogq xmm25, xmm5, xmm10, 0x96
        vpternlogq xmm25, xmm15, xmm20, 0x96
        vmovdqa64 xmm26, xmm1
        vpternlogq xmm26, xmm6, xmm11, 0x96
        vpternlogq xmm26, xmm16, xmm21, 0x96
        vmovdqa64 xmm27, xmm2
        vpternlogq xmm27, xmm7, xmm12, 0x96
        vpternlogq xmm27, xmm17, xmm22, 0x96
        vmovdqa64 xmm28, xmm3
        vpternlogq xmm28, xmm8, xmm13, 0x96
        vpternlogq xmm28, xmm18, xmm23, 0x96
        vmovdqa64 xmm29, xmm4
        vpternlogq xmm29, xmm9, xmm14, 0x96
        vpternlogq xmm29, xmm19, xmm24, 0x96
        vprolq  xmm30, xmm26, 1
        vpternlogq xmm0, xmm29, xmm30, 0x96
        vpternlogq xmm5, xmm29, xmm30, 0x96
        vpternlogq xmm10, xmm29, xmm30, 0x96
        vpternlogq xmm15, xmm29, xmm30, 0x96
        vpternlogq xmm20, xmm29, xmm30, 0x96
        vprolq  xmm30, xmm27, 1
        vpternlogq xmm1, xmm25, xmm30, 0x96
        vpternlogq xmm6, xmm25, xmm30, 0x96
        vpternlogq xmm11, xmm25, xmm30, 0x96
        vpternlogq xmm16, xmm25, xmm30, 0x96
        vpternlogq xmm21, xmm25, xmm30, 0x96
        vprolq  xmm30, xmm28, 1
        vpternlogq xmm2, xmm26, xmm30, 0x96
        vpternlogq xmm7, xmm26, xmm30, 0x96
        vpternlogq xmm12, xmm26, xmm30, 0x96
        vpternlogq xmm17, xmm26, xmm30, 0x96
        vpternlogq xmm22, xmm26, xmm30, 0x96
        vprolq  xmm30, xmm29, 1
        vpternlogq xmm3, xmm27, xmm30, 0x96
        vpternlogq xmm8, xmm27, xmm30, 0x96
        vpternlogq xmm13, xmm27, xmm30, 0x96
        vpternlogq xmm18, xmm27, xmm30, 0x96
        vpternlogq xmm23, xmm27, xmm30, 0x96
        vprolq  xmm30, xmm25, 1
        vpternlogq xmm4, xmm28, xmm30, 0x96
        vpternlogq xmm9, xmm28, xmm30, 0x96
        vpternlogq xmm14, xmm28, xmm30, 0x96
        vpternlogq xmm19, xmm28, xmm30, 0x96
        vpternlogq xmm24, xmm28, xmm30, 0x96

// rho

        vprolq  xmm5, xmm5, 36
        vprolq  xmm10, xmm10, 3
        vprolq  xmm15, xmm15, 41
        vprolq  xmm20, xmm20, 18
        vprolq  xmm1, xmm1, 1
        vprolq  xmm6, xmm6, 44
        vprolq  xmm11, xmm11, 10
        vprolq  xmm16, xmm16, 45
        vprolq  xmm21, xmm21, 2
        vprolq  xmm2, xmm2, 62
        vprolq  xmm7, xmm7, 6
        vprolq  xmm12, xmm12, 43
        vprolq  xmm17, xmm17, 15
        vprolq  xmm22, xmm22, 61
        vprolq  xmm3, xmm3, 28
        vprolq  xmm8, xmm8, 55
        vprolq  xmm13, xmm13, 25
        vprolq  xmm18, xmm18, 21
        vprolq  xmm23, xmm23, 56
        vprolq  xmm4, xmm4, 27
        vprolq  xmm9, xmm9, 20
        vprolq  xmm14, xmm14, 39
        vprolq  xmm19, xmm19, 8
        vprolq  xmm24, xmm24, 14

// pi (renaming the registers), chi and iota

        vmovdqa64 xmm30, xmm0
        vmovdqa64 xmm31, xmm6
        vpternlogq xmm0, xmm6, xmm12, 0xd2
        vpxorq  xmm0, xmm0, QWORD PTR [rsi+0]{1to2}
        vpternlogq xmm6, xmm12, xmm18, 0xd2
        vpternlogq xmm12, xmm18, xmm24, 0xd2
        vpternlogq xmm18, xmm24, xmm30, 0xd2
        vpternlogq xmm24, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm3
        vmovdqa64 xmm31, xmm9
        vpternlogq xmm3, xmm9, xmm10, 0xd2
        vpternlogq xmm9, xmm10, xmm16, 0xd2
        vpternlogq xmm10, xmm16, xmm22, 0xd2
        vpternlogq xmm16, xmm22, xmm30, 0xd2
        vpternlogq xmm22, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm1
        vmovdqa64 xmm31, xmm7
        vpternlogq xmm1, xmm7, xmm13, 0xd2
        vpternlogq xmm7, xmm13, xmm19, 0xd2
        vpternlogq xmm13, xmm19, xmm20, 0xd2
        vpternlogq xmm19, xmm20, xmm30, 0xd2
        vpternlogq xmm20, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm4
        vmovdqa64 xmm31, xmm5
        vpternlogq xmm4, xmm5, xmm11, 0xd2
        vpternlogq xmm5, xmm11, xmm17, 0xd2
        vpternlogq xmm11, xmm17, xmm23, 0xd2
        vpternlogq xmm17, xmm23, xmm30, 0xd2
        vpternlogq xmm23, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm2
        vmovdqa64 xmm31, xmm8
        vpternlogq xmm2, xmm8, xmm14, 0xd2
        vpternlogq xmm8, xmm14, xmm15, 0xd2
        vpternlogq xmm14, xmm15, xmm21, 0xd2
        vpternlogq xmm15, xmm21, xmm30, 0xd2
        vpternlogq xmm21, xmm30, xmm31, 0xd2

// Round 2 of 4: theta

        vmovdqa64 xmm25, xmm0
        vpternlogq xmm25, xmm3, xmm1, 0x96
        vpternlogq xmm25, xmm4, xmm2, 0x96
        vmovdqa64 xmm26, xmm6
        vpternlogq xmm26, xmm9, xmm7, 0x96
        vpternlogq xmm26, xmm5, xmm8, 0x96
        vmovdqa64 xmm27, xmm12
        vpternlogq xmm27, xmm10, xmm13, 0x96
        vpternlogq xmm27, xmm11, xmm14, 0x96
        vmovdqa64 xmm28, xmm18
        vpternlogq xmm28, xmm16, xmm19, 0x96
        vpternlogq xmm28, xmm17, xmm15, 0x96
        vmovdqa64 xmm29, xmm24
        vpternlogq xmm29, xmm22, xmm20, 0x96
        vpternlogq xmm29, xmm23, xmm21, 0x96
        vprolq  xmm30, xmm26, 1
        vpternlogq xmm0, xmm29, xmm30, 0x96
        vpternlogq xmm3, xmm29, xmm30, 0x96
        vpternlogq xmm1, xmm29, xmm30, 0x96
        vpternlogq xmm4, xmm29, xmm30, 0x96
        vpternlogq xmm2, xmm29, xmm30, 0x96
        vprolq  xmm30, xmm27, 1
        vpternlogq xmm6, xmm25, xmm30, 0x96
        vpternlogq xmm9, xmm25, xmm30, 0x96
        vpternlogq xmm7, xmm25, xmm30, 0x96
        vpternlogq xmm5, xmm25, xmm30, 0x96
        vpternlogq xmm8, xmm25, xmm30, 0x96
        vprolq  xmm30, xmm28, 1
        vpternlogq xmm12, xmm26, xmm30, 0x96
        vpternlogq xmm10, xmm26, xmm30, 0x96
        vpternlogq xmm13, xmm26, xmm30, 0x96
        vpternlogq xmm11, xmm26, xmm30, 0x96
        vpternlogq xmm14, xmm26, xmm30, 0x96
        vprolq  xmm30, xmm29, 1
        vpternlogq xmm18, xmm27, xmm30, 0x96
        vpternlogq xmm16, xmm27, xmm30, 0x96
        vpternlogq xmm19, xmm27, xmm30, 0x96
        vpternlogq xmm17, xmm27, xmm30, 0x96
        vpternlogq xmm15, xmm27, xmm30, 0x96
        vprolq  xmm30, xmm25, 1
        vpternlogq xmm24, xmm28, xmm30, 0x96
        vpternlogq xmm22, xmm28, xmm30, 0x96
        vpternlogq xmm20, xmm28, xmm30, 0x96
        vpternlogq xmm23, xmm28, xmm30, 0x96
        vpternlogq xmm21, xmm28, xmm30, 0x96

// rho

        vprolq  xmm3, xmm3, 36
        vprolq  xmm1, xmm1, 3
        vprolq  xmm4, xmm4, 41
        vprolq  xmm2, xmm2, 18
        vprolq  xmm6, xmm6, 1
        vprolq  xmm9, xmm9, 44
        vprolq  xmm7, xmm7, 10
        vprolq  xmm5, xmm5, 45
        vprolq  xmm8, xmm8, 2
        vprolq  xmm12, xmm12, 62
        vprolq  xmm10, xmm10, 6
        vprolq  xmm13, xmm13, 43
        vprolq  xmm11, xmm11, 15
        vprolq  xmm14, xmm14, 61
        vprolq  xmm18, xmm18, 28
        vprolq  xmm16, xmm16, 55
        vprolq  xmm19, xmm19, 25
        vprolq  xmm17, xmm17, 21
        vprolq  xmm15, xmm15, 56
        vprolq  xmm24, xmm24, 27
        vprolq  xmm22, xmm22, 20
        vprolq  xmm20, xmm20, 39
        vprolq  xmm23, xmm23, 8
        vprolq  xmm21, xmm21, 14

// pi (renaming the registers), chi and iota

        vmovdqa64 xmm30, xmm0
        vmovdqa64 xmm31, xmm9
        vpternlogq xmm0, xmm9, xmm13, 0xd2
        vpxorq  xmm0, xmm0, QWORD PTR [rsi+8]{1to2}
        vpternlogq xmm9, xmm13, xmm17, 0xd2
        vpternlogq xmm13, xmm17, xmm21, 0xd2
        vpternlogq xmm17, xmm21, xmm30, 0xd2
        vpternlogq xmm21, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm18
        vmovdqa64 xmm31, xmm22
        vpternlogq xmm18, xmm22, xmm1, 0xd2
        vpternlogq xmm22, xmm1, xmm5, 0xd2
        vpternlogq xmm1, xmm5, xmm14, 0xd2
        vpternlogq xmm5, xmm14, xmm30, 0xd2
        vpternlogq xmm14, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm6
        vmovdqa64 xmm31, xmm10
        vpternlogq xmm6, xmm10, xmm19, 0xd2
        vpternlogq xmm10, xmm19, xmm23, 0xd2
        vpternlogq xmm19, xmm23, xmm2, 0xd2
        vpternlogq xmm23, xmm2, xmm30, 0xd2
        vpternlogq xmm2, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm24
        vmovdqa64 xmm31, xmm3
        vpternlogq xmm24, xmm3, xmm7, 0xd2
        vpternlogq xmm3, xmm7, xmm11, 0xd2
        vpternlogq xmm7, xmm11, xmm15, 0xd2
        vpternlogq xmm11, xmm15, xmm30, 0xd2
        vpternlogq xmm15, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm12
        vmovdqa64 xmm31, xmm16
        vpternlogq xmm12, xmm16, xmm20, 0xd2
        vpternlogq xmm16, xmm20, xmm4, 0xd2
        vpternlogq xmm20, xmm4, xmm8, 0xd2
        vpternlogq xmm4, xmm8, xmm30, 0xd2
        vpternlogq xmm8, xmm30, xmm31, 0xd2

// Round 3 of 4: theta

        vmovdqa64 xmm25, xmm0
        vpternlogq xmm25, xmm18, xmm6, 0x96
        vpternlogq xmm25, xmm24, xmm12, 0x96
        vmovdqa64 xmm26, xmm9
        vpternlogq xmm26, xmm22, xmm10, 0x96
        vpternlogq xmm26, xmm3, xmm16, 0x96
        vmovdqa64 xmm27, xmm13
        vpternlogq xmm27, xmm1, xmm19, 0x96
        vpternlogq xmm27, xmm7, xmm20, 0x96
        vmovdqa64 xmm28, xmm17
        vpternlogq xmm28, xmm5, xmm23, 0x96
        vpternlogq xmm28, xmm11, xmm4, 0x96
        vmovdqa64 xmm29, xmm21
        vpternlogq xmm29, xmm14, xmm2, 0x96
        vpternlogq xmm29, xmm15, xmm8, 0x96
        vprolq  xmm30, xmm26, 1
        vpternlogq xmm0, xmm29, xmm30, 0x96
        vpternlogq xmm18, xmm29, xmm30, 0x96
        vpternlogq xmm6, xmm29, xmm30, 0x96
        vpternlogq xmm24, xmm29, xmm30, 0x96
        vpternlogq xmm12, xmm29, xmm30, 0x96
        vprolq  xmm30, xmm27, 1
        vpternlogq xmm9, xmm25, xmm30, 0x96
        vpternlogq xmm22, xmm25, xmm30, 0x96
        vpternlogq xmm10, xmm25, xmm30, 0x96
        vpternlogq xmm3, xmm25, xmm30, 0x96
        vpternlogq xmm16, xmm25, xmm30, 0x96
        vprolq  xmm30, xmm28, 1
        vpternlogq xmm13, xmm26, xmm30, 0x96
        vpternlogq xmm1, xmm26, xmm30, 0x96
        vpternlogq xmm19, xmm26, xmm30, 0x96
        vpternlogq xmm7, xmm26, xmm30, 0x96
        vpternlogq xmm20, xmm26, xmm30, 0x96
        vprolq  xmm30, xmm29, 1
        vpternlogq xmm17, xmm27, xmm30, 0x96
        vpternlogq xmm5, xmm27, xmm30, 0x96
        vpternlogq xmm23, xmm27, xmm30, 0x96
        vpternlogq xmm11, xmm27, xmm30, 0x96
        vpternlogq xmm4, xmm27, xmm30, 0x96
        vprolq  xmm30, xmm25, 1
        vpternlogq xmm21, xmm28, xmm30, 0x96
        vpternlogq xmm14, xmm28, xmm30, 0x96
        vpternlogq xmm2, xmm28, xmm30, 0x96
        vpternlogq xmm15, xmm28, xmm30, 0x96
        vpternlogq xmm8, xmm28, xmm30, 0x96

// rho

        vprolq  xmm18, xmm18, 36
        vprolq  xmm6, xmm6, 3
        vprolq  xmm24, xmm24, 41
        vprolq  xmm12, xmm12, 18
        vprolq  xmm9, xmm9, 1
        vprolq  xmm22, xmm22, 44
        vprolq  xmm10, xmm10, 10
        vprolq  xmm3, xmm3, 45
        vprolq  xmm16, xmm16, 2
        vprolq  xmm13, xmm13, 62
        vprolq  xmm1, xmm1, 6
        vprolq  xmm19, xmm19, 43
        vprolq  xmm7, xmm7, 15
        vprolq  xmm20, xmm20, 61
        vprolq  xmm17, xmm17, 28
        vprolq  xmm5, xmm5, 55
        vprolq  xmm23, xmm23, 25
        vprolq  xmm11, xmm11, 21
        vprolq  xmm4, xmm4, 56
        vprolq  xmm21, xmm21, 27
        vprolq  xmm14, xmm14, 20
        vprolq  xmm2, xmm2, 39
        vprolq  xmm15, xmm15, 8
        vprolq  xmm8, xmm8, 14

// pi (renaming the registers), chi and iota

        vmovdqa64 xmm30, xmm0
        vmovdqa64 xmm31, xmm22
        vpternlogq xmm0, xmm22, xmm19, 0xd2
        vpxorq  xmm0, xmm0, QWORD PTR [rsi+16]{1to2}
        vpternlogq xmm22, xmm19, xmm11, 0xd2
        vpternlogq xmm19, xmm11, xmm8, 0xd2
        vpternlogq xmm11, xmm8, xmm30, 0xd2
        vpternlogq xmm8, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm17
        vmovdqa64 xmm31, xmm14
        vpternlogq xmm17, xmm14, xmm6, 0xd2
        vpternlogq xmm14, xmm6, xmm3, 0xd2
        vpternlogq xmm6, xmm3, xmm20, 0xd2
        vpternlogq xmm3, xmm20, xmm30, 0xd2
        vpternlogq xmm20, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm9
        vmovdqa64 xmm31, xmm1
        vpternlogq xmm9, xmm1, xmm23, 0xd2
        vpternlogq xmm1, xmm23, xmm15, 0xd2
        vpternlogq xmm23, xmm15, xmm12, 0xd2
        vpternlogq xmm15, xmm12, xmm30, 0xd2
        vpternlogq xmm12, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm21
        vmovdqa64 xmm31, xmm18
        vpternlogq xmm21, xmm18, xmm10, 0xd2
        vpternlogq xmm18, xmm10, xmm7, 0xd2
        vpternlogq xmm10, xmm7, xmm4, 0xd2
        vpternlogq xmm7, xmm4, xmm30, 0xd2
        vpternlogq xmm4, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm13
        vmovdqa64 xmm31, xmm5
        vpternlogq xmm13, xmm5, xmm2, 0xd2
        vpternlogq xmm5, xmm2, xmm24, 0xd2
        vpternlogq xmm2, xmm24, xmm16, 0xd2
        vpternlogq xmm24, xmm16, xmm30, 0xd2
        vpternlogq xmm16, xmm30, xmm31, 0xd2

// Round 4 of 4: theta

        vmovdqa64 xmm25, xmm0
        vpternlogq xmm25, xmm17, xmm9, 0x96
        vpternlogq xmm25, xmm21, xmm13, 0x96
        vmovdqa64 xmm26, xmm22
        vpternlogq xmm26, xmm14, xmm1, 0x96
        vpternlogq xmm26, xmm18, xmm5, 0x96
        vmovdqa64 xmm27, xmm19
        vpternlogq xmm27, xmm6, xmm23, 0x96
        vpternlogq xmm27, xmm10, xmm2, 0x96
        vmovdqa64 xmm28, xmm11
        vpternlogq xmm28, xmm3, xmm15, 0x96
        vpternlogq xmm28, xmm7, xmm24, 0x96
        vmovdqa64 xmm29, xmm8
        vpternlogq xmm29, xmm20, xmm12, 0x96
        vpternlogq xmm29, xmm4, xmm16, 0x96
        vprolq  xmm30, xmm26, 1
        vpternlogq xmm0, xmm29, xmm30, 0x96
        vpternlogq xmm17, xmm29, xmm30, 0x96
        vpternlogq xmm9, xmm29, xmm30, 0x96
        vpternlogq xmm21, xmm29, xmm30, 0x96
        vpternlogq xmm13, xmm29, xmm30, 0x96
        vprolq  xmm30, xmm27, 1
        vpternlogq xmm22, xmm25, xmm30, 0x96
        vpternlogq xmm14, xmm25, xmm30, 0x96
        vpternlogq xmm1, xmm25, xmm30, 0x96
        vpternlogq xmm18, xmm25, xmm30, 0x96
        vpternlogq xmm5, xmm25, xmm30, 0x96
        vprolq  xmm30, xmm28, 1
        vpternlogq xmm19, xmm26, xmm30, 0x96
        vpternlogq xmm6, xmm26, xmm30, 0x96
        vpternlogq xmm23, xmm26, xmm30, 0x96
        vpternlogq xmm10, xmm26, xmm30, 0x96
        vpternlogq xmm2, xmm26, xmm30, 0x96
        vprolq  xmm30, xmm29, 1
        vpternlogq xmm11, xmm27, xmm30, 0x96
        vpternlogq xmm3, xmm27, xmm30, 0x96
        vpternlogq xmm15, xmm27, xmm30, 0x96
        vpternlogq xmm7, xmm27, xmm30, 0x96
        vpternlogq xmm24, xmm27, xmm30, 0x96
        vprolq  xmm30, xmm25, 1
        vpternlogq xmm8, xmm28, xmm30, 0x96
        vpternlogq xmm20, xmm28, xmm30, 0x96
        vpternlogq xmm12, xmm28, xmm30, 0x96
        vpternlogq xmm4, xmm28, xmm30, 0x96
        vpternlogq xmm16, xmm28, xmm30, 0x96

// rho

        vprolq  xmm17, xmm17, 36
        vprolq  xmm9, xmm9, 3
        vprolq  xmm21, xmm21, 41
        vprolq  xmm13, xmm13, 18
        vprolq  xmm22, xmm22, 1
        vprolq  xmm14, xmm14, 44
        vprolq  xmm1, xmm1, 10
        vprolq  xmm18, xmm18, 45
        vprolq  xmm5, xmm5, 2
        vprolq  xmm19, xmm19, 62
        vprolq  xmm6, xmm6, 6
        vprolq  xmm23, xmm23, 43
        vprolq  xmm10, xmm10, 15
        vprolq  xmm2, xmm2, 61
        vprolq  xmm11, xmm11, 28
        vprolq  xmm3, xmm3, 55
        vprolq  xmm15, xmm15, 25
        vprolq  xmm7, xmm7, 21
        vprolq  xmm24, xmm24, 56
        vprolq  xmm8, xmm8, 27
        vprolq  xmm20, xmm20, 20
        vprolq  xmm12, xmm12, 39
        vprolq  xmm4, xmm4, 8
        vprolq  xmm16, xmm16, 14

// pi (renaming the registers), chi and iota

        vmovdqa64 xmm30, xmm0
        vmovdqa64 xmm31, xmm14
        vpternlogq xmm0, xmm14, xmm23, 0xd2
        vpxorq  xmm0, xmm0, QWORD PTR [rsi+24]{1to2}
        vpternlogq xmm14, xmm23, xmm7, 0xd2
        vpternlogq xmm23, xmm7, xmm16, 0xd2
        vpternlogq xmm7, xmm16, xmm30, 0xd2
        vpternlogq xmm16, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm11
        vmovdqa64 xmm31, xmm20
        vpternlogq xmm11, xmm20, xmm9, 0xd2
        vpternlogq xmm20, xmm9, xmm18, 0xd2
        vpternlogq xmm9, xmm18, xmm2, 0xd2
        vpternlogq xmm18, xmm2, xmm30, 0xd2
        vpternlogq xmm2, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm22
        vmovdqa64 xmm31, xmm6
        vpternlogq xmm22, xmm6, xmm15, 0xd2
        vpternlogq xmm6, xmm15, xmm4, 0xd2
        vpternlogq xmm15, xmm4, xmm13, 0xd2
        vpternlogq xmm4, xmm13, xmm30, 0xd2
        vpternlogq xmm13, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm8
        vmovdqa64 xmm31, xmm17
        vpternlogq xmm8, xmm17, xmm1, 0xd2
        vpternlogq xmm17, xmm1, xmm10, 0xd2
        vpternlogq xmm1, xmm10, xmm24, 0xd2
        vpternlogq xmm10, xmm24, xmm30, 0xd2
        vpternlogq xmm24, xmm30, xmm31, 0xd2
        vmovdqa64 xmm30, xmm19
        vmovdqa64 xmm31, xmm3
        vpternlogq xmm19, xmm3, xmm12, 0xd2
        vpternlogq xmm3, xmm12, xmm21, 0xd2
        vpternlogq xmm12, xmm21, xmm5, 0xd2
        vpternlogq xmm21, xmm5, xmm30, 0xd2
        vpternlogq xmm5, xmm30, xmm31, 0xd2

// Restore lane i to register i

        vmovdqa64 xmm30, xmm1
        vmovdqa   xmm1, xmm14
        vmovdqa   xmm14, xmm13
        vmovdqa   xmm13, xmm4
        vmovdqa64 xmm4, xmm16
        vmovdqa64 xmm16, xmm17
        vmovdqa64 xmm17, xmm30
        vmovdqa64 xmm30, xmm2
        vmovdqa64 xmm2, xmm23
        vmovdqa64 xmm23, xmm21
        vmovdqa64 xmm21, xmm3
        vmovdqa   xmm3, xmm7
        vmovdqa   xmm7, xmm9
        vmovdqa64 xmm9, xmm30
        vmovdqa64 xmm30, xmm5
        vmovdqa   xmm5, xmm11
        vmovdqa   xmm11, xmm6
        vmovdqa64 xmm6, xmm20
        vmovdqa64 xmm20, xmm19
        vmovdqa64 xmm19, xmm24
        vmovdqa64 xmm24, xmm30
        vmovdqa64 xmm30, xmm8
        vmovdqa64 xmm8, xmm18
        vmovdqa64 xmm18, xmm10
        vmovdqa64 xmm10, xmm22
        vmovdqa64 xmm22, xmm12
        vmovdqa   xmm12, xmm15
        vmovdqa64 xmm15, xmm30

        add     rsi, 32
        cmp     rsi, rax
        jne     Lsha3_keccak_f1600_avx512_loop

// Store the state

        vmovq   QWORD PTR [rdi+0], xmm0
        vmovq   QWORD PTR [rdi+8], xmm1
        vmovq   QWORD PTR [rdi+16], xmm2
        vmovq   QWORD PTR [rdi+24], xmm3
        vmovq   QWORD PTR [rdi+32], xmm4
        vmovq   QWORD PTR [rdi+40], xmm5
        vmovq   QWORD PTR [rdi+48], xmm6
        vmovq   QWORD PTR [rdi+56], xmm7
        vmovq   QWORD PTR [rdi+64], xmm8
        vmovq   QWORD PTR [rdi+72], xmm9
        vmovq   QWORD PTR [rdi+80], xmm10
        vmovq   QWORD PTR [rdi+88], xmm11
        vmovq   QWORD PTR [rdi+96], xmm12
        vmovq   QWORD PTR [rdi+104], xmm13
        vmovq   QWORD PTR [rdi+112], xmm14
        vmovq   QWORD PTR [rdi+120], xmm15
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x47, 0x10  // vmovq QWORD PTR [rdi+128], xmm16
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x4f, 0x11  // vmovq QWORD PTR [rdi+136], xmm17
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x57, 0x12  // vmovq QWORD PTR [rdi+144], xmm18
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x5f, 0x13  // vmovq QWORD PTR [rdi+152], xmm19
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x67, 0x14  // vmovq QWORD PTR [rdi+160], xmm20
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x6f, 0x15  // vmovq QWORD PTR [rdi+168], xmm21
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x77, 0x16  // vmovq QWORD PTR [rdi+176], xmm22
        .byte   0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x7f, 0x17  // vmovq QWORD PTR [rdi+184], xmm23
        .byte   0x62, 0x61, 0xfd, 0x08, 0x7e, 0x47, 0x18  // vmovq QWORD PTR [rdi+192], xmm24

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOADU(xmm11,80)
        CFI_STACKLOADU(xmm12,96)
        CFI_STACKLOADU(xmm13,112)
        CFI_STACKLOADU(xmm14,128)
        CFI_STACKLOADU(xmm15,144)
        CFI_STACKLOAD(rdi,160)
        CFI_STACKLOAD(rsi,168)
        CFI_INC_RSP(176)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha3_keccak_f1600_avx512)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
