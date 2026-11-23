// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, batch of four independent operations,
// with AVX-512VL
// Input a[100], rc[24]; output a[100]
//
// The input/output argument is in effect four 25-element Keccak arrays
// a[0..24], a[25..49], a[50..74] and a[75..99], each replaced by its
// Keccak-f1600 permutation, with the round constants rc, as by
// sha3_keccak4_f1600_alt (this is the same function, for processors with
// AVX-512F and AVX-512VL). The four states are transposed into 25 ymm
// registers, lane i of state j in quadword j of register i, permuted
// there with vprolq and vpternlogq and no spills, and transposed back.
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
// extern void sha3_keccak4_f1600_avx512
//   (uint64_t a[S2N_BIGNUM_STATIC 100],
//    const uint64_t rc[S2N_BIGNUM_STATIC 24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak4_f1600_avx512)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak4_f1600_avx512)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak4_f1600_avx512)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak4_f1600_avx512):
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

// Transpose the four states into ymm0..ymm24, four lanes at a time, and
// lane 24 by itself

        vmovdqu64 ymm25, [rdi+0]
        vmovdqu64 ymm26, [rdi+200]
        vmovdqu64 ymm27, [rdi+400]
        vmovdqu64 ymm28, [rdi+600]
        vpunpcklqdq ymm29, ymm25, ymm26
        vpunpckhqdq ymm30, ymm25, ymm26
        vpunpcklqdq ymm31, ymm27, ymm28
        vpunpckhqdq ymm25, ymm27, ymm28
        vshufi64x2 ymm0, ymm29, ymm31, 0x0
        vshufi64x2 ymm1, ymm30, ymm25, 0x0
        vshufi64x2 ymm2, ymm29, ymm31, 0x3
        vshufi64x2 ymm3, ymm30, ymm25, 0x3
        vmovdqu64 ymm25, [rdi+32]
        vmovdqu64 ymm26, [rdi+232]
        vmovdqu64 ymm27, [rdi+432]
        vmovdqu64 ymm28, [rdi+632]
        vpunpcklqdq ymm29, ymm25, ymm26
        vpunpckhqdq ymm30, ymm25, ymm26
        vpunpcklqdq ymm31, ymm27, ymm28
        vpunpckhqdq ymm25, ymm27, ymm28
        vshufi64x2 ymm4, ymm29, ymm31, 0x0
        vshufi64x2 ymm5, ymm30, ymm25, 0x0
        vshufi64x2 ymm6, ymm29, ymm31, 0x3
        vshufi64x2 ymm7, ymm30, ymm25, 0x3
        vmovdqu64 ymm25, [rdi+64]
        vmovdqu64 ymm26, [rdi+264]
        vmovdqu64 ymm27, [rdi+464]
        vmovdqu64 ymm28, [rdi+664]
        vpunpcklqdq ymm29, ymm25, ymm26
        vpunpckhqdq ymm30, ymm25, ymm26
        vpunpcklqdq ymm31, ymm27, ymm28
        vpunpckhqdq ymm25, ymm27, ymm28
        vshufi64x2 ymm8, ymm29, ymm31, 0x0
        vshufi64x2 ymm9, ymm30, ymm25, 0x0
        vshufi64x2 ymm10, ymm29, ymm31, 0x3
        vshufi64x2 ymm11, ymm30, ymm25, 0x3
        vmovdqu64 ymm25, [rdi+96]
        vmovdqu64 ymm26, [rdi+296]
        vmovdqu64 ymm27, [rdi+496]
        vmovdqu64 ymm28, [rdi+696]
        vpunpcklqdq ymm29, ymm25, ymm26
        vpunpckhqdq ymm30, ymm25, ymm26
        vpunpcklqdq ymm31, ymm27, ymm28
        vpunpckhqdq ymm25, ymm27, ymm28
        vshufi64x2 ymm12, ymm29, ymm31, 0x0
        vshufi64x2 ymm13, ymm30, ymm25, 0x0
        vshufi64x2 ymm14, ymm29, ymm31, 0x3
        vshufi64x2 ymm15, ymm30, ymm25, 0x3
        vmovdqu64 ymm25, [rdi+128]
        vmovdqu64 ymm26, [rdi+328]
        vmovdqu64 ymm27, [rdi+528]
        vmovdqu64 ymm28, [rdi+728]
        vpunpcklqdq ymm29, ymm25, ymm26
        vpunpckhqdq ymm30, ymm25, ymm26
        vpunpcklqdq ymm31, ymm27, ymm28
        vpunpckhqdq ymm25, ymm27, ymm28
        vshufi64x2 ymm16, ymm29, ymm31, 0x0
        vshufi64x2 ymm17, ymm30, ymm25, 0x0
        vshufi64x2 ymm18, ymm29, ymm31, 0x3
        vshufi64x2 ymm19, ymm30, ymm25, 0x3
        vmovdqu64 ymm25, [rdi+160]
        vmovdqu64 ymm26, [rdi+360]
        vmovdqu64 ymm27, [rdi+560]
        vmovdqu64 ymm28, [rdi+760]
        vpunpcklqdq ymm29, ymm25, ymm26
        vpunpckhqdq ymm30, ymm25, ymm26
        vpunpcklqdq ymm31, ymm27, ymm28
        vpunpckhqdq ymm25, ymm27, ymm28
        vshufi64x2 ymm20, ymm29, ymm31, 0x0
        vshufi64x2 ymm21, ymm30, ymm25, 0x0
        vshufi64x2 ymm22, ymm29, ymm31, 0x3
        vshufi64x2 ymm23, ymm30, ymm25, 0x3
        // The loads and stores of the lanes in xmm16 and up are written as bytes:
        // for vmovq with an EVEX-only register, GNU as and clang choose different
        // (equivalent) opcodes, 66 0F 6E/7E and F3 0F 7E/66 0F D6, and no syntax
        // selects one. These are the bytes that GNU as assembles.
        .byte   0x62, 0x61, 0xfd, 0x08, 0x6e, 0x47, 0x18  // vmovq xmm24, QWORD PTR [rdi+192]
        vpinsrq xmm24, xmm24, QWORD PTR [rdi+392], 1
        .byte   0x62, 0x61, 0xfd, 0x08, 0x6e, 0x4f, 0x4a  // vmovq xmm25, QWORD PTR [rdi+592]
        vpinsrq xmm25, xmm25, QWORD PTR [rdi+792], 1
        vinserti32x4 ymm24, ymm24, xmm25, 1

// The 24 rounds, four at a time

        lea     rax, [rsi+192]
Lsha3_keccak4_f1600_avx512_loop:

// Round 1 of 4: theta

        vmovdqa64 ymm25, ymm0
        vpternlogq ymm25, ymm5, ymm10, 0x96
        vpternlogq ymm25, ymm15, ymm20, 0x96
        vmovdqa64 ymm26, ymm1
        vpternlogq ymm26, ymm6, ymm11, 0x96
        vpternlogq ymm26, ymm16, ymm21, 0x96
        vmovdqa64 ymm27, ymm2
        vpternlogq ymm27, ymm7, ymm12, 0x96
        vpternlogq ymm27, ymm17, ymm22, 0x96
        vmovdqa64 ymm28, ymm3
        vpternlogq ymm28, ymm8, ymm13, 0x96
        vpternlogq ymm28, ymm18, ymm23, 0x96
        vmovdqa64 ymm29, ymm4
        vpternlogq ymm29, ymm9, ymm14, 0x96
        vpternlogq ymm29, ymm19, ymm24, 0x96
        vprolq  ymm30, ymm26, 1
        vpternlogq ymm0, ymm29, ymm30, 0x96
        vpternlogq ymm5, ymm29, ymm30, 0x96
        vpternlogq ymm10, ymm29, ymm30, 0x96
        vpternlogq ymm15, ymm29, ymm30, 0x96
        vpternlogq ymm20, ymm29, ymm30, 0x96
        vprolq  ymm30, ymm27, 1
        vpternlogq ymm1, ymm25, ymm30, 0x96
        vpternlogq ymm6, ymm25, ymm30, 0x96
        vpternlogq ymm11, ymm25, ymm30, 0x96
        vpternlogq ymm16, ymm25, ymm30, 0x96
        vpternlogq ymm21, ymm25, ymm30, 0x96
        vprolq  ymm30, ymm28, 1
        vpternlogq ymm2, ymm26, ymm30, 0x96
        vpternlogq ymm7, ymm26, ymm30, 0x96
        vpternlogq ymm12, ymm26, ymm30, 0x96
        vpternlogq ymm17, ymm26, ymm30, 0x96
        vpternlogq ymm22, ymm26, ymm30, 0x96
        vprolq  ymm30, ymm29, 1
        vpternlogq ymm3, ymm27, ymm30, 0x96
        vpternlogq ymm8, ymm27, ymm30, 0x96
        vpternlogq ymm13, ymm27, ymm30, 0x96
        vpternlogq ymm18, ymm27, ymm30, 0x96
        vpternlogq ymm23, ymm27, ymm30, 0x96
        vprolq  ymm30, ymm25, 1
        vpternlogq ymm4, ymm28, ymm30, 0x96
        vpternlogq ymm9, ymm28, ymm30, 0x96
        vpternlogq ymm14, ymm28, ymm30, 0x96
        vpternlogq ymm19, ymm28, ymm30, 0x96
        vpternlogq ymm24, ymm28, ymm30, 0x96

// rho

        vprolq  ymm5, ymm5, 36
        vprolq  ymm10, ymm10, 3
        vprolq  ymm15, ymm15, 41
        vprolq  ymm20, ymm20, 18
        vprolq  ymm1, ymm1, 1
        vprolq  ymm6, ymm6, 44
        vprolq  ymm11, ymm11, 10
        vprolq  ymm16, ymm16, 45
        vprolq  ymm21, ymm21, 2
        vprolq  ymm2, ymm2, 62
        vprolq  ymm7, ymm7, 6
        vprolq  ymm12, ymm12, 43
        vprolq  ymm17, ymm17, 15
        vprolq  ymm22, ymm22, 61
        vprolq  ymm3, ymm3, 28
        vprolq  ymm8, ymm8, 55
        vprolq  ymm13, ymm13, 25
        vprolq  ymm18, ymm18, 21
        vprolq  ymm23, ymm23, 56
        vprolq  ymm4, ymm4, 27
        vprolq  ymm9, ymm9, 20
        vprolq  ymm14, ymm14, 39
        vprolq  ymm19, ymm19, 8
        vprolq  ymm24, ymm24, 14

// pi (renaming the registers), chi and iota

        vmovdqa64 ymm30, ymm0
        vmovdqa64 ymm31, ymm6
        vpternlogq ymm0, ymm6, ymm12, 0xd2
        vpxorq  ymm0, ymm0, QWORD PTR [rsi+0]{1to4}
        vpternlogq ymm6, ymm12, ymm18, 0xd2
        vpternlogq ymm12, ymm18, ymm24, 0xd2
        vpternlogq ymm18, ymm24, ymm30, 0xd2
        vpternlogq ymm24, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm3
        vmovdqa64 ymm31, ymm9
        vpternlogq ymm3, ymm9, ymm10, 0xd2
        vpternlogq ymm9, ymm10, ymm16, 0xd2
        vpternlogq ymm10, ymm16, ymm22, 0xd2
        vpternlogq ymm16, ymm22, ymm30, 0xd2
        vpternlogq ymm22, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm1
        vmovdqa64 ymm31, ymm7
        vpternlogq ymm1, ymm7, ymm13, 0xd2
        vpternlogq ymm7, ymm13, ymm19, 0xd2
        vpternlogq ymm13, ymm19, ymm20, 0xd2
        vpternlogq ymm19, ymm20, ymm30, 0xd2
        vpternlogq ymm20, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm4
        vmovdqa64 ymm31, ymm5
        vpternlogq ymm4, ymm5, ymm11, 0xd2
        vpternlogq ymm5, ymm11, ymm17, 0xd2
        vpternlogq ymm11, ymm17, ymm23, 0xd2
        vpternlogq ymm17, ymm23, ymm30, 0xd2
        vpternlogq ymm23, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm2
        vmovdqa64 ymm31, ymm8
        vpternlogq ymm2, ymm8, ymm14, 0xd2
        vpternlogq ymm8, ymm14, ymm15, 0xd2
        vpternlogq ymm14, ymm15, ymm21, 0xd2
        vpternlogq ymm15, ymm21, ymm30, 0xd2
        vpternlogq ymm21, ymm30, ymm31, 0xd2

// Round 2 of 4: theta

        vmovdqa64 ymm25, ymm0
        vpternlogq ymm25, ymm3, ymm1, 0x96
        vpternlogq ymm25, ymm4, ymm2, 0x96
        vmovdqa64 ymm26, ymm6
        vpternlogq ymm26, ymm9, ymm7, 0x96
        vpternlogq ymm26, ymm5, ymm8, 0x96
        vmovdqa64 ymm27, ymm12
        vpternlogq ymm27, ymm10, ymm13, 0x96
        vpternlogq ymm27, ymm11, ymm14, 0x96
        vmovdqa64 ymm28, ymm18
        vpternlogq ymm28, ymm16, ymm19, 0x96
        vpternlogq ymm28, ymm17, ymm15, 0x96
        vmovdqa64 ymm29, ymm24
        vpternlogq ymm29, ymm22, ymm20, 0x96
        vpternlogq ymm29, ymm23, ymm21, 0x96
        vprolq  ymm30, ymm26, 1
        vpternlogq ymm0, ymm29, ymm30, 0x96
        vpternlogq ymm3, ymm29, ymm30, 0x96
        vpternlogq ymm1, ymm29, ymm30, 0x96
        vpternlogq ymm4, ymm29, ymm30, 0x96
        vpternlogq ymm2, ymm29, ymm30, 0x96
        vprolq  ymm30, ymm27, 1
        vpternlogq ymm6, ymm25, ymm30, 0x96
        vpternlogq ymm9, ymm25, ymm30, 0x96
        vpternlogq ymm7, ymm25, ymm30, 0x96
        vpternlogq ymm5, ymm25, ymm30, 0x96
        vpternlogq ymm8, ymm25, ymm30, 0x96
        vprolq  ymm30, ymm28, 1
        vpternlogq ymm12, ymm26, ymm30, 0x96
        vpternlogq ymm10, ymm26, ymm30, 0x96
        vpternlogq ymm13, ymm26, ymm30, 0x96
        vpternlogq ymm11, ymm26, ymm30, 0x96
        vpternlogq ymm14, ymm26, ymm30, 0x96
        vprolq  ymm30, ymm29, 1
        vpternlogq ymm18, ymm27, ymm30, 0x96
        vpternlogq ymm16, ymm27, ymm30, 0x96
        vpternlogq ymm19, ymm27, ymm30, 0x96
        vpternlogq ymm17, ymm27, ymm30, 0x96
        vpternlogq ymm15, ymm27, ymm30, 0x96
        vprolq  ymm30, ymm25, 1
        vpternlogq ymm24, ymm28, ymm30, 0x96
        vpternlogq ymm22, ymm28, ymm30, 0x96
        vpternlogq ymm20, ymm28, ymm30, 0x96
        vpternlogq ymm23, ymm28, ymm30, 0x96
        vpternlogq ymm21, ymm28, ymm30, 0x96

// rho

        vprolq  ymm3, ymm3, 36
        vprolq  ymm1, ymm1, 3
        vprolq  ymm4, ymm4, 41
        vprolq  ymm2, ymm2, 18
        vprolq  ymm6, ymm6, 1
        vprolq  ymm9, ymm9, 44
        vprolq  ymm7, ymm7, 10
        vprolq  ymm5, ymm5, 45
        vprolq  ymm8, ymm8, 2
        vprolq  ymm12, ymm12, 62
        vprolq  ymm10, ymm10, 6
        vprolq  ymm13, ymm13, 43
        vprolq  ymm11, ymm11, 15
        vprolq  ymm14, ymm14, 61
        vprolq  ymm18, ymm18, 28
        vprolq  ymm16, ymm16, 55
        vprolq  ymm19, ymm19, 25
        vprolq  ymm17, ymm17, 21
        vprolq  ymm15, ymm15, 56
        vprolq  ymm24, ymm24, 27
        vprolq  ymm22, ymm22, 20
        vprolq  ymm20, ymm20, 39
        vprolq  ymm23, ymm23, 8
        vprolq  ymm21, ymm21, 14

// pi (renaming the registers), chi and iota

        vmovdqa64 ymm30, ymm0
        vmovdqa64 ymm31, ymm9
        vpternlogq ymm0, ymm9, ymm13, 0xd2
        vpxorq  ymm0, ymm0, QWORD PTR [rsi+8]{1to4}
        vpternlogq ymm9, ymm13, ymm17, 0xd2
        vpternlogq ymm13, ymm17, ymm21, 0xd2
        vpternlogq ymm17, ymm21, ymm30, 0xd2
        vpternlogq ymm21, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm18
        vmovdqa64 ymm31, ymm22
        vpternlogq ymm18, ymm22, ymm1, 0xd2
        vpternlogq ymm22, ymm1, ymm5, 0xd2
        vpternlogq ymm1, ymm5, ymm14, 0xd2
        vpternlogq ymm5, ymm14, ymm30, 0xd2
        vpternlogq ymm14, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm6
        vmovdqa64 ymm31, ymm10
        vpternlogq ymm6, ymm10, ymm19, 0xd2
        vpternlogq ymm10, ymm19, ymm23, 0xd2
        vpternlogq ymm19, ymm23, ymm2, 0xd2
        vpternlogq ymm23, ymm2, ymm30, 0xd2
        vpternlogq ymm2, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm24
        vmovdqa64 ymm31, ymm3
        vpternlogq ymm24, ymm3, ymm7, 0xd2
        vpternlogq ymm3, ymm7, ymm11, 0xd2
        vpternlogq ymm7, ymm11, ymm15, 0xd2
        vpternlogq ymm11, ymm15, ymm30, 0xd2
        vpternlogq ymm15, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm12
        vmovdqa64 ymm31, ymm16
        vpternlogq ymm12, ymm16, ymm20, 0xd2
        vpternlogq ymm16, ymm20, ymm4, 0xd2
        vpternlogq ymm20, ymm4, ymm8, 0xd2
        vpternlogq ymm4, ymm8, ymm30, 0xd2
        vpternlogq ymm8, ymm30, ymm31, 0xd2

// Round 3 of 4: theta

        vmovdqa64 ymm25, ymm0
        vpternlogq ymm25, ymm18, ymm6, 0x96
        vpternlogq ymm25, ymm24, ymm12, 0x96
        vmovdqa64 ymm26, ymm9
        vpternlogq ymm26, ymm22, ymm10, 0x96
        vpternlogq ymm26, ymm3, ymm16, 0x96
        vmovdqa64 ymm27, ymm13
        vpternlogq ymm27, ymm1, ymm19, 0x96
        vpternlogq ymm27, ymm7, ymm20, 0x96
        vmovdqa64 ymm28, ymm17
        vpternlogq ymm28, ymm5, ymm23, 0x96
        vpternlogq ymm28, ymm11, ymm4, 0x96
        vmovdqa64 ymm29, ymm21
        vpternlogq ymm29, ymm14, ymm2, 0x96
        vpternlogq ymm29, ymm15, ymm8, 0x96
        vprolq  ymm30, ymm26, 1
        vpternlogq ymm0, ymm29, ymm30, 0x96
        vpternlogq ymm18, ymm29, ymm30, 0x96
        vpternlogq ymm6, ymm29, ymm30, 0x96
        vpternlogq ymm24, ymm29, ymm30, 0x96
        vpternlogq ymm12, ymm29, ymm30, 0x96
        vprolq  ymm30, ymm27, 1
        vpternlogq ymm9, ymm25, ymm30, 0x96
        vpternlogq ymm22, ymm25, ymm30, 0x96
        vpternlogq ymm10, ymm25, ymm30, 0x96
        vpternlogq ymm3, ymm25, ymm30, 0x96
        vpternlogq ymm16, ymm25, ymm30, 0x96
        vprolq  ymm30, ymm28, 1
        vpternlogq ymm13, ymm26, ymm30, 0x96
        vpternlogq ymm1, ymm26, ymm30, 0x96
        vpternlogq ymm19, ymm26, ymm30, 0x96
        vpternlogq ymm7, ymm26, ymm30, 0x96
        vpternlogq ymm20, ymm26, ymm30, 0x96
        vprolq  ymm30, ymm29, 1
        vpternlogq ymm17, ymm27, ymm30, 0x96
        vpternlogq ymm5, ymm27, ymm30, 0x96
        vpternlogq ymm23, ymm27, ymm30, 0x96
        vpternlogq ymm11, ymm27, ymm30, 0x96
        vpternlogq ymm4, ymm27, ymm30, 0x96
        vprolq  ymm30, ymm25, 1
        vpternlogq ymm21, ymm28, ymm30, 0x96
        vpternlogq ymm14, ymm28, ymm30, 0x96
        vpternlogq ymm2, ymm28, ymm30, 0x96
        vpternlogq ymm15, ymm28, ymm30, 0x96
        vpternlogq ymm8, ymm28, ymm30, 0x96

// rho

        vprolq  ymm18, ymm18, 36
        vprolq  ymm6, ymm6, 3
        vprolq  ymm24, ymm24, 41
        vprolq  ymm12, ymm12, 18
        vprolq  ymm9, ymm9, 1
        vprolq  ymm22, ymm22, 44
        vprolq  ymm10, ymm10, 10
        vprolq  ymm3, ymm3, 45
        vprolq  ymm16, ymm16, 2
        vprolq  ymm13, ymm13, 62
        vprolq  ymm1, ymm1, 6
        vprolq  ymm19, ymm19, 43
        vprolq  ymm7, ymm7, 15
        vprolq  ymm20, ymm20, 61
        vprolq  ymm17, ymm17, 28
        vprolq  ymm5, ymm5, 55
        vprolq  ymm23, ymm23, 25
        vprolq  ymm11, ymm11, 21
        vprolq  ymm4, ymm4, 56
        vprolq  ymm21, ymm21, 27
        vprolq  ymm14, ymm14, 20
        vprolq  ymm2, ymm2, 39
        vprolq  ymm15, ymm15, 8
        vprolq  ymm8, ymm8, 14

// pi (renaming the registers), chi and iota

        vmovdqa64 ymm30, ymm0
        vmovdqa64 ymm31, ymm22
        vpternlogq ymm0, ymm22, ymm19, 0xd2
        vpxorq  ymm0, ymm0, QWORD PTR [rsi+16]{1to4}
        vpternlogq ymm22, ymm19, ymm11, 0xd2
        vpternlogq ymm19, ymm11, ymm8, 0xd2
        vpternlogq ymm11, ymm8, ymm30, 0xd2
        vpternlogq ymm8, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm17
        vmovdqa64 ymm31, ymm14
        vpternlogq ymm17, ymm14, ymm6, 0xd2
        vpternlogq ymm14, ymm6, ymm3, 0xd2
        vpternlogq ymm6, ymm3, ymm20, 0xd2
        vpternlogq ymm3, ymm20, ymm30, 0xd2
        vpternlogq ymm20, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm9
        vmovdqa64 ymm31, ymm1
        vpternlogq ymm9, ymm1, ymm23, 0xd2
        vpternlogq ymm1, ymm23, ymm15, 0xd2
        vpternlogq ymm23, ymm15, ymm12, 0xd2
        vpternlogq ymm15, ymm12, ymm30, 0xd2
        vpternlogq ymm12, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm21
        vmovdqa64 ymm31, ymm18
        vpternlogq ymm21, ymm18, ymm10, 0xd2
        vpternlogq ymm18, ymm10, ymm7, 0xd2
        vpternlogq ymm10, ymm7, ymm4, 0xd2
        vpternlogq ymm7, ymm4, ymm30, 0xd2
        vpternlogq ymm4, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm13
        vmovdqa64 ymm31, ymm5
        vpternlogq ymm13, ymm5, ymm2, 0xd2
        vpternlogq ymm5, ymm2, ymm24, 0xd2
        vpternlogq ymm2, ymm24, ymm16, 0xd2
        vpternlogq ymm24, ymm16, ymm30, 0xd2
        vpternlogq ymm16, ymm30, ymm31, 0xd2

// Round 4 of 4: theta

        vmovdqa64 ymm25, ymm0
        vpternlogq ymm25, ymm17, ymm9, 0x96
        vpternlogq ymm25, ymm21, ymm13, 0x96
        vmovdqa64 ymm26, ymm22
        vpternlogq ymm26, ymm14, ymm1, 0x96
        vpternlogq ymm26, ymm18, ymm5, 0x96
        vmovdqa64 ymm27, ymm19
        vpternlogq ymm27, ymm6, ymm23, 0x96
        vpternlogq ymm27, ymm10, ymm2, 0x96
        vmovdqa64 ymm28, ymm11
        vpternlogq ymm28, ymm3, ymm15, 0x96
        vpternlogq ymm28, ymm7, ymm24, 0x96
        vmovdqa64 ymm29, ymm8
        vpternlogq ymm29, ymm20, ymm12, 0x96
        vpternlogq ymm29, ymm4, ymm16, 0x96
        vprolq  ymm30, ymm26, 1
        vpternlogq ymm0, ymm29, ymm30, 0x96
        vpternlogq ymm17, ymm29, ymm30, 0x96
        vpternlogq ymm9, ymm29, ymm30, 0x96
        vpternlogq ymm21, ymm29, ymm30, 0x96
        vpternlogq ymm13, ymm29, ymm30, 0x96
        vprolq  ymm30, ymm27, 1
        vpternlogq ymm22, ymm25, ymm30, 0x96
        vpternlogq ymm14, ymm25, ymm30, 0x96
        vpternlogq ymm1, ymm25, ymm30, 0x96
        vpternlogq ymm18, ymm25, ymm30, 0x96
        vpternlogq ymm5, ymm25, ymm30, 0x96
        vprolq  ymm30, ymm28, 1
        vpternlogq ymm19, ymm26, ymm30, 0x96
        vpternlogq ymm6, ymm26, ymm30, 0x96
        vpternlogq ymm23, ymm26, ymm30, 0x96
        vpternlogq ymm10, ymm26, ymm30, 0x96
        vpternlogq ymm2, ymm26, ymm30, 0x96
        vprolq  ymm30, ymm29, 1
        vpternlogq ymm11, ymm27, ymm30, 0x96
        vpternlogq ymm3, ymm27, ymm30, 0x96
        vpternlogq ymm15, ymm27, ymm30, 0x96
        vpternlogq ymm7, ymm27, ymm30, 0x96
        vpternlogq ymm24, ymm27, ymm30, 0x96
        vprolq  ymm30, ymm25, 1
        vpternlogq ymm8, ymm28, ymm30, 0x96
        vpternlogq ymm20, ymm28, ymm30, 0x96
        vpternlogq ymm12, ymm28, ymm30, 0x96
        vpternlogq ymm4, ymm28, ymm30, 0x96
        vpternlogq ymm16, ymm28, ymm30, 0x96

// rho

        vprolq  ymm17, ymm17, 36
        vprolq  ymm9, ymm9, 3
        vprolq  ymm21, ymm21, 41
        vprolq  ymm13, ymm13, 18
        vprolq  ymm22, ymm22, 1
        vprolq  ymm14, ymm14, 44
        vprolq  ymm1, ymm1, 10
        vprolq  ymm18, ymm18, 45
        vprolq  ymm5, ymm5, 2
        vprolq  ymm19, ymm19, 62
        vprolq  ymm6, ymm6, 6
        vprolq  ymm23, ymm23, 43
        vprolq  ymm10, ymm10, 15
        vprolq  ymm2, ymm2, 61
        vprolq  ymm11, ymm11, 28
        vprolq  ymm3, ymm3, 55
        vprolq  ymm15, ymm15, 25
        vprolq  ymm7, ymm7, 21
        vprolq  ymm24, ymm24, 56
        vprolq  ymm8, ymm8, 27
        vprolq  ymm20, ymm20, 20
        vprolq  ymm12, ymm12, 39
        vprolq  ymm4, ymm4, 8
        vprolq  ymm16, ymm16, 14

// pi (renaming the registers), chi and iota

        vmovdqa64 ymm30, ymm0
        vmovdqa64 ymm31, ymm14
        vpternlogq ymm0, ymm14, ymm23, 0xd2
        vpxorq  ymm0, ymm0, QWORD PTR [rsi+24]{1to4}
        vpternlogq ymm14, ymm23, ymm7, 0xd2
        vpternlogq ymm23, ymm7, ymm16, 0xd2
        vpternlogq ymm7, ymm16, ymm30, 0xd2
        vpternlogq ymm16, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm11
        vmovdqa64 ymm31, ymm20
        vpternlogq ymm11, ymm20, ymm9, 0xd2
        vpternlogq ymm20, ymm9, ymm18, 0xd2
        vpternlogq ymm9, ymm18, ymm2, 0xd2
        vpternlogq ymm18, ymm2, ymm30, 0xd2
        vpternlogq ymm2, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm22
        vmovdqa64 ymm31, ymm6
        vpternlogq ymm22, ymm6, ymm15, 0xd2
        vpternlogq ymm6, ymm15, ymm4, 0xd2
        vpternlogq ymm15, ymm4, ymm13, 0xd2
        vpternlogq ymm4, ymm13, ymm30, 0xd2
        vpternlogq ymm13, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm8
        vmovdqa64 ymm31, ymm17
        vpternlogq ymm8, ymm17, ymm1, 0xd2
        vpternlogq ymm17, ymm1, ymm10, 0xd2
        vpternlogq ymm1, ymm10, ymm24, 0xd2
        vpternlogq ymm10, ymm24, ymm30, 0xd2
        vpternlogq ymm24, ymm30, ymm31, 0xd2
        vmovdqa64 ymm30, ymm19
        vmovdqa64 ymm31, ymm3
        vpternlogq ymm19, ymm3, ymm12, 0xd2
        vpternlogq ymm3, ymm12, ymm21, 0xd2
        vpternlogq ymm12, ymm21, ymm5, 0xd2
        vpternlogq ymm21, ymm5, ymm30, 0xd2
        vpternlogq ymm5, ymm30, ymm31, 0xd2

// Restore lane i to register i

        vmovdqa64 ymm30, ymm1
        vmovdqa   ymm1, ymm14
        vmovdqa   ymm14, ymm13
        vmovdqa   ymm13, ymm4
        vmovdqa64 ymm4, ymm16
        vmovdqa64 ymm16, ymm17
        vmovdqa64 ymm17, ymm30
        vmovdqa64 ymm30, ymm2
        vmovdqa64 ymm2, ymm23
        vmovdqa64 ymm23, ymm21
        vmovdqa64 ymm21, ymm3
        vmovdqa   ymm3, ymm7
        vmovdqa   ymm7, ymm9
        vmovdqa64 ymm9, ymm30
        vmovdqa64 ymm30, ymm5
        vmovdqa   ymm5, ymm11
        vmovdqa   ymm11, ymm6
        vmovdqa64 ymm6, ymm20
        vmovdqa64 ymm20, ymm19
        vmovdqa64 ymm19, ymm24
        vmovdqa64 ymm24, ymm30
        vmovdqa64 ymm30, ymm8
        vmovdqa64 ymm8, ymm18
        vmovdqa64 ymm18, ymm10
        vmovdqa64 ymm10, ymm22
        vmovdqa64 ymm22, ymm12
        vmovdqa   ymm12, ymm15
        vmovdqa64 ymm15, ymm30

        add     rsi, 32
        cmp     rsi, rax
        jne     Lsha3_keccak4_f1600_avx512_loop

// Transpose back and store the four states

        vpunpcklqdq ymm25, ymm0, ymm1
        vpunpckhqdq ymm26, ymm0, ymm1
        vpunpcklqdq ymm27, ymm2, ymm3
        vpunpckhqdq ymm28, ymm2, ymm3
        vshufi64x2 ymm29, ymm25, ymm27, 0x0
        vshufi64x2 ymm30, ymm26, ymm28, 0x0
        vshufi64x2 ymm31, ymm25, ymm27, 0x3
        vshufi64x2 ymm25, ymm26, ymm28, 0x3
        vmovdqu64 [rdi+0], ymm29
        vmovdqu64 [rdi+200], ymm30
        vmovdqu64 [rdi+400], ymm31
        vmovdqu64 [rdi+600], ymm25
        vpunpcklqdq ymm25, ymm4, ymm5
        vpunpckhqdq ymm26, ymm4, ymm5
        vpunpcklqdq ymm27, ymm6, ymm7
        vpunpckhqdq ymm28, ymm6, ymm7
        vshufi64x2 ymm29, ymm25, ymm27, 0x0
        vshufi64x2 ymm30, ymm26, ymm28, 0x0
        vshufi64x2 ymm31, ymm25, ymm27, 0x3
        vshufi64x2 ymm25, ymm26, ymm28, 0x3
        vmovdqu64 [rdi+32], ymm29
        vmovdqu64 [rdi+232], ymm30
        vmovdqu64 [rdi+432], ymm31
        vmovdqu64 [rdi+632], ymm25
        vpunpcklqdq ymm25, ymm8, ymm9
        vpunpckhqdq ymm26, ymm8, ymm9
        vpunpcklqdq ymm27, ymm10, ymm11
        vpunpckhqdq ymm28, ymm10, ymm11
        vshufi64x2 ymm29, ymm25, ymm27, 0x0
        vshufi64x2 ymm30, ymm26, ymm28, 0x0
        vshufi64x2 ymm31, ymm25, ymm27, 0x3
        vshufi64x2 ymm25, ymm26, ymm28, 0x3
        vmovdqu64 [rdi+64], ymm29
        vmovdqu64 [rdi+264], ymm30
        vmovdqu64 [rdi+464], ymm31
        vmovdqu64 [rdi+664], ymm25
        vpunpcklqdq ymm25, ymm12, ymm13
        vpunpckhqdq ymm26, ymm12, ymm13
        vpunpcklqdq ymm27, ymm14, ymm15
        vpunpckhqdq ymm28, ymm14, ymm15
        vshufi64x2 ymm29, ymm25, ymm27, 0x0
        vshufi64x2 ymm30, ymm26, ymm28, 0x0
        vshufi64x2 ymm31, ymm25, ymm27, 0x3
        vshufi64x2 ymm25, ymm26, ymm28, 0x3
        vmovdqu64 [rdi+96], ymm29
        vmovdqu64 [rdi+296], ymm30
        vmovdqu64 [rdi+496], ymm31
        vmovdqu64 [rdi+696], ymm25
        vpunpcklqdq ymm25, ymm16, ymm17
        vpunpckhqdq ymm26, ymm16, ymm17
        vpunpcklqdq ymm27, ymm18, ymm19
        vpunpckhqdq ymm28, ymm18, ymm19
        vshufi64x2 ymm29, ymm25, ymm27, 0x0
        vshufi64x2 ymm30, ymm26, ymm28, 0x0
        vshufi64x2 ymm31, ymm25, ymm27, 0x3
        vshufi64x2 ymm25, ymm26, ymm28, 0x3
        vmovdqu64 [rdi+128], ymm29
        vmovdqu64 [rdi+328], ymm30
        vmovdqu64 [rdi+528], ymm31
        vmovdqu64 [rdi+728], ymm25
        vpunpcklqdq ymm25, ymm20, ymm21
        vpunpckhqdq ymm26, ymm20, ymm21
        vpunpcklqdq ymm27, ymm22, ymm23
        vpunpckhqdq ymm28, ymm22, ymm23
        vshufi64x2 ymm29, ymm25, ymm27, 0x0
        vshufi64x2 ymm30, ymm26, ymm28, 0x0
        vshufi64x2 ymm31, ymm25, ymm27, 0x3
        vshufi64x2 ymm25, ymm26, ymm28, 0x3
        vmovdqu64 [rdi+160], ymm29
        vmovdqu64 [rdi+360], ymm30
        vmovdqu64 [rdi+560], ymm31
        vmovdqu64 [rdi+760], ymm25
        .byte   0x62, 0x61, 0xfd, 0x08, 0x7e, 0x47, 0x18  // vmovq QWORD PTR [rdi+192], xmm24
        vpextrq QWORD PTR [rdi+392], xmm24, 1
        vextracti32x4 xmm25, ymm24, 1
        .byte   0x62, 0x61, 0xfd, 0x08, 0x7e, 0x4f, 0x4a  // vmovq QWORD PTR [rdi+592], xmm25
        vpextrq QWORD PTR [rdi+792], xmm25, 1

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

S2N_BN_SIZE_DIRECTIVE(sha3_keccak4_f1600_avx512)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
