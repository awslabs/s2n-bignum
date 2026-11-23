// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Unpack 5-bit ML-KEM compressed coefficients and decompress them
// Inputs a[160], data[96] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 5-bit fields u[i], least significant first
// (ByteDecode_5), and each is mapped to round(u[i] * 3329 / 2^5),
// rounding halves up (Decompress_5 of FIPS 203, section 4.2.1), which
// is in the range 0 <= r[i] < 3329. This is mlkem-native's
// mlk_poly_decompress_d5. The table data is mlkem-native's
// mlk_decompress_d5_data (as in the mlkem_native2 constants block),
// and r and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_decompress_d5_avx2_asm, unchanged.
//
// extern void mlkem_decompress_d5_x86(int16_t r[S2N_BIGNUM_STATIC 256],
//     const uint8_t a[S2N_BIGNUM_STATIC 160],
//     const uint8_t data[S2N_BIGNUM_STATIC 96]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d5_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d5_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d5_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_decompress_d5_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(16)
        CFI_STACKSAVE(rdi,0)
        CFI_STACKSAVE(rsi,8)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        mov     eax, 0xd010d01
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        vmovdqa ymm1, [rdx]
        vmovdqa ymm2, [rdx+0x20]
        vmovdqa ymm3, [rdx+0x40]
        vmovq   xmm4, QWORD PTR [rsi]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x8], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0xa]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x12], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x20], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x14]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x1c], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x40], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x1e]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x26], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x60], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x28]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x30], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x80], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x32]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x3a], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0xa0], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x3c]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x44], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0xc0], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x46]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x4e], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0xe0], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x50]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x58], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x100], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x5a]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x62], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x120], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x64]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x6c], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x140], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x6e]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x76], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x160], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x78]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x80], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x180], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x82]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x8a], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x1a0], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x8c]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x94], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x1c0], ymm4
        vmovq   xmm4, QWORD PTR [rsi+0x96]
        vpinsrw xmm4, xmm4, WORD PTR [rsi+0x9e], 0x4
        vinserti128 ymm4, ymm4, xmm4, 0x1
        vpshufb ymm4, ymm4, ymm1
        vpand   ymm4, ymm4, ymm2
        vpmullw ymm4, ymm4, ymm3
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x1e0], ymm4
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(rdi,0)
        CFI_STACKLOAD(rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d5_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
