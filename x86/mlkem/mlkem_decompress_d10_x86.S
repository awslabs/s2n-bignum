// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Unpack 10-bit ML-KEM compressed coefficients and decompress them
// Inputs a[320], data[32] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 10-bit fields u[i], least significant first
// (ByteDecode_10), and each is mapped to round(u[i] * 3329 / 2^10),
// rounding halves up (Decompress_10 of FIPS 203, section 4.2.1), which
// is in the range 0 <= r[i] < 3329. This is mlkem-native's
// mlk_poly_decompress_d10. The table data is mlkem-native's
// mlk_decompress_d10_data (as in the mlkem_native2 constants block),
// and r and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_decompress_d10_avx2_asm, unchanged.
//
// extern void mlkem_decompress_d10_x86(int16_t r[S2N_BIGNUM_STATIC 256],
//     const uint8_t a[S2N_BIGNUM_STATIC 320],
//     const uint8_t data[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d10_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d10_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d10_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_decompress_d10_x86):
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

        mov     eax, 0xd013404
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        mov     eax, 0x4
        vmovq   xmm1, rax
        vpbroadcastq ymm1, xmm1
        mov     eax, 0x7fe01ff8
        vmovd   xmm2, eax
        vpbroadcastd ymm2, xmm2
        vmovdqa ymm3, [rdx]
        vmovdqu xmm4, [rsi]
        vmovd   xmm5, DWORD PTR [rsi+0x10]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi], ymm4
        vmovdqu xmm4, [rsi+0x14]
        vmovd   xmm5, DWORD PTR [rsi+0x24]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x20], ymm4
        vmovdqu xmm4, [rsi+0x28]
        vmovd   xmm5, DWORD PTR [rsi+0x38]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x40], ymm4
        vmovdqu xmm4, [rsi+0x3c]
        vmovd   xmm5, DWORD PTR [rsi+0x4c]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x60], ymm4
        vmovdqu xmm4, [rsi+0x50]
        vmovd   xmm5, DWORD PTR [rsi+0x60]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x80], ymm4
        vmovdqu xmm4, [rsi+0x64]
        vmovd   xmm5, DWORD PTR [rsi+0x74]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0xa0], ymm4
        vmovdqu xmm4, [rsi+0x78]
        vmovd   xmm5, DWORD PTR [rsi+0x88]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0xc0], ymm4
        vmovdqu xmm4, [rsi+0x8c]
        vmovd   xmm5, DWORD PTR [rsi+0x9c]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0xe0], ymm4
        vmovdqu xmm4, [rsi+0xa0]
        vmovd   xmm5, DWORD PTR [rsi+0xb0]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x100], ymm4
        vmovdqu xmm4, [rsi+0xb4]
        vmovd   xmm5, DWORD PTR [rsi+0xc4]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x120], ymm4
        vmovdqu xmm4, [rsi+0xc8]
        vmovd   xmm5, DWORD PTR [rsi+0xd8]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x140], ymm4
        vmovdqu xmm4, [rsi+0xdc]
        vmovd   xmm5, DWORD PTR [rsi+0xec]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x160], ymm4
        vmovdqu xmm4, [rsi+0xf0]
        vmovd   xmm5, DWORD PTR [rsi+0x100]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x180], ymm4
        vmovdqu xmm4, [rsi+0x104]
        vmovd   xmm5, DWORD PTR [rsi+0x114]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x1a0], ymm4
        vmovdqu xmm4, [rsi+0x118]
        vmovd   xmm5, DWORD PTR [rsi+0x128]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x1c0], ymm4
        vmovdqu xmm4, [rsi+0x12c]
        vmovd   xmm5, DWORD PTR [rsi+0x13c]
        vinserti128 ymm4, ymm4, xmm5, 0x1
        vpermq  ymm4, ymm4, 0x94
        vpshufb ymm4, ymm4, ymm3
        vpsllvd ymm4, ymm4, ymm1
        vpsrlw  ymm4, ymm4, 0x1
        vpand   ymm4, ymm4, ymm2
        vpmulhrsw ymm4, ymm4, ymm0
        vmovdqu [rdi+0x1e0], ymm4
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(rdi,0)
        CFI_STACKLOAD(rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d10_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
