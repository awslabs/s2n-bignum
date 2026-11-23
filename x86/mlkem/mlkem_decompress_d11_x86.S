// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Unpack 11-bit ML-KEM compressed coefficients and decompress them
// Inputs a[352], data[128] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 11-bit fields u[i], least significant first
// (ByteDecode_11), and each is mapped to round(u[i] * 3329 / 2^11),
// rounding halves up (Decompress_11 of FIPS 203, section 4.2.1), which
// is in the range 0 <= r[i] < 3329. This is mlkem-native's
// mlk_poly_decompress_d11. The table data is mlkem-native's
// mlk_decompress_d11_data (as in the mlkem_native2 constants block),
// and r and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_decompress_d11_avx2_asm, unchanged.
//
// extern void mlkem_decompress_d11_x86(int16_t r[S2N_BIGNUM_STATIC 256],
//     const uint8_t a[S2N_BIGNUM_STATIC 352],
//     const uint8_t data[S2N_BIGNUM_STATIC 128]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d11_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d11_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d11_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_decompress_d11_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(48)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVE(rdi,32)
        CFI_STACKSAVE(rsi,40)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        mov     eax, 0xd010d01
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        mov     eax, 0x7ff07ff0
        vmovd   xmm1, eax
        vpbroadcastd ymm1, xmm1
        vmovdqa ymm2, [rdx]
        vmovdqa ymm3, [rdx+0x20]
        vmovdqa ymm4, [rdx+0x40]
        vmovdqa ymm5, [rdx+0x60]
        vmovdqu xmm6, [rsi]
        vmovd   xmm7, DWORD PTR [rsi+0x10]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x14], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi], ymm6
        vmovdqu xmm6, [rsi+0x16]
        vmovd   xmm7, DWORD PTR [rsi+0x26]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x2a], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x20], ymm6
        vmovdqu xmm6, [rsi+0x2c]
        vmovd   xmm7, DWORD PTR [rsi+0x3c]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x40], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x40], ymm6
        vmovdqu xmm6, [rsi+0x42]
        vmovd   xmm7, DWORD PTR [rsi+0x52]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x56], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x60], ymm6
        vmovdqu xmm6, [rsi+0x58]
        vmovd   xmm7, DWORD PTR [rsi+0x68]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x6c], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x80], ymm6
        vmovdqu xmm6, [rsi+0x6e]
        vmovd   xmm7, DWORD PTR [rsi+0x7e]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x82], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0xa0], ymm6
        vmovdqu xmm6, [rsi+0x84]
        vmovd   xmm7, DWORD PTR [rsi+0x94]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x98], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0xc0], ymm6
        vmovdqu xmm6, [rsi+0x9a]
        vmovd   xmm7, DWORD PTR [rsi+0xaa]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0xae], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0xe0], ymm6
        vmovdqu xmm6, [rsi+0xb0]
        vmovd   xmm7, DWORD PTR [rsi+0xc0]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0xc4], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x100], ymm6
        vmovdqu xmm6, [rsi+0xc6]
        vmovd   xmm7, DWORD PTR [rsi+0xd6]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0xda], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x120], ymm6
        vmovdqu xmm6, [rsi+0xdc]
        vmovd   xmm7, DWORD PTR [rsi+0xec]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0xf0], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x140], ymm6
        vmovdqu xmm6, [rsi+0xf2]
        vmovd   xmm7, DWORD PTR [rsi+0x102]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x106], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x160], ymm6
        vmovdqu xmm6, [rsi+0x108]
        vmovd   xmm7, DWORD PTR [rsi+0x118]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x11c], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x180], ymm6
        vmovdqu xmm6, [rsi+0x11e]
        vmovd   xmm7, DWORD PTR [rsi+0x12e]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x132], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x1a0], ymm6
        vmovdqu xmm6, [rsi+0x134]
        vmovd   xmm7, DWORD PTR [rsi+0x144]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x148], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x1c0], ymm6
        vmovdqu xmm6, [rsi+0x14a]
        vmovd   xmm7, DWORD PTR [rsi+0x15a]
        vpinsrw xmm7, xmm7, WORD PTR [rsi+0x15e], 0x2
        vinserti128 ymm6, ymm6, xmm7, 0x1
        vpermq  ymm6, ymm6, 0x94
        vpshufb ymm6, ymm6, ymm2
        vpsrlvd ymm6, ymm6, ymm3
        vpsrlvq ymm6, ymm6, ymm4
        vpmullw ymm6, ymm6, ymm5
        vpsrlw  ymm6, ymm6, 0x1
        vpand   ymm6, ymm6, ymm1
        vpmulhrsw ymm6, ymm6, ymm0
        vmovdqu [rdi+0x1e0], ymm6
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOAD(rdi,32)
        CFI_STACKLOAD(rsi,40)
        CFI_INC_RSP(48)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d11_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
