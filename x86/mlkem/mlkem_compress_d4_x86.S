// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 4 bits and pack them
// Inputs a[256] (signed 16-bit words), data[32] (bytes);
// output r[128] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^4 / 3329) mod 2^4 (Compress_4 of FIPS
// 203, section 4.2.1), and the 256 results are packed 4 bits each in
// order, least significant first (ByteEncode_4), as in mlkem-native's
// mlk_poly_compress_d4. The table data is mlkem-native's
// mlk_compress_d4_data (as in the mlkem_native2 constants block), and
// a and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_compress_d4_avx2_asm, unchanged.
//
// extern void mlkem_compress_d4_x86(uint8_t r[S2N_BIGNUM_STATIC 128],
//                                   const int16_t a[S2N_BIGNUM_STATIC 256],
//                                   const uint8_t data[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d4_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d4_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d4_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_compress_d4_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(64)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVE(rdi,48)
        CFI_STACKSAVE(rsi,56)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        mov     eax, 0x4ebf4ebf
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        mov     eax, 0x2000200
        vmovd   xmm1, eax
        vpbroadcastd ymm1, xmm1
        mov     eax, 0xf000f
        vmovd   xmm2, eax
        vpbroadcastd ymm2, xmm2
        mov     eax, 0x10011001
        vmovd   xmm3, eax
        vpbroadcastd ymm3, xmm3
        vmovdqa ymm4, [rdx]
        vmovdqa ymm5, [rsi]
        vmovdqa ymm6, [rsi+0x20]
        vmovdqa ymm7, [rsi+0x40]
        vmovdqa ymm8, [rsi+0x60]
        vpmulhw ymm5, ymm5, ymm0
        vpmulhw ymm6, ymm6, ymm0
        vpmulhw ymm7, ymm7, ymm0
        vpmulhw ymm8, ymm8, ymm0
        vpmulhrsw ymm5, ymm5, ymm1
        vpmulhrsw ymm6, ymm6, ymm1
        vpmulhrsw ymm7, ymm7, ymm1
        vpmulhrsw ymm8, ymm8, ymm1
        vpand   ymm5, ymm5, ymm2
        vpand   ymm6, ymm6, ymm2
        vpand   ymm7, ymm7, ymm2
        vpand   ymm8, ymm8, ymm2
        vpackuswb ymm5, ymm5, ymm6
        vpackuswb ymm7, ymm7, ymm8
        vpmaddubsw ymm5, ymm5, ymm3
        vpmaddubsw ymm7, ymm7, ymm3
        vpackuswb ymm5, ymm5, ymm7
        vpermd  ymm5, ymm4, ymm5
        vmovdqu [rdi], ymm5
        vmovdqa ymm5, [rsi+0x80]
        vmovdqa ymm6, [rsi+0xa0]
        vmovdqa ymm7, [rsi+0xc0]
        vmovdqa ymm8, [rsi+0xe0]
        vpmulhw ymm5, ymm5, ymm0
        vpmulhw ymm6, ymm6, ymm0
        vpmulhw ymm7, ymm7, ymm0
        vpmulhw ymm8, ymm8, ymm0
        vpmulhrsw ymm5, ymm5, ymm1
        vpmulhrsw ymm6, ymm6, ymm1
        vpmulhrsw ymm7, ymm7, ymm1
        vpmulhrsw ymm8, ymm8, ymm1
        vpand   ymm5, ymm5, ymm2
        vpand   ymm6, ymm6, ymm2
        vpand   ymm7, ymm7, ymm2
        vpand   ymm8, ymm8, ymm2
        vpackuswb ymm5, ymm5, ymm6
        vpackuswb ymm7, ymm7, ymm8
        vpmaddubsw ymm5, ymm5, ymm3
        vpmaddubsw ymm7, ymm7, ymm3
        vpackuswb ymm5, ymm5, ymm7
        vpermd  ymm5, ymm4, ymm5
        vmovdqu [rdi+0x20], ymm5
        vmovdqa ymm5, [rsi+0x100]
        vmovdqa ymm6, [rsi+0x120]
        vmovdqa ymm7, [rsi+0x140]
        vmovdqa ymm8, [rsi+0x160]
        vpmulhw ymm5, ymm5, ymm0
        vpmulhw ymm6, ymm6, ymm0
        vpmulhw ymm7, ymm7, ymm0
        vpmulhw ymm8, ymm8, ymm0
        vpmulhrsw ymm5, ymm5, ymm1
        vpmulhrsw ymm6, ymm6, ymm1
        vpmulhrsw ymm7, ymm7, ymm1
        vpmulhrsw ymm8, ymm8, ymm1
        vpand   ymm5, ymm5, ymm2
        vpand   ymm6, ymm6, ymm2
        vpand   ymm7, ymm7, ymm2
        vpand   ymm8, ymm8, ymm2
        vpackuswb ymm5, ymm5, ymm6
        vpackuswb ymm7, ymm7, ymm8
        vpmaddubsw ymm5, ymm5, ymm3
        vpmaddubsw ymm7, ymm7, ymm3
        vpackuswb ymm5, ymm5, ymm7
        vpermd  ymm5, ymm4, ymm5
        vmovdqu [rdi+0x40], ymm5
        vmovdqa ymm5, [rsi+0x180]
        vmovdqa ymm6, [rsi+0x1a0]
        vmovdqa ymm7, [rsi+0x1c0]
        vmovdqa ymm8, [rsi+0x1e0]
        vpmulhw ymm5, ymm5, ymm0
        vpmulhw ymm6, ymm6, ymm0
        vpmulhw ymm7, ymm7, ymm0
        vpmulhw ymm8, ymm8, ymm0
        vpmulhrsw ymm5, ymm5, ymm1
        vpmulhrsw ymm6, ymm6, ymm1
        vpmulhrsw ymm7, ymm7, ymm1
        vpmulhrsw ymm8, ymm8, ymm1
        vpand   ymm5, ymm5, ymm2
        vpand   ymm6, ymm6, ymm2
        vpand   ymm7, ymm7, ymm2
        vpand   ymm8, ymm8, ymm2
        vpackuswb ymm5, ymm5, ymm6
        vpackuswb ymm7, ymm7, ymm8
        vpmaddubsw ymm5, ymm5, ymm3
        vpmaddubsw ymm7, ymm7, ymm3
        vpackuswb ymm5, ymm5, ymm7
        vpermd  ymm5, ymm4, ymm5
        vmovdqu [rdi+0x60], ymm5
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOAD(rdi,48)
        CFI_STACKLOAD(rsi,56)
        CFI_INC_RSP(64)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d4_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
