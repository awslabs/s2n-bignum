// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 10 bits and pack them
// Inputs a[256] (signed 16-bit words), data[32] (bytes);
// output r[320] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^10 / 3329) mod 2^10 (Compress_10 of FIPS
// 203, section 4.2.1), and the 256 results are packed 10 bits each in
// order, least significant first (ByteEncode_10), as in mlkem-native's
// mlk_poly_compress_d10. The table data is mlkem-native's
// mlk_compress_d10_data (as in the mlkem_native2 constants block), and
// a and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_compress_d10_avx2_asm, unchanged.
//
// extern void mlkem_compress_d10_x86(uint8_t r[S2N_BIGNUM_STATIC 320],
//     const int16_t a[S2N_BIGNUM_STATIC 256],
//     const uint8_t data[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d10_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d10_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d10_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_compress_d10_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(96)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVE(rdi,80)
        CFI_STACKSAVE(rsi,88)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        mov     eax, 0x4ebf4ebf
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        vpsllw  ymm1, ymm0, 0x3
        mov     eax, 0xf000f
        vmovd   xmm2, eax
        vpbroadcastd ymm2, xmm2
        mov     eax, 0x10001000
        vmovd   xmm3, eax
        vpbroadcastd ymm3, xmm3
        mov     eax, 0x3ff03ff
        vmovd   xmm4, eax
        vpbroadcastd ymm4, xmm4
        movabs  rax, 0x400000104000001
        vmovq   xmm5, rax
        vpbroadcastq ymm5, xmm5
        mov     eax, 0xc
        vmovq   xmm6, rax
        vpbroadcastq ymm6, xmm6
        vmovdqa ymm7, [rdx]
        vmovdqa ymm8, [rsi]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi], xmm8
        vmovd   DWORD PTR [rdi+0x10], xmm9
        vmovdqa ymm8, [rsi+0x20]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x14], xmm8
        vmovd   DWORD PTR [rdi+0x24], xmm9
        vmovdqa ymm8, [rsi+0x40]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x28], xmm8
        vmovd   DWORD PTR [rdi+0x38], xmm9
        vmovdqa ymm8, [rsi+0x60]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x3c], xmm8
        vmovd   DWORD PTR [rdi+0x4c], xmm9
        vmovdqa ymm8, [rsi+0x80]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x50], xmm8
        vmovd   DWORD PTR [rdi+0x60], xmm9
        vmovdqa ymm8, [rsi+0xa0]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x64], xmm8
        vmovd   DWORD PTR [rdi+0x74], xmm9
        vmovdqa ymm8, [rsi+0xc0]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x78], xmm8
        vmovd   DWORD PTR [rdi+0x88], xmm9
        vmovdqa ymm8, [rsi+0xe0]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x8c], xmm8
        vmovd   DWORD PTR [rdi+0x9c], xmm9
        vmovdqa ymm8, [rsi+0x100]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0xa0], xmm8
        vmovd   DWORD PTR [rdi+0xb0], xmm9
        vmovdqa ymm8, [rsi+0x120]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0xb4], xmm8
        vmovd   DWORD PTR [rdi+0xc4], xmm9
        vmovdqa ymm8, [rsi+0x140]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0xc8], xmm8
        vmovd   DWORD PTR [rdi+0xd8], xmm9
        vmovdqa ymm8, [rsi+0x160]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0xdc], xmm8
        vmovd   DWORD PTR [rdi+0xec], xmm9
        vmovdqa ymm8, [rsi+0x180]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0xf0], xmm8
        vmovd   DWORD PTR [rdi+0x100], xmm9
        vmovdqa ymm8, [rsi+0x1a0]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x104], xmm8
        vmovd   DWORD PTR [rdi+0x114], xmm9
        vmovdqa ymm8, [rsi+0x1c0]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x118], xmm8
        vmovd   DWORD PTR [rdi+0x128], xmm9
        vmovdqa ymm8, [rsi+0x1e0]
        vpmullw ymm9, ymm8, ymm1
        vpaddw  ymm10, ymm8, ymm2
        vpsllw  ymm8, ymm8, 0x3
        vpmulhw ymm8, ymm8, ymm0
        vpsubw  ymm10, ymm9, ymm10
        vpandn  ymm9, ymm9, ymm10
        vpsrlw  ymm9, ymm9, 0xf
        vpsubw  ymm8, ymm8, ymm9
        vpmulhrsw ymm8, ymm8, ymm3
        vpand   ymm8, ymm8, ymm4
        vpmaddwd ymm8, ymm8, ymm5
        vpsllvd ymm8, ymm8, ymm6
        vpsrlq  ymm8, ymm8, 0xc
        vpshufb ymm8, ymm8, ymm7
        vextracti128 xmm9, ymm8, 0x1
        vpblendw xmm8, xmm8, xmm9, 0xe0
        vmovdqu [rdi+0x12c], xmm8
        vmovd   DWORD PTR [rdi+0x13c], xmm9
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOAD(rdi,80)
        CFI_STACKLOAD(rsi,88)
        CFI_INC_RSP(96)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d10_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
