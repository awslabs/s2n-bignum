// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 11 bits and pack them
// Inputs a[256] (signed 16-bit words), data[64] (bytes);
// output r[352] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^11 / 3329) mod 2^11 (Compress_11 of FIPS
// 203, section 4.2.1), and the 256 results are packed 11 bits each in
// order, least significant first (ByteEncode_11), as in mlkem-native's
// mlk_poly_compress_d11. The table data is mlkem-native's
// mlk_compress_d11_data (as in the mlkem_native2 constants block), and
// a and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_compress_d11_avx2_asm, unchanged.
//
// extern void mlkem_compress_d11_x86(uint8_t r[S2N_BIGNUM_STATIC 352],
//     const int16_t a[S2N_BIGNUM_STATIC 256],
//     const uint8_t data[S2N_BIGNUM_STATIC 64]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d11_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d11_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d11_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_compress_d11_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(112)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVEU(xmm11,80)
        CFI_STACKSAVE(rdi,96)
        CFI_STACKSAVE(rsi,104)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        mov     eax, 0x4ebf4ebf
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        vpsllw  ymm1, ymm0, 0x3
        mov     eax, 0x240024
        vmovd   xmm2, eax
        vpbroadcastd ymm2, xmm2
        mov     eax, 0x20002000
        vmovd   xmm3, eax
        vpbroadcastd ymm3, xmm3
        mov     eax, 0x7ff07ff
        vmovd   xmm4, eax
        vpbroadcastd ymm4, xmm4
        movabs  rax, 0x800000108000001
        vmovq   xmm5, rax
        vpbroadcastq ymm5, xmm5
        mov     eax, 0xa
        vmovq   xmm6, rax
        vpbroadcastq ymm6, xmm6
        vmovdqa ymm7, [rdx]
        vmovdqa ymm8, [rdx+0x20]
        vmovdqa ymm9, [rsi]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi], xmm9
        vmovd   DWORD PTR [rdi+0x10], xmm10
        vpextrw WORD PTR [rdi+0x14], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x20]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x16], xmm9
        vmovd   DWORD PTR [rdi+0x26], xmm10
        vpextrw WORD PTR [rdi+0x2a], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x40]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x2c], xmm9
        vmovd   DWORD PTR [rdi+0x3c], xmm10
        vpextrw WORD PTR [rdi+0x40], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x60]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x42], xmm9
        vmovd   DWORD PTR [rdi+0x52], xmm10
        vpextrw WORD PTR [rdi+0x56], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x80]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x58], xmm9
        vmovd   DWORD PTR [rdi+0x68], xmm10
        vpextrw WORD PTR [rdi+0x6c], xmm10, 0x2
        vmovdqa ymm9, [rsi+0xa0]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x6e], xmm9
        vmovd   DWORD PTR [rdi+0x7e], xmm10
        vpextrw WORD PTR [rdi+0x82], xmm10, 0x2
        vmovdqa ymm9, [rsi+0xc0]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x84], xmm9
        vmovd   DWORD PTR [rdi+0x94], xmm10
        vpextrw WORD PTR [rdi+0x98], xmm10, 0x2
        vmovdqa ymm9, [rsi+0xe0]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x9a], xmm9
        vmovd   DWORD PTR [rdi+0xaa], xmm10
        vpextrw WORD PTR [rdi+0xae], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x100]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0xb0], xmm9
        vmovd   DWORD PTR [rdi+0xc0], xmm10
        vpextrw WORD PTR [rdi+0xc4], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x120]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0xc6], xmm9
        vmovd   DWORD PTR [rdi+0xd6], xmm10
        vpextrw WORD PTR [rdi+0xda], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x140]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0xdc], xmm9
        vmovd   DWORD PTR [rdi+0xec], xmm10
        vpextrw WORD PTR [rdi+0xf0], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x160]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0xf2], xmm9
        vmovd   DWORD PTR [rdi+0x102], xmm10
        vpextrw WORD PTR [rdi+0x106], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x180]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x108], xmm9
        vmovd   DWORD PTR [rdi+0x118], xmm10
        vpextrw WORD PTR [rdi+0x11c], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x1a0]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x11e], xmm9
        vmovd   DWORD PTR [rdi+0x12e], xmm10
        vpextrw WORD PTR [rdi+0x132], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x1c0]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x134], xmm9
        vmovd   DWORD PTR [rdi+0x144], xmm10
        vpextrw WORD PTR [rdi+0x148], xmm10, 0x2
        vmovdqa ymm9, [rsi+0x1e0]
        vpmullw ymm10, ymm9, ymm1
        vpaddw  ymm11, ymm9, ymm2
        vpsllw  ymm9, ymm9, 0x3
        vpmulhw ymm9, ymm9, ymm0
        vpsubw  ymm11, ymm10, ymm11
        vpandn  ymm10, ymm10, ymm11
        vpsrlw  ymm10, ymm10, 0xf
        vpsubw  ymm9, ymm9, ymm10
        vpmulhrsw ymm9, ymm9, ymm3
        vpand   ymm9, ymm9, ymm4
        vpmaddwd ymm9, ymm9, ymm5
        vpsllvd ymm9, ymm9, ymm6
        vpsrldq ymm10, ymm9, 0x8
        vpsrlvq ymm9, ymm9, ymm7
        vpsllq  ymm10, ymm10, 0x22
        vpaddq  ymm9, ymm9, ymm10
        vpshufb ymm9, ymm9, ymm8
        vextracti128 xmm10, ymm9, 0x1
        vpblendvb xmm9, xmm9, xmm10, xmm8
        vmovdqu [rdi+0x14a], xmm9
        vmovd   DWORD PTR [rdi+0x15a], xmm10
        vpextrw WORD PTR [rdi+0x15e], xmm10, 0x2
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOADU(xmm11,80)
        CFI_STACKLOAD(rdi,96)
        CFI_STACKLOAD(rsi,104)
        CFI_INC_RSP(112)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d11_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
