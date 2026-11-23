// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add ML-KEM polynomials and reduce the coefficients
// Inputs r[256], a[256] (signed 16-bit words);
// output r[256] (signed 16-bit words)
//
// Sets r[i] := (r[i] + a[i]) mod 3329 in the range 0 <= r[i] < 3329, for
// inputs with |r[i] + a[i]| < 2^15. This is mlkem-native's mlk_poly_add
// followed by mlk_poly_reduce.
//
// extern void mlkem_add_reduce(int16_t r[S2N_BIGNUM_STATIC 256],
//                              const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard x86-64 ABI: RDI = r, RSI = a
// Microsoft x64 ABI:   RCX = r, RDX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_add_reduce)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_add_reduce)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_add_reduce)
        .text
        .balign 32

S2N_BN_SYMBOL(mlkem_add_reduce):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(96)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm12,64)
        CFI_STACKSAVE(rdi,80)
        CFI_STACKSAVE(rsi,88)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// ymm0 = 3329 and ymm1 = 20159 in each word

        mov     eax, 0xd010d01
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        mov     eax, 0x4ebf4ebf
        vmovd   xmm1, eax
        vpbroadcastd ymm1, xmm1

// Coefficients 0..127

        vmovdqu ymm2, [rdi+0]
        vmovdqu ymm3, [rdi+32]
        vmovdqu ymm4, [rdi+64]
        vmovdqu ymm5, [rdi+96]
        vmovdqu ymm6, [rdi+128]
        vmovdqu ymm7, [rdi+160]
        vmovdqu ymm8, [rdi+192]
        vmovdqu ymm9, [rdi+224]
        vpaddw  ymm2, ymm2, [rsi+0]
        vpaddw  ymm3, ymm3, [rsi+32]
        vpaddw  ymm4, ymm4, [rsi+64]
        vpaddw  ymm5, ymm5, [rsi+96]
        vpaddw  ymm6, ymm6, [rsi+128]
        vpaddw  ymm7, ymm7, [rsi+160]
        vpaddw  ymm8, ymm8, [rsi+192]
        vpaddw  ymm9, ymm9, [rsi+224]
        vpmulhw ymm12, ymm2, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm2, ymm2, ymm12
        vpmulhw ymm12, ymm3, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm3, ymm3, ymm12
        vpmulhw ymm12, ymm4, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm4, ymm4, ymm12
        vpmulhw ymm12, ymm5, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm5, ymm5, ymm12
        vpmulhw ymm12, ymm6, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm6, ymm6, ymm12
        vpmulhw ymm12, ymm7, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm7, ymm7, ymm12
        vpmulhw ymm12, ymm8, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm8, ymm8, ymm12
        vpmulhw ymm12, ymm9, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm9, ymm9, ymm12
        vpsubw  ymm2, ymm2, ymm0
        vpsraw  ymm12, ymm2, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm2, ymm12, ymm2
        vpsubw  ymm3, ymm3, ymm0
        vpsraw  ymm12, ymm3, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm3, ymm12, ymm3
        vpsubw  ymm4, ymm4, ymm0
        vpsraw  ymm12, ymm4, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm4, ymm12, ymm4
        vpsubw  ymm5, ymm5, ymm0
        vpsraw  ymm12, ymm5, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm5, ymm12, ymm5
        vpsubw  ymm6, ymm6, ymm0
        vpsraw  ymm12, ymm6, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm6, ymm12, ymm6
        vpsubw  ymm7, ymm7, ymm0
        vpsraw  ymm12, ymm7, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm7, ymm12, ymm7
        vpsubw  ymm8, ymm8, ymm0
        vpsraw  ymm12, ymm8, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm8, ymm8, ymm12
        vpsubw  ymm9, ymm9, ymm0
        vpsraw  ymm12, ymm9, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm9, ymm9, ymm12
        vmovdqu [rdi+0], ymm2
        vmovdqu [rdi+32], ymm3
        vmovdqu [rdi+64], ymm4
        vmovdqu [rdi+96], ymm5
        vmovdqu [rdi+128], ymm6
        vmovdqu [rdi+160], ymm7
        vmovdqu [rdi+192], ymm8
        vmovdqu [rdi+224], ymm9

// Coefficients 128..255

        vmovdqu ymm2, [rdi+256]
        vmovdqu ymm3, [rdi+288]
        vmovdqu ymm4, [rdi+320]
        vmovdqu ymm5, [rdi+352]
        vmovdqu ymm6, [rdi+384]
        vmovdqu ymm7, [rdi+416]
        vmovdqu ymm8, [rdi+448]
        vmovdqu ymm9, [rdi+480]
        vpaddw  ymm2, ymm2, [rsi+256]
        vpaddw  ymm3, ymm3, [rsi+288]
        vpaddw  ymm4, ymm4, [rsi+320]
        vpaddw  ymm5, ymm5, [rsi+352]
        vpaddw  ymm6, ymm6, [rsi+384]
        vpaddw  ymm7, ymm7, [rsi+416]
        vpaddw  ymm8, ymm8, [rsi+448]
        vpaddw  ymm9, ymm9, [rsi+480]
        vpmulhw ymm12, ymm2, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm2, ymm2, ymm12
        vpmulhw ymm12, ymm3, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm3, ymm3, ymm12
        vpmulhw ymm12, ymm4, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm4, ymm4, ymm12
        vpmulhw ymm12, ymm5, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm5, ymm5, ymm12
        vpmulhw ymm12, ymm6, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm6, ymm6, ymm12
        vpmulhw ymm12, ymm7, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm7, ymm7, ymm12
        vpmulhw ymm12, ymm8, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm8, ymm8, ymm12
        vpmulhw ymm12, ymm9, ymm1
        vpsraw  ymm12, ymm12, 10
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm9, ymm9, ymm12
        vpsubw  ymm2, ymm2, ymm0
        vpsraw  ymm12, ymm2, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm2, ymm12, ymm2
        vpsubw  ymm3, ymm3, ymm0
        vpsraw  ymm12, ymm3, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm3, ymm12, ymm3
        vpsubw  ymm4, ymm4, ymm0
        vpsraw  ymm12, ymm4, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm4, ymm12, ymm4
        vpsubw  ymm5, ymm5, ymm0
        vpsraw  ymm12, ymm5, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm5, ymm12, ymm5
        vpsubw  ymm6, ymm6, ymm0
        vpsraw  ymm12, ymm6, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm6, ymm12, ymm6
        vpsubw  ymm7, ymm7, ymm0
        vpsraw  ymm12, ymm7, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm7, ymm12, ymm7
        vpsubw  ymm8, ymm8, ymm0
        vpsraw  ymm12, ymm8, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm8, ymm8, ymm12
        vpsubw  ymm9, ymm9, ymm0
        vpsraw  ymm12, ymm9, 15
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm9, ymm9, ymm12
        vmovdqu [rdi+256], ymm2
        vmovdqu [rdi+288], ymm3
        vmovdqu [rdi+320], ymm4
        vmovdqu [rdi+352], ymm5
        vmovdqu [rdi+384], ymm6
        vmovdqu [rdi+416], ymm7
        vmovdqu [rdi+448], ymm8
        vmovdqu [rdi+480], ymm9

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm12,64)
        CFI_STACKLOAD(rdi,80)
        CFI_STACKLOAD(rsi,88)
        CFI_INC_RSP(96)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_add_reduce)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
