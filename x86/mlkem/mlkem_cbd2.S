// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Sample from the centered binomial distribution with eta = 2 for ML-KEM
// Input buf[128] (bytes); output r[256] (signed 16-bit words)
//
// Each input byte b = buf[i], with bits b_0 (least significant) to b_7,
// gives two coefficients, each in the range -2..2:
//
//   r[2*i]   = (b_0 + b_1) - (b_2 + b_3)
//   r[2*i+1] = (b_4 + b_5) - (b_6 + b_7)
//
// This is SamplePolyCBD_2 of FIPS 203 (Algorithm 8) on the 128 bytes, as in
// mlkem-native's mlk_poly_cbd2.
//
// extern void mlkem_cbd2(int16_t r[S2N_BIGNUM_STATIC 256],
//                        const uint8_t buf[S2N_BIGNUM_STATIC 128]);
//
// Standard x86-64 ABI: RDI = r, RSI = buf
// Microsoft x64 ABI:   RCX = r, RDX = buf
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_cbd2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_cbd2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_cbd2)
        .text
        .balign 32

S2N_BN_SYMBOL(mlkem_cbd2):
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
#endif

// ymm0 = 0x000f in each word, ymm1 = 0x8000 in each word,
// ymm2 = the table T2 in each lane, ymm3 = 2 in each word

        mov     eax, 0xf000f
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        mov     eax, 0x80008000
        vmovd   xmm1, eax
        vpbroadcastd ymm1, xmm1
        movabs  rax, 0x0302020104030302
        vmovq   xmm2, rax
        movabs  rax, 0x0201010003020201
        vpinsrq xmm2, xmm2, rax, 1
        vinserti128 ymm2, ymm2, xmm2, 1
        mov     eax, 0x20002
        vmovd   xmm3, eax
        vpbroadcastd ymm3, xmm3

// For each 8 bytes, 16 coefficients

        vpmovzxbd ymm4, QWORD PTR [rsi+0]
        vpslld  ymm5, ymm4, 12
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm0
        vpor    ymm4, ymm4, ymm1
        vpshufb ymm4, ymm2, ymm4
        vpsubw  ymm4, ymm4, ymm3
        vmovdqu [rdi+0], ymm4
        vpmovzxbd ymm6, QWORD PTR [rsi+8]
        vpslld  ymm7, ymm6, 12
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm0
        vpor    ymm6, ymm6, ymm1
        vpshufb ymm6, ymm2, ymm6
        vpsubw  ymm6, ymm6, ymm3
        vmovdqu [rdi+32], ymm6
        vpmovzxbd ymm4, QWORD PTR [rsi+16]
        vpslld  ymm5, ymm4, 12
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm0
        vpor    ymm4, ymm4, ymm1
        vpshufb ymm4, ymm2, ymm4
        vpsubw  ymm4, ymm4, ymm3
        vmovdqu [rdi+64], ymm4
        vpmovzxbd ymm6, QWORD PTR [rsi+24]
        vpslld  ymm7, ymm6, 12
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm0
        vpor    ymm6, ymm6, ymm1
        vpshufb ymm6, ymm2, ymm6
        vpsubw  ymm6, ymm6, ymm3
        vmovdqu [rdi+96], ymm6
        vpmovzxbd ymm4, QWORD PTR [rsi+32]
        vpslld  ymm5, ymm4, 12
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm0
        vpor    ymm4, ymm4, ymm1
        vpshufb ymm4, ymm2, ymm4
        vpsubw  ymm4, ymm4, ymm3
        vmovdqu [rdi+128], ymm4
        vpmovzxbd ymm6, QWORD PTR [rsi+40]
        vpslld  ymm7, ymm6, 12
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm0
        vpor    ymm6, ymm6, ymm1
        vpshufb ymm6, ymm2, ymm6
        vpsubw  ymm6, ymm6, ymm3
        vmovdqu [rdi+160], ymm6
        vpmovzxbd ymm4, QWORD PTR [rsi+48]
        vpslld  ymm5, ymm4, 12
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm0
        vpor    ymm4, ymm4, ymm1
        vpshufb ymm4, ymm2, ymm4
        vpsubw  ymm4, ymm4, ymm3
        vmovdqu [rdi+192], ymm4
        vpmovzxbd ymm6, QWORD PTR [rsi+56]
        vpslld  ymm7, ymm6, 12
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm0
        vpor    ymm6, ymm6, ymm1
        vpshufb ymm6, ymm2, ymm6
        vpsubw  ymm6, ymm6, ymm3
        vmovdqu [rdi+224], ymm6
        vpmovzxbd ymm4, QWORD PTR [rsi+64]
        vpslld  ymm5, ymm4, 12
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm0
        vpor    ymm4, ymm4, ymm1
        vpshufb ymm4, ymm2, ymm4
        vpsubw  ymm4, ymm4, ymm3
        vmovdqu [rdi+256], ymm4
        vpmovzxbd ymm6, QWORD PTR [rsi+72]
        vpslld  ymm7, ymm6, 12
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm0
        vpor    ymm6, ymm6, ymm1
        vpshufb ymm6, ymm2, ymm6
        vpsubw  ymm6, ymm6, ymm3
        vmovdqu [rdi+288], ymm6
        vpmovzxbd ymm4, QWORD PTR [rsi+80]
        vpslld  ymm5, ymm4, 12
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm0
        vpor    ymm4, ymm4, ymm1
        vpshufb ymm4, ymm2, ymm4
        vpsubw  ymm4, ymm4, ymm3
        vmovdqu [rdi+320], ymm4
        vpmovzxbd ymm6, QWORD PTR [rsi+88]
        vpslld  ymm7, ymm6, 12
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm0
        vpor    ymm6, ymm6, ymm1
        vpshufb ymm6, ymm2, ymm6
        vpsubw  ymm6, ymm6, ymm3
        vmovdqu [rdi+352], ymm6
        vpmovzxbd ymm4, QWORD PTR [rsi+96]
        vpslld  ymm5, ymm4, 12
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm0
        vpor    ymm4, ymm4, ymm1
        vpshufb ymm4, ymm2, ymm4
        vpsubw  ymm4, ymm4, ymm3
        vmovdqu [rdi+384], ymm4
        vpmovzxbd ymm6, QWORD PTR [rsi+104]
        vpslld  ymm7, ymm6, 12
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm0
        vpor    ymm6, ymm6, ymm1
        vpshufb ymm6, ymm2, ymm6
        vpsubw  ymm6, ymm6, ymm3
        vmovdqu [rdi+416], ymm6
        vpmovzxbd ymm4, QWORD PTR [rsi+112]
        vpslld  ymm5, ymm4, 12
        vpor    ymm4, ymm4, ymm5
        vpand   ymm4, ymm4, ymm0
        vpor    ymm4, ymm4, ymm1
        vpshufb ymm4, ymm2, ymm4
        vpsubw  ymm4, ymm4, ymm3
        vmovdqu [rdi+448], ymm4
        vpmovzxbd ymm6, QWORD PTR [rsi+120]
        vpslld  ymm7, ymm6, 12
        vpor    ymm6, ymm6, ymm7
        vpand   ymm6, ymm6, ymm0
        vpor    ymm6, ymm6, ymm1
        vpshufb ymm6, ymm2, ymm6
        vpsubw  ymm6, ymm6, ymm3
        vmovdqu [rdi+480], ymm6

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOAD(rdi,32)
        CFI_STACKLOAD(rsi,40)
        CFI_INC_RSP(48)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_cbd2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
