// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert a 32-byte message to an ML-KEM polynomial
// Input msg[32] (bytes); output r[256] (signed 16-bit words)
//
// Coefficient 8 * i + j is 1665 = (3329 + 1) / 2 if bit j of msg[i] is
// set and 0 otherwise, i.e. Decompress_1 of FIPS 203 (section 4.2.1)
// applied to ByteDecode_1(msg), as in mlkem-native's mlk_poly_frommsg.
//
// extern void mlkem_frommsg(int16_t r[S2N_BIGNUM_STATIC 256],
//                           const uint8_t msg[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = msg
// Microsoft x64 ABI:   RCX = r, RDX = msg
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_frommsg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_frommsg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_frommsg)
        .text
        .balign 32

S2N_BN_SYMBOL(mlkem_frommsg):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(16)
        CFI_STACKSAVE(rdi,0)
        CFI_STACKSAVE(rsi,8)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// ymm0 = 1665 in each word, ymm1 = 2^(15-k) in word k

        mov     eax, 0x6810681
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        movabs  rax, 0x1000200040008000
        vmovq   xmm1, rax
        movabs  rax, 0x0100020004000800
        vpinsrq xmm1, xmm1, rax, 1
        movabs  rax, 0x0010002000400080
        vmovq   xmm2, rax
        movabs  rax, 0x0001000200040008
        vpinsrq xmm2, xmm2, rax, 1
        vinserti128 ymm1, ymm1, xmm2, 1

// For each 16-bit chunk of the message, 16 coefficients

        vpbroadcastw ymm2, WORD PTR [rsi+0]
        vpmullw ymm2, ymm2, ymm1
        vpsraw  ymm2, ymm2, 15
        vpand   ymm2, ymm2, ymm0
        vmovdqu [rdi+0], ymm2
        vpbroadcastw ymm3, WORD PTR [rsi+2]
        vpmullw ymm3, ymm3, ymm1
        vpsraw  ymm3, ymm3, 15
        vpand   ymm3, ymm3, ymm0
        vmovdqu [rdi+32], ymm3
        vpbroadcastw ymm4, WORD PTR [rsi+4]
        vpmullw ymm4, ymm4, ymm1
        vpsraw  ymm4, ymm4, 15
        vpand   ymm4, ymm4, ymm0
        vmovdqu [rdi+64], ymm4
        vpbroadcastw ymm5, WORD PTR [rsi+6]
        vpmullw ymm5, ymm5, ymm1
        vpsraw  ymm5, ymm5, 15
        vpand   ymm5, ymm5, ymm0
        vmovdqu [rdi+96], ymm5
        vpbroadcastw ymm2, WORD PTR [rsi+8]
        vpmullw ymm2, ymm2, ymm1
        vpsraw  ymm2, ymm2, 15
        vpand   ymm2, ymm2, ymm0
        vmovdqu [rdi+128], ymm2
        vpbroadcastw ymm3, WORD PTR [rsi+10]
        vpmullw ymm3, ymm3, ymm1
        vpsraw  ymm3, ymm3, 15
        vpand   ymm3, ymm3, ymm0
        vmovdqu [rdi+160], ymm3
        vpbroadcastw ymm4, WORD PTR [rsi+12]
        vpmullw ymm4, ymm4, ymm1
        vpsraw  ymm4, ymm4, 15
        vpand   ymm4, ymm4, ymm0
        vmovdqu [rdi+192], ymm4
        vpbroadcastw ymm5, WORD PTR [rsi+14]
        vpmullw ymm5, ymm5, ymm1
        vpsraw  ymm5, ymm5, 15
        vpand   ymm5, ymm5, ymm0
        vmovdqu [rdi+224], ymm5
        vpbroadcastw ymm2, WORD PTR [rsi+16]
        vpmullw ymm2, ymm2, ymm1
        vpsraw  ymm2, ymm2, 15
        vpand   ymm2, ymm2, ymm0
        vmovdqu [rdi+256], ymm2
        vpbroadcastw ymm3, WORD PTR [rsi+18]
        vpmullw ymm3, ymm3, ymm1
        vpsraw  ymm3, ymm3, 15
        vpand   ymm3, ymm3, ymm0
        vmovdqu [rdi+288], ymm3
        vpbroadcastw ymm4, WORD PTR [rsi+20]
        vpmullw ymm4, ymm4, ymm1
        vpsraw  ymm4, ymm4, 15
        vpand   ymm4, ymm4, ymm0
        vmovdqu [rdi+320], ymm4
        vpbroadcastw ymm5, WORD PTR [rsi+22]
        vpmullw ymm5, ymm5, ymm1
        vpsraw  ymm5, ymm5, 15
        vpand   ymm5, ymm5, ymm0
        vmovdqu [rdi+352], ymm5
        vpbroadcastw ymm2, WORD PTR [rsi+24]
        vpmullw ymm2, ymm2, ymm1
        vpsraw  ymm2, ymm2, 15
        vpand   ymm2, ymm2, ymm0
        vmovdqu [rdi+384], ymm2
        vpbroadcastw ymm3, WORD PTR [rsi+26]
        vpmullw ymm3, ymm3, ymm1
        vpsraw  ymm3, ymm3, 15
        vpand   ymm3, ymm3, ymm0
        vmovdqu [rdi+416], ymm3
        vpbroadcastw ymm4, WORD PTR [rsi+28]
        vpmullw ymm4, ymm4, ymm1
        vpsraw  ymm4, ymm4, 15
        vpand   ymm4, ymm4, ymm0
        vmovdqu [rdi+448], ymm4
        vpbroadcastw ymm5, WORD PTR [rsi+30]
        vpmullw ymm5, ymm5, ymm1
        vpsraw  ymm5, ymm5, 15
        vpand   ymm5, ymm5, ymm0
        vmovdqu [rdi+480], ymm5

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(rdi,0)
        CFI_STACKLOAD(rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_frommsg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
