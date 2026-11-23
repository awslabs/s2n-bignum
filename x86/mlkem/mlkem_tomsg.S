// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert an ML-KEM polynomial to a 32-byte message
// Input a[256] (signed 16-bit words); output msg[32] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Bit j of msg[i] is round(2 * a[8 * i + j] / 3329) mod 2, i.e. 1 exactly
// when 833 <= a[8 * i + j] <= 2496: ByteEncode_1 of Compress_1 (FIPS 203,
// section 4.2.1), as in mlkem-native's mlk_poly_tomsg.
//
// extern void mlkem_tomsg(uint8_t msg[S2N_BIGNUM_STATIC 32],
//                         const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard x86-64 ABI: RDI = msg, RSI = a
// Microsoft x64 ABI:   RCX = msg, RDX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_tomsg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_tomsg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_tomsg)
        .text
        .balign 32

S2N_BN_SYMBOL(mlkem_tomsg):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(16)
        CFI_STACKSAVE(rdi,0)
        CFI_STACKSAVE(rsi,8)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// ymm0 = 833 and ymm1 = 2497 in each word

        mov     eax, 0x3410341
        vmovd   xmm0, eax
        vpbroadcastd ymm0, xmm0
        mov     eax, 0x9c109c1
        vmovd   xmm1, eax
        vpbroadcastd ymm1, xmm1

// For each pair of vectors, 32 coefficients to 4 bytes

        vmovdqu ymm2, [rsi+0]
        vpsubw  ymm3, ymm2, ymm0
        vpsubw  ymm2, ymm2, ymm1
        vpandn  ymm2, ymm3, ymm2
        vpsrlw  ymm2, ymm2, 15
        vmovdqu ymm4, [rsi+32]
        vpsubw  ymm5, ymm4, ymm0
        vpsubw  ymm4, ymm4, ymm1
        vpandn  ymm4, ymm5, ymm4
        vpsrlw  ymm4, ymm4, 15
        vpackuswb ymm2, ymm2, ymm4
        vpermq  ymm2, ymm2, 0xd8
        vpsllw  ymm2, ymm2, 7
        vpmovmskb eax, ymm2
        mov     [rdi+0], eax
        vmovdqu ymm2, [rsi+64]
        vpsubw  ymm3, ymm2, ymm0
        vpsubw  ymm2, ymm2, ymm1
        vpandn  ymm2, ymm3, ymm2
        vpsrlw  ymm2, ymm2, 15
        vmovdqu ymm4, [rsi+96]
        vpsubw  ymm5, ymm4, ymm0
        vpsubw  ymm4, ymm4, ymm1
        vpandn  ymm4, ymm5, ymm4
        vpsrlw  ymm4, ymm4, 15
        vpackuswb ymm2, ymm2, ymm4
        vpermq  ymm2, ymm2, 0xd8
        vpsllw  ymm2, ymm2, 7
        vpmovmskb eax, ymm2
        mov     [rdi+4], eax
        vmovdqu ymm2, [rsi+128]
        vpsubw  ymm3, ymm2, ymm0
        vpsubw  ymm2, ymm2, ymm1
        vpandn  ymm2, ymm3, ymm2
        vpsrlw  ymm2, ymm2, 15
        vmovdqu ymm4, [rsi+160]
        vpsubw  ymm5, ymm4, ymm0
        vpsubw  ymm4, ymm4, ymm1
        vpandn  ymm4, ymm5, ymm4
        vpsrlw  ymm4, ymm4, 15
        vpackuswb ymm2, ymm2, ymm4
        vpermq  ymm2, ymm2, 0xd8
        vpsllw  ymm2, ymm2, 7
        vpmovmskb eax, ymm2
        mov     [rdi+8], eax
        vmovdqu ymm2, [rsi+192]
        vpsubw  ymm3, ymm2, ymm0
        vpsubw  ymm2, ymm2, ymm1
        vpandn  ymm2, ymm3, ymm2
        vpsrlw  ymm2, ymm2, 15
        vmovdqu ymm4, [rsi+224]
        vpsubw  ymm5, ymm4, ymm0
        vpsubw  ymm4, ymm4, ymm1
        vpandn  ymm4, ymm5, ymm4
        vpsrlw  ymm4, ymm4, 15
        vpackuswb ymm2, ymm2, ymm4
        vpermq  ymm2, ymm2, 0xd8
        vpsllw  ymm2, ymm2, 7
        vpmovmskb eax, ymm2
        mov     [rdi+12], eax
        vmovdqu ymm2, [rsi+256]
        vpsubw  ymm3, ymm2, ymm0
        vpsubw  ymm2, ymm2, ymm1
        vpandn  ymm2, ymm3, ymm2
        vpsrlw  ymm2, ymm2, 15
        vmovdqu ymm4, [rsi+288]
        vpsubw  ymm5, ymm4, ymm0
        vpsubw  ymm4, ymm4, ymm1
        vpandn  ymm4, ymm5, ymm4
        vpsrlw  ymm4, ymm4, 15
        vpackuswb ymm2, ymm2, ymm4
        vpermq  ymm2, ymm2, 0xd8
        vpsllw  ymm2, ymm2, 7
        vpmovmskb eax, ymm2
        mov     [rdi+16], eax
        vmovdqu ymm2, [rsi+320]
        vpsubw  ymm3, ymm2, ymm0
        vpsubw  ymm2, ymm2, ymm1
        vpandn  ymm2, ymm3, ymm2
        vpsrlw  ymm2, ymm2, 15
        vmovdqu ymm4, [rsi+352]
        vpsubw  ymm5, ymm4, ymm0
        vpsubw  ymm4, ymm4, ymm1
        vpandn  ymm4, ymm5, ymm4
        vpsrlw  ymm4, ymm4, 15
        vpackuswb ymm2, ymm2, ymm4
        vpermq  ymm2, ymm2, 0xd8
        vpsllw  ymm2, ymm2, 7
        vpmovmskb eax, ymm2
        mov     [rdi+20], eax
        vmovdqu ymm2, [rsi+384]
        vpsubw  ymm3, ymm2, ymm0
        vpsubw  ymm2, ymm2, ymm1
        vpandn  ymm2, ymm3, ymm2
        vpsrlw  ymm2, ymm2, 15
        vmovdqu ymm4, [rsi+416]
        vpsubw  ymm5, ymm4, ymm0
        vpsubw  ymm4, ymm4, ymm1
        vpandn  ymm4, ymm5, ymm4
        vpsrlw  ymm4, ymm4, 15
        vpackuswb ymm2, ymm2, ymm4
        vpermq  ymm2, ymm2, 0xd8
        vpsllw  ymm2, ymm2, 7
        vpmovmskb eax, ymm2
        mov     [rdi+24], eax
        vmovdqu ymm2, [rsi+448]
        vpsubw  ymm3, ymm2, ymm0
        vpsubw  ymm2, ymm2, ymm1
        vpandn  ymm2, ymm3, ymm2
        vpsrlw  ymm2, ymm2, 15
        vmovdqu ymm4, [rsi+480]
        vpsubw  ymm5, ymm4, ymm0
        vpsubw  ymm4, ymm4, ymm1
        vpandn  ymm4, ymm5, ymm4
        vpsrlw  ymm4, ymm4, 15
        vpackuswb ymm2, ymm2, ymm4
        vpermq  ymm2, ymm2, 0xd8
        vpsllw  ymm2, ymm2, 7
        vpmovmskb eax, ymm2
        mov     [rdi+28], eax

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(rdi,0)
        CFI_STACKLOAD(rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_tomsg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
