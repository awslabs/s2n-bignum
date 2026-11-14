// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, batch of eight independent operations
// Input a[200], rc[24]; output a[200]
//
// The input/output argument is in effect eight 25-element Keccak arrays
// a[0...24], a[25..49], ..., a[175..199], which could be considered
// as type a[25][8].
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
//    extern void sha3_keccak8_f1600_avx512(uint64_t a[200], const uint64_t rc[24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak8_f1600_avx512)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak8_f1600_avx512)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak8_f1600_avx512)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak8_f1600_avx512):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(176)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVEU(xmm11,80)
        CFI_STACKSAVEU(xmm12,96)
        CFI_STACKSAVEU(xmm13,112)
        CFI_STACKSAVEU(xmm14,128)
        CFI_STACKSAVEU(xmm15,144)
        CFI_STACKSAVE(rdi,160)
        CFI_STACKSAVE(rsi,168)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

        // Load and interleave 64 bytes from each of the 8 states (A[0-7])
        vmovdqu64       zmm0, [rdi+0+0]
        vmovdqu64       zmm1, [rdi+0+200]
        vmovdqu64       zmm2, [rdi+0+400]
        vmovdqu64       zmm3, [rdi+0+600]
        vmovdqu64       zmm4, [rdi+0+800]
        vmovdqu64       zmm5, [rdi+0+1000]
        vmovdqu64       zmm6, [rdi+0+1200]
        vmovdqu64       zmm7, [rdi+0+1400]
        vpunpckhqdq     zmm25, zmm0, zmm1
        vpunpcklqdq     zmm0, zmm0, zmm1
        vmovdqa64       zmm1, zmm25
        vpunpckhqdq     zmm25, zmm2, zmm3
        vpunpcklqdq     zmm2, zmm2, zmm3
        vmovdqa64       zmm3, zmm25
        vpunpckhqdq     zmm25, zmm4, zmm5
        vpunpcklqdq     zmm4, zmm4, zmm5
        vmovdqa64       zmm5, zmm25
        vpunpckhqdq     zmm25, zmm6, zmm7
        vpunpcklqdq     zmm6, zmm6, zmm7
        vmovdqa64       zmm7, zmm25
        vshufi64x2      zmm25, zmm0, zmm2, 0xdd
        vshufi64x2      zmm0, zmm0, zmm2, 0x88
        vmovdqa64       zmm2, zmm25
        vshufi64x2      zmm25, zmm1, zmm3, 0xdd
        vshufi64x2      zmm1, zmm1, zmm3, 0x88
        vmovdqa64       zmm3, zmm25
        vshufi64x2      zmm25, zmm4, zmm6, 0xdd
        vshufi64x2      zmm4, zmm4, zmm6, 0x88
        vmovdqa64       zmm6, zmm25
        vshufi64x2      zmm25, zmm5, zmm7, 0xdd
        vshufi64x2      zmm5, zmm5, zmm7, 0x88
        vmovdqa64       zmm7, zmm25
        vshufi64x2      zmm25, zmm0, zmm4, 0xdd
        vshufi64x2      zmm0, zmm0, zmm4, 0x88
        vmovdqa64       zmm4, zmm25
        vshufi64x2      zmm25, zmm1, zmm5, 0xdd
        vshufi64x2      zmm1, zmm1, zmm5, 0x88
        vmovdqa64       zmm5, zmm25
        vshufi64x2      zmm25, zmm2, zmm6, 0xdd
        vshufi64x2      zmm2, zmm2, zmm6, 0x88
        vmovdqa64       zmm6, zmm25
        vshufi64x2      zmm25, zmm3, zmm7, 0xdd
        vshufi64x2      zmm3, zmm3, zmm7, 0x88
        vmovdqa64       zmm7, zmm25

        // Load and interleave 64 bytes from each of the 8 states (A[8-15])
        vmovdqu64       zmm8, [rdi+64+0]
        vmovdqu64       zmm9, [rdi+64+200]
        vmovdqu64       zmm10, [rdi+64+400]
        vmovdqu64       zmm11, [rdi+64+600]
        vmovdqu64       zmm12, [rdi+64+800]
        vmovdqu64       zmm13, [rdi+64+1000]
        vmovdqu64       zmm14, [rdi+64+1200]
        vmovdqu64       zmm15, [rdi+64+1400]
        vpunpckhqdq     zmm25, zmm8, zmm9
        vpunpcklqdq     zmm8, zmm8, zmm9
        vmovdqa64       zmm9, zmm25
        vpunpckhqdq     zmm25, zmm10, zmm11
        vpunpcklqdq     zmm10, zmm10, zmm11
        vmovdqa64       zmm11, zmm25
        vpunpckhqdq     zmm25, zmm12, zmm13
        vpunpcklqdq     zmm12, zmm12, zmm13
        vmovdqa64       zmm13, zmm25
        vpunpckhqdq     zmm25, zmm14, zmm15
        vpunpcklqdq     zmm14, zmm14, zmm15
        vmovdqa64       zmm15, zmm25
        vshufi64x2      zmm25, zmm8, zmm10, 0xdd
        vshufi64x2      zmm8, zmm8, zmm10, 0x88
        vmovdqa64       zmm10, zmm25
        vshufi64x2      zmm25, zmm9, zmm11, 0xdd
        vshufi64x2      zmm9, zmm9, zmm11, 0x88
        vmovdqa64       zmm11, zmm25
        vshufi64x2      zmm25, zmm12, zmm14, 0xdd
        vshufi64x2      zmm12, zmm12, zmm14, 0x88
        vmovdqa64       zmm14, zmm25
        vshufi64x2      zmm25, zmm13, zmm15, 0xdd
        vshufi64x2      zmm13, zmm13, zmm15, 0x88
        vmovdqa64       zmm15, zmm25
        vshufi64x2      zmm25, zmm8, zmm12, 0xdd
        vshufi64x2      zmm8, zmm8, zmm12, 0x88
        vmovdqa64       zmm12, zmm25
        vshufi64x2      zmm25, zmm9, zmm13, 0xdd
        vshufi64x2      zmm9, zmm9, zmm13, 0x88
        vmovdqa64       zmm13, zmm25
        vshufi64x2      zmm25, zmm10, zmm14, 0xdd
        vshufi64x2      zmm10, zmm10, zmm14, 0x88
        vmovdqa64       zmm14, zmm25
        vshufi64x2      zmm25, zmm11, zmm15, 0xdd
        vshufi64x2      zmm11, zmm11, zmm15, 0x88
        vmovdqa64       zmm15, zmm25

        // Load and interleave 64 bytes from each of the 8 states (A[16-23])
        vmovdqu64       zmm16, [rdi+128+0]
        vmovdqu64       zmm17, [rdi+128+200]
        vmovdqu64       zmm18, [rdi+128+400]
        vmovdqu64       zmm19, [rdi+128+600]
        vmovdqu64       zmm20, [rdi+128+800]
        vmovdqu64       zmm21, [rdi+128+1000]
        vmovdqu64       zmm22, [rdi+128+1200]
        vmovdqu64       zmm23, [rdi+128+1400]
        vpunpckhqdq     zmm25, zmm16, zmm17
        vpunpcklqdq     zmm16, zmm16, zmm17
        vmovdqa64       zmm17, zmm25
        vpunpckhqdq     zmm25, zmm18, zmm19
        vpunpcklqdq     zmm18, zmm18, zmm19
        vmovdqa64       zmm19, zmm25
        vpunpckhqdq     zmm25, zmm20, zmm21
        vpunpcklqdq     zmm20, zmm20, zmm21
        vmovdqa64       zmm21, zmm25
        vpunpckhqdq     zmm25, zmm22, zmm23
        vpunpcklqdq     zmm22, zmm22, zmm23
        vmovdqa64       zmm23, zmm25
        vshufi64x2      zmm25, zmm16, zmm18, 0xdd
        vshufi64x2      zmm16, zmm16, zmm18, 0x88
        vmovdqa64       zmm18, zmm25
        vshufi64x2      zmm25, zmm17, zmm19, 0xdd
        vshufi64x2      zmm17, zmm17, zmm19, 0x88
        vmovdqa64       zmm19, zmm25
        vshufi64x2      zmm25, zmm20, zmm22, 0xdd
        vshufi64x2      zmm20, zmm20, zmm22, 0x88
        vmovdqa64       zmm22, zmm25
        vshufi64x2      zmm25, zmm21, zmm23, 0xdd
        vshufi64x2      zmm21, zmm21, zmm23, 0x88
        vmovdqa64       zmm23, zmm25
        vshufi64x2      zmm25, zmm16, zmm20, 0xdd
        vshufi64x2      zmm16, zmm16, zmm20, 0x88
        vmovdqa64       zmm20, zmm25
        vshufi64x2      zmm25, zmm17, zmm21, 0xdd
        vshufi64x2      zmm17, zmm17, zmm21, 0x88
        vmovdqa64       zmm21, zmm25
        vshufi64x2      zmm25, zmm18, zmm22, 0xdd
        vshufi64x2      zmm18, zmm18, zmm22, 0x88
        vmovdqa64       zmm22, zmm25
        vshufi64x2      zmm25, zmm19, zmm23, 0xdd
        vshufi64x2      zmm19, zmm19, zmm23, 0x88
        vmovdqa64       zmm23, zmm25

        // A[24] is the last element (only 8 bytes per state)
        vmovq   xmm24, [rdi+192+0]
        vpinsrq xmm24, xmm24, [rdi+192+200], 1
        vmovq   xmm25, [rdi+192+400]
        vpinsrq xmm25, xmm25, [rdi+192+600], 1
        vinserti32x4    zmm24, zmm24, xmm25, 1
        vmovq   xmm25, [rdi+192+800]
        vpinsrq xmm25, xmm25, [rdi+192+1000], 1
        vinserti32x4    zmm24, zmm24, xmm25, 2
        vmovq   xmm25, [rdi+192+1200]
        vpinsrq xmm25, xmm25, [rdi+192+1400], 1
        vinserti32x4    zmm24, zmm24, xmm25, 3

        // Initialize the loop counter
        mov     rax, 0
.Lkeccak8_rnd_loop:

        // Theta step
        vmovdqa64       zmm25, zmm0
        vpternlogq      zmm25, zmm10, zmm5, 0x96
        vmovdqa64       zmm26, zmm1
        vpternlogq      zmm26, zmm6, zmm11, 0x96
        vmovdqa64       zmm27, zmm2
        vpternlogq      zmm27, zmm7, zmm12, 0x96

        vmovdqa64       zmm28, zmm3
        vpternlogq      zmm28, zmm8, zmm13, 0x96
        vmovdqa64       zmm29, zmm4
        vpternlogq      zmm29, zmm9, zmm14, 0x96
        vpternlogq      zmm25, zmm15, zmm20, 0x96

        vpternlogq      zmm26, zmm16, zmm21, 0x96
        vpternlogq      zmm27, zmm17, zmm22, 0x96
        vpternlogq      zmm28, zmm18, zmm23, 0x96

        vprolq  zmm30, zmm26, 1
        vprolq  zmm31, zmm27, 1
        vpternlogq      zmm29, zmm19, zmm24, 0x96

        vpternlogq      zmm0, zmm29, zmm30, 0x96
        vpternlogq      zmm10, zmm29, zmm30, 0x96
        vpternlogq      zmm20, zmm29, zmm30, 0x96

        vpternlogq      zmm5, zmm29, zmm30, 0x96
        vpternlogq      zmm15, zmm29, zmm30, 0x96
        vprolq  zmm30, zmm28, 1

        vpternlogq      zmm6, zmm25, zmm31, 0x96
        vpternlogq      zmm16, zmm25, zmm31, 0x96
        vpternlogq      zmm1, zmm25, zmm31, 0x96

        vpternlogq      zmm11, zmm25, zmm31, 0x96
        vpternlogq      zmm21, zmm25, zmm31, 0x96
        vprolq  zmm31, zmm29, 1

        vpbroadcastq    zmm29, [rsi]
        add     rsi, 8

        vpternlogq      zmm12, zmm26, zmm30, 0x96
        vpternlogq      zmm7, zmm26, zmm30, 0x96
        vpternlogq      zmm22, zmm26, zmm30, 0x96

        vpternlogq      zmm17, zmm26, zmm30, 0x96
        vpternlogq      zmm2, zmm26, zmm30, 0x96
        vprolq  zmm30, zmm25, 1

        vpternlogq      zmm3, zmm27, zmm31, 0x96
        vpternlogq      zmm13, zmm27, zmm31, 0x96
        vpternlogq      zmm23, zmm27, zmm31, 0x96

        // Rho step
        vprolq  zmm6, zmm6, 44
        vpternlogq      zmm18, zmm27, zmm31, 0x96
        vpternlogq      zmm8, zmm27, zmm31, 0x96

        vprolq  zmm12, zmm12, 43
        vprolq  zmm18, zmm18, 21
        vpternlogq      zmm24, zmm28, zmm30, 0x96

        vprolq  zmm24, zmm24, 14
        vprolq  zmm3, zmm3, 28
        vpternlogq      zmm9, zmm28, zmm30, 0x96

        vprolq  zmm9, zmm9, 20
        vprolq  zmm10, zmm10, 3
        vpternlogq      zmm19, zmm28, zmm30, 0x96

        vprolq  zmm16, zmm16, 45
        vprolq  zmm22, zmm22, 61
        vpternlogq      zmm4, zmm28, zmm30, 0x96

        vprolq  zmm1, zmm1, 1
        vprolq  zmm7, zmm7, 6
        vpternlogq      zmm14, zmm28, zmm30, 0x96

        vprolq  zmm13, zmm13, 25
        vprolq  zmm19, zmm19, 8
        // Chi step
        vmovdqa64       zmm30, zmm0
        vpternlogq      zmm30, zmm6, zmm12, 0xD2

        vprolq  zmm20, zmm20, 18
        vprolq  zmm4, zmm4, 27
        // Iota step
        vpxorq  zmm30, zmm30, zmm29

        vprolq  zmm5, zmm5, 36
        vprolq  zmm11, zmm11, 10
        vmovdqa64       zmm31, zmm6
        vpternlogq      zmm31, zmm12, zmm18, 0xD2

        vprolq  zmm17, zmm17, 15
        vprolq  zmm23, zmm23, 56
        vpternlogq      zmm12, zmm18, zmm24, 0xD2

        vprolq  zmm2, zmm2, 62
        vprolq  zmm8, zmm8, 55
        vpternlogq      zmm18, zmm24, zmm0, 0xD2

        vprolq  zmm14, zmm14, 39
        vprolq  zmm15, zmm15, 41
        vpternlogq      zmm24, zmm0, zmm6, 0xD2
        vmovdqa64       zmm0, zmm30
        vmovdqa64       zmm6, zmm31

        vprolq  zmm21, zmm21, 2
        vmovdqa64       zmm30, zmm3
        vpternlogq      zmm30, zmm9, zmm10, 0xD2
        vmovdqa64       zmm31, zmm9
        vpternlogq      zmm31, zmm10, zmm16, 0xD2

        vpternlogq      zmm10, zmm16, zmm22, 0xD2
        vpternlogq      zmm16, zmm22, zmm3, 0xD2
        vpternlogq      zmm22, zmm3, zmm9, 0xD2
        vmovdqa64       zmm3, zmm30
        vmovdqa64       zmm9, zmm31

        vmovdqa64       zmm30, zmm1
        vpternlogq      zmm30, zmm7, zmm13, 0xD2
        vmovdqa64       zmm31, zmm7
        vpternlogq      zmm31, zmm13, zmm19, 0xD2
        vpternlogq      zmm13, zmm19, zmm20, 0xD2

        vpternlogq      zmm19, zmm20, zmm1, 0xD2
        vpternlogq      zmm20, zmm1, zmm7, 0xD2
        vmovdqa64       zmm1, zmm30
        vmovdqa64       zmm7, zmm31
        vmovdqa64       zmm30, zmm4
        vpternlogq      zmm30, zmm5, zmm11, 0xD2

        vmovdqa64       zmm31, zmm5
        vpternlogq      zmm31, zmm11, zmm17, 0xD2
        vpternlogq      zmm11, zmm17, zmm23, 0xD2
        vpternlogq      zmm17, zmm23, zmm4, 0xD2

        vpternlogq      zmm23, zmm4, zmm5, 0xD2
        vmovdqa64       zmm4, zmm30
        vmovdqa64       zmm5, zmm31
        vmovdqa64       zmm30, zmm2
        vpternlogq      zmm30, zmm8, zmm14, 0xD2
        vmovdqa64       zmm31, zmm8
        vpternlogq      zmm31, zmm14, zmm15, 0xD2

        vpternlogq      zmm14, zmm15, zmm21, 0xD2
        vpternlogq      zmm15, zmm21, zmm2, 0xD2
        vpternlogq      zmm21, zmm2, zmm8, 0xD2
        vmovdqa64       zmm2, zmm30
        vmovdqa64       zmm8, zmm31

        // Pi step
        vmovdqa64       zmm30, zmm3
        vmovdqa64       zmm3, zmm18
        vmovdqa64       zmm18, zmm17
        vmovdqa64       zmm17, zmm11
        vmovdqa64       zmm11, zmm7
        vmovdqa64       zmm7, zmm10
        vmovdqa64       zmm10, zmm1
        vmovdqa64       zmm1, zmm6
        vmovdqa64       zmm6, zmm9
        vmovdqa64       zmm9, zmm22
        vmovdqa64       zmm22, zmm14
        vmovdqa64       zmm14, zmm20
        vmovdqa64       zmm20, zmm2
        vmovdqa64       zmm2, zmm12
        vmovdqa64       zmm12, zmm13
        vmovdqa64       zmm13, zmm19
        vmovdqa64       zmm19, zmm23
        vmovdqa64       zmm23, zmm15
        vmovdqa64       zmm15, zmm4
        vmovdqa64       zmm4, zmm24
        vmovdqa64       zmm24, zmm21
        vmovdqa64       zmm21, zmm8
        vmovdqa64       zmm8, zmm16
        vmovdqa64       zmm16, zmm5
        vmovdqa64       zmm5, zmm30

        add     rax, 1
        cmp     rax, 24
        jne     .Lkeccak8_rnd_loop

        // De-interleave and store 64 bytes to each of the 8 states (A[0-7])
        vpunpckhqdq     zmm25, zmm0, zmm1
        vpunpcklqdq     zmm0, zmm0, zmm1
        vmovdqa64       zmm1, zmm25
        vpunpckhqdq     zmm25, zmm2, zmm3
        vpunpcklqdq     zmm2, zmm2, zmm3
        vmovdqa64       zmm3, zmm25
        vpunpckhqdq     zmm25, zmm4, zmm5
        vpunpcklqdq     zmm4, zmm4, zmm5
        vmovdqa64       zmm5, zmm25
        vpunpckhqdq     zmm25, zmm6, zmm7
        vpunpcklqdq     zmm6, zmm6, zmm7
        vmovdqa64       zmm7, zmm25
        vshufi64x2      zmm25, zmm0, zmm2, 0xdd
        vshufi64x2      zmm0, zmm0, zmm2, 0x88
        vmovdqa64       zmm2, zmm25
        vshufi64x2      zmm25, zmm1, zmm3, 0xdd
        vshufi64x2      zmm1, zmm1, zmm3, 0x88
        vmovdqa64       zmm3, zmm25
        vshufi64x2      zmm25, zmm4, zmm6, 0xdd
        vshufi64x2      zmm4, zmm4, zmm6, 0x88
        vmovdqa64       zmm6, zmm25
        vshufi64x2      zmm25, zmm5, zmm7, 0xdd
        vshufi64x2      zmm5, zmm5, zmm7, 0x88
        vmovdqa64       zmm7, zmm25
        vshufi64x2      zmm25, zmm0, zmm4, 0xdd
        vshufi64x2      zmm0, zmm0, zmm4, 0x88
        vmovdqa64       zmm4, zmm25
        vshufi64x2      zmm25, zmm1, zmm5, 0xdd
        vshufi64x2      zmm1, zmm1, zmm5, 0x88
        vmovdqa64       zmm5, zmm25
        vshufi64x2      zmm25, zmm2, zmm6, 0xdd
        vshufi64x2      zmm2, zmm2, zmm6, 0x88
        vmovdqa64       zmm6, zmm25
        vshufi64x2      zmm25, zmm3, zmm7, 0xdd
        vshufi64x2      zmm3, zmm3, zmm7, 0x88
        vmovdqa64       zmm7, zmm25
        vmovdqu64       [rdi+0+0], zmm0
        vmovdqu64       [rdi+0+200], zmm1
        vmovdqu64       [rdi+0+400], zmm2
        vmovdqu64       [rdi+0+600], zmm3
        vmovdqu64       [rdi+0+800], zmm4
        vmovdqu64       [rdi+0+1000], zmm5
        vmovdqu64       [rdi+0+1200], zmm6
        vmovdqu64       [rdi+0+1400], zmm7

        // De-interleave and store 64 bytes to each of the 8 states (A[8-15])
        vpunpckhqdq     zmm25, zmm8, zmm9
        vpunpcklqdq     zmm8, zmm8, zmm9
        vmovdqa64       zmm9, zmm25
        vpunpckhqdq     zmm25, zmm10, zmm11
        vpunpcklqdq     zmm10, zmm10, zmm11
        vmovdqa64       zmm11, zmm25
        vpunpckhqdq     zmm25, zmm12, zmm13
        vpunpcklqdq     zmm12, zmm12, zmm13
        vmovdqa64       zmm13, zmm25
        vpunpckhqdq     zmm25, zmm14, zmm15
        vpunpcklqdq     zmm14, zmm14, zmm15
        vmovdqa64       zmm15, zmm25
        vshufi64x2      zmm25, zmm8, zmm10, 0xdd
        vshufi64x2      zmm8, zmm8, zmm10, 0x88
        vmovdqa64       zmm10, zmm25
        vshufi64x2      zmm25, zmm9, zmm11, 0xdd
        vshufi64x2      zmm9, zmm9, zmm11, 0x88
        vmovdqa64       zmm11, zmm25
        vshufi64x2      zmm25, zmm12, zmm14, 0xdd
        vshufi64x2      zmm12, zmm12, zmm14, 0x88
        vmovdqa64       zmm14, zmm25
        vshufi64x2      zmm25, zmm13, zmm15, 0xdd
        vshufi64x2      zmm13, zmm13, zmm15, 0x88
        vmovdqa64       zmm15, zmm25
        vshufi64x2      zmm25, zmm8, zmm12, 0xdd
        vshufi64x2      zmm8, zmm8, zmm12, 0x88
        vmovdqa64       zmm12, zmm25
        vshufi64x2      zmm25, zmm9, zmm13, 0xdd
        vshufi64x2      zmm9, zmm9, zmm13, 0x88
        vmovdqa64       zmm13, zmm25
        vshufi64x2      zmm25, zmm10, zmm14, 0xdd
        vshufi64x2      zmm10, zmm10, zmm14, 0x88
        vmovdqa64       zmm14, zmm25
        vshufi64x2      zmm25, zmm11, zmm15, 0xdd
        vshufi64x2      zmm11, zmm11, zmm15, 0x88
        vmovdqa64       zmm15, zmm25
        vmovdqu64       [rdi+64+0], zmm8
        vmovdqu64       [rdi+64+200], zmm9
        vmovdqu64       [rdi+64+400], zmm10
        vmovdqu64       [rdi+64+600], zmm11
        vmovdqu64       [rdi+64+800], zmm12
        vmovdqu64       [rdi+64+1000], zmm13
        vmovdqu64       [rdi+64+1200], zmm14
        vmovdqu64       [rdi+64+1400], zmm15

        // De-interleave and store 64 bytes to each of the 8 states (A[16-23])
        vpunpckhqdq     zmm25, zmm16, zmm17
        vpunpcklqdq     zmm16, zmm16, zmm17
        vmovdqa64       zmm17, zmm25
        vpunpckhqdq     zmm25, zmm18, zmm19
        vpunpcklqdq     zmm18, zmm18, zmm19
        vmovdqa64       zmm19, zmm25
        vpunpckhqdq     zmm25, zmm20, zmm21
        vpunpcklqdq     zmm20, zmm20, zmm21
        vmovdqa64       zmm21, zmm25
        vpunpckhqdq     zmm25, zmm22, zmm23
        vpunpcklqdq     zmm22, zmm22, zmm23
        vmovdqa64       zmm23, zmm25
        vshufi64x2      zmm25, zmm16, zmm18, 0xdd
        vshufi64x2      zmm16, zmm16, zmm18, 0x88
        vmovdqa64       zmm18, zmm25
        vshufi64x2      zmm25, zmm17, zmm19, 0xdd
        vshufi64x2      zmm17, zmm17, zmm19, 0x88
        vmovdqa64       zmm19, zmm25
        vshufi64x2      zmm25, zmm20, zmm22, 0xdd
        vshufi64x2      zmm20, zmm20, zmm22, 0x88
        vmovdqa64       zmm22, zmm25
        vshufi64x2      zmm25, zmm21, zmm23, 0xdd
        vshufi64x2      zmm21, zmm21, zmm23, 0x88
        vmovdqa64       zmm23, zmm25
        vshufi64x2      zmm25, zmm16, zmm20, 0xdd
        vshufi64x2      zmm16, zmm16, zmm20, 0x88
        vmovdqa64       zmm20, zmm25
        vshufi64x2      zmm25, zmm17, zmm21, 0xdd
        vshufi64x2      zmm17, zmm17, zmm21, 0x88
        vmovdqa64       zmm21, zmm25
        vshufi64x2      zmm25, zmm18, zmm22, 0xdd
        vshufi64x2      zmm18, zmm18, zmm22, 0x88
        vmovdqa64       zmm22, zmm25
        vshufi64x2      zmm25, zmm19, zmm23, 0xdd
        vshufi64x2      zmm19, zmm19, zmm23, 0x88
        vmovdqa64       zmm23, zmm25
        vmovdqu64       [rdi+128+0], zmm16
        vmovdqu64       [rdi+128+200], zmm17
        vmovdqu64       [rdi+128+400], zmm18
        vmovdqu64       [rdi+128+600], zmm19
        vmovdqu64       [rdi+128+800], zmm20
        vmovdqu64       [rdi+128+1000], zmm21
        vmovdqu64       [rdi+128+1200], zmm22
        vmovdqu64       [rdi+128+1400], zmm23

        // A[24] is the last element (only 8 bytes per state)
        vmovq   [rdi+192+0], xmm24
        vpextrq [rdi+192+200], xmm24, 1
        vextracti32x4   xmm25, zmm24, 1
        vmovq   [rdi+192+400], xmm25
        vpextrq [rdi+192+600], xmm25, 1
        vextracti32x4   xmm25, zmm24, 2
        vmovq   [rdi+192+800], xmm25
        vpextrq [rdi+192+1000], xmm25, 1
        vextracti32x4   xmm25, zmm24, 3
        vmovq   [rdi+192+1200], xmm25
        vpextrq [rdi+192+1400], xmm25, 1
        vzeroupper
#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOADU(xmm11,80)
        CFI_STACKLOADU(xmm12,96)
        CFI_STACKLOADU(xmm13,112)
        CFI_STACKLOADU(xmm14,128)
        CFI_STACKLOADU(xmm15,144)
        CFI_STACKLOAD(rdi,160)
        CFI_STACKLOAD(rsi,168)
        CFI_INC_RSP(176)
#endif
        CFI_RET

        S2N_BN_SIZE_DIRECTIVE(sha3_keccak8_f1600_avx512)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif
