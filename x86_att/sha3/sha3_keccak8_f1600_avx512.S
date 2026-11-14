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

#include "_internal_s2n_bignum_x86_att.h"


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
        CFI_STACKSAVEU(%xmm6,0)
        CFI_STACKSAVEU(%xmm7,16)
        CFI_STACKSAVEU(%xmm8,32)
        CFI_STACKSAVEU(%xmm9,48)
        CFI_STACKSAVEU(%xmm10,64)
        CFI_STACKSAVEU(%xmm11,80)
        CFI_STACKSAVEU(%xmm12,96)
        CFI_STACKSAVEU(%xmm13,112)
        CFI_STACKSAVEU(%xmm14,128)
        CFI_STACKSAVEU(%xmm15,144)
        CFI_STACKSAVE(%rdi,160)
        CFI_STACKSAVE(%rsi,168)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

        // Load and interleave 64 bytes from each of the 8 states (A(0-7))
        vmovdqu64       0+0(%rdi), %zmm0
        vmovdqu64       0+200(%rdi), %zmm1
        vmovdqu64       0+400(%rdi), %zmm2
        vmovdqu64       0+600(%rdi), %zmm3
        vmovdqu64       0+800(%rdi), %zmm4
        vmovdqu64       0+1000(%rdi), %zmm5
        vmovdqu64       0+1200(%rdi), %zmm6
        vmovdqu64       0+1400(%rdi), %zmm7
        vpunpckhqdq     %zmm1, %zmm0, %zmm25
        vpunpcklqdq     %zmm1, %zmm0, %zmm0
        vmovdqa64       %zmm25, %zmm1
        vpunpckhqdq     %zmm3, %zmm2, %zmm25
        vpunpcklqdq     %zmm3, %zmm2, %zmm2
        vmovdqa64       %zmm25, %zmm3
        vpunpckhqdq     %zmm5, %zmm4, %zmm25
        vpunpcklqdq     %zmm5, %zmm4, %zmm4
        vmovdqa64       %zmm25, %zmm5
        vpunpckhqdq     %zmm7, %zmm6, %zmm25
        vpunpcklqdq     %zmm7, %zmm6, %zmm6
        vmovdqa64       %zmm25, %zmm7
        vshufi64x2      $0xdd, %zmm2, %zmm0, %zmm25
        vshufi64x2      $0x88, %zmm2, %zmm0, %zmm0
        vmovdqa64       %zmm25, %zmm2
        vshufi64x2      $0xdd, %zmm3, %zmm1, %zmm25
        vshufi64x2      $0x88, %zmm3, %zmm1, %zmm1
        vmovdqa64       %zmm25, %zmm3
        vshufi64x2      $0xdd, %zmm6, %zmm4, %zmm25
        vshufi64x2      $0x88, %zmm6, %zmm4, %zmm4
        vmovdqa64       %zmm25, %zmm6
        vshufi64x2      $0xdd, %zmm7, %zmm5, %zmm25
        vshufi64x2      $0x88, %zmm7, %zmm5, %zmm5
        vmovdqa64       %zmm25, %zmm7
        vshufi64x2      $0xdd, %zmm4, %zmm0, %zmm25
        vshufi64x2      $0x88, %zmm4, %zmm0, %zmm0
        vmovdqa64       %zmm25, %zmm4
        vshufi64x2      $0xdd, %zmm5, %zmm1, %zmm25
        vshufi64x2      $0x88, %zmm5, %zmm1, %zmm1
        vmovdqa64       %zmm25, %zmm5
        vshufi64x2      $0xdd, %zmm6, %zmm2, %zmm25
        vshufi64x2      $0x88, %zmm6, %zmm2, %zmm2
        vmovdqa64       %zmm25, %zmm6
        vshufi64x2      $0xdd, %zmm7, %zmm3, %zmm25
        vshufi64x2      $0x88, %zmm7, %zmm3, %zmm3
        vmovdqa64       %zmm25, %zmm7

        // Load and interleave 64 bytes from each of the 8 states (A(8-15))
        vmovdqu64       64+0(%rdi), %zmm8
        vmovdqu64       64+200(%rdi), %zmm9
        vmovdqu64       64+400(%rdi), %zmm10
        vmovdqu64       64+600(%rdi), %zmm11
        vmovdqu64       64+800(%rdi), %zmm12
        vmovdqu64       64+1000(%rdi), %zmm13
        vmovdqu64       64+1200(%rdi), %zmm14
        vmovdqu64       64+1400(%rdi), %zmm15
        vpunpckhqdq     %zmm9, %zmm8, %zmm25
        vpunpcklqdq     %zmm9, %zmm8, %zmm8
        vmovdqa64       %zmm25, %zmm9
        vpunpckhqdq     %zmm11, %zmm10, %zmm25
        vpunpcklqdq     %zmm11, %zmm10, %zmm10
        vmovdqa64       %zmm25, %zmm11
        vpunpckhqdq     %zmm13, %zmm12, %zmm25
        vpunpcklqdq     %zmm13, %zmm12, %zmm12
        vmovdqa64       %zmm25, %zmm13
        vpunpckhqdq     %zmm15, %zmm14, %zmm25
        vpunpcklqdq     %zmm15, %zmm14, %zmm14
        vmovdqa64       %zmm25, %zmm15
        vshufi64x2      $0xdd, %zmm10, %zmm8, %zmm25
        vshufi64x2      $0x88, %zmm10, %zmm8, %zmm8
        vmovdqa64       %zmm25, %zmm10
        vshufi64x2      $0xdd, %zmm11, %zmm9, %zmm25
        vshufi64x2      $0x88, %zmm11, %zmm9, %zmm9
        vmovdqa64       %zmm25, %zmm11
        vshufi64x2      $0xdd, %zmm14, %zmm12, %zmm25
        vshufi64x2      $0x88, %zmm14, %zmm12, %zmm12
        vmovdqa64       %zmm25, %zmm14
        vshufi64x2      $0xdd, %zmm15, %zmm13, %zmm25
        vshufi64x2      $0x88, %zmm15, %zmm13, %zmm13
        vmovdqa64       %zmm25, %zmm15
        vshufi64x2      $0xdd, %zmm12, %zmm8, %zmm25
        vshufi64x2      $0x88, %zmm12, %zmm8, %zmm8
        vmovdqa64       %zmm25, %zmm12
        vshufi64x2      $0xdd, %zmm13, %zmm9, %zmm25
        vshufi64x2      $0x88, %zmm13, %zmm9, %zmm9
        vmovdqa64       %zmm25, %zmm13
        vshufi64x2      $0xdd, %zmm14, %zmm10, %zmm25
        vshufi64x2      $0x88, %zmm14, %zmm10, %zmm10
        vmovdqa64       %zmm25, %zmm14
        vshufi64x2      $0xdd, %zmm15, %zmm11, %zmm25
        vshufi64x2      $0x88, %zmm15, %zmm11, %zmm11
        vmovdqa64       %zmm25, %zmm15

        // Load and interleave 64 bytes from each of the 8 states (A(16-23))
        vmovdqu64       128+0(%rdi), %zmm16
        vmovdqu64       128+200(%rdi), %zmm17
        vmovdqu64       128+400(%rdi), %zmm18
        vmovdqu64       128+600(%rdi), %zmm19
        vmovdqu64       128+800(%rdi), %zmm20
        vmovdqu64       128+1000(%rdi), %zmm21
        vmovdqu64       128+1200(%rdi), %zmm22
        vmovdqu64       128+1400(%rdi), %zmm23
        vpunpckhqdq     %zmm17, %zmm16, %zmm25
        vpunpcklqdq     %zmm17, %zmm16, %zmm16
        vmovdqa64       %zmm25, %zmm17
        vpunpckhqdq     %zmm19, %zmm18, %zmm25
        vpunpcklqdq     %zmm19, %zmm18, %zmm18
        vmovdqa64       %zmm25, %zmm19
        vpunpckhqdq     %zmm21, %zmm20, %zmm25
        vpunpcklqdq     %zmm21, %zmm20, %zmm20
        vmovdqa64       %zmm25, %zmm21
        vpunpckhqdq     %zmm23, %zmm22, %zmm25
        vpunpcklqdq     %zmm23, %zmm22, %zmm22
        vmovdqa64       %zmm25, %zmm23
        vshufi64x2      $0xdd, %zmm18, %zmm16, %zmm25
        vshufi64x2      $0x88, %zmm18, %zmm16, %zmm16
        vmovdqa64       %zmm25, %zmm18
        vshufi64x2      $0xdd, %zmm19, %zmm17, %zmm25
        vshufi64x2      $0x88, %zmm19, %zmm17, %zmm17
        vmovdqa64       %zmm25, %zmm19
        vshufi64x2      $0xdd, %zmm22, %zmm20, %zmm25
        vshufi64x2      $0x88, %zmm22, %zmm20, %zmm20
        vmovdqa64       %zmm25, %zmm22
        vshufi64x2      $0xdd, %zmm23, %zmm21, %zmm25
        vshufi64x2      $0x88, %zmm23, %zmm21, %zmm21
        vmovdqa64       %zmm25, %zmm23
        vshufi64x2      $0xdd, %zmm20, %zmm16, %zmm25
        vshufi64x2      $0x88, %zmm20, %zmm16, %zmm16
        vmovdqa64       %zmm25, %zmm20
        vshufi64x2      $0xdd, %zmm21, %zmm17, %zmm25
        vshufi64x2      $0x88, %zmm21, %zmm17, %zmm17
        vmovdqa64       %zmm25, %zmm21
        vshufi64x2      $0xdd, %zmm22, %zmm18, %zmm25
        vshufi64x2      $0x88, %zmm22, %zmm18, %zmm18
        vmovdqa64       %zmm25, %zmm22
        vshufi64x2      $0xdd, %zmm23, %zmm19, %zmm25
        vshufi64x2      $0x88, %zmm23, %zmm19, %zmm19
        vmovdqa64       %zmm25, %zmm23

        // A24 is the last element (only 8 bytes per state)
        vmovq   192+0(%rdi), %xmm24
        vpinsrq $1, 192+200(%rdi), %xmm24, %xmm24
        vmovq   192+400(%rdi), %xmm25
        vpinsrq $1, 192+600(%rdi), %xmm25, %xmm25
        vinserti32x4    $1, %xmm25, %zmm24, %zmm24
        vmovq   192+800(%rdi), %xmm25
        vpinsrq $1, 192+1000(%rdi), %xmm25, %xmm25
        vinserti32x4    $2, %xmm25, %zmm24, %zmm24
        vmovq   192+1200(%rdi), %xmm25
        vpinsrq $1, 192+1400(%rdi), %xmm25, %xmm25
        vinserti32x4    $3, %xmm25, %zmm24, %zmm24

        // Initialize the loop counter
        movq    $0, %rax
.Lkeccak8_rnd_loop:

        // Theta step
        vmovdqa64       %zmm0, %zmm25
        vpternlogq      $0x96, %zmm5, %zmm10, %zmm25
        vmovdqa64       %zmm1, %zmm26
        vpternlogq      $0x96, %zmm11, %zmm6, %zmm26
        vmovdqa64       %zmm2, %zmm27
        vpternlogq      $0x96, %zmm12, %zmm7, %zmm27

        vmovdqa64       %zmm3, %zmm28
        vpternlogq      $0x96, %zmm13, %zmm8, %zmm28
        vmovdqa64       %zmm4, %zmm29
        vpternlogq      $0x96, %zmm14, %zmm9, %zmm29
        vpternlogq      $0x96, %zmm20, %zmm15, %zmm25

        vpternlogq      $0x96, %zmm21, %zmm16, %zmm26
        vpternlogq      $0x96, %zmm22, %zmm17, %zmm27
        vpternlogq      $0x96, %zmm23, %zmm18, %zmm28

        vprolq  $1, %zmm26, %zmm30
        vprolq  $1, %zmm27, %zmm31
        vpternlogq      $0x96, %zmm24, %zmm19, %zmm29

        vpternlogq      $0x96, %zmm30, %zmm29, %zmm0
        vpternlogq      $0x96, %zmm30, %zmm29, %zmm10
        vpternlogq      $0x96, %zmm30, %zmm29, %zmm20

        vpternlogq      $0x96, %zmm30, %zmm29, %zmm5
        vpternlogq      $0x96, %zmm30, %zmm29, %zmm15
        vprolq  $1, %zmm28, %zmm30

        vpternlogq      $0x96, %zmm31, %zmm25, %zmm6
        vpternlogq      $0x96, %zmm31, %zmm25, %zmm16
        vpternlogq      $0x96, %zmm31, %zmm25, %zmm1

        vpternlogq      $0x96, %zmm31, %zmm25, %zmm11
        vpternlogq      $0x96, %zmm31, %zmm25, %zmm21
        vprolq  $1, %zmm29, %zmm31

        vpbroadcastq    (%rsi), %zmm29
        addq    $8, %rsi

        vpternlogq      $0x96, %zmm30, %zmm26, %zmm12
        vpternlogq      $0x96, %zmm30, %zmm26, %zmm7
        vpternlogq      $0x96, %zmm30, %zmm26, %zmm22

        vpternlogq      $0x96, %zmm30, %zmm26, %zmm17
        vpternlogq      $0x96, %zmm30, %zmm26, %zmm2
        vprolq  $1, %zmm25, %zmm30

        vpternlogq      $0x96, %zmm31, %zmm27, %zmm3
        vpternlogq      $0x96, %zmm31, %zmm27, %zmm13
        vpternlogq      $0x96, %zmm31, %zmm27, %zmm23

        // Rho step
        vprolq  $44, %zmm6, %zmm6
        vpternlogq      $0x96, %zmm31, %zmm27, %zmm18
        vpternlogq      $0x96, %zmm31, %zmm27, %zmm8

        vprolq  $43, %zmm12, %zmm12
        vprolq  $21, %zmm18, %zmm18
        vpternlogq      $0x96, %zmm30, %zmm28, %zmm24

        vprolq  $14, %zmm24, %zmm24
        vprolq  $28, %zmm3, %zmm3
        vpternlogq      $0x96, %zmm30, %zmm28, %zmm9

        vprolq  $20, %zmm9, %zmm9
        vprolq  $3, %zmm10, %zmm10
        vpternlogq      $0x96, %zmm30, %zmm28, %zmm19

        vprolq  $45, %zmm16, %zmm16
        vprolq  $61, %zmm22, %zmm22
        vpternlogq      $0x96, %zmm30, %zmm28, %zmm4

        vprolq  $1, %zmm1, %zmm1
        vprolq  $6, %zmm7, %zmm7
        vpternlogq      $0x96, %zmm30, %zmm28, %zmm14

        vprolq  $25, %zmm13, %zmm13
        vprolq  $8, %zmm19, %zmm19
        // Chi step
        vmovdqa64       %zmm0, %zmm30
        vpternlogq      $0xD2, %zmm12, %zmm6, %zmm30

        vprolq  $18, %zmm20, %zmm20
        vprolq  $27, %zmm4, %zmm4
        // Iota step
        vpxorq  %zmm29, %zmm30, %zmm30

        vprolq  $36, %zmm5, %zmm5
        vprolq  $10, %zmm11, %zmm11
        vmovdqa64       %zmm6, %zmm31
        vpternlogq      $0xD2, %zmm18, %zmm12, %zmm31

        vprolq  $15, %zmm17, %zmm17
        vprolq  $56, %zmm23, %zmm23
        vpternlogq      $0xD2, %zmm24, %zmm18, %zmm12

        vprolq  $62, %zmm2, %zmm2
        vprolq  $55, %zmm8, %zmm8
        vpternlogq      $0xD2, %zmm0, %zmm24, %zmm18

        vprolq  $39, %zmm14, %zmm14
        vprolq  $41, %zmm15, %zmm15
        vpternlogq      $0xD2, %zmm6, %zmm0, %zmm24
        vmovdqa64       %zmm30, %zmm0
        vmovdqa64       %zmm31, %zmm6

        vprolq  $2, %zmm21, %zmm21
        vmovdqa64       %zmm3, %zmm30
        vpternlogq      $0xD2, %zmm10, %zmm9, %zmm30
        vmovdqa64       %zmm9, %zmm31
        vpternlogq      $0xD2, %zmm16, %zmm10, %zmm31

        vpternlogq      $0xD2, %zmm22, %zmm16, %zmm10
        vpternlogq      $0xD2, %zmm3, %zmm22, %zmm16
        vpternlogq      $0xD2, %zmm9, %zmm3, %zmm22
        vmovdqa64       %zmm30, %zmm3
        vmovdqa64       %zmm31, %zmm9

        vmovdqa64       %zmm1, %zmm30
        vpternlogq      $0xD2, %zmm13, %zmm7, %zmm30
        vmovdqa64       %zmm7, %zmm31
        vpternlogq      $0xD2, %zmm19, %zmm13, %zmm31
        vpternlogq      $0xD2, %zmm20, %zmm19, %zmm13

        vpternlogq      $0xD2, %zmm1, %zmm20, %zmm19
        vpternlogq      $0xD2, %zmm7, %zmm1, %zmm20
        vmovdqa64       %zmm30, %zmm1
        vmovdqa64       %zmm31, %zmm7
        vmovdqa64       %zmm4, %zmm30
        vpternlogq      $0xD2, %zmm11, %zmm5, %zmm30

        vmovdqa64       %zmm5, %zmm31
        vpternlogq      $0xD2, %zmm17, %zmm11, %zmm31
        vpternlogq      $0xD2, %zmm23, %zmm17, %zmm11
        vpternlogq      $0xD2, %zmm4, %zmm23, %zmm17

        vpternlogq      $0xD2, %zmm5, %zmm4, %zmm23
        vmovdqa64       %zmm30, %zmm4
        vmovdqa64       %zmm31, %zmm5
        vmovdqa64       %zmm2, %zmm30
        vpternlogq      $0xD2, %zmm14, %zmm8, %zmm30
        vmovdqa64       %zmm8, %zmm31
        vpternlogq      $0xD2, %zmm15, %zmm14, %zmm31

        vpternlogq      $0xD2, %zmm21, %zmm15, %zmm14
        vpternlogq      $0xD2, %zmm2, %zmm21, %zmm15
        vpternlogq      $0xD2, %zmm8, %zmm2, %zmm21
        vmovdqa64       %zmm30, %zmm2
        vmovdqa64       %zmm31, %zmm8

        // Pi step
        vmovdqa64       %zmm3, %zmm30
        vmovdqa64       %zmm18, %zmm3
        vmovdqa64       %zmm17, %zmm18
        vmovdqa64       %zmm11, %zmm17
        vmovdqa64       %zmm7, %zmm11
        vmovdqa64       %zmm10, %zmm7
        vmovdqa64       %zmm1, %zmm10
        vmovdqa64       %zmm6, %zmm1
        vmovdqa64       %zmm9, %zmm6
        vmovdqa64       %zmm22, %zmm9
        vmovdqa64       %zmm14, %zmm22
        vmovdqa64       %zmm20, %zmm14
        vmovdqa64       %zmm2, %zmm20
        vmovdqa64       %zmm12, %zmm2
        vmovdqa64       %zmm13, %zmm12
        vmovdqa64       %zmm19, %zmm13
        vmovdqa64       %zmm23, %zmm19
        vmovdqa64       %zmm15, %zmm23
        vmovdqa64       %zmm4, %zmm15
        vmovdqa64       %zmm24, %zmm4
        vmovdqa64       %zmm21, %zmm24
        vmovdqa64       %zmm8, %zmm21
        vmovdqa64       %zmm16, %zmm8
        vmovdqa64       %zmm5, %zmm16
        vmovdqa64       %zmm30, %zmm5

        addq    $1, %rax
        cmpq    $24, %rax
        jne     .Lkeccak8_rnd_loop

        // De-interleave and store 64 bytes to each of the 8 states (A(0-7))
        vpunpckhqdq     %zmm1, %zmm0, %zmm25
        vpunpcklqdq     %zmm1, %zmm0, %zmm0
        vmovdqa64       %zmm25, %zmm1
        vpunpckhqdq     %zmm3, %zmm2, %zmm25
        vpunpcklqdq     %zmm3, %zmm2, %zmm2
        vmovdqa64       %zmm25, %zmm3
        vpunpckhqdq     %zmm5, %zmm4, %zmm25
        vpunpcklqdq     %zmm5, %zmm4, %zmm4
        vmovdqa64       %zmm25, %zmm5
        vpunpckhqdq     %zmm7, %zmm6, %zmm25
        vpunpcklqdq     %zmm7, %zmm6, %zmm6
        vmovdqa64       %zmm25, %zmm7
        vshufi64x2      $0xdd, %zmm2, %zmm0, %zmm25
        vshufi64x2      $0x88, %zmm2, %zmm0, %zmm0
        vmovdqa64       %zmm25, %zmm2
        vshufi64x2      $0xdd, %zmm3, %zmm1, %zmm25
        vshufi64x2      $0x88, %zmm3, %zmm1, %zmm1
        vmovdqa64       %zmm25, %zmm3
        vshufi64x2      $0xdd, %zmm6, %zmm4, %zmm25
        vshufi64x2      $0x88, %zmm6, %zmm4, %zmm4
        vmovdqa64       %zmm25, %zmm6
        vshufi64x2      $0xdd, %zmm7, %zmm5, %zmm25
        vshufi64x2      $0x88, %zmm7, %zmm5, %zmm5
        vmovdqa64       %zmm25, %zmm7
        vshufi64x2      $0xdd, %zmm4, %zmm0, %zmm25
        vshufi64x2      $0x88, %zmm4, %zmm0, %zmm0
        vmovdqa64       %zmm25, %zmm4
        vshufi64x2      $0xdd, %zmm5, %zmm1, %zmm25
        vshufi64x2      $0x88, %zmm5, %zmm1, %zmm1
        vmovdqa64       %zmm25, %zmm5
        vshufi64x2      $0xdd, %zmm6, %zmm2, %zmm25
        vshufi64x2      $0x88, %zmm6, %zmm2, %zmm2
        vmovdqa64       %zmm25, %zmm6
        vshufi64x2      $0xdd, %zmm7, %zmm3, %zmm25
        vshufi64x2      $0x88, %zmm7, %zmm3, %zmm3
        vmovdqa64       %zmm25, %zmm7
        vmovdqu64       %zmm0, 0+0(%rdi)
        vmovdqu64       %zmm1, 0+200(%rdi)
        vmovdqu64       %zmm2, 0+400(%rdi)
        vmovdqu64       %zmm3, 0+600(%rdi)
        vmovdqu64       %zmm4, 0+800(%rdi)
        vmovdqu64       %zmm5, 0+1000(%rdi)
        vmovdqu64       %zmm6, 0+1200(%rdi)
        vmovdqu64       %zmm7, 0+1400(%rdi)

        // De-interleave and store 64 bytes to each of the 8 states (A(8-15))
        vpunpckhqdq     %zmm9, %zmm8, %zmm25
        vpunpcklqdq     %zmm9, %zmm8, %zmm8
        vmovdqa64       %zmm25, %zmm9
        vpunpckhqdq     %zmm11, %zmm10, %zmm25
        vpunpcklqdq     %zmm11, %zmm10, %zmm10
        vmovdqa64       %zmm25, %zmm11
        vpunpckhqdq     %zmm13, %zmm12, %zmm25
        vpunpcklqdq     %zmm13, %zmm12, %zmm12
        vmovdqa64       %zmm25, %zmm13
        vpunpckhqdq     %zmm15, %zmm14, %zmm25
        vpunpcklqdq     %zmm15, %zmm14, %zmm14
        vmovdqa64       %zmm25, %zmm15
        vshufi64x2      $0xdd, %zmm10, %zmm8, %zmm25
        vshufi64x2      $0x88, %zmm10, %zmm8, %zmm8
        vmovdqa64       %zmm25, %zmm10
        vshufi64x2      $0xdd, %zmm11, %zmm9, %zmm25
        vshufi64x2      $0x88, %zmm11, %zmm9, %zmm9
        vmovdqa64       %zmm25, %zmm11
        vshufi64x2      $0xdd, %zmm14, %zmm12, %zmm25
        vshufi64x2      $0x88, %zmm14, %zmm12, %zmm12
        vmovdqa64       %zmm25, %zmm14
        vshufi64x2      $0xdd, %zmm15, %zmm13, %zmm25
        vshufi64x2      $0x88, %zmm15, %zmm13, %zmm13
        vmovdqa64       %zmm25, %zmm15
        vshufi64x2      $0xdd, %zmm12, %zmm8, %zmm25
        vshufi64x2      $0x88, %zmm12, %zmm8, %zmm8
        vmovdqa64       %zmm25, %zmm12
        vshufi64x2      $0xdd, %zmm13, %zmm9, %zmm25
        vshufi64x2      $0x88, %zmm13, %zmm9, %zmm9
        vmovdqa64       %zmm25, %zmm13
        vshufi64x2      $0xdd, %zmm14, %zmm10, %zmm25
        vshufi64x2      $0x88, %zmm14, %zmm10, %zmm10
        vmovdqa64       %zmm25, %zmm14
        vshufi64x2      $0xdd, %zmm15, %zmm11, %zmm25
        vshufi64x2      $0x88, %zmm15, %zmm11, %zmm11
        vmovdqa64       %zmm25, %zmm15
        vmovdqu64       %zmm8, 64+0(%rdi)
        vmovdqu64       %zmm9, 64+200(%rdi)
        vmovdqu64       %zmm10, 64+400(%rdi)
        vmovdqu64       %zmm11, 64+600(%rdi)
        vmovdqu64       %zmm12, 64+800(%rdi)
        vmovdqu64       %zmm13, 64+1000(%rdi)
        vmovdqu64       %zmm14, 64+1200(%rdi)
        vmovdqu64       %zmm15, 64+1400(%rdi)

        // De-interleave and store 64 bytes to each of the 8 states (A(16-23))
        vpunpckhqdq     %zmm17, %zmm16, %zmm25
        vpunpcklqdq     %zmm17, %zmm16, %zmm16
        vmovdqa64       %zmm25, %zmm17
        vpunpckhqdq     %zmm19, %zmm18, %zmm25
        vpunpcklqdq     %zmm19, %zmm18, %zmm18
        vmovdqa64       %zmm25, %zmm19
        vpunpckhqdq     %zmm21, %zmm20, %zmm25
        vpunpcklqdq     %zmm21, %zmm20, %zmm20
        vmovdqa64       %zmm25, %zmm21
        vpunpckhqdq     %zmm23, %zmm22, %zmm25
        vpunpcklqdq     %zmm23, %zmm22, %zmm22
        vmovdqa64       %zmm25, %zmm23
        vshufi64x2      $0xdd, %zmm18, %zmm16, %zmm25
        vshufi64x2      $0x88, %zmm18, %zmm16, %zmm16
        vmovdqa64       %zmm25, %zmm18
        vshufi64x2      $0xdd, %zmm19, %zmm17, %zmm25
        vshufi64x2      $0x88, %zmm19, %zmm17, %zmm17
        vmovdqa64       %zmm25, %zmm19
        vshufi64x2      $0xdd, %zmm22, %zmm20, %zmm25
        vshufi64x2      $0x88, %zmm22, %zmm20, %zmm20
        vmovdqa64       %zmm25, %zmm22
        vshufi64x2      $0xdd, %zmm23, %zmm21, %zmm25
        vshufi64x2      $0x88, %zmm23, %zmm21, %zmm21
        vmovdqa64       %zmm25, %zmm23
        vshufi64x2      $0xdd, %zmm20, %zmm16, %zmm25
        vshufi64x2      $0x88, %zmm20, %zmm16, %zmm16
        vmovdqa64       %zmm25, %zmm20
        vshufi64x2      $0xdd, %zmm21, %zmm17, %zmm25
        vshufi64x2      $0x88, %zmm21, %zmm17, %zmm17
        vmovdqa64       %zmm25, %zmm21
        vshufi64x2      $0xdd, %zmm22, %zmm18, %zmm25
        vshufi64x2      $0x88, %zmm22, %zmm18, %zmm18
        vmovdqa64       %zmm25, %zmm22
        vshufi64x2      $0xdd, %zmm23, %zmm19, %zmm25
        vshufi64x2      $0x88, %zmm23, %zmm19, %zmm19
        vmovdqa64       %zmm25, %zmm23
        vmovdqu64       %zmm16, 128+0(%rdi)
        vmovdqu64       %zmm17, 128+200(%rdi)
        vmovdqu64       %zmm18, 128+400(%rdi)
        vmovdqu64       %zmm19, 128+600(%rdi)
        vmovdqu64       %zmm20, 128+800(%rdi)
        vmovdqu64       %zmm21, 128+1000(%rdi)
        vmovdqu64       %zmm22, 128+1200(%rdi)
        vmovdqu64       %zmm23, 128+1400(%rdi)

        // A24 is the last element (only 8 bytes per state)
        vmovq   %xmm24, 192+0(%rdi)
        vpextrq $1, %xmm24, 192+200(%rdi)
        vextracti32x4   $1, %zmm24, %xmm25
        vmovq   %xmm25, 192+400(%rdi)
        vpextrq $1, %xmm25, 192+600(%rdi)
        vextracti32x4   $2, %zmm24, %xmm25
        vmovq   %xmm25, 192+800(%rdi)
        vpextrq $1, %xmm25, 192+1000(%rdi)
        vextracti32x4   $3, %zmm24, %xmm25
        vmovq   %xmm25, 192+1200(%rdi)
        vpextrq $1, %xmm25, 192+1400(%rdi)
        vzeroupper
#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOADU(%xmm8,32)
        CFI_STACKLOADU(%xmm9,48)
        CFI_STACKLOADU(%xmm10,64)
        CFI_STACKLOADU(%xmm11,80)
        CFI_STACKLOADU(%xmm12,96)
        CFI_STACKLOADU(%xmm13,112)
        CFI_STACKLOADU(%xmm14,128)
        CFI_STACKLOADU(%xmm15,144)
        CFI_STACKLOAD(%rdi,160)
        CFI_STACKLOAD(%rsi,168)
        CFI_INC_RSP(176)
#endif
        CFI_RET

        S2N_BN_SIZE_DIRECTIVE(sha3_keccak8_f1600_avx512)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif
