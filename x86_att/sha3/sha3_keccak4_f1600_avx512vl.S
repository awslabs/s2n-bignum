// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, batch of four independent operations,
// AVX-512VL variant (256-bit EVEX registers, 4 x 64-bit lanes each).
// Input a[100], rc[24]; output a[100]
//
// The input/output argument is in effect four 25-element Keccak arrays
// a[0...24], a[25..49], a[50..74] and a[75..99], which could be considered
// as type a[25][4].
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
//    extern void sha3_keccak4_f1600_avx512vl(uint64_t a[100],
//                                            const uint64_t rc[24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
//
// s2n-vendored single-function form, flattened from aws-lc
// KeccakF1600_x4_avx512vl (PR #2720): the shared keccak_1600_permute
// subroutine is inlined into the 4x wrapper, and its embedded %rip-relative
// round-constant table is replaced by the caller-supplied rc pointer (RSI),
// matching the sha3_keccak4_f1600 convention, so the object is
// relocation-free (rep;ret -> ret; alignment padding removed). The whole
// 25-lane state is register-resident in %ymm0..%ymm24 for the entire 24-round
// loop (no stack spill); %ymm25..%ymm31 are scratch.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak4_f1600_avx512vl)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak4_f1600_avx512vl)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak4_f1600_avx512vl)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak4_f1600_avx512vl):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
// Microsoft x64 ABI trampoline: RCX=bitstate_in, RDX=rc_pointer, and XMM6-15,
// RDI, RSI are callee-saved. Spill them, then shuffle args into the SysV
// registers (RDI, RSI) the register-resident body below expects.
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

// Load the four independent 200-byte states from a[] and transpose them into
// the register-resident 4-lane packed layout: %ymm_k holds Keccak lane k of all
// four states (lane j of %ymm_k = state j's word k). vpunpck{l,h}qdq + vshufi64x2
// do the 4-way interleave; lane 24 (the odd one) is packed via vmovq/vpinsrq/
// vinserti32x4 into the low 128 bits of %ymm24.
        vmovdqu64       0+0(%rdi), %ymm25
        vmovdqu64       0+200(%rdi), %ymm26
        vmovdqu64       0+400(%rdi), %ymm27
        vmovdqu64       0+600(%rdi), %ymm28
        vpunpcklqdq     %ymm26, %ymm25, %ymm29
        vpunpckhqdq     %ymm26, %ymm25, %ymm30
        vpunpcklqdq     %ymm28, %ymm27, %ymm25
        vpunpckhqdq     %ymm28, %ymm27, %ymm26
        vshufi64x2      $0, %ymm25, %ymm29, %ymm0
        vshufi64x2      $0, %ymm26, %ymm30, %ymm1
        vshufi64x2      $3, %ymm25, %ymm29, %ymm2
        vshufi64x2      $3, %ymm26, %ymm30, %ymm3
        vmovdqu64       32+0(%rdi), %ymm25
        vmovdqu64       32+200(%rdi), %ymm26
        vmovdqu64       32+400(%rdi), %ymm27
        vmovdqu64       32+600(%rdi), %ymm28
        vpunpcklqdq     %ymm26, %ymm25, %ymm29
        vpunpckhqdq     %ymm26, %ymm25, %ymm30
        vpunpcklqdq     %ymm28, %ymm27, %ymm25
        vpunpckhqdq     %ymm28, %ymm27, %ymm26
        vshufi64x2      $0, %ymm25, %ymm29, %ymm4
        vshufi64x2      $0, %ymm26, %ymm30, %ymm5
        vshufi64x2      $3, %ymm25, %ymm29, %ymm6
        vshufi64x2      $3, %ymm26, %ymm30, %ymm7
        vmovdqu64       64+0(%rdi), %ymm25
        vmovdqu64       64+200(%rdi), %ymm26
        vmovdqu64       64+400(%rdi), %ymm27
        vmovdqu64       64+600(%rdi), %ymm28
        vpunpcklqdq     %ymm26, %ymm25, %ymm29
        vpunpckhqdq     %ymm26, %ymm25, %ymm30
        vpunpcklqdq     %ymm28, %ymm27, %ymm25
        vpunpckhqdq     %ymm28, %ymm27, %ymm26
        vshufi64x2      $0, %ymm25, %ymm29, %ymm8
        vshufi64x2      $0, %ymm26, %ymm30, %ymm9
        vshufi64x2      $3, %ymm25, %ymm29, %ymm10
        vshufi64x2      $3, %ymm26, %ymm30, %ymm11
        vmovdqu64       96+0(%rdi), %ymm25
        vmovdqu64       96+200(%rdi), %ymm26
        vmovdqu64       96+400(%rdi), %ymm27
        vmovdqu64       96+600(%rdi), %ymm28
        vpunpcklqdq     %ymm26, %ymm25, %ymm29
        vpunpckhqdq     %ymm26, %ymm25, %ymm30
        vpunpcklqdq     %ymm28, %ymm27, %ymm25
        vpunpckhqdq     %ymm28, %ymm27, %ymm26
        vshufi64x2      $0, %ymm25, %ymm29, %ymm12
        vshufi64x2      $0, %ymm26, %ymm30, %ymm13
        vshufi64x2      $3, %ymm25, %ymm29, %ymm14
        vshufi64x2      $3, %ymm26, %ymm30, %ymm15
        vmovdqu64       128+0(%rdi), %ymm25
        vmovdqu64       128+200(%rdi), %ymm26
        vmovdqu64       128+400(%rdi), %ymm27
        vmovdqu64       128+600(%rdi), %ymm28
        vpunpcklqdq     %ymm26, %ymm25, %ymm29
        vpunpckhqdq     %ymm26, %ymm25, %ymm30
        vpunpcklqdq     %ymm28, %ymm27, %ymm25
        vpunpckhqdq     %ymm28, %ymm27, %ymm26
        vshufi64x2      $0, %ymm25, %ymm29, %ymm16
        vshufi64x2      $0, %ymm26, %ymm30, %ymm17
        vshufi64x2      $3, %ymm25, %ymm29, %ymm18
        vshufi64x2      $3, %ymm26, %ymm30, %ymm19
        vmovdqu64       160+0(%rdi), %ymm25
        vmovdqu64       160+200(%rdi), %ymm26
        vmovdqu64       160+400(%rdi), %ymm27
        vmovdqu64       160+600(%rdi), %ymm28
        vpunpcklqdq     %ymm26, %ymm25, %ymm29
        vpunpckhqdq     %ymm26, %ymm25, %ymm30
        vpunpcklqdq     %ymm28, %ymm27, %ymm25
        vpunpckhqdq     %ymm28, %ymm27, %ymm26
        vshufi64x2      $0, %ymm25, %ymm29, %ymm20
        vshufi64x2      $0, %ymm26, %ymm30, %ymm21
        vshufi64x2      $3, %ymm25, %ymm29, %ymm22
        vshufi64x2      $3, %ymm26, %ymm30, %ymm23
        vmovq   192+0(%rdi), %xmm24
        vpinsrq $1, 192+200(%rdi), %xmm24, %xmm24
        vmovq   192+400(%rdi), %xmm25
        vpinsrq $1, 192+600(%rdi), %xmm25, %xmm25
        vinserti32x4    $1, %xmm25, %ymm24, %ymm24

// 24-round permutation loop. %r10d counts rounds down (24 -> 0); %r11 walks the
// round-constant array (%r11 = rc + 8*i, advanced once per round).
        movl    $24, %r10d
        movq    %rsi, %r11
.Lkeccak_rnd_loop:
// One Keccak round on all four lanes at once. The theta/rho/pi/chi/iota steps
// are software-pipelined (interleaved) for throughput, so they do not appear
// as cleanly separated blocks:
//   Theta: column parities C[x] via 3-input XOR (vpternlogq imm 0x96), then
//          D[x] = C[x-1] ^ rotl(C[x+1],1) (vprolq by 1) folded into every lane.
//   Rho:   per-lane fixed left-rotations (vprolq by the rho offsets).
//   Pi:    lane permutation, realised by the 25-register vmovdqa64 shuffle at
//          the end of the round (so inputs are back in canonical %ymm_k slots).
//   Chi:   a ^ ((~b) & c) via vpternlogq imm 0xD2.
//   Iota:  RC[i] XORed into lane (0,0); see the vpbroadcastq below.

        // Theta, column parities: C(x) = state(x)[0]^state[x][1]^...^state[x][4]
        vmovdqa64       %ymm0, %ymm25
        vpternlogq      $0x96, %ymm5, %ymm10, %ymm25
        vmovdqa64       %ymm1, %ymm26
        vpternlogq      $0x96, %ymm11, %ymm6, %ymm26
        vmovdqa64       %ymm2, %ymm27
        vpternlogq      $0x96, %ymm12, %ymm7, %ymm27

        vmovdqa64       %ymm3, %ymm28
        vpternlogq      $0x96, %ymm13, %ymm8, %ymm28
        vmovdqa64       %ymm4, %ymm29
        vpternlogq      $0x96, %ymm14, %ymm9, %ymm29
        vpternlogq      $0x96, %ymm20, %ymm15, %ymm25

        vpternlogq      $0x96, %ymm21, %ymm16, %ymm26
        vpternlogq      $0x96, %ymm22, %ymm17, %ymm27
        vpternlogq      $0x96, %ymm23, %ymm18, %ymm28

        // Theta, D values: D(x) = C((x+4) mod 5) XOR rotl(C[(x+1) mod 5], 1)
        vprolq  $1, %ymm26, %ymm30
        vprolq  $1, %ymm27, %ymm31
        vpternlogq      $0x96, %ymm24, %ymm19, %ymm29

        // Theta, apply to state: state(x)(y) ^= D[x]  (D[x] held in %ymm29..%ymm31,
        // folded into every lane; theta and the D computation stay interleaved)
        vpternlogq      $0x96, %ymm30, %ymm29, %ymm0
        vpternlogq      $0x96, %ymm30, %ymm29, %ymm10
        vpternlogq      $0x96, %ymm30, %ymm29, %ymm20

        vpternlogq      $0x96, %ymm30, %ymm29, %ymm5
        vpternlogq      $0x96, %ymm30, %ymm29, %ymm15
        vprolq  $1, %ymm28, %ymm30

        vpternlogq      $0x96, %ymm31, %ymm25, %ymm6
        vpternlogq      $0x96, %ymm31, %ymm25, %ymm16
        vpternlogq      $0x96, %ymm31, %ymm25, %ymm1

        vpternlogq      $0x96, %ymm31, %ymm25, %ymm11
        vpternlogq      $0x96, %ymm31, %ymm25, %ymm21
        vprolq  $1, %ymm29, %ymm31

// Iota: broadcast this round's constant RC[i] to all four lanes and advance
// %r11 to RC[i+1]; it is XORed into lane (0,0) below (vpxorq into %ymm30/A[0,0]).
        vpbroadcastq    (%r11), %ymm29
        addq    $8, %r11

        vpternlogq      $0x96, %ymm30, %ymm26, %ymm12
        vpternlogq      $0x96, %ymm30, %ymm26, %ymm7
        vpternlogq      $0x96, %ymm30, %ymm26, %ymm22

        vpternlogq      $0x96, %ymm30, %ymm26, %ymm17
        vpternlogq      $0x96, %ymm30, %ymm26, %ymm2
        vprolq  $1, %ymm25, %ymm30

        // Rho (starts here, theta tail still finishing): state(x)(y) = rotl(state[x][y], RHO[x][y]),
        // RHO = ( 0  1 62 28 27 ; 36 44  6 55 20 ;  3 10 43 25 39 ; 41 45 15 21  8 ; 18  2 61 56 14 )
        // (the vprolq immediates interleaved below are exactly these offsets).
        vpternlogq      $0x96, %ymm31, %ymm27, %ymm3
        vpternlogq      $0x96, %ymm31, %ymm27, %ymm13
        vpternlogq      $0x96, %ymm31, %ymm27, %ymm23

        vprolq  $44, %ymm6, %ymm6
        vpternlogq      $0x96, %ymm31, %ymm27, %ymm18
        vpternlogq      $0x96, %ymm31, %ymm27, %ymm8

        vprolq  $43, %ymm12, %ymm12
        vprolq  $21, %ymm18, %ymm18
        vpternlogq      $0x96, %ymm30, %ymm28, %ymm24

        vprolq  $14, %ymm24, %ymm24
        vprolq  $28, %ymm3, %ymm3
        vpternlogq      $0x96, %ymm30, %ymm28, %ymm9

        vprolq  $20, %ymm9, %ymm9
        vprolq  $3, %ymm10, %ymm10
        vpternlogq      $0x96, %ymm30, %ymm28, %ymm19

        vprolq  $45, %ymm16, %ymm16
        vprolq  $61, %ymm22, %ymm22
        vpternlogq      $0x96, %ymm30, %ymm28, %ymm4

        vprolq  $1, %ymm1, %ymm1
        vprolq  $6, %ymm7, %ymm7
        vpternlogq      $0x96, %ymm30, %ymm28, %ymm14

        // Chi (interleaved with the rest of Rho and with Pi): each lane becomes
        //   state(x)(y) ^= (NOT state[(x+1) mod 5][y]) AND state[(x+2) mod 5][y]
        // computed by vpternlogq imm 0xD2. Pi (the x,y -> y,(2x+3y) relabelling) is
        // realised as the register shuffle at the end of the round, below.
        vprolq  $25, %ymm13, %ymm13
        vprolq  $8, %ymm19, %ymm19
        vmovdqa64       %ymm0, %ymm30
        vpternlogq      $0xD2, %ymm12, %ymm6, %ymm30

        vprolq  $18, %ymm20, %ymm20
        vprolq  $27, %ymm4, %ymm4
        // Iota step: XOR round constant RC(i) (broadcast in %ymm29) into lane (0,0).
        vpxorq  %ymm29, %ymm30, %ymm30

        vprolq  $36, %ymm5, %ymm5
        vprolq  $10, %ymm11, %ymm11
        vmovdqa64       %ymm6, %ymm31
        vpternlogq      $0xD2, %ymm18, %ymm12, %ymm31

        vprolq  $15, %ymm17, %ymm17
        vprolq  $56, %ymm23, %ymm23
        vpternlogq      $0xD2, %ymm24, %ymm18, %ymm12

        vprolq  $62, %ymm2, %ymm2
        vprolq  $55, %ymm8, %ymm8
        vpternlogq      $0xD2, %ymm0, %ymm24, %ymm18

        vprolq  $39, %ymm14, %ymm14
        vprolq  $41, %ymm15, %ymm15
        vpternlogq      $0xD2, %ymm6, %ymm0, %ymm24
        vmovdqa64       %ymm30, %ymm0
        vmovdqa64       %ymm31, %ymm6

        vprolq  $2, %ymm21, %ymm21
        vmovdqa64       %ymm3, %ymm30
        vpternlogq      $0xD2, %ymm10, %ymm9, %ymm30
        vmovdqa64       %ymm9, %ymm31
        vpternlogq      $0xD2, %ymm16, %ymm10, %ymm31

        vpternlogq      $0xD2, %ymm22, %ymm16, %ymm10
        vpternlogq      $0xD2, %ymm3, %ymm22, %ymm16
        vpternlogq      $0xD2, %ymm9, %ymm3, %ymm22
        vmovdqa64       %ymm30, %ymm3
        vmovdqa64       %ymm31, %ymm9

        vmovdqa64       %ymm1, %ymm30
        vpternlogq      $0xD2, %ymm13, %ymm7, %ymm30
        vmovdqa64       %ymm7, %ymm31
        vpternlogq      $0xD2, %ymm19, %ymm13, %ymm31
        vpternlogq      $0xD2, %ymm20, %ymm19, %ymm13

        vpternlogq      $0xD2, %ymm1, %ymm20, %ymm19
        vpternlogq      $0xD2, %ymm7, %ymm1, %ymm20
        vmovdqa64       %ymm30, %ymm1
        vmovdqa64       %ymm31, %ymm7
        vmovdqa64       %ymm4, %ymm30
        vpternlogq      $0xD2, %ymm11, %ymm5, %ymm30

        vmovdqa64       %ymm5, %ymm31
        vpternlogq      $0xD2, %ymm17, %ymm11, %ymm31
        vpternlogq      $0xD2, %ymm23, %ymm17, %ymm11
        vpternlogq      $0xD2, %ymm4, %ymm23, %ymm17

        vpternlogq      $0xD2, %ymm5, %ymm4, %ymm23
        vmovdqa64       %ymm30, %ymm4
        vmovdqa64       %ymm31, %ymm5
        vmovdqa64       %ymm2, %ymm30
        vpternlogq      $0xD2, %ymm14, %ymm8, %ymm30
        vmovdqa64       %ymm8, %ymm31
        vpternlogq      $0xD2, %ymm15, %ymm14, %ymm31

        vpternlogq      $0xD2, %ymm21, %ymm15, %ymm14
        vpternlogq      $0xD2, %ymm2, %ymm21, %ymm15
        vpternlogq      $0xD2, %ymm8, %ymm2, %ymm21
        vmovdqa64       %ymm30, %ymm2
        vmovdqa64       %ymm31, %ymm8

// Pi/rho lane permutation: physically rotate the 25 lane registers so that at
// the next loop-head each %ymm_k again holds lane k (canonical layout). This is
// why the round body can address lanes by fixed register number.
        vmovdqa64       %ymm3, %ymm30
        vmovdqa64       %ymm18, %ymm3
        vmovdqa64       %ymm17, %ymm18
        vmovdqa64       %ymm11, %ymm17
        vmovdqa64       %ymm7, %ymm11
        vmovdqa64       %ymm10, %ymm7
        vmovdqa64       %ymm1, %ymm10
        vmovdqa64       %ymm6, %ymm1
        vmovdqa64       %ymm9, %ymm6
        vmovdqa64       %ymm22, %ymm9
        vmovdqa64       %ymm14, %ymm22
        vmovdqa64       %ymm20, %ymm14
        vmovdqa64       %ymm2, %ymm20
        vmovdqa64       %ymm12, %ymm2
        vmovdqa64       %ymm13, %ymm12
        vmovdqa64       %ymm19, %ymm13
        vmovdqa64       %ymm23, %ymm19
        vmovdqa64       %ymm15, %ymm23
        vmovdqa64       %ymm4, %ymm15
        vmovdqa64       %ymm24, %ymm4
        vmovdqa64       %ymm21, %ymm24
        vmovdqa64       %ymm8, %ymm21
        vmovdqa64       %ymm16, %ymm8
        vmovdqa64       %ymm5, %ymm16
        vmovdqa64       %ymm30, %ymm5

        decl    %r10d
        jnz     .Lkeccak_rnd_loop

// Un-transpose the 4-lane packed state back into the four separate 200-byte
// states and store them to a[] (inverse of the load/transpose prologue).
        vpunpcklqdq     %ymm1, %ymm0, %ymm25
        vpunpckhqdq     %ymm1, %ymm0, %ymm26
        vpunpcklqdq     %ymm3, %ymm2, %ymm27
        vpunpckhqdq     %ymm3, %ymm2, %ymm28
        vshufi64x2      $0, %ymm27, %ymm25, %ymm0
        vshufi64x2      $0, %ymm28, %ymm26, %ymm1
        vshufi64x2      $3, %ymm27, %ymm25, %ymm2
        vshufi64x2      $3, %ymm28, %ymm26, %ymm3
        vmovdqu64       %ymm0, 0+0(%rdi)
        vmovdqu64       %ymm1, 0+200(%rdi)
        vmovdqu64       %ymm2, 0+400(%rdi)
        vmovdqu64       %ymm3, 0+600(%rdi)
        vpunpcklqdq     %ymm5, %ymm4, %ymm25
        vpunpckhqdq     %ymm5, %ymm4, %ymm26
        vpunpcklqdq     %ymm7, %ymm6, %ymm27
        vpunpckhqdq     %ymm7, %ymm6, %ymm28
        vshufi64x2      $0, %ymm27, %ymm25, %ymm4
        vshufi64x2      $0, %ymm28, %ymm26, %ymm5
        vshufi64x2      $3, %ymm27, %ymm25, %ymm6
        vshufi64x2      $3, %ymm28, %ymm26, %ymm7
        vmovdqu64       %ymm4, 32+0(%rdi)
        vmovdqu64       %ymm5, 32+200(%rdi)
        vmovdqu64       %ymm6, 32+400(%rdi)
        vmovdqu64       %ymm7, 32+600(%rdi)
        vpunpcklqdq     %ymm9, %ymm8, %ymm25
        vpunpckhqdq     %ymm9, %ymm8, %ymm26
        vpunpcklqdq     %ymm11, %ymm10, %ymm27
        vpunpckhqdq     %ymm11, %ymm10, %ymm28
        vshufi64x2      $0, %ymm27, %ymm25, %ymm8
        vshufi64x2      $0, %ymm28, %ymm26, %ymm9
        vshufi64x2      $3, %ymm27, %ymm25, %ymm10
        vshufi64x2      $3, %ymm28, %ymm26, %ymm11
        vmovdqu64       %ymm8, 64+0(%rdi)
        vmovdqu64       %ymm9, 64+200(%rdi)
        vmovdqu64       %ymm10, 64+400(%rdi)
        vmovdqu64       %ymm11, 64+600(%rdi)
        vpunpcklqdq     %ymm13, %ymm12, %ymm25
        vpunpckhqdq     %ymm13, %ymm12, %ymm26
        vpunpcklqdq     %ymm15, %ymm14, %ymm27
        vpunpckhqdq     %ymm15, %ymm14, %ymm28
        vshufi64x2      $0, %ymm27, %ymm25, %ymm12
        vshufi64x2      $0, %ymm28, %ymm26, %ymm13
        vshufi64x2      $3, %ymm27, %ymm25, %ymm14
        vshufi64x2      $3, %ymm28, %ymm26, %ymm15
        vmovdqu64       %ymm12, 96+0(%rdi)
        vmovdqu64       %ymm13, 96+200(%rdi)
        vmovdqu64       %ymm14, 96+400(%rdi)
        vmovdqu64       %ymm15, 96+600(%rdi)
        vpunpcklqdq     %ymm17, %ymm16, %ymm25
        vpunpckhqdq     %ymm17, %ymm16, %ymm26
        vpunpcklqdq     %ymm19, %ymm18, %ymm27
        vpunpckhqdq     %ymm19, %ymm18, %ymm28
        vshufi64x2      $0, %ymm27, %ymm25, %ymm16
        vshufi64x2      $0, %ymm28, %ymm26, %ymm17
        vshufi64x2      $3, %ymm27, %ymm25, %ymm18
        vshufi64x2      $3, %ymm28, %ymm26, %ymm19
        vmovdqu64       %ymm16, 128+0(%rdi)
        vmovdqu64       %ymm17, 128+200(%rdi)
        vmovdqu64       %ymm18, 128+400(%rdi)
        vmovdqu64       %ymm19, 128+600(%rdi)
        vpunpcklqdq     %ymm21, %ymm20, %ymm25
        vpunpckhqdq     %ymm21, %ymm20, %ymm26
        vpunpcklqdq     %ymm23, %ymm22, %ymm27
        vpunpckhqdq     %ymm23, %ymm22, %ymm28
        vshufi64x2      $0, %ymm27, %ymm25, %ymm20
        vshufi64x2      $0, %ymm28, %ymm26, %ymm21
        vshufi64x2      $3, %ymm27, %ymm25, %ymm22
        vshufi64x2      $3, %ymm28, %ymm26, %ymm23
        vmovdqu64       %ymm20, 160+0(%rdi)
        vmovdqu64       %ymm21, 160+200(%rdi)
        vmovdqu64       %ymm22, 160+400(%rdi)
        vmovdqu64       %ymm23, 160+600(%rdi)
        vextracti32x4   $1, %ymm24, %xmm25
        vmovq   %xmm24, 192+0(%rdi)
        vpextrq $1, %xmm24, 192+200(%rdi)
        vmovq   %xmm25, 192+400(%rdi)
        vpextrq $1, %xmm25, 192+600(%rdi)
        vzeroupper
#if WINDOWS_ABI
// Restore the Microsoft x64 callee-saved registers spilled in the prologue.
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

        S2N_BN_SIZE_DIRECTIVE(sha3_keccak4_f1600_avx512vl)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif
