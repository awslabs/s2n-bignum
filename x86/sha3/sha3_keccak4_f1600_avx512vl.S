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
// subroutine is inlined into the 4x wrapper, and its embedded rip-relative
// round-constant table is replaced by the caller-supplied rc pointer (RSI),
// matching the sha3_keccak4_f1600 convention, so the object is
// relocation-free (rep;ret -> ret; alignment padding removed). The whole
// 25-lane state is register-resident in ymm0..ymm24 for the entire 24-round
// loop (no stack spill); ymm25..ymm31 are scratch.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
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

// Load the four independent 200-byte states from a[] and transpose them into
// the register-resident 4-lane packed layout: ymm_k holds Keccak lane k of all
// four states (lane j of ymm_k = state j's word k). vpunpck{l,h}qdq + vshufi64x2
// do the 4-way interleave; lane 24 (the odd one) is packed via vmovq/vpinsrq/
// vinserti32x4 into the low 128 bits of ymm24.
        vmovdqu64       ymm25, [rdi+0+0]
        vmovdqu64       ymm26, [rdi+0+200]
        vmovdqu64       ymm27, [rdi+0+400]
        vmovdqu64       ymm28, [rdi+0+600]
        vpunpcklqdq     ymm29, ymm25, ymm26
        vpunpckhqdq     ymm30, ymm25, ymm26
        vpunpcklqdq     ymm25, ymm27, ymm28
        vpunpckhqdq     ymm26, ymm27, ymm28
        vshufi64x2      ymm0, ymm29, ymm25, 0
        vshufi64x2      ymm1, ymm30, ymm26, 0
        vshufi64x2      ymm2, ymm29, ymm25, 3
        vshufi64x2      ymm3, ymm30, ymm26, 3
        vmovdqu64       ymm25, [rdi+32+0]
        vmovdqu64       ymm26, [rdi+32+200]
        vmovdqu64       ymm27, [rdi+32+400]
        vmovdqu64       ymm28, [rdi+32+600]
        vpunpcklqdq     ymm29, ymm25, ymm26
        vpunpckhqdq     ymm30, ymm25, ymm26
        vpunpcklqdq     ymm25, ymm27, ymm28
        vpunpckhqdq     ymm26, ymm27, ymm28
        vshufi64x2      ymm4, ymm29, ymm25, 0
        vshufi64x2      ymm5, ymm30, ymm26, 0
        vshufi64x2      ymm6, ymm29, ymm25, 3
        vshufi64x2      ymm7, ymm30, ymm26, 3
        vmovdqu64       ymm25, [rdi+64+0]
        vmovdqu64       ymm26, [rdi+64+200]
        vmovdqu64       ymm27, [rdi+64+400]
        vmovdqu64       ymm28, [rdi+64+600]
        vpunpcklqdq     ymm29, ymm25, ymm26
        vpunpckhqdq     ymm30, ymm25, ymm26
        vpunpcklqdq     ymm25, ymm27, ymm28
        vpunpckhqdq     ymm26, ymm27, ymm28
        vshufi64x2      ymm8, ymm29, ymm25, 0
        vshufi64x2      ymm9, ymm30, ymm26, 0
        vshufi64x2      ymm10, ymm29, ymm25, 3
        vshufi64x2      ymm11, ymm30, ymm26, 3
        vmovdqu64       ymm25, [rdi+96+0]
        vmovdqu64       ymm26, [rdi+96+200]
        vmovdqu64       ymm27, [rdi+96+400]
        vmovdqu64       ymm28, [rdi+96+600]
        vpunpcklqdq     ymm29, ymm25, ymm26
        vpunpckhqdq     ymm30, ymm25, ymm26
        vpunpcklqdq     ymm25, ymm27, ymm28
        vpunpckhqdq     ymm26, ymm27, ymm28
        vshufi64x2      ymm12, ymm29, ymm25, 0
        vshufi64x2      ymm13, ymm30, ymm26, 0
        vshufi64x2      ymm14, ymm29, ymm25, 3
        vshufi64x2      ymm15, ymm30, ymm26, 3
        vmovdqu64       ymm25, [rdi+128+0]
        vmovdqu64       ymm26, [rdi+128+200]
        vmovdqu64       ymm27, [rdi+128+400]
        vmovdqu64       ymm28, [rdi+128+600]
        vpunpcklqdq     ymm29, ymm25, ymm26
        vpunpckhqdq     ymm30, ymm25, ymm26
        vpunpcklqdq     ymm25, ymm27, ymm28
        vpunpckhqdq     ymm26, ymm27, ymm28
        vshufi64x2      ymm16, ymm29, ymm25, 0
        vshufi64x2      ymm17, ymm30, ymm26, 0
        vshufi64x2      ymm18, ymm29, ymm25, 3
        vshufi64x2      ymm19, ymm30, ymm26, 3
        vmovdqu64       ymm25, [rdi+160+0]
        vmovdqu64       ymm26, [rdi+160+200]
        vmovdqu64       ymm27, [rdi+160+400]
        vmovdqu64       ymm28, [rdi+160+600]
        vpunpcklqdq     ymm29, ymm25, ymm26
        vpunpckhqdq     ymm30, ymm25, ymm26
        vpunpcklqdq     ymm25, ymm27, ymm28
        vpunpckhqdq     ymm26, ymm27, ymm28
        vshufi64x2      ymm20, ymm29, ymm25, 0
        vshufi64x2      ymm21, ymm30, ymm26, 0
        vshufi64x2      ymm22, ymm29, ymm25, 3
        vshufi64x2      ymm23, ymm30, ymm26, 3
        vmovq   xmm24, [rdi+192+0]
        vpinsrq xmm24, xmm24, [rdi+192+200], 1
        vmovq   xmm25, [rdi+192+400]
        vpinsrq xmm25, xmm25, [rdi+192+600], 1
        vinserti32x4    ymm24, ymm24, xmm25, 1

// 24-round permutation loop. r10d counts rounds down (24 -> 0); r11 walks the
// round-constant array (r11 = rc + 8*i, advanced once per round).
        mov     r10d, 24
        mov     r11, rsi
.Lkeccak_rnd_loop:
// One Keccak round on all four lanes at once. The theta/rho/pi/chi/iota steps
// are software-pipelined (interleaved) for throughput, so they do not appear
// as cleanly separated blocks:
//   Theta: column parities C[x] via 3-input XOR (vpternlogq imm 0x96), then
//          D[x] = C[x-1] ^ rotl(C[x+1],1) (vprolq by 1) folded into every lane.
//   Rho:   per-lane fixed left-rotations (vprolq by the rho offsets).
//   Pi:    lane permutation, realised by the 25-register vmovdqa64 shuffle at
//          the end of the round (so inputs are back in canonical ymm_k slots).
//   Chi:   a ^ ((~b) & c) via vpternlogq imm 0xD2.
//   Iota:  RC[i] XORed into lane (0,0); see the vpbroadcastq below.

        // Theta, column parities: C[x] = state[x][0]^state[x][1]^...^state[x][4]
        vmovdqa64       ymm25, ymm0
        vpternlogq      ymm25, ymm10, ymm5, 0x96
        vmovdqa64       ymm26, ymm1
        vpternlogq      ymm26, ymm6, ymm11, 0x96
        vmovdqa64       ymm27, ymm2
        vpternlogq      ymm27, ymm7, ymm12, 0x96

        vmovdqa64       ymm28, ymm3
        vpternlogq      ymm28, ymm8, ymm13, 0x96
        vmovdqa64       ymm29, ymm4
        vpternlogq      ymm29, ymm9, ymm14, 0x96
        vpternlogq      ymm25, ymm15, ymm20, 0x96

        vpternlogq      ymm26, ymm16, ymm21, 0x96
        vpternlogq      ymm27, ymm17, ymm22, 0x96
        vpternlogq      ymm28, ymm18, ymm23, 0x96

        // Theta, D values: D[x] = C[(x+4) mod 5] XOR rotl(C[(x+1) mod 5], 1)
        vprolq  ymm30, ymm26, 1
        vprolq  ymm31, ymm27, 1
        vpternlogq      ymm29, ymm19, ymm24, 0x96

        // Theta, apply to state: state[x][y] ^= D[x]  (D[x] held in ymm29..ymm31,
        // folded into every lane; theta and the D computation stay interleaved)
        vpternlogq      ymm0, ymm29, ymm30, 0x96
        vpternlogq      ymm10, ymm29, ymm30, 0x96
        vpternlogq      ymm20, ymm29, ymm30, 0x96

        vpternlogq      ymm5, ymm29, ymm30, 0x96
        vpternlogq      ymm15, ymm29, ymm30, 0x96
        vprolq  ymm30, ymm28, 1

        vpternlogq      ymm6, ymm25, ymm31, 0x96
        vpternlogq      ymm16, ymm25, ymm31, 0x96
        vpternlogq      ymm1, ymm25, ymm31, 0x96

        vpternlogq      ymm11, ymm25, ymm31, 0x96
        vpternlogq      ymm21, ymm25, ymm31, 0x96
        vprolq  ymm31, ymm29, 1

// Iota: broadcast this round's constant RC[i] to all four lanes and advance
// r11 to RC[i+1]; it is XORed into lane (0,0) below (vpxorq into ymm30/A[0,0]).
        vpbroadcastq    ymm29, [r11]
        add     r11, 8

        vpternlogq      ymm12, ymm26, ymm30, 0x96
        vpternlogq      ymm7, ymm26, ymm30, 0x96
        vpternlogq      ymm22, ymm26, ymm30, 0x96

        vpternlogq      ymm17, ymm26, ymm30, 0x96
        vpternlogq      ymm2, ymm26, ymm30, 0x96
        vprolq  ymm30, ymm25, 1

        // Rho (starts here, theta tail still finishing): state[x][y] = rotl(state[x][y], RHO[x][y]),
        // RHO = [ 0  1 62 28 27 ; 36 44  6 55 20 ;  3 10 43 25 39 ; 41 45 15 21  8 ; 18  2 61 56 14 ]
        // (the vprolq immediates interleaved below are exactly these offsets).
        vpternlogq      ymm3, ymm27, ymm31, 0x96
        vpternlogq      ymm13, ymm27, ymm31, 0x96
        vpternlogq      ymm23, ymm27, ymm31, 0x96

        vprolq  ymm6, ymm6, 44
        vpternlogq      ymm18, ymm27, ymm31, 0x96
        vpternlogq      ymm8, ymm27, ymm31, 0x96

        vprolq  ymm12, ymm12, 43
        vprolq  ymm18, ymm18, 21
        vpternlogq      ymm24, ymm28, ymm30, 0x96

        vprolq  ymm24, ymm24, 14
        vprolq  ymm3, ymm3, 28
        vpternlogq      ymm9, ymm28, ymm30, 0x96

        vprolq  ymm9, ymm9, 20
        vprolq  ymm10, ymm10, 3
        vpternlogq      ymm19, ymm28, ymm30, 0x96

        vprolq  ymm16, ymm16, 45
        vprolq  ymm22, ymm22, 61
        vpternlogq      ymm4, ymm28, ymm30, 0x96

        vprolq  ymm1, ymm1, 1
        vprolq  ymm7, ymm7, 6
        vpternlogq      ymm14, ymm28, ymm30, 0x96

        // Chi (interleaved with the rest of Rho and with Pi): each lane becomes
        //   state[x][y] ^= (NOT state[(x+1) mod 5][y]) AND state[(x+2) mod 5][y]
        // computed by vpternlogq imm 0xD2. Pi (the x,y -> y,(2x+3y) relabelling) is
        // realised as the register shuffle at the end of the round, below.
        vprolq  ymm13, ymm13, 25
        vprolq  ymm19, ymm19, 8
        vmovdqa64       ymm30, ymm0
        vpternlogq      ymm30, ymm6, ymm12, 0xD2

        vprolq  ymm20, ymm20, 18
        vprolq  ymm4, ymm4, 27
        // Iota step: XOR round constant RC[i] (broadcast in ymm29) into lane (0,0).
        vpxorq  ymm30, ymm30, ymm29

        vprolq  ymm5, ymm5, 36
        vprolq  ymm11, ymm11, 10
        vmovdqa64       ymm31, ymm6
        vpternlogq      ymm31, ymm12, ymm18, 0xD2

        vprolq  ymm17, ymm17, 15
        vprolq  ymm23, ymm23, 56
        vpternlogq      ymm12, ymm18, ymm24, 0xD2

        vprolq  ymm2, ymm2, 62
        vprolq  ymm8, ymm8, 55
        vpternlogq      ymm18, ymm24, ymm0, 0xD2

        vprolq  ymm14, ymm14, 39
        vprolq  ymm15, ymm15, 41
        vpternlogq      ymm24, ymm0, ymm6, 0xD2
        vmovdqa64       ymm0, ymm30
        vmovdqa64       ymm6, ymm31

        vprolq  ymm21, ymm21, 2
        vmovdqa64       ymm30, ymm3
        vpternlogq      ymm30, ymm9, ymm10, 0xD2
        vmovdqa64       ymm31, ymm9
        vpternlogq      ymm31, ymm10, ymm16, 0xD2

        vpternlogq      ymm10, ymm16, ymm22, 0xD2
        vpternlogq      ymm16, ymm22, ymm3, 0xD2
        vpternlogq      ymm22, ymm3, ymm9, 0xD2
        vmovdqa64       ymm3, ymm30
        vmovdqa64       ymm9, ymm31

        vmovdqa64       ymm30, ymm1
        vpternlogq      ymm30, ymm7, ymm13, 0xD2
        vmovdqa64       ymm31, ymm7
        vpternlogq      ymm31, ymm13, ymm19, 0xD2
        vpternlogq      ymm13, ymm19, ymm20, 0xD2

        vpternlogq      ymm19, ymm20, ymm1, 0xD2
        vpternlogq      ymm20, ymm1, ymm7, 0xD2
        vmovdqa64       ymm1, ymm30
        vmovdqa64       ymm7, ymm31
        vmovdqa64       ymm30, ymm4
        vpternlogq      ymm30, ymm5, ymm11, 0xD2

        vmovdqa64       ymm31, ymm5
        vpternlogq      ymm31, ymm11, ymm17, 0xD2
        vpternlogq      ymm11, ymm17, ymm23, 0xD2
        vpternlogq      ymm17, ymm23, ymm4, 0xD2

        vpternlogq      ymm23, ymm4, ymm5, 0xD2
        vmovdqa64       ymm4, ymm30
        vmovdqa64       ymm5, ymm31
        vmovdqa64       ymm30, ymm2
        vpternlogq      ymm30, ymm8, ymm14, 0xD2
        vmovdqa64       ymm31, ymm8
        vpternlogq      ymm31, ymm14, ymm15, 0xD2

        vpternlogq      ymm14, ymm15, ymm21, 0xD2
        vpternlogq      ymm15, ymm21, ymm2, 0xD2
        vpternlogq      ymm21, ymm2, ymm8, 0xD2
        vmovdqa64       ymm2, ymm30
        vmovdqa64       ymm8, ymm31

// Pi/rho lane permutation: physically rotate the 25 lane registers so that at
// the next loop-head each ymm_k again holds lane k (canonical layout). This is
// why the round body can address lanes by fixed register number.
        vmovdqa64       ymm30, ymm3
        vmovdqa64       ymm3, ymm18
        vmovdqa64       ymm18, ymm17
        vmovdqa64       ymm17, ymm11
        vmovdqa64       ymm11, ymm7
        vmovdqa64       ymm7, ymm10
        vmovdqa64       ymm10, ymm1
        vmovdqa64       ymm1, ymm6
        vmovdqa64       ymm6, ymm9
        vmovdqa64       ymm9, ymm22
        vmovdqa64       ymm22, ymm14
        vmovdqa64       ymm14, ymm20
        vmovdqa64       ymm20, ymm2
        vmovdqa64       ymm2, ymm12
        vmovdqa64       ymm12, ymm13
        vmovdqa64       ymm13, ymm19
        vmovdqa64       ymm19, ymm23
        vmovdqa64       ymm23, ymm15
        vmovdqa64       ymm15, ymm4
        vmovdqa64       ymm4, ymm24
        vmovdqa64       ymm24, ymm21
        vmovdqa64       ymm21, ymm8
        vmovdqa64       ymm8, ymm16
        vmovdqa64       ymm16, ymm5
        vmovdqa64       ymm5, ymm30

        dec     r10d
        jnz     .Lkeccak_rnd_loop

// Un-transpose the 4-lane packed state back into the four separate 200-byte
// states and store them to a[] (inverse of the load/transpose prologue).
        vpunpcklqdq     ymm25, ymm0, ymm1
        vpunpckhqdq     ymm26, ymm0, ymm1
        vpunpcklqdq     ymm27, ymm2, ymm3
        vpunpckhqdq     ymm28, ymm2, ymm3
        vshufi64x2      ymm0, ymm25, ymm27, 0
        vshufi64x2      ymm1, ymm26, ymm28, 0
        vshufi64x2      ymm2, ymm25, ymm27, 3
        vshufi64x2      ymm3, ymm26, ymm28, 3
        vmovdqu64       [rdi+0+0], ymm0
        vmovdqu64       [rdi+0+200], ymm1
        vmovdqu64       [rdi+0+400], ymm2
        vmovdqu64       [rdi+0+600], ymm3
        vpunpcklqdq     ymm25, ymm4, ymm5
        vpunpckhqdq     ymm26, ymm4, ymm5
        vpunpcklqdq     ymm27, ymm6, ymm7
        vpunpckhqdq     ymm28, ymm6, ymm7
        vshufi64x2      ymm4, ymm25, ymm27, 0
        vshufi64x2      ymm5, ymm26, ymm28, 0
        vshufi64x2      ymm6, ymm25, ymm27, 3
        vshufi64x2      ymm7, ymm26, ymm28, 3
        vmovdqu64       [rdi+32+0], ymm4
        vmovdqu64       [rdi+32+200], ymm5
        vmovdqu64       [rdi+32+400], ymm6
        vmovdqu64       [rdi+32+600], ymm7
        vpunpcklqdq     ymm25, ymm8, ymm9
        vpunpckhqdq     ymm26, ymm8, ymm9
        vpunpcklqdq     ymm27, ymm10, ymm11
        vpunpckhqdq     ymm28, ymm10, ymm11
        vshufi64x2      ymm8, ymm25, ymm27, 0
        vshufi64x2      ymm9, ymm26, ymm28, 0
        vshufi64x2      ymm10, ymm25, ymm27, 3
        vshufi64x2      ymm11, ymm26, ymm28, 3
        vmovdqu64       [rdi+64+0], ymm8
        vmovdqu64       [rdi+64+200], ymm9
        vmovdqu64       [rdi+64+400], ymm10
        vmovdqu64       [rdi+64+600], ymm11
        vpunpcklqdq     ymm25, ymm12, ymm13
        vpunpckhqdq     ymm26, ymm12, ymm13
        vpunpcklqdq     ymm27, ymm14, ymm15
        vpunpckhqdq     ymm28, ymm14, ymm15
        vshufi64x2      ymm12, ymm25, ymm27, 0
        vshufi64x2      ymm13, ymm26, ymm28, 0
        vshufi64x2      ymm14, ymm25, ymm27, 3
        vshufi64x2      ymm15, ymm26, ymm28, 3
        vmovdqu64       [rdi+96+0], ymm12
        vmovdqu64       [rdi+96+200], ymm13
        vmovdqu64       [rdi+96+400], ymm14
        vmovdqu64       [rdi+96+600], ymm15
        vpunpcklqdq     ymm25, ymm16, ymm17
        vpunpckhqdq     ymm26, ymm16, ymm17
        vpunpcklqdq     ymm27, ymm18, ymm19
        vpunpckhqdq     ymm28, ymm18, ymm19
        vshufi64x2      ymm16, ymm25, ymm27, 0
        vshufi64x2      ymm17, ymm26, ymm28, 0
        vshufi64x2      ymm18, ymm25, ymm27, 3
        vshufi64x2      ymm19, ymm26, ymm28, 3
        vmovdqu64       [rdi+128+0], ymm16
        vmovdqu64       [rdi+128+200], ymm17
        vmovdqu64       [rdi+128+400], ymm18
        vmovdqu64       [rdi+128+600], ymm19
        vpunpcklqdq     ymm25, ymm20, ymm21
        vpunpckhqdq     ymm26, ymm20, ymm21
        vpunpcklqdq     ymm27, ymm22, ymm23
        vpunpckhqdq     ymm28, ymm22, ymm23
        vshufi64x2      ymm20, ymm25, ymm27, 0
        vshufi64x2      ymm21, ymm26, ymm28, 0
        vshufi64x2      ymm22, ymm25, ymm27, 3
        vshufi64x2      ymm23, ymm26, ymm28, 3
        vmovdqu64       [rdi+160+0], ymm20
        vmovdqu64       [rdi+160+200], ymm21
        vmovdqu64       [rdi+160+400], ymm22
        vmovdqu64       [rdi+160+600], ymm23
        vextracti32x4   xmm25, ymm24, 1
        vmovq   [rdi+192+0], xmm24
        vpextrq [rdi+192+200], xmm24, 1
        vmovq   [rdi+192+400], xmm25
        vpextrq [rdi+192+600], xmm25, 1
        vzeroupper
#if WINDOWS_ABI
// Restore the Microsoft x64 callee-saved registers spilled in the prologue.
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

        S2N_BN_SIZE_DIRECTIVE(sha3_keccak4_f1600_avx512vl)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif
