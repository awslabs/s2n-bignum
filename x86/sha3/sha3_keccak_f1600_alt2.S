// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, with AVX2
// Input a[25], rc[24]; output a[25]
//
// The input/output argument is a 25-element Keccak array, replaced by its
// Keccak-f1600 permutation with the round constants rc, as by
// sha3_keccak_f1600 (this is the same function, with AVX2).
//
// With lane (x, y) = a[x + 5 y] over Z5 x Z5, pi is the linear map
// (x, y) -> (y, 2x + 3y), so it maps each line through the origin onto
// another. The state is kept as these six lines without the origin, four
// lanes to a ymm register: R_m (ymm1 + m, m = 0..4) holds the lanes (t, m t)
// and K (ymm6) the lanes (0, t), t = 1..4, and lane (0, 0) is in all four
// quadwords of ymm0, so that pi moves no lane between registers, only
// within them. For theta the lanes of each R_m are in increasing order of
// x and those of K of y: the column parities C[1..4] are then the XOR of
// the five R_m. For chi the lanes of R_1..R_4 and K are in increasing
// order of y: blends gather from them the columns x = 1..4 of the rows
// y = 1..4 (column 0 is K), chi is applied to whole columns, and blends
// put the results back into the lines; row 0 is R_0 with lane (0, 0).
// vpermq goes between the two orders, after rho (with pi) and after chi.
// The instructions of a round are in the order of a list schedule, each
// marked with its step; the rotation counts of rho are in a table after
// the code, read RIP-relatively.
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
// extern void sha3_keccak_f1600_alt2(uint64_t a[S2N_BIGNUM_STATIC 25],
//                                    const uint64_t rc[S2N_BIGNUM_STATIC 24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak_f1600_alt2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak_f1600_alt2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak_f1600_alt2)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak_f1600_alt2):
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

        lea     rax, [rip+Lsha3_keccak_f1600_alt2_rotations]
        vpbroadcastq ymm0, QWORD PTR [rdi]
        vmovdqu ymm1, YMMWORD PTR [rdi+8]
        vmovq   xmm2, QWORD PTR [rdi+48]
        vpinsrq xmm2, xmm2, QWORD PTR [rdi+96], 1
        vmovq   xmm7, QWORD PTR [rdi+144]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+192], 1
        vinserti128 ymm2, ymm2, xmm7, 1
        vmovq   xmm3, QWORD PTR [rdi+88]
        vpinsrq xmm3, xmm3, QWORD PTR [rdi+176], 1
        vmovq   xmm7, QWORD PTR [rdi+64]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+152], 1
        vinserti128 ymm3, ymm3, xmm7, 1
        vmovq   xmm4, QWORD PTR [rdi+128]
        vpinsrq xmm4, xmm4, QWORD PTR [rdi+56], 1
        vmovq   xmm7, QWORD PTR [rdi+184]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+112], 1
        vinserti128 ymm4, ymm4, xmm7, 1
        vmovq   xmm5, QWORD PTR [rdi+168]
        vpinsrq xmm5, xmm5, QWORD PTR [rdi+136], 1
        vmovq   xmm7, QWORD PTR [rdi+104]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+72], 1
        vinserti128 ymm5, ymm5, xmm7, 1
        vmovq   xmm6, QWORD PTR [rdi+40]
        vpinsrq xmm6, xmm6, QWORD PTR [rdi+80], 1
        vmovq   xmm7, QWORD PTR [rdi+120]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+160], 1
        vinserti128 ymm6, ymm6, xmm7, 1
        mov     ecx, 24

        // .balign 32, written as the NOPs that GNU as pads with (clang pads
        // with others)
#if WINDOWS_ABI
        .byte   0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00
        .byte   0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00
        .byte   0x0f, 0x1f, 0x00
#else
        .byte   0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00
        .byte   0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00
#endif
Lsha3_keccak_f1600_alt2_loop:
        vpunpcklqdq ymm7, ymm6, ymm6                    // theta
        vpxor   ymm8, ymm1, ymm2                        // theta
        vpxor   ymm9, ymm3, ymm4                        // theta
        vpbroadcastq ymm10, QWORD PTR [rsi+0]           // iota
        vpunpckhqdq ymm11, ymm6, ymm6                   // theta
        vpxor   ymm8, ymm8, ymm5                        // theta
        vpxor   ymm7, ymm11, ymm7                       // theta
        vpxor   ymm8, ymm8, ymm9                        // theta
        vpermq  ymm9, ymm7, 0x4e                        // theta
        vpsrlq  ymm11, ymm8, 63                         // theta
        vpaddq  ymm12, ymm8, ymm8                       // theta
        vpor    ymm11, ymm11, ymm12                     // theta
        vpermq  ymm12, ymm8, 0x90                       // theta
        vpermq  ymm13, ymm11, 0x39                      // theta
        vpxor   ymm7, ymm9, ymm7                        // theta
        vpermq  ymm9, ymm11, 0x00                       // theta
        vpxor   ymm7, ymm7, ymm0                        // theta
        vpermq  ymm8, ymm8, 0xff                        // theta
        vpsrlq  ymm11, ymm7, 63                         // theta
        vpaddq  ymm14, ymm7, ymm7                       // theta
        vpblendd ymm7, ymm12, ymm7, 0x03                // theta
        vpor    ymm11, ymm11, ymm14                     // theta
        vpblendd ymm11, ymm13, ymm11, 0xc0              // theta
        vpxor   ymm8, ymm8, ymm9                        // theta
        vpxor   ymm7, ymm11, ymm7                       // theta
        vpxor   ymm9, ymm8, ymm6                        // theta
        vpxor   ymm8, ymm8, ymm0                        // theta
        vpxor   ymm11, ymm3, ymm7                       // theta
        vpxor   ymm12, ymm5, ymm7                       // theta
        vpxor   ymm13, ymm1, ymm7                       // theta
        vpsrlvq ymm14, ymm12, YMMWORD PTR [rax+288]     // rho
        vpsllvq ymm12, ymm12, YMMWORD PTR [rax+256]     // rho
        vpxor   ymm15, ymm4, ymm7                       // theta
        vpsllvq ymm0, ymm9, YMMWORD PTR [rax+320]       // rho
        vpsrlvq ymm1, ymm11, YMMWORD PTR [rax+160]      // rho
        vpor    ymm12, ymm12, ymm14                     // rho
        vpsrlvq ymm9, ymm9, YMMWORD PTR [rax+352]       // rho
        vpsllvq ymm11, ymm11, YMMWORD PTR [rax+128]     // rho
        vpermq  ymm12, ymm12, 0x1b                      // pi
        vpor    ymm9, ymm9, ymm0                        // rho
        vpor    ymm11, ymm11, ymm1                      // rho
        vpxor   ymm7, ymm2, ymm7                        // theta
        vpermq  ymm9, ymm9, 0x8d                        // pi
        vpsrlvq ymm14, ymm13, YMMWORD PTR [rax+32]      // rho
        vpsllvq ymm13, ymm13, YMMWORD PTR [rax+0]       // rho
        vpermq  ymm11, ymm11, 0x8d                      // pi
        vpsrlvq ymm0, ymm15, YMMWORD PTR [rax+224]      // rho
        vpsllvq ymm15, ymm15, YMMWORD PTR [rax+192]     // rho
        vpor    ymm13, ymm13, ymm14                     // rho
        vpor    ymm14, ymm15, ymm0                      // rho
        vpermq  ymm13, ymm13, 0x72                      // pi
        vpblendd ymm15, ymm12, ymm14, 0x03              // chi
        vpblendd ymm0, ymm12, ymm14, 0xc0               // chi
        vpblendd ymm1, ymm9, ymm11, 0xc0                // chi
        vpblendd ymm2, ymm12, ymm14, 0x0c               // chi
        vpblendd ymm3, ymm9, ymm11, 0x30                // chi
        vpblendd ymm4, ymm9, ymm11, 0x03                // chi
        vpsllvq ymm5, ymm7, YMMWORD PTR [rax+64]        // rho
        vpblendd ymm12, ymm12, ymm14, 0x30              // chi
        vpblendd ymm9, ymm9, ymm11, 0x0c                // chi
        vpsrlvq ymm7, ymm7, YMMWORD PTR [rax+96]        // rho
        vpblendd ymm11, ymm2, ymm1, 0xf0                // chi
        vpblendd ymm12, ymm12, ymm4, 0x0f               // chi
        vpblendd ymm14, ymm0, ymm3, 0x33                // chi
        vpblendd ymm9, ymm15, ymm9, 0xcc                // chi
        vpor    ymm7, ymm5, ymm7                        // rho
        vpandn  ymm15, ymm13, ymm11                     // chi
        vpandn  ymm0, ymm12, ymm13                      // chi
        vpandn  ymm1, ymm9, ymm12                       // chi
        vpandn  ymm2, ymm14, ymm9                       // chi
        vpermq  ymm3, ymm7, 0x3e                        // chi
        vpermq  ymm4, ymm7, 0xf9                        // chi
        vpxor   ymm2, ymm11, ymm2                       // chi
        vpxor   ymm1, ymm14, ymm1                       // chi
        vpxor   ymm12, ymm12, ymm15                     // chi
        vpxor   ymm9, ymm9, ymm0                        // chi
        vpblendd ymm15, ymm2, ymm1, 0x30                // chi
        vpblendd ymm0, ymm9, ymm12, 0x0c                // chi
        vpblendd ymm5, ymm9, ymm12, 0x03                // chi
        vpblendd ymm6, ymm9, ymm12, 0x30                // chi
        vpandn  ymm11, ymm11, ymm14                     // chi
        vpblendd ymm14, ymm4, ymm8, 0xc0                // chi
        vpblendd ymm3, ymm3, ymm8, 0x30                 // chi
        vpblendd ymm4, ymm2, ymm1, 0x03                 // chi
        vpblendd ymm15, ymm15, ymm5, 0x0f               // chi
        vpxor   ymm11, ymm13, ymm11                     // chi
        vpblendd ymm13, ymm2, ymm1, 0xc0                // chi
        vpblendd ymm0, ymm4, ymm0, 0xcc                 // chi
        vpblendd ymm1, ymm2, ymm1, 0x0c                 // chi
        vpblendd ymm13, ymm13, ymm6, 0x33               // chi
        vpandn  ymm2, ymm14, ymm3                       // chi
        vpermq  ymm4, ymm0, 0x72                        // chi
        vpermq  ymm3, ymm13, 0x8d                       // chi
        vpblendd ymm9, ymm9, ymm12, 0xc0                // chi
        vpxor   ymm12, ymm7, ymm2                       // chi
        vpermq  ymm5, ymm15, 0x1b                       // chi
        vpblendd ymm2, ymm1, ymm9, 0xf0                 // chi
        vpandn  ymm7, ymm7, ymm14                       // chi
        vpermq  ymm7, ymm7, 0x00                        // chi
        vpxor   ymm7, ymm8, ymm7                        // chi
        vpxor   ymm0, ymm10, ymm7                       // iota
        vmovdqa ymm1, ymm12
        vmovdqa ymm6, ymm11

        // .balign 32, written as the NOPs of GNU as as above (the same for
        // both ABIs here)
        .byte   0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00
        .byte   0x90
        add     rsi, 8
        dec     ecx
        jnz     Lsha3_keccak_f1600_alt2_loop

        vmovq   QWORD PTR [rdi], xmm0
        vmovdqu YMMWORD PTR [rdi+8], ymm1
        vmovq   QWORD PTR [rdi+48], xmm2
        vpextrq QWORD PTR [rdi+96], xmm2, 1
        vextracti128 xmm7, ymm2, 1
        vmovq   QWORD PTR [rdi+144], xmm7
        vpextrq QWORD PTR [rdi+192], xmm7, 1
        vmovq   QWORD PTR [rdi+88], xmm3
        vpextrq QWORD PTR [rdi+176], xmm3, 1
        vextracti128 xmm7, ymm3, 1
        vmovq   QWORD PTR [rdi+64], xmm7
        vpextrq QWORD PTR [rdi+152], xmm7, 1
        vmovq   QWORD PTR [rdi+128], xmm4
        vpextrq QWORD PTR [rdi+56], xmm4, 1
        vextracti128 xmm7, ymm4, 1
        vmovq   QWORD PTR [rdi+184], xmm7
        vpextrq QWORD PTR [rdi+112], xmm7, 1
        vmovq   QWORD PTR [rdi+168], xmm5
        vpextrq QWORD PTR [rdi+136], xmm5, 1
        vextracti128 xmm7, ymm5, 1
        vmovq   QWORD PTR [rdi+104], xmm7
        vpextrq QWORD PTR [rdi+72], xmm7, 1
        vmovq   QWORD PTR [rdi+40], xmm6
        vpextrq QWORD PTR [rdi+80], xmm6, 1
        vextracti128 xmm7, ymm6, 1
        vmovq   QWORD PTR [rdi+120], xmm7
        vpextrq QWORD PTR [rdi+160], xmm7, 1

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

S2N_BN_SIZE_DIRECTIVE(sha3_keccak_f1600_alt2)

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 32
Lsha3_keccak_f1600_alt2_rotations:
        .quad   1, 62, 28, 27
        .quad   63, 2, 36, 37
        .quad   44, 43, 21, 14
        .quad   20, 21, 43, 50
        .quad   10, 61, 55, 8
        .quad   54, 3, 9, 56
        .quad   45, 6, 56, 39
        .quad   19, 58, 8, 25
        .quad   2, 15, 25, 20
        .quad   62, 49, 39, 44
        .quad   36, 3, 41, 18
        .quad   28, 61, 23, 46

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
