// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Conditional addition of Q to polynomial coefficients for ML-DSA
// Input a[256] (signed 32-bit words); output a[256] (signed 32-bit words)
//
// For each coefficient, if it is negative, add Q = 8380417. This maps
// centered representatives (-Q < x < Q) to non-negative representatives
// (0 <= x < Q).
//
// extern void mldsa_caddq(int32_t a[static 256]);
//
// Standard x86-64 ABI: RDI = a
// Microsoft x64 ABI:   RCX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_caddq)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_caddq)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_caddq)
        .text

#define a rdi

S2N_BN_SYMBOL(mldsa_caddq):
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
        mov     rdi, rcx
#endif

// Load constants
        vpxor   xmm0, xmm0, xmm0                    // zero in all lanes
        mov     eax, 8380417                          // MLDSA_Q
        movd    xmm1, eax
        vpbroadcastd ymm1, xmm1                      // Q in all lanes

// First batch: vectors 0-7
        vmovdqa ymm4,   [a+0]
        vmovdqa ymm5,  [a+32]
        vmovdqa ymm6,  [a+64]
        vmovdqa ymm7,  [a+96]
        vmovdqa ymm8, [a+128]
        vmovdqa ymm9, [a+160]
        vmovdqa ymm10,[a+192]
        vmovdqa ymm11,[a+224]

// Process vectors 0-3: mask = (0 > coeff), coeff += mask & Q
        vpcmpgtd ymm12, ymm0, ymm4
        vpcmpgtd ymm13, ymm0, ymm5
        vpcmpgtd ymm14, ymm0, ymm6
        vpcmpgtd ymm15, ymm0, ymm7
        vpand   ymm12, ymm12, ymm1
        vpand   ymm13, ymm13, ymm1
        vpand   ymm14, ymm14, ymm1
        vpand   ymm15, ymm15, ymm1
        vpaddd  ymm4, ymm4, ymm12
        vpaddd  ymm5, ymm5, ymm13
        vpaddd  ymm6, ymm6, ymm14
        vpaddd  ymm7, ymm7, ymm15

// Process vectors 4-7
        vpcmpgtd ymm12, ymm0, ymm8
        vpcmpgtd ymm13, ymm0, ymm9
        vpcmpgtd ymm14, ymm0, ymm10
        vpcmpgtd ymm15, ymm0, ymm11
        vpand   ymm12, ymm12, ymm1
        vpand   ymm13, ymm13, ymm1
        vpand   ymm14, ymm14, ymm1
        vpand   ymm15, ymm15, ymm1
        vpaddd  ymm8, ymm8, ymm12
        vpaddd  ymm9, ymm9, ymm13
        vpaddd  ymm10, ymm10, ymm14
        vpaddd  ymm11, ymm11, ymm15

// Store first batch
        vmovdqa   [a+0], ymm4
        vmovdqa  [a+32], ymm5
        vmovdqa  [a+64], ymm6
        vmovdqa  [a+96], ymm7
        vmovdqa [a+128], ymm8
        vmovdqa [a+160], ymm9
        vmovdqa [a+192], ymm10
        vmovdqa [a+224], ymm11

// Second batch: vectors 8-15
        vmovdqa ymm4, [a+256]
        vmovdqa ymm5, [a+288]
        vmovdqa ymm6, [a+320]
        vmovdqa ymm7, [a+352]
        vmovdqa ymm8, [a+384]
        vmovdqa ymm9, [a+416]
        vmovdqa ymm10,[a+448]
        vmovdqa ymm11,[a+480]

        vpcmpgtd ymm12, ymm0, ymm4
        vpcmpgtd ymm13, ymm0, ymm5
        vpcmpgtd ymm14, ymm0, ymm6
        vpcmpgtd ymm15, ymm0, ymm7
        vpand   ymm12, ymm12, ymm1
        vpand   ymm13, ymm13, ymm1
        vpand   ymm14, ymm14, ymm1
        vpand   ymm15, ymm15, ymm1
        vpaddd  ymm4, ymm4, ymm12
        vpaddd  ymm5, ymm5, ymm13
        vpaddd  ymm6, ymm6, ymm14
        vpaddd  ymm7, ymm7, ymm15

        vpcmpgtd ymm12, ymm0, ymm8
        vpcmpgtd ymm13, ymm0, ymm9
        vpcmpgtd ymm14, ymm0, ymm10
        vpcmpgtd ymm15, ymm0, ymm11
        vpand   ymm12, ymm12, ymm1
        vpand   ymm13, ymm13, ymm1
        vpand   ymm14, ymm14, ymm1
        vpand   ymm15, ymm15, ymm1
        vpaddd  ymm8, ymm8, ymm12
        vpaddd  ymm9, ymm9, ymm13
        vpaddd  ymm10, ymm10, ymm14
        vpaddd  ymm11, ymm11, ymm15

// Store second batch
        vmovdqa [a+256], ymm4
        vmovdqa [a+288], ymm5
        vmovdqa [a+320], ymm6
        vmovdqa [a+352], ymm7
        vmovdqa [a+384], ymm8
        vmovdqa [a+416], ymm9
        vmovdqa [a+448], ymm10
        vmovdqa [a+480], ymm11

// Third batch: vectors 16-23
        vmovdqa ymm4, [a+512]
        vmovdqa ymm5, [a+544]
        vmovdqa ymm6, [a+576]
        vmovdqa ymm7, [a+608]
        vmovdqa ymm8, [a+640]
        vmovdqa ymm9, [a+672]
        vmovdqa ymm10,[a+704]
        vmovdqa ymm11,[a+736]

        vpcmpgtd ymm12, ymm0, ymm4
        vpcmpgtd ymm13, ymm0, ymm5
        vpcmpgtd ymm14, ymm0, ymm6
        vpcmpgtd ymm15, ymm0, ymm7
        vpand   ymm12, ymm12, ymm1
        vpand   ymm13, ymm13, ymm1
        vpand   ymm14, ymm14, ymm1
        vpand   ymm15, ymm15, ymm1
        vpaddd  ymm4, ymm4, ymm12
        vpaddd  ymm5, ymm5, ymm13
        vpaddd  ymm6, ymm6, ymm14
        vpaddd  ymm7, ymm7, ymm15

        vpcmpgtd ymm12, ymm0, ymm8
        vpcmpgtd ymm13, ymm0, ymm9
        vpcmpgtd ymm14, ymm0, ymm10
        vpcmpgtd ymm15, ymm0, ymm11
        vpand   ymm12, ymm12, ymm1
        vpand   ymm13, ymm13, ymm1
        vpand   ymm14, ymm14, ymm1
        vpand   ymm15, ymm15, ymm1
        vpaddd  ymm8, ymm8, ymm12
        vpaddd  ymm9, ymm9, ymm13
        vpaddd  ymm10, ymm10, ymm14
        vpaddd  ymm11, ymm11, ymm15

// Store third batch
        vmovdqa [a+512], ymm4
        vmovdqa [a+544], ymm5
        vmovdqa [a+576], ymm6
        vmovdqa [a+608], ymm7
        vmovdqa [a+640], ymm8
        vmovdqa [a+672], ymm9
        vmovdqa [a+704], ymm10
        vmovdqa [a+736], ymm11

// Fourth batch: vectors 24-31
        vmovdqa ymm4, [a+768]
        vmovdqa ymm5, [a+800]
        vmovdqa ymm6, [a+832]
        vmovdqa ymm7, [a+864]
        vmovdqa ymm8, [a+896]
        vmovdqa ymm9, [a+928]
        vmovdqa ymm10,[a+960]
        vmovdqa ymm11,[a+992]

        vpcmpgtd ymm12, ymm0, ymm4
        vpcmpgtd ymm13, ymm0, ymm5
        vpcmpgtd ymm14, ymm0, ymm6
        vpcmpgtd ymm15, ymm0, ymm7
        vpand   ymm12, ymm12, ymm1
        vpand   ymm13, ymm13, ymm1
        vpand   ymm14, ymm14, ymm1
        vpand   ymm15, ymm15, ymm1
        vpaddd  ymm4, ymm4, ymm12
        vpaddd  ymm5, ymm5, ymm13
        vpaddd  ymm6, ymm6, ymm14
        vpaddd  ymm7, ymm7, ymm15

        vpcmpgtd ymm12, ymm0, ymm8
        vpcmpgtd ymm13, ymm0, ymm9
        vpcmpgtd ymm14, ymm0, ymm10
        vpcmpgtd ymm15, ymm0, ymm11
        vpand   ymm12, ymm12, ymm1
        vpand   ymm13, ymm13, ymm1
        vpand   ymm14, ymm14, ymm1
        vpand   ymm15, ymm15, ymm1
        vpaddd  ymm8, ymm8, ymm12
        vpaddd  ymm9, ymm9, ymm13
        vpaddd  ymm10, ymm10, ymm14
        vpaddd  ymm11, ymm11, ymm15

// Store final batch
        vmovdqa [a+768], ymm4
        vmovdqa [a+800], ymm5
        vmovdqa [a+832], ymm6
        vmovdqa [a+864], ymm7
        vmovdqa [a+896], ymm8
        vmovdqa [a+928], ymm9
        vmovdqa [a+960], ymm10
        vmovdqa [a+992], ymm11

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
        CFI_INC_RSP(176)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_caddq)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
