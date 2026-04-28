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

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_caddq)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_caddq)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_caddq)
        .text

#define a %rdi

S2N_BN_SYMBOL(mldsa_caddq):
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
        movq    %rcx, %rdi
#endif

// Load constants
        vpxor   %xmm0, %xmm0, %xmm0 // zero in all lanes
        movl    $8380417, %eax // MLDSA_Q
        movd    %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1 // Q in all lanes

// First batch: vectors 0-7
        vmovdqa 0(a), %ymm4
        vmovdqa 32(a), %ymm5
        vmovdqa 64(a), %ymm6
        vmovdqa 96(a), %ymm7
        vmovdqa 128(a), %ymm8
        vmovdqa 160(a), %ymm9
        vmovdqa 192(a), %ymm10
        vmovdqa 224(a), %ymm11

// Process vectors 0-3: mask = (0 > coeff), coeff += mask & Q
        vpcmpgtd %ymm4, %ymm0, %ymm12
        vpcmpgtd %ymm5, %ymm0, %ymm13
        vpcmpgtd %ymm6, %ymm0, %ymm14
        vpcmpgtd %ymm7, %ymm0, %ymm15
        vpand   %ymm1, %ymm12, %ymm12
        vpand   %ymm1, %ymm13, %ymm13
        vpand   %ymm1, %ymm14, %ymm14
        vpand   %ymm1, %ymm15, %ymm15
        vpaddd  %ymm12, %ymm4, %ymm4
        vpaddd  %ymm13, %ymm5, %ymm5
        vpaddd  %ymm14, %ymm6, %ymm6
        vpaddd  %ymm15, %ymm7, %ymm7

// Process vectors 4-7
        vpcmpgtd %ymm8, %ymm0, %ymm12
        vpcmpgtd %ymm9, %ymm0, %ymm13
        vpcmpgtd %ymm10, %ymm0, %ymm14
        vpcmpgtd %ymm11, %ymm0, %ymm15
        vpand   %ymm1, %ymm12, %ymm12
        vpand   %ymm1, %ymm13, %ymm13
        vpand   %ymm1, %ymm14, %ymm14
        vpand   %ymm1, %ymm15, %ymm15
        vpaddd  %ymm12, %ymm8, %ymm8
        vpaddd  %ymm13, %ymm9, %ymm9
        vpaddd  %ymm14, %ymm10, %ymm10
        vpaddd  %ymm15, %ymm11, %ymm11

// Store first batch
        vmovdqa   %ymm4, 0(a)
        vmovdqa  %ymm5, 32(a)
        vmovdqa  %ymm6, 64(a)
        vmovdqa  %ymm7, 96(a)
        vmovdqa %ymm8, 128(a)
        vmovdqa %ymm9, 160(a)
        vmovdqa %ymm10, 192(a)
        vmovdqa %ymm11, 224(a)

// Second batch: vectors 8-15
        vmovdqa 256(a), %ymm4
        vmovdqa 288(a), %ymm5
        vmovdqa 320(a), %ymm6
        vmovdqa 352(a), %ymm7
        vmovdqa 384(a), %ymm8
        vmovdqa 416(a), %ymm9
        vmovdqa 448(a), %ymm10
        vmovdqa 480(a), %ymm11

        vpcmpgtd %ymm4, %ymm0, %ymm12
        vpcmpgtd %ymm5, %ymm0, %ymm13
        vpcmpgtd %ymm6, %ymm0, %ymm14
        vpcmpgtd %ymm7, %ymm0, %ymm15
        vpand   %ymm1, %ymm12, %ymm12
        vpand   %ymm1, %ymm13, %ymm13
        vpand   %ymm1, %ymm14, %ymm14
        vpand   %ymm1, %ymm15, %ymm15
        vpaddd  %ymm12, %ymm4, %ymm4
        vpaddd  %ymm13, %ymm5, %ymm5
        vpaddd  %ymm14, %ymm6, %ymm6
        vpaddd  %ymm15, %ymm7, %ymm7

        vpcmpgtd %ymm8, %ymm0, %ymm12
        vpcmpgtd %ymm9, %ymm0, %ymm13
        vpcmpgtd %ymm10, %ymm0, %ymm14
        vpcmpgtd %ymm11, %ymm0, %ymm15
        vpand   %ymm1, %ymm12, %ymm12
        vpand   %ymm1, %ymm13, %ymm13
        vpand   %ymm1, %ymm14, %ymm14
        vpand   %ymm1, %ymm15, %ymm15
        vpaddd  %ymm12, %ymm8, %ymm8
        vpaddd  %ymm13, %ymm9, %ymm9
        vpaddd  %ymm14, %ymm10, %ymm10
        vpaddd  %ymm15, %ymm11, %ymm11

// Store second batch
        vmovdqa %ymm4, 256(a)
        vmovdqa %ymm5, 288(a)
        vmovdqa %ymm6, 320(a)
        vmovdqa %ymm7, 352(a)
        vmovdqa %ymm8, 384(a)
        vmovdqa %ymm9, 416(a)
        vmovdqa %ymm10, 448(a)
        vmovdqa %ymm11, 480(a)

// Third batch: vectors 16-23
        vmovdqa 512(a), %ymm4
        vmovdqa 544(a), %ymm5
        vmovdqa 576(a), %ymm6
        vmovdqa 608(a), %ymm7
        vmovdqa 640(a), %ymm8
        vmovdqa 672(a), %ymm9
        vmovdqa 704(a), %ymm10
        vmovdqa 736(a), %ymm11

        vpcmpgtd %ymm4, %ymm0, %ymm12
        vpcmpgtd %ymm5, %ymm0, %ymm13
        vpcmpgtd %ymm6, %ymm0, %ymm14
        vpcmpgtd %ymm7, %ymm0, %ymm15
        vpand   %ymm1, %ymm12, %ymm12
        vpand   %ymm1, %ymm13, %ymm13
        vpand   %ymm1, %ymm14, %ymm14
        vpand   %ymm1, %ymm15, %ymm15
        vpaddd  %ymm12, %ymm4, %ymm4
        vpaddd  %ymm13, %ymm5, %ymm5
        vpaddd  %ymm14, %ymm6, %ymm6
        vpaddd  %ymm15, %ymm7, %ymm7

        vpcmpgtd %ymm8, %ymm0, %ymm12
        vpcmpgtd %ymm9, %ymm0, %ymm13
        vpcmpgtd %ymm10, %ymm0, %ymm14
        vpcmpgtd %ymm11, %ymm0, %ymm15
        vpand   %ymm1, %ymm12, %ymm12
        vpand   %ymm1, %ymm13, %ymm13
        vpand   %ymm1, %ymm14, %ymm14
        vpand   %ymm1, %ymm15, %ymm15
        vpaddd  %ymm12, %ymm8, %ymm8
        vpaddd  %ymm13, %ymm9, %ymm9
        vpaddd  %ymm14, %ymm10, %ymm10
        vpaddd  %ymm15, %ymm11, %ymm11

// Store third batch
        vmovdqa %ymm4, 512(a)
        vmovdqa %ymm5, 544(a)
        vmovdqa %ymm6, 576(a)
        vmovdqa %ymm7, 608(a)
        vmovdqa %ymm8, 640(a)
        vmovdqa %ymm9, 672(a)
        vmovdqa %ymm10, 704(a)
        vmovdqa %ymm11, 736(a)

// Fourth batch: vectors 24-31
        vmovdqa 768(a), %ymm4
        vmovdqa 800(a), %ymm5
        vmovdqa 832(a), %ymm6
        vmovdqa 864(a), %ymm7
        vmovdqa 896(a), %ymm8
        vmovdqa 928(a), %ymm9
        vmovdqa 960(a), %ymm10
        vmovdqa 992(a), %ymm11

        vpcmpgtd %ymm4, %ymm0, %ymm12
        vpcmpgtd %ymm5, %ymm0, %ymm13
        vpcmpgtd %ymm6, %ymm0, %ymm14
        vpcmpgtd %ymm7, %ymm0, %ymm15
        vpand   %ymm1, %ymm12, %ymm12
        vpand   %ymm1, %ymm13, %ymm13
        vpand   %ymm1, %ymm14, %ymm14
        vpand   %ymm1, %ymm15, %ymm15
        vpaddd  %ymm12, %ymm4, %ymm4
        vpaddd  %ymm13, %ymm5, %ymm5
        vpaddd  %ymm14, %ymm6, %ymm6
        vpaddd  %ymm15, %ymm7, %ymm7

        vpcmpgtd %ymm8, %ymm0, %ymm12
        vpcmpgtd %ymm9, %ymm0, %ymm13
        vpcmpgtd %ymm10, %ymm0, %ymm14
        vpcmpgtd %ymm11, %ymm0, %ymm15
        vpand   %ymm1, %ymm12, %ymm12
        vpand   %ymm1, %ymm13, %ymm13
        vpand   %ymm1, %ymm14, %ymm14
        vpand   %ymm1, %ymm15, %ymm15
        vpaddd  %ymm12, %ymm8, %ymm8
        vpaddd  %ymm13, %ymm9, %ymm9
        vpaddd  %ymm14, %ymm10, %ymm10
        vpaddd  %ymm15, %ymm11, %ymm11

// Store final batch
        vmovdqa %ymm4, 768(a)
        vmovdqa %ymm5, 800(a)
        vmovdqa %ymm6, 832(a)
        vmovdqa %ymm7, 864(a)
        vmovdqa %ymm8, 896(a)
        vmovdqa %ymm9, 928(a)
        vmovdqa %ymm10, 960(a)
        vmovdqa %ymm11, 992(a)

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
        CFI_INC_RSP(176)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_caddq)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
