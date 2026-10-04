// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
//
// Emitted by Ragamuffin transpiler.

// ----------------------------------------------------------------------------
// SHA-256 block data order (Intel SHA extensions, x86_64)
//
// extern void sha256_compress_hw(uint32_t state[static 8],
//                                const uint8_t *data,
//                                size_t num_blocks);
//
// SysV: RDI = state, RSI = data, RDX = num_blocks. Win64 shim copies RCX,RDX,R8.
// ----------------------------------------------------------------------------


#include "_internal_s2n_bignum_x86_att.h"



        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha256_compress_hw)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha256_compress_hw)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha256_compress_hw)
        .text

S2N_BN_SYMBOL(sha256_compress_hw):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(%rdi)
        CFI_PUSH(%rsi)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
        CFI_DEC_RSP(80)
        CFI_STACKSAVEU(%xmm6, 0)
        CFI_STACKSAVEU(%xmm7, 16)
        CFI_STACKSAVEU(%xmm8, 32)
        CFI_STACKSAVEU(%xmm9, 48)
        CFI_STACKSAVEU(%xmm10, 64)
#endif

        lea K256+128(%rip), %rcx
        movdqu (%rdi), %xmm1
        movdqu 16(%rdi), %xmm2
        movdqa 512-128(%rcx), %xmm7
        pshufd $27, %xmm1, %xmm0
        pshufd $177, %xmm1, %xmm1
        pshufd $27, %xmm2, %xmm2
        movdqa %xmm7, %xmm8
        palignr $8, %xmm2, %xmm1
        punpcklqdq %xmm0, %xmm2
        jmp Lsha256_compress_hw_oop_shaext

Lsha256_compress_hw_oop_shaext:
        movdqu (%rsi), %xmm3
        movdqu 16(%rsi), %xmm4
        movdqu 32(%rsi), %xmm5
        pshufb %xmm7, %xmm3
        movdqu 48(%rsi), %xmm6
        movdqa 0-128(%rcx), %xmm0
        paddd %xmm3, %xmm0
        pshufb %xmm7, %xmm4
        movdqa %xmm2, %xmm10
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        nop
        movdqa %xmm1, %xmm9
        sha256rnds2 %xmm2, %xmm1
        movdqa 32-128(%rcx), %xmm0
        paddd %xmm4, %xmm0
        pshufb %xmm7, %xmm5
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        lea 64(%rsi), %rsi
        sha256msg1 %xmm4, %xmm3
        sha256rnds2 %xmm2, %xmm1
        movdqa 64-128(%rcx), %xmm0
        paddd %xmm5, %xmm0
        pshufb %xmm7, %xmm6
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm6, %xmm7
        palignr $4, %xmm5, %xmm7
        nop
        paddd %xmm7, %xmm3
        sha256msg1 %xmm5, %xmm4
        sha256rnds2 %xmm2, %xmm1
        movdqa 96-128(%rcx), %xmm0
        paddd %xmm6, %xmm0
        sha256msg2 %xmm6, %xmm3
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm3, %xmm7
        palignr $4, %xmm6, %xmm7
        nop
        paddd %xmm7, %xmm4
        sha256msg1 %xmm6, %xmm5
        sha256rnds2 %xmm2, %xmm1
        movdqa 128-128(%rcx), %xmm0
        paddd %xmm3, %xmm0
        sha256msg2 %xmm3, %xmm4
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm4, %xmm7
        palignr $4, %xmm3, %xmm7
        nop
        paddd %xmm7, %xmm5
        sha256msg1 %xmm3, %xmm6
        sha256rnds2 %xmm2, %xmm1
        movdqa 160-128(%rcx), %xmm0
        paddd %xmm4, %xmm0
        sha256msg2 %xmm4, %xmm5
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm5, %xmm7
        palignr $4, %xmm4, %xmm7
        nop
        paddd %xmm7, %xmm6
        sha256msg1 %xmm4, %xmm3
        sha256rnds2 %xmm2, %xmm1
        movdqa 192-128(%rcx), %xmm0
        paddd %xmm5, %xmm0
        sha256msg2 %xmm5, %xmm6
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm6, %xmm7
        palignr $4, %xmm5, %xmm7
        nop
        paddd %xmm7, %xmm3
        sha256msg1 %xmm5, %xmm4
        sha256rnds2 %xmm2, %xmm1
        movdqa 224-128(%rcx), %xmm0
        paddd %xmm6, %xmm0
        sha256msg2 %xmm6, %xmm3
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm3, %xmm7
        palignr $4, %xmm6, %xmm7
        nop
        paddd %xmm7, %xmm4
        sha256msg1 %xmm6, %xmm5
        sha256rnds2 %xmm2, %xmm1
        movdqa 256-128(%rcx), %xmm0
        paddd %xmm3, %xmm0
        sha256msg2 %xmm3, %xmm4
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm4, %xmm7
        palignr $4, %xmm3, %xmm7
        nop
        paddd %xmm7, %xmm5
        sha256msg1 %xmm3, %xmm6
        sha256rnds2 %xmm2, %xmm1
        movdqa 288-128(%rcx), %xmm0
        paddd %xmm4, %xmm0
        sha256msg2 %xmm4, %xmm5
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm5, %xmm7
        palignr $4, %xmm4, %xmm7
        nop
        paddd %xmm7, %xmm6
        sha256msg1 %xmm4, %xmm3
        sha256rnds2 %xmm2, %xmm1
        movdqa 320-128(%rcx), %xmm0
        paddd %xmm5, %xmm0
        sha256msg2 %xmm5, %xmm6
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm6, %xmm7
        palignr $4, %xmm5, %xmm7
        nop
        paddd %xmm7, %xmm3
        sha256msg1 %xmm5, %xmm4
        sha256rnds2 %xmm2, %xmm1
        movdqa 352-128(%rcx), %xmm0
        paddd %xmm6, %xmm0
        sha256msg2 %xmm6, %xmm3
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm3, %xmm7
        palignr $4, %xmm6, %xmm7
        nop
        paddd %xmm7, %xmm4
        sha256msg1 %xmm6, %xmm5
        sha256rnds2 %xmm2, %xmm1
        movdqa 384-128(%rcx), %xmm0
        paddd %xmm3, %xmm0
        sha256msg2 %xmm3, %xmm4
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm4, %xmm7
        palignr $4, %xmm3, %xmm7
        nop
        paddd %xmm7, %xmm5
        sha256msg1 %xmm3, %xmm6
        sha256rnds2 %xmm2, %xmm1
        movdqa 416-128(%rcx), %xmm0
        paddd %xmm4, %xmm0
        sha256msg2 %xmm4, %xmm5
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        movdqa %xmm5, %xmm7
        palignr $4, %xmm4, %xmm7
        sha256rnds2 %xmm2, %xmm1
        paddd %xmm7, %xmm6
        movdqa 448-128(%rcx), %xmm0
        paddd %xmm5, %xmm0
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        sha256msg2 %xmm5, %xmm6
        movdqa %xmm8, %xmm7
        sha256rnds2 %xmm2, %xmm1
        movdqa 480-128(%rcx), %xmm0
        paddd %xmm6, %xmm0
        nop
        sha256rnds2 %xmm1, %xmm2
        pshufd $14, %xmm0, %xmm0
        dec %rdx
        nop
        sha256rnds2 %xmm2, %xmm1
        paddd %xmm10, %xmm2
        paddd %xmm9, %xmm1
        jnz Lsha256_compress_hw_oop_shaext
        pshufd $177, %xmm2, %xmm2
        pshufd $27, %xmm1, %xmm7
        pshufd $177, %xmm1, %xmm1
        punpckhqdq %xmm2, %xmm1
        palignr $8, %xmm7, %xmm2
        movdqu %xmm1, (%rdi)
        movdqu %xmm2, 16(%rdi)

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6, 0)
        CFI_STACKLOADU(%xmm7, 16)
        CFI_STACKLOADU(%xmm8, 32)
        CFI_STACKLOADU(%xmm9, 48)
        CFI_STACKLOADU(%xmm10, 64)
        CFI_INC_RSP(80)
        CFI_POP(%rsi)
        CFI_POP(%rdi)
#endif
        CFI_RET


S2N_BN_SIZE_DIRECTIVE(sha256_compress_hw)


#if defined(__ELF__)
.section .rodata
.align 64
.type K256,@object
K256:
.long 0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5
.long 0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5
.long 0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5
.long 0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5
.long 0xd807aa98,0x12835b01,0x243185be,0x550c7dc3
.long 0xd807aa98,0x12835b01,0x243185be,0x550c7dc3
.long 0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174
.long 0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174
.long 0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc
.long 0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc
.long 0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da
.long 0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da
.long 0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7
.long 0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7
.long 0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967
.long 0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967
.long 0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13
.long 0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13
.long 0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85
.long 0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85
.long 0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3
.long 0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3
.long 0xd192e819,0xd6990624,0xf40e3585,0x106aa070
.long 0xd192e819,0xd6990624,0xf40e3585,0x106aa070
.long 0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5
.long 0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5
.long 0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3
.long 0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3
.long 0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208
.long 0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208
.long 0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
.long 0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
.long 0x00010203,0x04050607,0x08090a0b,0x0c0d0e0f
.long 0x00010203,0x04050607,0x08090a0b,0x0c0d0e0f
.long 0x03020100,0x0b0a0908,0xffffffff,0xffffffff
.long 0x03020100,0x0b0a0908,0xffffffff,0xffffffff
.long 0xffffffff,0xffffffff,0x03020100,0x0b0a0908
.long 0xffffffff,0xffffffff,0x03020100,0x0b0a0908
.size K256,.-K256
#endif

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
