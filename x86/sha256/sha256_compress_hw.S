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


#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha256_compress_hw)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha256_compress_hw)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha256_compress_hw)
        .text

S2N_BN_SYMBOL(sha256_compress_hw):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        CFI_DEC_RSP(80)
        CFI_STACKSAVEU(xmm6, 0)
        CFI_STACKSAVEU(xmm7, 16)
        CFI_STACKSAVEU(xmm8, 32)
        CFI_STACKSAVEU(xmm9, 48)
        CFI_STACKSAVEU(xmm10, 64)
#endif

        lea rcx, [rip+K256+128]
        movdqu xmm1, [rdi]
        movdqu xmm2, [rdi+16]
        movdqa xmm7, [rcx+512-128]
        pshufd xmm0, xmm1, 27
        pshufd xmm1, xmm1, 177
        pshufd xmm2, xmm2, 27
        movdqa xmm8, xmm7
        palignr xmm1, xmm2, 8
        punpcklqdq xmm2, xmm0
        jmp Lsha256_compress_hw_oop_shaext

Lsha256_compress_hw_oop_shaext:
        movdqu xmm3, [rsi]
        movdqu xmm4, [rsi+16]
        movdqu xmm5, [rsi+32]
        pshufb xmm3, xmm7
        movdqu xmm6, [rsi+48]
        movdqa xmm0, [rcx+0-128]
        paddd xmm0, xmm3
        pshufb xmm4, xmm7
        movdqa xmm10, xmm2
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        nop
        movdqa xmm9, xmm1
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+32-128]
        paddd xmm0, xmm4
        pshufb xmm5, xmm7
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        lea rsi, [rsi+64]
        sha256msg1 xmm3, xmm4
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+64-128]
        paddd xmm0, xmm5
        pshufb xmm6, xmm7
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm6
        palignr xmm7, xmm5, 4
        nop
        paddd xmm3, xmm7
        sha256msg1 xmm4, xmm5
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+96-128]
        paddd xmm0, xmm6
        sha256msg2 xmm3, xmm6
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm3
        palignr xmm7, xmm6, 4
        nop
        paddd xmm4, xmm7
        sha256msg1 xmm5, xmm6
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+128-128]
        paddd xmm0, xmm3
        sha256msg2 xmm4, xmm3
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm4
        palignr xmm7, xmm3, 4
        nop
        paddd xmm5, xmm7
        sha256msg1 xmm6, xmm3
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+160-128]
        paddd xmm0, xmm4
        sha256msg2 xmm5, xmm4
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm5
        palignr xmm7, xmm4, 4
        nop
        paddd xmm6, xmm7
        sha256msg1 xmm3, xmm4
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+192-128]
        paddd xmm0, xmm5
        sha256msg2 xmm6, xmm5
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm6
        palignr xmm7, xmm5, 4
        nop
        paddd xmm3, xmm7
        sha256msg1 xmm4, xmm5
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+224-128]
        paddd xmm0, xmm6
        sha256msg2 xmm3, xmm6
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm3
        palignr xmm7, xmm6, 4
        nop
        paddd xmm4, xmm7
        sha256msg1 xmm5, xmm6
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+256-128]
        paddd xmm0, xmm3
        sha256msg2 xmm4, xmm3
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm4
        palignr xmm7, xmm3, 4
        nop
        paddd xmm5, xmm7
        sha256msg1 xmm6, xmm3
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+288-128]
        paddd xmm0, xmm4
        sha256msg2 xmm5, xmm4
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm5
        palignr xmm7, xmm4, 4
        nop
        paddd xmm6, xmm7
        sha256msg1 xmm3, xmm4
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+320-128]
        paddd xmm0, xmm5
        sha256msg2 xmm6, xmm5
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm6
        palignr xmm7, xmm5, 4
        nop
        paddd xmm3, xmm7
        sha256msg1 xmm4, xmm5
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+352-128]
        paddd xmm0, xmm6
        sha256msg2 xmm3, xmm6
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm3
        palignr xmm7, xmm6, 4
        nop
        paddd xmm4, xmm7
        sha256msg1 xmm5, xmm6
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+384-128]
        paddd xmm0, xmm3
        sha256msg2 xmm4, xmm3
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm4
        palignr xmm7, xmm3, 4
        nop
        paddd xmm5, xmm7
        sha256msg1 xmm6, xmm3
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+416-128]
        paddd xmm0, xmm4
        sha256msg2 xmm5, xmm4
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        movdqa xmm7, xmm5
        palignr xmm7, xmm4, 4
        sha256rnds2 xmm1, xmm2
        paddd xmm6, xmm7
        movdqa xmm0, [rcx+448-128]
        paddd xmm0, xmm5
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        sha256msg2 xmm6, xmm5
        movdqa xmm7, xmm8
        sha256rnds2 xmm1, xmm2
        movdqa xmm0, [rcx+480-128]
        paddd xmm0, xmm6
        nop
        sha256rnds2 xmm2, xmm1
        pshufd xmm0, xmm0, 14
        dec rdx
        nop
        sha256rnds2 xmm1, xmm2
        paddd xmm2, xmm10
        paddd xmm1, xmm9
        jnz Lsha256_compress_hw_oop_shaext
        pshufd xmm2, xmm2, 177
        pshufd xmm7, xmm1, 27
        pshufd xmm1, xmm1, 177
        punpckhqdq xmm1, xmm2
        palignr xmm2, xmm7, 8
        movdqu [rdi], xmm1
        movdqu [rdi+16], xmm2

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6, 0)
        CFI_STACKLOADU(xmm7, 16)
        CFI_STACKLOADU(xmm8, 32)
        CFI_STACKLOADU(xmm9, 48)
        CFI_STACKLOADU(xmm10, 64)
        CFI_INC_RSP(80)
        CFI_POP(rsi)
        CFI_POP(rdi)
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
