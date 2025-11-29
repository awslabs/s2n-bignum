// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Uniform rejection sampling for ML-KEM
// Inputs *buf (unsigned bytes), buflen, table (unsigned bytes); output r[256] (signed 16-bit words), return
//
// extern uint64_t mlkem_rej_uniform_VARIABLE_TIME
//                     (int16_t r[S2N_BIGNUM_STATIC 256],
//                      const uint8_t *buf,uint64_t buflen)
//
// Interprets the input buffer as packed 12-bit numbers with a length of
// buflen bytes, assumed to be a multiple of 24. Fills the output array
// with those numbers from the packed buffer that are < 3329, in the order
// of appearance, returning the total number of entries written, with a
// maximum of 256.
//
// Unique (at the moment) among s2n-bignum functions this is *not* a
// constant-time function. The time taken depends not only on the
// buffer size "buflen", but also how many elements of the buffer are
// needed to provide the 256 entries for the output.
//
// Standard x86-64 ABI: RDI = r, RSI = buf, RDX = buflen
// Microsoft x64 ABI:   RCX = r, RDX = buf, R8 = buflen
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_rej_uniform_VARIABLE_TIME)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_rej_uniform_VARIABLE_TIME)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_rej_uniform_VARIABLE_TIME)
        .text
        .balign 4

// This code is effectively the same as the original here:
// https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/src/native/x86_64/src/rej_uniform_asm.S 

S2N_BN_SYMBOL(mlkem_rej_uniform_VARIABLE_TIME):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(96)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm12,64)
        CFI_STACKSAVE(rdi,80)
        mov     rdi, rcx
#endif

        CFI_DEC_RSP(0x210)

        movabs rax, 0xd010d010d010d01
        movq   xmm0, rax
        pinsrq xmm0, rax, 0x1
        movabs rax, 0xfff0fff0fff0fff
        movq   xmm5, rax
        pinsrq xmm5, rax, 0x1
        movabs rax, 0x504040302010100
        movq   xmm4, rax
        movabs rax, 0xb0a0a0908070706
        pinsrq xmm4, rax, 0x1
        mov    rax, 0x0
        mov    r8, 0x0
        mov    r9, 0x5555

Lmlkem_rej_uniform_VARIABLE_TIME_loop:
        movdqu xmm2, XMMWORD PTR [rsi+r8*1]
        pshufb xmm2, xmm4
        movdqa xmm6, xmm2
        psrlw  xmm6, 0x4
        pblendw xmm2, xmm6, 0xaa
        pand   xmm2, xmm5
        movdqa xmm1, xmm0
        pcmpgtw xmm1, xmm2
        pmovmskb r11d, xmm1
        pext   r11, r11, r9
        mov    r10, r11
        shl    r10, 0x4
        movdqu xmm3, XMMWORD PTR [rcx+r10*1]
        pshufb xmm2, xmm3
        movdqu XMMWORD PTR [rsp+rax*2], xmm2
        popcnt r11, r11
        add    rax, r11
        cmp    rax, 0x100
        jae    Lmlkem_rej_uniform_VARIABLE_TIME_final_copy
        add    r8, 0xc
        cmp    rdx, r8
        ja     Lmlkem_rej_uniform_VARIABLE_TIME_loop

Lmlkem_rej_uniform_VARIABLE_TIME_final_copy:
        mov    rcx, 0x100
        cmp    rax, 0x100
        cmova  rax, rcx
        mov    rsi, rsp
        mov    rcx, rax
        shl    rcx, 1
        rep movs BYTE PTR es:[rdi],BYTE PTR ds:[rsi]

        CFI_INC_RSP(0x210)

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm12,64)
        CFI_STACKLOAD(rdi,80)
        CFI_INC_RSP(96)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_rej_uniform_VARIABLE_TIME)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
