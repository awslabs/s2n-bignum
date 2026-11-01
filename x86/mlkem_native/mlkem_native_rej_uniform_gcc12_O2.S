// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Uniform rejection sampling for ML-KEM
// Inputs r[256] (signed 16-bit words), offset, buf[buflen] (bytes);
// output r[offset...] (signed 16-bit words), returning the new offset
//
// This reads 12-bit values from consecutive groups of 3 bytes of buf, and
// appends those that are less than 3329 to r starting at index offset,
// stopping when there are 256 coefficients or the buffer is exhausted. It
// returns the final number of coefficients. This is the code for
// mlk_rej_uniform_c from mlkem-native's portable C implementation as
// specialized and compiled by gcc 12.3.0 with -O2 for x86-64, the function
// mlk_rej_uniform_c.constprop.0 in the binary (see README.md for details). The
// specialization fixes the target number of coefficients at 256, and since all
// the callers pass a buffer length of 168 or 504, it omits the initial test
// that the buffer has at least one group of 3 bytes.
//
// extern unsigned mlkem_native_rej_uniform_gcc12_O2
//   (int16_t r[static 256], unsigned offset, const uint8_t *buf,
//    unsigned buflen);
//
// Standard x86-64 ABI: RDI = r, RSI = offset, RDX = buf, RCX = buflen,
//                      returns RAX
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_rej_uniform_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_rej_uniform_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_rej_uniform_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_rej_uniform_gcc12_O2):
        CFI_START

        mov     r8, rdi
        mov     r9d, ecx
        cmp     esi, 0xff
        ja      Lmlkem_native_rej_uniform_gcc12_O2_98
        mov     r10d, 0x3
        sub     r10d, edx
        jmp     Lmlkem_native_rej_uniform_gcc12_O2_4d
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
Lmlkem_native_rej_uniform_gcc12_O2_20:
        cmp     esi, 0xff
        ja      Lmlkem_native_rej_uniform_gcc12_O2_40
        mov     edi, esi
        cmp     ax, 0xd00
        jg      Lmlkem_native_rej_uniform_gcc12_O2_40
Lmlkem_native_rej_uniform_gcc12_O2_30:
        lea     esi, [rdi+0x1]
        mov     WORD PTR [r8+rdi*2], ax
        cmp     esi, 0x100
        je      Lmlkem_native_rej_uniform_gcc12_O2_98
Lmlkem_native_rej_uniform_gcc12_O2_40:
        add     rdx, 0x3
        lea     eax, [r10+rdx*1]
        cmp     r9d, eax
        jb      Lmlkem_native_rej_uniform_gcc12_O2_98
Lmlkem_native_rej_uniform_gcc12_O2_4d:
        movzx   eax, BYTE PTR [rdx+0x1]
        movzx   edi, BYTE PTR [rdx]
        mov     ecx, eax
        shr     al, 0x4
        shl     ecx, 0x8
        movzx   eax, al
        or      ecx, edi
        movzx   edi, BYTE PTR [rdx+0x2]
        and     cx, 0xfff
        shl     edi, 0x4
        or      eax, edi
        cmp     cx, 0xd00
        jg      Lmlkem_native_rej_uniform_gcc12_O2_20
        lea     edi, [rsi+0x1]
        mov     esi, esi
        mov     WORD PTR [r8+rsi*2], cx
        cmp     edi, 0xff
        ja      Lmlkem_native_rej_uniform_gcc12_O2_8e
        cmp     ax, 0xd00
        jle     Lmlkem_native_rej_uniform_gcc12_O2_30
Lmlkem_native_rej_uniform_gcc12_O2_8e:
        mov     esi, edi
        cmp     esi, 0x100
        jne     Lmlkem_native_rej_uniform_gcc12_O2_40
Lmlkem_native_rej_uniform_gcc12_O2_98:
        mov     eax, esi
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_rej_uniform_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
