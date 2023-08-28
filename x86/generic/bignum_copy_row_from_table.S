// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC


// ----------------------------------------------------------------------------
// Given table: uint64_t[height*width], copy table[idx*width...(idx+1)*width-1]
// into z[0..width-1].
//
//    extern void bignum_copy_from_table
//     (uint64_t *z, uint64_t *table, uint64_t height, uint64_t width,
//      uint64_t idx);
//
// Standard ARM ABI: X0 = z, X1 = table, X2 = height, X3 = width, X4 = idx
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_copy_row_from_table)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_copy_row_from_table)
        .text


S2N_BN_SYMBOL(bignum_copy_row_from_table):
        push    rbp
        push    rbx
        mov     rbp, rdx
        mov     rbx, rcx
        test    rcx, rcx
        je      bignum_copy_row_from_table_initzero_done
        mov     rax, rdi
        lea     rdx, [rdi+rcx*8]

bignum_copy_row_from_table_initzero:
        mov     QWORD PTR [rax], 0
        add     rax, 8
        cmp     rax, rdx
        jne     bignum_copy_row_from_table_initzero

bignum_copy_row_from_table_initzero_done:
        test    rbp, rbp
        je      bignum_copy_row_from_table_end
        lea     rcx, [0+rbx*8]
        mov     r11d, 0
        mov     r10d, 0

bignum_copy_row_from_table_outerloop:
        cmp     r8, r11
        sete    r9b
        test    rbx, rbx
        je      bignum_copy_row_from_table_innerloop_done
        mov     eax, 0

bignum_copy_row_from_table_innerloop:
        test    r9b, r9b
        mov     rdx, r10
        cmovne  rdx, QWORD PTR [rsi+rax]
        or      QWORD PTR [rdi+rax], rdx
        add     rax, 8
        cmp     rax, rcx
        jne     bignum_copy_row_from_table_innerloop

bignum_copy_row_from_table_innerloop_done:
        add     r11, 1
        add     rsi, rcx
        cmp     rbp, r11
				jne			bignum_copy_row_from_table_outerloop

bignum_copy_row_from_table_end:
        pop     rbx
        pop     rbp
        ret


#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
