// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Forward number-theoretic transform from ML-KEM
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// The transform is in-place with input and output a[256], with the output in
// bitreversed order. This is the same operation as mlkem_ntt, but this is the
// code for mlkem_poly_ntt from mlkem-native's portable C implementation as
// compiled by gcc 12.3.0 with -O2 for x86-64 (see README.md for details). It
// uses its own table of zetas, which is the mlk_zetas array in mlkem-native,
// instead of taking tables as arguments.
//
// extern void mlkem_native_poly_ntt_gcc12_O2(int16_t a[static 256]);
//
// Standard x86-64 ABI: RDI = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_ntt_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_ntt_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_ntt_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_ntt_gcc12_O2):
        CFI_START

        push    r15
        mov     edx, 0x1
        mov     r15d, 0x100
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12d, 0x1
        push    rbp
        lea     rbp, [rdi+0x2]
        push    rbx
        lea     rbx, [rip+mlk_zetas]
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
Lmlkem_native_poly_ntt_gcc12_O2_30:
        lea     ecx, [rdx-0x1]
        mov     r8d, r12d
        mov     edi, r15d
        mov     DWORD PTR [rsp-0x4], edx
        shl     r8d, cl
        mov     ecx, edx
        shr     edi, cl
        xor     ecx, ecx
        lea     r11d, [rdi+rdi*1]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Lmlkem_native_poly_ntt_gcc12_O2_50:
        mov     eax, r8d
        add     r8d, 0x1
        movsx   r9d, WORD PTR [rbx+rax*2]
        cmp     ecx, edi
        jae     Lmlkem_native_poly_ntt_gcc12_O2_b4
        mov     esi, edi
        mov     eax, ecx
        sub     esi, ecx
        lea     rdx, [r13+rax*2+0x0]
        sub     esi, 0x1
        add     rsi, rax
        lea     r10, [rbp+rsi*2+0x0]
        mov     esi, edi
        sub     rsi, rax
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
Lmlkem_native_poly_ntt_gcc12_O2_80:
        movsx   r14d, WORD PTR [rdx+rsi*2]
        imul    r14d, r9d
        imul    ax, r14w, 0xf301
        cwde
        imul    eax, eax, 0xfffff2ff
        add     eax, r14d
        movzx   r14d, WORD PTR [rdx]
        sar     eax, 0x10
        sub     r14d, eax
        mov     WORD PTR [rdx+rsi*2], r14w
        add     WORD PTR [rdx], ax
        add     rdx, 0x2
        cmp     r10, rdx
        jne     Lmlkem_native_poly_ntt_gcc12_O2_80
Lmlkem_native_poly_ntt_gcc12_O2_b4:
        add     ecx, r11d
        add     edi, r11d
        cmp     ecx, 0xff
        jbe     Lmlkem_native_poly_ntt_gcc12_O2_50
        mov     edx, DWORD PTR [rsp-0x4]
        add     edx, 0x1
        cmp     edx, 0x8
        jne     Lmlkem_native_poly_ntt_gcc12_O2_30
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_ntt_gcc12_O2)

// The table mlk_zetas from mlkem-native

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 32
#if defined(__ELF__)
        .type   mlk_zetas, %object
        .size   mlk_zetas, 256
#endif
mlk_zetas:
        .short  -1044, -758, -359, -1517, 1493, 1422, 287, 202
        .short  -171, 622, 1577, 182, 962, -1202, -1474, 1468
        .short  573, -1325, 264, 383, -829, 1458, -1602, -130
        .short  -681, 1017, 732, 608, -1542, 411, -205, -1571
        .short  1223, 652, -552, 1015, -1293, 1491, -282, -1544
        .short  516, -8, -320, -666, -1618, -1162, 126, 1469
        .short  -853, -90, -271, 830, 107, -1421, -247, -951
        .short  -398, 961, -1508, -725, 448, -1065, 677, -1275
        .short  -1103, 430, 555, 843, -1251, 871, 1550, 105
        .short  422, 587, 177, -235, -291, -460, 1574, 1653
        .short  -246, 778, 1159, -147, -777, 1483, -602, 1119
        .short  -1590, 644, -872, 349, 418, 329, -156, -75
        .short  817, 1097, 603, 610, 1322, -1285, -1465, 384
        .short  -1215, -136, 1218, -1335, -874, 220, -1187, -1659
        .short  -1185, -1530, -1278, 794, -1510, -854, -870, 478
        .short  -108, -308, 996, 991, 958, -1460, 1522, 1628

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
