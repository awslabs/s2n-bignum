// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Inverse number-theoretic transform from ML-KEM
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// The transform is in-place with input and output a[256], with the input in
// bitreversed order and the output mapped into the Montgomery domain via x |->
// (2^16 * x) mod 3329. This is the same operation as mlkem_intt, but this is
// the code for mlkem_poly_invntt_tomont from mlkem-native's portable C
// implementation as compiled by gcc 12.3.0 with -O2 for x86-64 (see README.md
// for details). It starts by scaling the coefficients in a loop that the
// compiler has vectorized, using its own vectors of constants, which are the
// anonymous constants at addresses 0x8080, 0x8090 and 0x80a0 in the binary. It
// then uses its own table of zetas, which is the mlk_zetas array in
// mlkem-native, instead of taking tables as arguments.
//
// extern void mlkem_native_poly_invntt_tomont_gcc12_O2(int16_t a[static 256]);
//
// Standard x86-64 ABI: RDI = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_invntt_tomont_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_invntt_tomont_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_invntt_tomont_gcc12_O2)
        .text
        .balign 4

// The tables are separate objects, so that the proofs can allow them to be
// anywhere, as they are in the binary. For ELF they are given global (but
// hidden) symbols, since references to local symbols would become
// references to the section as a whole.

#define CONSTANTS mlkem_native_poly_invntt_tomont_gcc12_O2_constants

S2N_BN_SYMBOL(mlkem_native_poly_invntt_tomont_gcc12_O2):
        CFI_START

        push    r15
        movdqa  xmm5, XMMWORD PTR [rip+CONSTANTS+0x20]
        lea     rdx, [rdi+0x200]
        mov     rax, rdi
        push    r14
        movdqa  xmm6, XMMWORD PTR [rip+CONSTANTS]
        push    r13
        movdqa  xmm4, XMMWORD PTR [rip+CONSTANTS+0x10]
        push    r12
        mov     r12, rdi
        push    rbp
        push    rbx
        // nop
        .byte   0x90
Lmlkem_native_poly_invntt_tomont_gcc12_O2_30:
        movdqu  xmm3, XMMWORD PTR [rax]
        movdqu  xmm0, XMMWORD PTR [rax]
        add     rax, 0x10
        pmullw  xmm3, xmm5
        pmulhw  xmm0, xmm5
        movdqa  xmm7, xmm3
        punpckhwd xmm3, xmm0
        punpcklwd xmm7, xmm0
        movdqa  xmm0, xmm7
        movdqa  xmm1, xmm7
        punpcklwd xmm0, xmm3
        punpckhwd xmm1, xmm3
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm2
        pmullw  xmm0, xmm6
        movdqa  xmm2, xmm0
        movdqa  xmm1, xmm0
        pmulhw  xmm1, xmm4
        pmullw  xmm2, xmm4
        movdqa  xmm0, xmm2
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm1
        movdqa  xmm1, xmm2
        paddd   xmm0, xmm7
        paddd   xmm1, xmm3
        psrad   xmm1, 0x10
        psrad   xmm0, 0x10
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        movdqa  xmm1, xmm0
        punpckhwd xmm1, xmm2
        punpcklwd xmm0, xmm2
        punpcklwd xmm0, xmm1
        movups  XMMWORD PTR [rax-0x10], xmm0
        cmp     rax, rdx
        jne     Lmlkem_native_poly_invntt_tomont_gcc12_O2_30
        mov     r9d, 0x65c
        mov     ecx, 0x7
        mov     r15d, 0x1
        lea     r14, [r12+0x2]
        lea     r13, [rip+mlk_zetas]
        movsx   r8d, r9w
Lmlkem_native_poly_invntt_tomont_gcc12_O2_f0:
        mov     edi, 0x100
        mov     r10d, r15d
        xor     esi, esi
        mov     r11d, ecx
        shr     edi, cl
        shl     r10d, cl
        sub     r10d, 0x1
        lea     ebx, [rdi+rdi*1]
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
Lmlkem_native_poly_invntt_tomont_gcc12_O2_110:
        sub     r10d, 0x1
        cmp     esi, edi
        jae     Lmlkem_native_poly_invntt_tomont_gcc12_O2_19d
        mov     eax, edi
        mov     r9d, esi
        mov     DWORD PTR [rsp-0xc], esi
        lea     rdx, [r12+rax*2]
        mov     eax, edi
        lea     rcx, [r12+r9*2]
        sub     eax, esi
        sub     eax, 0x1
        add     rax, r9
        lea     rbp, [r14+rax*2]
        mov     rsi, rbp
        // xchg    ax, ax
        .byte   0x66,0x90
Lmlkem_native_poly_invntt_tomont_gcc12_O2_140:
        movzx   r9d, WORD PTR [rcx]
        movzx   ebp, WORD PTR [rdx]
        add     rcx, 0x2
        add     rdx, 0x2
        add     ebp, r9d
        movsx   eax, bp
        imul    eax, eax, 0x4ebf
        add     eax, 0x2000000
        sar     eax, 0x1a
        imul    ax, ax, 0xf2ff
        add     eax, ebp
        mov     WORD PTR [rcx-0x2], ax
        movzx   eax, WORD PTR [rdx-0x2]
        sub     eax, r9d
        movsx   r9d, ax
        imul    r9d, r8d
        imul    ax, r9w, 0xf301
        cwde
        imul    eax, eax, 0xfffff2ff
        add     eax, r9d
        sar     eax, 0x10
        mov     WORD PTR [rdx-0x2], ax
        cmp     rcx, rsi
        jne     Lmlkem_native_poly_invntt_tomont_gcc12_O2_140
        mov     esi, DWORD PTR [rsp-0xc]
Lmlkem_native_poly_invntt_tomont_gcc12_O2_19d:
        add     esi, ebx
        add     edi, ebx
        cmp     esi, 0xff
        ja      Lmlkem_native_poly_invntt_tomont_gcc12_O2_1c0
        mov     eax, r10d
        movsx   r8d, WORD PTR [r13+rax*2+0x0]
        jmp     Lmlkem_native_poly_invntt_tomont_gcc12_O2_110
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
Lmlkem_native_poly_invntt_tomont_gcc12_O2_1c0:
        mov     ecx, r11d
        sub     ecx, 0x1
        je      Lmlkem_native_poly_invntt_tomont_gcc12_O2_1db
        mov     eax, r15d
        shl     eax, cl
        sub     eax, 0x1
        movsx   r8d, WORD PTR [r13+rax*2+0x0]
        jmp     Lmlkem_native_poly_invntt_tomont_gcc12_O2_f0
Lmlkem_native_poly_invntt_tomont_gcc12_O2_1db:
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_invntt_tomont_gcc12_O2)

// Vectors of constants for the multiplications

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 32
#if defined(__ELF__)
        .globl  CONSTANTS
        .hidden CONSTANTS
        .type   CONSTANTS, %object
        .size   CONSTANTS, 48
#endif
CONSTANTS:
        .short  -3327, -3327, -3327, -3327, -3327, -3327, -3327, -3327
        .short  -3329, -3329, -3329, -3329, -3329, -3329, -3329, -3329
        .short  1441, 1441, 1441, 1441, 1441, 1441, 1441, 1441

// The table mlk_zetas from mlkem-native

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 32
#if defined(__ELF__)
        .globl  mlk_zetas
        .hidden mlk_zetas
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
