// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Precompute the mulcache data for a polynomial in the NTT domain
// Input a[256] (signed 16-bit words); output x[128] (signed 16-bit words)
//
// This is the same operation as mlkem_mulcache_compute, but this is the code
// for mlkem_poly_mulcache_compute from mlkem-native's portable C
// implementation as compiled by gcc 12.3.0 with -O2 for x86-64 (see README.md
// for details). It uses its own table of zetas, which is the mlk_zetas array
// in mlkem-native, instead of taking tables as arguments.
//
// extern void mlkem_native_poly_mulcache_compute_gcc12_O2
//      (int16_t x[static 128],const int16_t a[static 256]);
//
// Standard x86-64 ABI: RDI = x, RSI = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_mulcache_compute_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_mulcache_compute_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_mulcache_compute_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_mulcache_compute_gcc12_O2):
        CFI_START

        xor     ecx, ecx
        lea     r8, [rip+mlk_zetas+0x80]
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
Lmlkem_native_poly_mulcache_compute_gcc12_O2_10:
        movsx   eax, WORD PTR [r8+rcx*1]
        movsx   r9d, WORD PTR [rsi+rcx*4+0x2]
        imul    r9d, eax
        mov     edx, eax
        neg     edx
        movsx   edx, dx
        imul    ax, r9w, 0xf301
        cwde
        imul    eax, eax, 0xfffff2ff
        add     eax, r9d
        sar     eax, 0x10
        mov     WORD PTR [rdi+rcx*2], ax
        movsx   eax, WORD PTR [rsi+rcx*4+0x6]
        imul    edx, eax
        imul    ax, dx, 0xf301
        cwde
        imul    eax, eax, 0xfffff2ff
        add     eax, edx
        sar     eax, 0x10
        mov     WORD PTR [rdi+rcx*2+0x2], ax
        add     rcx, 0x2
        cmp     rcx, 0x80
        jne     Lmlkem_native_poly_mulcache_compute_gcc12_O2_10
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_mulcache_compute_gcc12_O2)

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
