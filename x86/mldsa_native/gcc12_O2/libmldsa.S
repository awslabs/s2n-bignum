// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mldsa-native's libmldsa.so (gcc 12, -O2)
//
// This is a transcription of the binary multilevel/gcc12/O2/libmldsa.so for
// x86-64 (see README.md), as loaded at an address that is a multiple of 4096:
// its bytes from address 0 up to the end of the read-only data, which are its
// first two loadable segments and the start of the third, with the padding
// between them. The ELF header and dynamic linking information at the start,
// the padding and the read-only data are given as data, while the procedure
// linkage table and the code are given as instructions. The instructions that
// refer to the global offset table, which is outside the image, are given as
// bytes, as are the NOPs and any instruction that the assembler would encode
// differently. The labels are named after the addresses in the binary.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_native_libmldsa_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_native_libmldsa_gcc12_O2)
        .text
        .balign 16

S2N_BN_SYMBOL(mldsa_native_libmldsa_gcc12_O2):

// ELF header and dynamic linking information, and padding
// (0x0 to 0x1000)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x00000001003e0003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x000000000002fcb8
        .quad   0x0038004000000000
        .quad   0x0019001a00400009
        .quad   0x0000000400000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000e48
        .quad   0x0000000000000e48
        .quad   0x0000000000001000
        .quad   0x0000000500000001
        .quad   0x0000000000001000
        .quad   0x0000000000001000
        .quad   0x0000000000001000
        .quad   0x000000000000ad70
        .quad   0x000000000000ad70
        .quad   0x0000000000001000
        .quad   0x0000000400000001
        .quad   0x000000000000c000
        .quad   0x000000000000c000
        .quad   0x000000000000c000
        .quad   0x0000000000002b10
        .quad   0x0000000000002b10
        .quad   0x0000000000001000
        .quad   0x0000000600000001
        .quad   0x000000000000ee80
        .quad   0x000000000000fe80
        .quad   0x000000000000fe80
        .quad   0x0000000000000180
        .quad   0x0000000000000180
        .quad   0x0000000000001000
        .quad   0x0000000600000002
        .quad   0x000000000000ee80
        .quad   0x000000000000fe80
        .quad   0x000000000000fe80
        .quad   0x0000000000000150
        .quad   0x0000000000000150
        .quad   0x0000000000000008
        .quad   0x0000000400000004
        .quad   0x000000000000eae0
        .quad   0x000000000000eae0
        .quad   0x000000000000eae0
        .quad   0x0000000000000030
        .quad   0x0000000000000030
        .quad   0x0000000000000008
        .quad   0x000000046474e553
        .quad   0x000000000000eae0
        .quad   0x000000000000eae0
        .quad   0x000000000000eae0
        .quad   0x0000000000000030
        .quad   0x0000000000000030
        .quad   0x0000000000000008
        .quad   0x000000066474e551
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000010
        .quad   0x000000046474e552
        .quad   0x000000000000ee80
        .quad   0x000000000000fe80
        .quad   0x000000000000fe80
        .quad   0x0000000000000180
        .quad   0x0000000000000180
        .quad   0x0000000000000001
        .quad   0x0000002e00000025
        .quad   0x0000000000000011
        .quad   0x0000002900000023
        .quad   0x0000000000000000
        .quad   0x000000000000001d
        .quad   0x0000000a00000021
        .quad   0x0000001700000018
        .quad   0x0000002400000009
        .quad   0x0000000000000015
        .quad   0x0000001c00000028
        .quad   0x000000000000000d
        .quad   0x0000001400000000
        .quad   0x0000002500000004
        .quad   0x0000001b00000007
        .quad   0x000000160000001a
        .quad   0x0000000000000000
        .quad   0x0000000c00000027
        .quad   0x0000002000000003
        .quad   0x000000120000000f
        .quad   0x000000000000002d
        .quad   0x0000000000000000
        .quad   0x0000000000000019
        .quad   0x0000000000000000
        .quad   0x000000000000001e
        .quad   0x0000002200000006
        .quad   0x000000000000002c
        .quad   0x0000000000000000
        .quad   0x000000000000001f
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000000b
        .quad   0x0000000200000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000e00000000
        .quad   0x0000000000000000
        .quad   0x0000002a00000001
        .quad   0x0000000800000000
        .quad   0x0000000000000026
        .quad   0x000000130000002b
        .quad   0x0000000500000000
        .quad   0x0000000000000000
        .quad   0x0000000400000025
        .quad   0x0000000800000004
        .quad   0x0a6340a0460288d5
        .quad   0x10a640204e3c180a
        .quad   0x087445801d011110
        .quad   0x00a4c96828348108
        .quad   0x0000000500000004
        .quad   0x0000000900000008
        .quad   0x000000000000000a
        .quad   0x0000000e0000000b
        .quad   0x000000100000000f
        .quad   0x0000001100000000
        .quad   0x0000000000000013
        .quad   0x0000001500000014
        .quad   0x0000001800000016
        .quad   0x0000001b00000000
        .quad   0x0000001e0000001d
        .quad   0x0000002200000020
        .quad   0x0000002500000023
        .quad   0x0000002700000026
        .quad   0x0000002800000000
        .quad   0x0000000000000000
        .quad   0x0000000000000029
        .quad   0x0000002a00000000
        .quad   0x28bfc2110000002b
        .quad   0x60a975ee0ad39b84
        .quad   0xc9ece7bb9bcd7541
        .quad   0xc1a4dcb513a9654b
        .quad   0xbc52da720f65255e
        .quad   0x2b49a6c3bfc4d471
        .quad   0xcaf4dde766a0d2d5
        .quad   0xed1218b379ef9254
        .quad   0x0ab43507e133b6b5
        .quad   0x9a1db104d8fc14eb
        .quad   0x81ea88aea4b4db73
        .quad   0x3b6c1e193418aef6
        .quad   0x806f9a0fb48d0b36
        .quad   0x3f6d7b24b0195be9
        .quad   0xf40f4fc847ece5f3
        .quad   0xe0e1688dd8f4d36f
        .quad   0x5ab1b03921fb0400
        .quad   0x1becc627502c72ab
        .quad   0x69a3abf58a2d909b
        .quad   0x7fcacc4bea825977
        .quad   0x50beae2e0cb3a3c8
        .quad   0x0000000074dffc43
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00000010000000c6
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000031
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000700120000018b
        .quad   0x0000000000007350
        .quad   0x0000000000000362
        .quad   0x00070012000001cf
        .quad   0x0000000000007d60
        .quad   0x0000000000000087
        .quad   0x00070012000000cd
        .quad   0x0000000000005640
        .quad   0x0000000000000125
        .quad   0x0007001200000058
        .quad   0x0000000000004ee0
        .quad   0x0000000000000087
        .quad   0x00070012000003ce
        .quad   0x000000000000b720
        .quad   0x00000000000000cc
        .quad   0x000700120000003d
        .quad   0x00000000000048b0
        .quad   0x000000000000062a
        .quad   0x0007001200000357
        .quad   0x000000000000ae20
        .quad   0x00000000000005af
        .quad   0x0007001200000416
        .quad   0x000000000000b880
        .quad   0x000000000000009e
        .quad   0x0007001200000324
        .quad   0x000000000000a750
        .quad   0x0000000000000639
        .quad   0x00070012000001e7
        .quad   0x0000000000007df0
        .quad   0x000000000000057f
        .quad   0x0007001200000282
        .quad   0x0000000000008790
        .quad   0x0000000000000090
        .quad   0x00070012000002fb
        .quad   0x000000000000a2f0
        .quad   0x00000000000003f2
        .quad   0x00070012000002c7
        .quad   0x00000000000088c0
        .quad   0x000000000000008d
        .quad   0x000700120000024f
        .quad   0x0000000000008620
        .quad   0x000000000000009f
        .quad   0x0007001200000021
        .quad   0x0000000000004850
        .quad   0x000000000000005f
        .quad   0x00070012000000ee
        .quad   0x0000000000005810
        .quad   0x00000000000000cc
        .quad   0x00070012000003f2
        .quad   0x000000000000b7f0
        .quad   0x0000000000000090
        .quad   0x000700120000036f
        .quad   0x000000000000b3d0
        .quad   0x000000000000001d
        .quad   0x0007001200000088
        .quad   0x00000000000054c0
        .quad   0x000000000000001d
        .quad   0x00070012000000df
        .quad   0x0000000000005770
        .quad   0x000000000000009f
        .quad   0x00070012000001b4
        .quad   0x0000000000007720
        .quad   0x0000000000000631
        .quad   0x0007001200000136
        .quad   0x0000000000005970
        .quad   0x000000000000009e
        .quad   0x00070012000003bf
        .quad   0x000000000000b680
        .quad   0x000000000000009f
        .quad   0x00070012000003ad
        .quad   0x000000000000b550
        .quad   0x0000000000000125
        .quad   0x0007001200000458
        .quad   0x000000000000b9b0
        .quad   0x00000000000003c0
        .quad   0x0007001200000178
        .quad   0x0000000000005aa0
        .quad   0x00000000000003c0
        .quad   0x000700120000009d
        .quad   0x00000000000054e0
        .quad   0x000000000000015f
        .quad   0x000700120000023d
        .quad   0x00000000000084f0
        .quad   0x0000000000000125
        .quad   0x0007001200000214
        .quad   0x0000000000008390
        .quad   0x000000000000015f
        .quad   0x0007001200000008
        .quad   0x0000000000004560
        .quad   0x00000000000002eb
        .quad   0x0007001200000384
        .quad   0x000000000000b3f0
        .quad   0x000000000000015f
        .quad   0x0007001200000112
        .quad   0x00000000000058e0
        .quad   0x0000000000000090
        .quad   0x0007001200000314
        .quad   0x000000000000a6f0
        .quad   0x000000000000005f
        .quad   0x0007001200000437
        .quad   0x000000000000b920
        .quad   0x000000000000008d
        .quad   0x00070012000001ff
        .quad   0x0000000000008370
        .quad   0x000000000000001d
        .quad   0x00070012000002a6
        .quad   0x0000000000008820
        .quad   0x000000000000009e
        .quad   0x00070012000001a4
        .quad   0x00000000000076c0
        .quad   0x000000000000005f
        .quad   0x000700120000025e
        .quad   0x00000000000086c0
        .quad   0x00000000000000cc
        .quad   0x00070012000002e8
        .quad   0x0000000000008950
        .quad   0x00000000000003c0
        .quad   0x000700120000033f
        .quad   0x000000000000ad90
        .quad   0x0000000000000087
        .quad   0x0007001200000070
        .quad   0x0000000000004f70
        .quad   0x000000000000054f
        .quad   0x0007001200000157
        .quad   0x0000000000005a10
        .quad   0x000000000000008d
        .quad   0x007465736d656d00
        .quad   0x5f34346173646c6d
        .quad   0x5f7269617079656b
        .quad   0x6c616e7265746e69
        .quad   0x34346173646c6d00
        .quad   0x7269617079656b5f
        .quad   0x626d6f646e617200
        .quad   0x646c6d0073657479
        .quad   0x6769735f34346173
        .quad   0x695f65727574616e
        .quad   0x006c616e7265746e
        .quad   0x5f34346173646c6d
        .quad   0x727574616e676973
        .quad   0x00756d7478655f65
        .quad   0x5f34346173646c6d
        .quad   0x695f796669726576
        .quad   0x006c616e7265746e
        .quad   0x5f34346173646c6d
        .quad   0x655f796669726576
        .quad   0x646c6d00756d7478
        .quad   0x6572705f34346173
        .quad   0x6d6f645f65726170
        .quad   0x617065735f6e6961
        .quad   0x705f6e6f69746172
        .quad   0x656d007869666572
        .quad   0x646c6d007970636d
        .quad   0x6769735f34346173
        .quad   0x6d0065727574616e
        .quad   0x765f34346173646c
        .quad   0x6c6d007966697265
        .quad   0x69735f3434617364
        .quad   0x5f65727574616e67
        .quad   0x687361685f657270
        .quad   0x616e7265746e695f
        .quad   0x346173646c6d006c
        .quad   0x74616e6769735f34
        .quad   0x5f6572705f657275
        .quad   0x6168735f68736168
        .quad   0x6c6d00363532656b
        .quad   0x65765f3434617364
        .quad   0x6572705f79666972
        .quad   0x6e695f687361685f
        .quad   0x6d006c616e726574
        .quad   0x765f34346173646c
        .quad   0x72705f7966697265
        .quad   0x735f687361685f65
        .quad   0x00363532656b6168
        .quad   0x5f34346173646c6d
        .quad   0x5f6d6f72665f6b70
        .quad   0x6173646c6d006b73
        .quad   0x617079656b5f3536
        .quad   0x7265746e695f7269
        .quad   0x73646c6d006c616e
        .quad   0x7079656b5f353661
        .quad   0x73646c6d00726961
        .quad   0x6e6769735f353661
        .quad   0x6e695f6572757461
        .quad   0x6d006c616e726574
        .quad   0x735f35366173646c
        .quad   0x65727574616e6769
        .quad   0x6d00756d7478655f
        .quad   0x765f35366173646c
        .quad   0x6e695f7966697265
        .quad   0x6d006c616e726574
        .quad   0x765f35366173646c
        .quad   0x78655f7966697265
        .quad   0x73646c6d00756d74
        .quad   0x706572705f353661
        .quad   0x616d6f645f657261
        .quad   0x72617065735f6e69
        .quad   0x72705f6e6f697461
        .quad   0x646c6d0078696665
        .quad   0x6769735f35366173
        .quad   0x6d0065727574616e
        .quad   0x765f35366173646c
        .quad   0x6c6d007966697265
        .quad   0x69735f3536617364
        .quad   0x5f65727574616e67
        .quad   0x687361685f657270
        .quad   0x616e7265746e695f
        .quad   0x366173646c6d006c
        .quad   0x74616e6769735f35
        .quad   0x5f6572705f657275
        .quad   0x6168735f68736168
        .quad   0x6c6d00363532656b
        .quad   0x65765f3536617364
        .quad   0x6572705f79666972
        .quad   0x6e695f687361685f
        .quad   0x6d006c616e726574
        .quad   0x765f35366173646c
        .quad   0x72705f7966697265
        .quad   0x735f687361685f65
        .quad   0x00363532656b6168
        .quad   0x5f35366173646c6d
        .quad   0x5f6d6f72665f6b70
        .quad   0x6173646c6d006b73
        .quad   0x617079656b5f3738
        .quad   0x7265746e695f7269
        .quad   0x73646c6d006c616e
        .quad   0x7079656b5f373861
        .quad   0x73646c6d00726961
        .quad   0x6e6769735f373861
        .quad   0x6e695f6572757461
        .quad   0x6d006c616e726574
        .quad   0x735f37386173646c
        .quad   0x65727574616e6769
        .quad   0x6d00756d7478655f
        .quad   0x765f37386173646c
        .quad   0x6e695f7966697265
        .quad   0x6d006c616e726574
        .quad   0x765f37386173646c
        .quad   0x78655f7966697265
        .quad   0x73646c6d00756d74
        .quad   0x706572705f373861
        .quad   0x616d6f645f657261
        .quad   0x72617065735f6e69
        .quad   0x72705f6e6f697461
        .quad   0x646c6d0078696665
        .quad   0x6769735f37386173
        .quad   0x6d0065727574616e
        .quad   0x765f37386173646c
        .quad   0x6c6d007966697265
        .quad   0x69735f3738617364
        .quad   0x5f65727574616e67
        .quad   0x687361685f657270
        .quad   0x616e7265746e695f
        .quad   0x386173646c6d006c
        .quad   0x74616e6769735f37
        .quad   0x5f6572705f657275
        .quad   0x6168735f68736168
        .quad   0x6c6d00363532656b
        .quad   0x65765f3738617364
        .quad   0x6572705f79666972
        .quad   0x6e695f687361685f
        .quad   0x6d006c616e726574
        .quad   0x765f37386173646c
        .quad   0x72705f7966697265
        .quad   0x735f687361685f65
        .quad   0x00363532656b6168
        .quad   0x5f37386173646c6d
        .quad   0x5f6d6f72665f6b70
        .quad   0x6c6d62696c006b73
        .quad   0x2f006f732e617364
        .quad   0x616c632f656d6f68
        .quad   0x73646c6d2f656475
        .quad   0x782f6b726f772f61
        .quad   0x646c6975622f3638
        .quad   0x7374757074756f2f
        .quad   0x62696c2f74756f2f
        .quad   0x0000000000000000
        .quad   0x000000000000ffe8
        .quad   0x0000000100000007
        .quad   0x0000000000000000
        .quad   0x000000000000fff0
        .quad   0x0000000200000007
        .quad   0x0000000000000000
        .quad   0x000000000000fff8
        .quad   0x0000000300000007
        .zero   448

// The procedure linkage table (0x1000 to 0x1040)

L1000:
        // push    QWORD PTR [rip+0xefd2]
        .byte   0xff,0x35,0xd2,0xef,0x00,0x00
        // jmp     QWORD PTR [rip+0xefd4]
        .byte   0xff,0x25,0xd4,0xef,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L1010:
        // jmp     QWORD PTR [rip+0xefd2]
        .byte   0xff,0x25,0xd2,0xef,0x00,0x00
        // push    0x0
        .byte   0x68,0x00,0x00,0x00,0x00
        {disp32} jmp     L1000
L1020:
        // jmp     QWORD PTR [rip+0xefca]
        .byte   0xff,0x25,0xca,0xef,0x00,0x00
        // push    0x1
        .byte   0x68,0x01,0x00,0x00,0x00
        {disp32} jmp     L1000
L1030:
        // jmp     QWORD PTR [rip+0xefc2]
        .byte   0xff,0x25,0xc2,0xef,0x00,0x00
        // push    0x2
        .byte   0x68,0x02,0x00,0x00,0x00
        {disp32} jmp     L1000

// The code (0x1040 to 0xbd70)

// mldsa_shake128_init (0x1040)

L1040:
        mov     QWORD PTR [rdi], 0x0
        mov     rdx, rdi
        lea     rdi, [rdi+0x8]
        xor     eax, eax
        mov     QWORD PTR [rdi+0xb8], 0x0
        mov     rcx, rdx
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xc8
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdx+0xc8], 0x0
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake128_absorb (0x1080)

L1080:
        push    r13
        mov     ecx, 0xa8
        mov     r13, rdi
        push    r12
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdx
        sub     rsp, 0x18
        mov     edx, DWORD PTR [rdi+0xc8]
        sub     ecx, edx
        mov     r12d, ecx
        cmp     rbx, r12
        jb      L10df
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L10b0:
        mov     rsi, rbp
        mov     rdi, r13
        sub     rbx, r12
        add     rbp, r12
        call    L18d0
        mov     rdi, r13
        mov     r12d, 0xa8
        call    L1a00
        xor     edx, edx
        mov     ecx, 0xa8
        cmp     rbx, 0xa7
        ja      L10b0
L10df:
        mov     ecx, ebx
        mov     rsi, rbp
        mov     rdi, r13
        mov     DWORD PTR [rsp+0xc], edx
        call    L18d0
        mov     edx, DWORD PTR [rsp+0xc]
        add     edx, ebx
        mov     DWORD PTR [r13+0xc8], edx
        add     rsp, 0x18
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_shake128_finalize (0x1110)

L1110:
        push    rbx
        mov     ecx, 0x1
        mov     rbx, rdi
        sub     rsp, 0x10
        mov     edx, DWORD PTR [rdi+0xc8]
        lea     rsi, [rsp+0xf]
        mov     BYTE PTR [rsp+0xf], 0x1f
        mov     BYTE PTR [rsp+0xe], 0x80
        call    L18d0
        lea     rsi, [rsp+0xe]
        mov     rdi, rbx
        mov     ecx, 0x1
        mov     edx, 0xa7
        call    L18d0
        mov     DWORD PTR [rbx+0xc8], 0xa8
        add     rsp, 0x10
        pop     rbx
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_shake128_squeeze (0x1160)

L1160:
        push    r15
        push    r14
        push    r13
        mov     r13, rdx
        push    r12
        push    rbp
        push    rbx
        sub     rsp, 0x8
        mov     r12d, DWORD PTR [rdx+0xc8]
        test    rsi, rsi
        je      L11e8
        mov     r14, rdi
        mov     rbx, rsi
        xor     r15d, r15d
        jmp     L11c5
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L1190:
        mov     ecx, 0xa8
        mov     edx, r12d
        sub     ecx, r12d
        mov     ebp, ecx
L119d:
        mov     r12d, 0xa8
        cmp     rbx, rbp
        jae     L11b1
        mov     ecx, ebx
        lea     r12d, [rdx+rbx*1]
        mov     rbp, rbx
L11b1:
        lea     rsi, [r14+r15*1]
        mov     rdi, r13
        add     r15, rbp
        call    L18a0
        sub     rbx, rbp
        je      L11e8
L11c5:
        cmp     r12d, 0xa8
        jne     L1190
        mov     rdi, r13
        mov     ebp, 0xa8
        call    L1a00
        mov     ecx, 0xa8
        xor     edx, edx
        jmp     L119d
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L11e8:
        mov     DWORD PTR [r13+0xc8], r12d
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_shake128_release (0x1200)

L1200:
        mov     QWORD PTR [rdi], 0x0
        mov     rdx, rdi
        lea     rdi, [rdi+0x8]
        xor     eax, eax
        mov     QWORD PTR [rdi+0xc0], 0x0
        mov     rcx, rdx
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xd0
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_shake256_init (0x1240)

L1240:
        mov     QWORD PTR [rdi], 0x0
        mov     rdx, rdi
        lea     rdi, [rdi+0x8]
        xor     eax, eax
        mov     QWORD PTR [rdi+0xb8], 0x0
        mov     rcx, rdx
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xc8
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdx+0xc8], 0x0
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake256_absorb (0x1280)

L1280:
        push    r13
        mov     ecx, 0x88
        mov     r13, rdi
        push    r12
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdx
        sub     rsp, 0x18
        mov     edx, DWORD PTR [rdi+0xc8]
        sub     ecx, edx
        mov     r12d, ecx
        cmp     rbx, r12
        jb      L12df
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L12b0:
        mov     rsi, rbp
        mov     rdi, r13
        sub     rbx, r12
        add     rbp, r12
        call    L18d0
        mov     rdi, r13
        mov     r12d, 0x88
        call    L1a00
        xor     edx, edx
        mov     ecx, 0x88
        cmp     rbx, 0x87
        ja      L12b0
L12df:
        mov     ecx, ebx
        mov     rsi, rbp
        mov     rdi, r13
        mov     DWORD PTR [rsp+0xc], edx
        call    L18d0
        mov     edx, DWORD PTR [rsp+0xc]
        add     edx, ebx
        mov     DWORD PTR [r13+0xc8], edx
        add     rsp, 0x18
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_shake256_finalize (0x1310)

L1310:
        push    rbx
        mov     ecx, 0x1
        mov     rbx, rdi
        sub     rsp, 0x10
        mov     edx, DWORD PTR [rdi+0xc8]
        lea     rsi, [rsp+0xf]
        mov     BYTE PTR [rsp+0xf], 0x1f
        mov     BYTE PTR [rsp+0xe], 0x80
        call    L18d0
        lea     rsi, [rsp+0xe]
        mov     rdi, rbx
        mov     ecx, 0x1
        mov     edx, 0x87
        call    L18d0
        mov     DWORD PTR [rbx+0xc8], 0x88
        add     rsp, 0x10
        pop     rbx
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_shake256_squeeze (0x1360)

L1360:
        push    r15
        push    r14
        push    r13
        mov     r13, rdx
        push    r12
        push    rbp
        push    rbx
        sub     rsp, 0x8
        mov     r12d, DWORD PTR [rdx+0xc8]
        test    rsi, rsi
        je      L13e8
        mov     r14, rdi
        mov     rbx, rsi
        xor     r15d, r15d
        jmp     L13c5
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L1390:
        mov     ecx, 0x88
        mov     edx, r12d
        sub     ecx, r12d
        mov     ebp, ecx
L139d:
        mov     r12d, 0x88
        cmp     rbx, rbp
        jae     L13b1
        mov     ecx, ebx
        lea     r12d, [rdx+rbx*1]
        mov     rbp, rbx
L13b1:
        lea     rsi, [r14+r15*1]
        mov     rdi, r13
        add     r15, rbp
        call    L18a0
        sub     rbx, rbp
        je      L13e8
L13c5:
        cmp     r12d, 0x88
        jne     L1390
        mov     rdi, r13
        mov     ebp, 0x88
        call    L1a00
        mov     ecx, 0x88
        xor     edx, edx
        jmp     L139d
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L13e8:
        mov     DWORD PTR [r13+0xc8], r12d
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_shake256_release (0x1400)

L1400:
        mov     QWORD PTR [rdi], 0x0
        mov     rdx, rdi
        lea     rdi, [rdi+0x8]
        xor     eax, eax
        mov     QWORD PTR [rdi+0xc0], 0x0
        mov     rcx, rdx
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xd0
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_shake256 (0x1440)

L1440:
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rsi
        push    rbp
        mov     rbp, rdi
        push    rbx
        sub     rsp, 0xd0
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1240
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, rbx
        call    L1280
        mov     rdi, rbx
        call    L1310
        mov     rdx, rbx
        mov     rsi, r12
        mov     rdi, rbp
        call    L1360
        mov     rdi, rbx
        call    L1400
        add     rsp, 0xd0
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mld_keccak_absorb_once_x4.constprop.0 (0x14b0)

L14b0:
        push    r15
        mov     r15, r8
        mov     r8, r9
        push    r14
        mov     r14, rdi
        push    r13
        mov     r13, rcx
        push    r12
        mov     r12, rdx
        push    rbp
        push    rbx
        mov     ebx, esi
        sub     rsp, 0x28
        mov     rbp, QWORD PTR [rsp+0x60]
        mov     DWORD PTR [rsp+0xc], esi
        mov     BYTE PTR [rsp+0x1f], 0x1f
        cmp     rbp, rbx
        jb      L152f
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L14e8:
        sub     rsp, 0x8
        xor     r9d, r9d
        mov     rcx, r15
        mov     rdx, r13
        mov     eax, DWORD PTR [rsp+0x14]
        mov     rsi, r12
        mov     rdi, r14
        sub     rbp, rbx
        add     r12, rbx
        add     r13, rbx
        add     r15, rbx
        push    rax
        mov     QWORD PTR [rsp+0x10], r8
        call    L1980
        mov     rdi, r14
        call    L22d0
        mov     r8, QWORD PTR [rsp+0x10]
        pop     r9
        pop     r10
        add     r8, rbx
        cmp     rbp, rbx
        jae     L14e8
L152f:
        mov     eax, DWORD PTR [rsp+0xc]
        mov     ebx, ebp
        sub     eax, 0x1
        mov     DWORD PTR [rsp], eax
        test    rbp, rbp
        jne     L15a0
L1540:
        lea     rbp, [rsp+0x1f]
        sub     rsp, 0x8
        mov     r9d, ebx
        mov     rdi, r14
        push    0x1
        mov     r8, rbp
        mov     rcx, rbp
        mov     rdx, rbp
        mov     rsi, rbp
        call    L1980
        mov     r9d, DWORD PTR [rsp+0x10]
        mov     rdx, rbp
        mov     r8, rbp
        mov     rcx, rbp
        mov     rsi, rbp
        mov     rdi, r14
        mov     BYTE PTR [rsp+0x2f], 0x80
        mov     DWORD PTR [rsp], 0x1
        call    L1980
        pop     rax
        pop     rdx
        add     rsp, 0x28
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L15a0:
        sub     rsp, 0x8
        mov     rdi, r14
        xor     r9d, r9d
        mov     rcx, r15
        push    rbp
        mov     rdx, r13
        mov     rsi, r12
        call    L1980
        mov     eax, DWORD PTR [rsp+0x10]
        pop     rdi
        pop     r8
        cmp     rax, rbp
        jne     L1540
        lea     rsi, [rsp+0x1f]
        or      BYTE PTR [rsp+0x1f], 0x80
        mov     r9d, ebp
        mov     rdi, r14
        sub     rsp, 0x8
        mov     rcx, rsi
        mov     r8, rsi
        mov     rdx, rsi
        push    0x1
        call    L1980
        pop     rcx
        pop     rsi
        add     rsp, 0x28
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_shake128x4_absorb_once (0x1600)

L1600:
        sub     rsp, 0x10
        mov     r10, rdi
        mov     QWORD PTR [rdi], 0x0
        xor     eax, eax
        mov     QWORD PTR [rdi+0x318], 0x0
        lea     rdi, [rdi+0x8]
        mov     r11, rcx
        mov     rcx, r10
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        push    r9
        mov     rcx, rdx
        mov     r9, r8
        mov     rdx, rsi
        mov     r8, r11
        mov     esi, 0xa8
        mov     rdi, r10
        call    L14b0
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_shake128x4_squeezeblocks (0x1660)

L1660:
        test    r8, r8
        je      L16f0
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12, rsi
        push    rbp
        mov     rbp, rdx
        push    rbx
        mov     rbx, rcx
        sub     rsp, 0x8
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L1690:
        mov     rdi, r15
        call    L22d0
        sub     rsp, 0x8
        mov     rdx, r12
        mov     r8, rbx
        push    0xa8
        mov     rcx, rbp
        mov     rsi, r13
        xor     r9d, r9d
        mov     rdi, r15
        add     r13, 0xa8
        add     r12, 0xa8
        add     rbp, 0xa8
        add     rbx, 0xa8
        call    L1900
        pop     rax
        pop     rdx
        sub     r14, 0x1
        jne     L1690
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L16f0:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake128x4_init (0x1700)

L1700:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake128x4_release (0x1710)

L1710:
        mov     QWORD PTR [rdi], 0x0
        mov     rdx, rdi
        lea     rdi, [rdi+0x8]
        xor     eax, eax
        mov     QWORD PTR [rdi+0x310], 0x0
        mov     rcx, rdx
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_shake256x4_absorb_once (0x1750)

L1750:
        sub     rsp, 0x10
        mov     r10, rdi
        mov     QWORD PTR [rdi], 0x0
        xor     eax, eax
        mov     QWORD PTR [rdi+0x318], 0x0
        lea     rdi, [rdi+0x8]
        mov     r11, rcx
        mov     rcx, r10
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        push    r9
        mov     rcx, rdx
        mov     r9, r8
        mov     rdx, rsi
        mov     r8, r11
        mov     esi, 0x88
        mov     rdi, r10
        call    L14b0
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_shake256x4_squeezeblocks (0x17b0)

L17b0:
        test    r8, r8
        je      L1840
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12, rsi
        push    rbp
        mov     rbp, rdx
        push    rbx
        mov     rbx, rcx
        sub     rsp, 0x8
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L17e0:
        mov     rdi, r15
        call    L22d0
        sub     rsp, 0x8
        mov     rdx, r12
        mov     r8, rbx
        push    0x88
        mov     rcx, rbp
        mov     rsi, r13
        xor     r9d, r9d
        mov     rdi, r15
        add     r13, 0x88
        add     r12, 0x88
        add     rbp, 0x88
        add     rbx, 0x88
        call    L1900
        pop     rax
        pop     rdx
        sub     r14, 0x1
        jne     L17e0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L1840:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake256x4_init (0x1850)

L1850:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake256x4_release (0x1860)

L1860:
        mov     QWORD PTR [rdi], 0x0
        mov     rdx, rdi
        lea     rdi, [rdi+0x8]
        xor     eax, eax
        mov     QWORD PTR [rdi+0x310], 0x0
        mov     rcx, rdx
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_keccakf1600_extract_bytes (0x18a0)

L18a0:
        mov     edx, edx
        test    ecx, ecx
        je      L18c0
        mov     ecx, ecx
        xor     eax, eax
        add     rdi, rdx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L18b0:
        movzx   edx, BYTE PTR [rdi+rax*1]
        mov     BYTE PTR [rsi+rax*1], dl
        add     rax, 0x1
        cmp     rcx, rax
        jne     L18b0
L18c0:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_keccakf1600_xor_bytes (0x18d0)

L18d0:
        mov     edx, edx
        test    ecx, ecx
        je      L18f2
        mov     ecx, ecx
        add     rdi, rdx
        lea     rdx, [rsi+rcx*1]
        // nop
        .byte   0x90
L18e0:
        movzx   eax, BYTE PTR [rsi]
        add     rsi, 0x1
        xor     BYTE PTR [rdi], al
        add     rdi, 0x1
        cmp     rsi, rdx
        jne     L18e0
L18f2:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_keccakf1600x4_extract_bytes (0x1900)

L1900:
        push    r15
        mov     r15, rdx
        mov     edx, r9d
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, r8
        push    r12
        push    rbp
        mov     ebp, r9d
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        mov     r12d, DWORD PTR [rsp+0x40]
        mov     ecx, r12d
        call    L18a0
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r15
        lea     rdi, [rbx+0xc8]
        call    L18a0
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r14
        lea     rdi, [rbx+0x190]
        call    L18a0
        add     rsp, 0x8
        mov     ecx, r12d
        mov     edx, ebp
        lea     rdi, [rbx+0x258]
        mov     rsi, r13
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        jmp     L18a0
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_keccakf1600x4_xor_bytes (0x1980)

L1980:
        push    r15
        mov     r15, rdx
        mov     edx, r9d
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, r8
        push    r12
        push    rbp
        mov     ebp, r9d
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        mov     r12d, DWORD PTR [rsp+0x40]
        mov     ecx, r12d
        call    L18d0
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r15
        lea     rdi, [rbx+0xc8]
        call    L18d0
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r14
        lea     rdi, [rbx+0x190]
        call    L18d0
        add     rsp, 0x8
        mov     ecx, r12d
        mov     edx, ebp
        lea     rdi, [rbx+0x258]
        mov     rsi, r13
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        jmp     L18d0
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_keccakf1600_permute (0x1a00)

L1a00:
        push    r15
        mov     rax, rdi
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        sub     rsp, 0x58
        mov     rdx, QWORD PTR [rdi+0x8]
        mov     r13, QWORD PTR [rdi+0x18]
        mov     r15, QWORD PTR [rdi]
        mov     r12, QWORD PTR [rdi+0x60]
        mov     QWORD PTR [rsp-0x70], rdx
        mov     rdx, QWORD PTR [rdi+0x10]
        mov     QWORD PTR [rsp-0x68], rdx
        mov     rdx, QWORD PTR [rdi+0x20]
        mov     QWORD PTR [rsp-0x60], rdx
        mov     rdx, QWORD PTR [rdi+0x28]
        mov     QWORD PTR [rsp-0x58], rdx
        mov     rdx, QWORD PTR [rdi+0x30]
        mov     QWORD PTR [rsp-0x50], rdx
        mov     rdx, QWORD PTR [rdi+0x38]
        mov     QWORD PTR [rsp-0x48], rdx
        mov     rdx, QWORD PTR [rdi+0x40]
        mov     QWORD PTR [rsp-0x40], rdx
        mov     rdx, QWORD PTR [rdi+0x48]
        mov     QWORD PTR [rsp-0x38], rdx
        mov     rdx, QWORD PTR [rdi+0x50]
        mov     QWORD PTR [rsp-0x30], rdx
        mov     rdx, QWORD PTR [rdi+0x58]
        mov     QWORD PTR [rsp-0x28], rdx
        mov     rdx, QWORD PTR [rdi+0x68]
        mov     QWORD PTR [rsp-0x20], rdx
        mov     rdx, QWORD PTR [rdi+0x70]
        mov     QWORD PTR [rsp+0x18], r13
        mov     r11, QWORD PTR [rax+0x90]
        mov     QWORD PTR [rsp-0x18], rdx
        mov     rdx, QWORD PTR [rdi+0x78]
        mov     QWORD PTR [rsp+0x50], rax
        mov     rdi, QWORD PTR [rdi+0x80]
        mov     QWORD PTR [rsp-0x10], rdx
        mov     rdx, QWORD PTR [rax+0x88]
        mov     r14, QWORD PTR [rax+0xa0]
        mov     r8, QWORD PTR [rax+0xb0]
        mov     QWORD PTR [rsp-0x8], rdx
        mov     rdx, QWORD PTR [rax+0x98]
        mov     rbx, QWORD PTR [rax+0xc0]
        mov     QWORD PTR [rsp], rdx
        mov     rdx, QWORD PTR [rax+0xa8]
        mov     QWORD PTR [rsp+0x8], rdx
        mov     rdx, QWORD PTR [rax+0xb8]
        mov     QWORD PTR [rsp+0x10], rdx
        lea     rdx, [rip+Lc000]
        mov     QWORD PTR [rsp-0x78], rdx
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L1b00:
        mov     rcx, QWORD PTR [rsp-0x58]
        mov     rax, QWORD PTR [rsp-0x30]
        mov     rsi, QWORD PTR [rsp-0x10]
        mov     r13, QWORD PTR [rsp-0x70]
        xor     rcx, r15
        mov     rdx, QWORD PTR [rsp-0x28]
        mov     rbp, QWORD PTR [rsp+0x8]
        xor     rcx, rax
        mov     r9, QWORD PTR [rsp+0x18]
        mov     r10, QWORD PTR [rsp-0x68]
        xor     rcx, rsi
        mov     rsi, QWORD PTR [rsp-0x50]
        mov     rax, QWORD PTR [rsp-0x8]
        xor     rcx, r14
        xor     r13, rsi
        mov     rsi, QWORD PTR [rsp-0x20]
        xor     r13, rdx
        mov     rdx, QWORD PTR [rsp-0x40]
        xor     r13, rdi
        xor     r13, rbp
        xor     r9, rdx
        mov     rbp, QWORD PTR [rsp-0x48]
        mov     rdx, QWORD PTR [rsp+0x10]
        xor     r9, rsi
        xor     r10, rbp
        xor     r9, r11
        mov     rbp, QWORD PTR [rsp-0x38]
        xor     r9, rdx
        xor     r10, r12
        mov     rdx, QWORD PTR [rsp-0x60]
        xor     r10, rax
        mov     rax, QWORD PTR [rsp-0x18]
        xor     rdx, rbp
        mov     rbp, r13
        xor     r10, r8
        xor     rdx, rax
        mov     rax, QWORD PTR [rsp]
        rol     rbp, 1
        mov     rsi, r10
        rol     rsi, 1
        xor     rdx, rax
        xor     rsi, rcx
        mov     rax, r9
        rol     rcx, 1
        xor     rdx, rbx
        rol     rax, 1
        xor     rcx, r9
        xor     rbp, rdx
        rol     rdx, 1
        xor     rax, r13
        xor     rdx, r10
        mov     r10, QWORD PTR [rsp-0x50]
        xor     r15, rbp
        mov     r9, r15
        xor     r10, rsi
        ror     r10, 0x14
        xor     r12, rax
        xor     r11, rdx
        xor     rbx, rcx
        mov     r15, r10
        ror     r12, 0x15
        xor     rdi, rsi
        xor     r8, rax
        rol     r11, 0x15
        not     r15
        rol     rbx, 0xe
        ror     rdi, 0x13
        mov     r13, r15
        mov     r15, QWORD PTR [rsp-0x78]
        ror     r8, 0x3
        and     r13, r12
        mov     QWORD PTR [rsp-0x50], r13
        mov     r13, QWORD PTR [r15]
        xor     r13, r9
        mov     r15, r13
        mov     r13, QWORD PTR [rsp-0x50]
        xor     r15, r13
        mov     r13, r12
        not     r13
        and     r13, r11
        xor     r13, r10
        mov     QWORD PTR [rsp+0x20], r13
        mov     r13, r11
        not     r13
        and     r13, rbx
        xor     r13, r12
        mov     r12, rbx
        not     r12
        mov     QWORD PTR [rsp+0x28], r13
        and     r12, r9
        not     r9
        and     r9, r10
        xor     r12, r11
        mov     r11, QWORD PTR [rsp-0x30]
        mov     r10, r9
        mov     r9, QWORD PTR [rsp+0x18]
        mov     QWORD PTR [rsp-0x50], r12
        mov     r12, rdi
        xor     r10, rbx
        xor     r11, rbp
        not     r12
        mov     QWORD PTR [rsp+0x30], r10
        mov     r10, QWORD PTR [rsp-0x38]
        rol     r11, 0x3
        xor     r9, rdx
        rol     r9, 0x1c
        xor     r10, rcx
        rol     r10, 0x14
        mov     rbx, r10
        not     rbx
        and     rbx, r11
        xor     rbx, r9
        mov     QWORD PTR [rsp+0x38], rbx
        mov     rbx, r11
        not     rbx
        and     rbx, rdi
        xor     rbx, r10
        mov     QWORD PTR [rsp+0x18], rbx
        mov     rbx, r12
        and     rbx, r8
        xor     r14, rbp
        mov     r12, rbx
        rol     r14, 0x12
        xor     r12, r11
        mov     r11, r8
        not     r11
        mov     QWORD PTR [rsp-0x30], r12
        mov     rbx, QWORD PTR [rsp-0x58]
        and     r11, r9
        not     r9
        and     r9, r10
        xor     r11, rdi
        mov     rdi, QWORD PTR [rsp-0x70]
        xor     rbx, rbp
        xor     r9, r8
        mov     r8, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rsp+0x40], r11
        ror     rbx, 0x1c
        mov     r11, QWORD PTR [rsp-0x20]
        xor     rdi, rsi
        mov     QWORD PTR [rsp-0x38], r9
        xor     r8, rax
        mov     r9, QWORD PTR [rsp]
        rol     rdi, 1
        rol     r8, 0x6
        xor     r11, rdx
        mov     r10, r8
        rol     r11, 0x19
        xor     r9, rcx
        not     r10
        mov     r13, r11
        rol     r9, 0x8
        and     r10, r11
        not     r13
        xor     r10, rdi
        mov     QWORD PTR [rsp-0x48], r10
        mov     r10, r13
        mov     r13, r9
        and     r10, r9
        not     r13
        xor     r10, r8
        mov     QWORD PTR [rsp], r10
        mov     r10, r13
        and     r10, r14
        xor     r10, r11
        mov     r11, r14
        not     r11
        and     r11, rdi
        not     rdi
        and     rdi, r8
        xor     r11, r9
        mov     r8, QWORD PTR [rsp-0x60]
        mov     r9, QWORD PTR [rsp-0x28]
        xor     rdi, r14
        mov     QWORD PTR [rsp-0x20], r11
        mov     r14, QWORD PTR [rsp-0x68]
        mov     QWORD PTR [rsp+0x48], rdi
        mov     rdi, QWORD PTR [rsp-0x8]
        xor     r8, rcx
        xor     r9, rsi
        rol     r9, 0xa
        rol     r8, 0x1b
        xor     rdi, rax
        xor     rax, r14
        mov     r14, QWORD PTR [rsp-0x40]
        mov     r12, rdi
        mov     rdi, QWORD PTR [rsp+0x10]
        ror     rax, 0x2
        rol     r12, 0xf
        xor     rdi, rdx
        mov     r13, r12
        xor     rdx, r14
        mov     r14, QWORD PTR [rsp-0x18]
        mov     r11, rdi
        mov     rdi, rbx
        not     r13
        ror     rdx, 0x9
        not     rdi
        ror     r11, 0x8
        xor     rcx, r14
        and     rdi, r9
        and     r13, r11
        ror     rcx, 0x19
        xor     rdi, r8
        xor     r13, r9
        mov     QWORD PTR [rsp+0x10], rdi
        mov     rdi, r9
        mov     r9, r11
        not     r9
        not     rdi
        and     r9, r8
        not     r8
        and     rdi, r12
        and     r8, rbx
        xor     rdi, rbx
        xor     r9, r12
        mov     r12, QWORD PTR [rsp+0x20]
        xor     r8, r11
        mov     r11, rcx
        mov     rcx, QWORD PTR [rsp-0x10]
        mov     QWORD PTR [rsp-0x28], r8
        xor     rbp, rcx
        mov     rcx, QWORD PTR [rsp+0x8]
        ror     rbp, 0x17
        xor     rsi, rcx
        mov     rcx, rdx
        rol     rsi, 0x2
        not     rcx
        mov     r8, rsi
        mov     rsi, r11
        and     rcx, r11
        not     rsi
        mov     r14, r8
        xor     rcx, rax
        and     rsi, rbp
        not     r14
        mov     QWORD PTR [rsp-0x18], rcx
        xor     rsi, rdx
        mov     rbx, rsi
        mov     rsi, rbp
        not     rsi
        mov     QWORD PTR [rsp+0x8], rbx
        and     rsi, r8
        xor     rsi, r11
        mov     r11, r14
        and     r11, rax
        not     rax
        mov     r14, r11
        xor     r14, rbp
        and     rax, rdx
        mov     rbp, QWORD PTR [rsp+0x10]
        mov     rdx, QWORD PTR [rsp]
        xor     rax, r8
        mov     r8, QWORD PTR [rsp+0x38]
        mov     QWORD PTR [rsp-0x10], r14
        mov     r14, QWORD PTR [rsp-0x48]
        xor     r8, r15
        xor     r8, r14
        xor     r8, rbp
        mov     rbp, QWORD PTR [rsp+0x28]
        xor     r8, rcx
        mov     rcx, QWORD PTR [rsp+0x18]
        xor     r12, rcx
        xor     r12, rdx
        mov     rdx, QWORD PTR [rsp-0x30]
        mov     r11, QWORD PTR [rsp-0x50]
        mov     QWORD PTR [rsp-0x8], r13
        xor     r12, rdi
        mov     r14, QWORD PTR [rsp-0x10]
        xor     rbp, rdx
        xor     r12, rbx
        mov     rbx, QWORD PTR [rsp+0x40]
        mov     rdx, QWORD PTR [rsp-0x38]
        xor     rbp, r10
        xor     rbp, r13
        mov     r13, QWORD PTR [rsp-0x20]
        xor     r11, rbx
        mov     rbx, QWORD PTR [rsp+0x48]
        xor     rbp, rsi
        xor     r11, r13
        xor     rdx, rbx
        mov     rbx, QWORD PTR [rsp+0x30]
        mov     r13, rbp
        xor     r11, r9
        rol     r13, 1
        xor     r11, r14
        mov     r14, QWORD PTR [rsp-0x28]
        xor     rdx, rbx
        xor     r13, r8
        mov     rbx, r11
        rol     r8, 1
        xor     rdx, r14
        mov     r14, r12
        rol     rbx, 1
        xor     r8, r11
        xor     rdx, rax
        rol     r14, 1
        xor     rbx, r12
        xor     r14, rdx
        rol     rdx, 1
        xor     rdx, rbp
        mov     rbp, rcx
        xor     r15, r14
        xor     r10, rbx
        xor     rbp, r13
        mov     r11, r15
        ror     r10, 0x15
        xor     r9, rdx
        ror     rbp, 0x14
        rol     r9, 0x15
        xor     rax, r8
        xor     rdi, r13
        rol     rax, 0xe
        mov     r15, rbp
        ror     rdi, 0x13
        xor     rsi, rbx
        not     r15
        ror     rsi, 0x3
        mov     r12, r15
        mov     r15, QWORD PTR [rsp-0x78]
        and     r12, r10
        mov     rcx, QWORD PTR [r15+0x8]
        xor     rcx, r11
        mov     r15, rcx
        mov     rcx, QWORD PTR [rsp-0x18]
        xor     r15, r12
        mov     r12, r10
        not     r12
        and     r12, r9
        xor     r12, rbp
        mov     QWORD PTR [rsp-0x70], r12
        mov     r12, r9
        not     r12
        and     r12, rax
        xor     r12, r10
        mov     r10, rax
        not     r10
        mov     QWORD PTR [rsp-0x68], r12
        mov     r12, QWORD PTR [rsp+0x20]
        and     r10, r11
        not     r11
        and     r11, rbp
        xor     r10, r9
        mov     r9, QWORD PTR [rsp-0x38]
        xor     r11, rax
        mov     QWORD PTR [rsp+0x18], r10
        mov     r10, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rsp-0x60], r11
        mov     r11, QWORD PTR [rsp-0x50]
        xor     r9, r8
        rol     r9, 0x14
        xor     r10, r14
        xor     r11, rdx
        rol     r10, 0x3
        mov     rax, r11
        mov     r11, r9
        not     r11
        rol     rax, 0x1c
        and     r11, r10
        xor     r11, rax
        mov     QWORD PTR [rsp-0x58], r11
        mov     r11, r10
        not     r11
        and     r11, rdi
        xor     r12, r13
        xor     rcx, r14
        xor     r11, r9
        rol     rcx, 0x12
        mov     QWORD PTR [rsp-0x50], r11
        mov     r11, rdi
        not     r11
        and     r11, rsi
        xor     r11, r10
        mov     r10, rsi
        not     r10
        mov     QWORD PTR [rsp-0x48], r11
        and     r10, rax
        not     rax
        xor     r10, rdi
        and     rax, r9
        mov     rdi, QWORD PTR [rsp-0x20]
        mov     r11, rax
        mov     QWORD PTR [rsp-0x40], r10
        mov     rax, r12
        xor     r11, rsi
        xor     rdi, rdx
        mov     rsi, QWORD PTR [rsp-0x30]
        rol     rax, 1
        mov     r9, rdi
        mov     rdi, QWORD PTR [rsp-0x28]
        mov     QWORD PTR [rsp-0x38], r11
        xor     rsi, rbx
        rol     r9, 0x19
        rol     rsi, 0x6
        xor     rdi, r8
        rol     rdi, 0x8
        mov     r10, rsi
        mov     r12, rdi
        not     r10
        and     r10, r9
        not     r12
        xor     r10, rax
        and     r12, rcx
        mov     QWORD PTR [rsp-0x30], r10
        xor     r12, r9
        mov     r10, r9
        mov     r9, rcx
        not     r9
        not     r10
        and     r9, rax
        not     rax
        and     r10, rdi
        and     rax, rsi
        xor     r9, rdi
        xor     r10, rsi
        mov     rdi, rax
        mov     QWORD PTR [rsp-0x28], r10
        xor     rdi, rcx
        mov     QWORD PTR [rsp-0x20], r9
        mov     QWORD PTR [rsp-0x18], rdi
        mov     rax, QWORD PTR [rsp+0x30]
        mov     rsi, QWORD PTR [rsp+0x38]
        mov     r9, QWORD PTR [rsp]
        mov     r10, QWORD PTR [rsp-0x8]
        xor     rax, r8
        mov     rcx, QWORD PTR [rsp-0x10]
        xor     rsi, r14
        rol     rax, 0x1b
        mov     rbp, QWORD PTR [rsp+0x28]
        ror     rsi, 0x1c
        xor     r9, r13
        xor     r10, rbx
        xor     rcx, rdx
        rol     r10, 0xf
        ror     rcx, 0x8
        mov     rdi, rsi
        xor     rbx, rbp
        rol     r9, 0xa
        mov     r11, r10
        not     rdi
        ror     rbx, 0x2
        not     r11
        and     rdi, r9
        and     r11, rcx
        xor     rdi, rax
        xor     r11, r9
        mov     QWORD PTR [rsp-0x10], rdi
        mov     rdi, r9
        mov     QWORD PTR [rsp-0x8], r11
        mov     r11, rcx
        not     rdi
        not     r11
        and     rdi, r10
        and     r11, rax
        not     rax
        xor     rdi, rsi
        and     rax, rsi
        mov     rsi, QWORD PTR [rsp+0x8]
        xor     r11, r10
        mov     r9, rax
        mov     rax, QWORD PTR [rsp+0x40]
        xor     r9, rcx
        mov     rcx, QWORD PTR [rsp+0x48]
        xor     rsi, r13
        xor     rax, rdx
        mov     rdx, QWORD PTR [rsp+0x10]
        rol     rsi, 0x2
        mov     QWORD PTR [rsp], r9
        xor     rcx, r8
        ror     rax, 0x9
        ror     rcx, 0x19
        xor     rdx, r14
        mov     r14, rax
        mov     r8, rcx
        ror     rdx, 0x17
        not     r14
        not     r8
        and     r14, rcx
        and     r8, rdx
        xor     r14, rbx
        xor     r8, rax
        mov     QWORD PTR [rsp+0x8], r8
        mov     r8, rdx
        not     r8
        and     r8, rsi
        xor     r8, rcx
        mov     rcx, rsi
        not     rcx
        and     rcx, rbx
        not     rbx
        add     QWORD PTR [rsp-0x78], 0x10
        and     rbx, rax
        mov     rax, QWORD PTR [rsp-0x78]
        xor     rcx, rdx
        lea     rdx, [rip+Lc0c0]
        mov     QWORD PTR [rsp+0x10], rcx
        xor     rbx, rsi
        cmp     rdx, rax
        jne     L1b00
        mov     rax, QWORD PTR [rsp+0x50]
        mov     rdx, QWORD PTR [rsp-0x70]
        mov     r13, QWORD PTR [rsp+0x18]
        mov     QWORD PTR [rax+0x8], rdx
        mov     rdx, QWORD PTR [rsp-0x68]
        mov     QWORD PTR [rax], r15
        mov     QWORD PTR [rax+0x10], rdx
        mov     rdx, QWORD PTR [rsp-0x60]
        mov     QWORD PTR [rax+0x18], r13
        mov     QWORD PTR [rax+0x20], rdx
        mov     rdx, QWORD PTR [rsp-0x58]
        mov     QWORD PTR [rax+0x60], r12
        mov     QWORD PTR [rax+0x28], rdx
        mov     rdx, QWORD PTR [rsp-0x50]
        mov     QWORD PTR [rax+0x80], rdi
        mov     QWORD PTR [rax+0x30], rdx
        mov     rdx, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rax+0x38], rdx
        mov     rdx, QWORD PTR [rsp-0x40]
        mov     QWORD PTR [rax+0x40], rdx
        mov     rdx, QWORD PTR [rsp-0x38]
        mov     QWORD PTR [rax+0x48], rdx
        mov     rdx, QWORD PTR [rsp-0x30]
        mov     QWORD PTR [rax+0x50], rdx
        mov     rdx, QWORD PTR [rsp-0x28]
        mov     QWORD PTR [rax+0x58], rdx
        mov     rdx, QWORD PTR [rsp-0x20]
        mov     QWORD PTR [rax+0x68], rdx
        mov     rdx, QWORD PTR [rsp-0x18]
        mov     QWORD PTR [rax+0x70], rdx
        mov     rdx, QWORD PTR [rsp-0x10]
        mov     QWORD PTR [rax+0x78], rdx
        mov     rdx, QWORD PTR [rsp-0x8]
        mov     QWORD PTR [rax+0x90], r11
        mov     QWORD PTR [rax+0x88], rdx
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     QWORD PTR [rax+0x98], r9
        mov     QWORD PTR [rax+0xa0], r14
        mov     QWORD PTR [rax+0xa8], rdx
        mov     QWORD PTR [rax+0xb0], r8
        mov     QWORD PTR [rax+0xb8], rcx
        mov     QWORD PTR [rax+0xc0], rbx
        add     rsp, 0x58
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_keccakf1600x4_permute (0x22d0)

L22d0:
        push    rbx
        mov     rbx, rdi
        call    L1a00
        lea     rdi, [rbx+0xc8]
        call    L1a00
        lea     rdi, [rbx+0x190]
        call    L1a00
        lea     rdi, [rbx+0x258]
        pop     rbx
        jmp     L1a00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_unpack_pk_t1 (0x2300)

L2300:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x6
        lea     rsi, [rax+rsi*1+0x20]
        jmp     L2e10

// mldsa44_pack_sk_rho_key_tr (0x2310)

L2310:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rcx]
        movups  XMMWORD PTR [rdi+0x20], xmm2
        movdqu  xmm3, XMMWORD PTR [rcx+0x10]
        movups  XMMWORD PTR [rdi+0x30], xmm3
        movdqu  xmm4, XMMWORD PTR [rdx]
        movups  XMMWORD PTR [rdi+0x40], xmm4
        movdqu  xmm5, XMMWORD PTR [rdx+0x10]
        movups  XMMWORD PTR [rdi+0x50], xmm5
        movdqu  xmm6, XMMWORD PTR [rdx+0x20]
        movups  XMMWORD PTR [rdi+0x60], xmm6
        movdqu  xmm7, XMMWORD PTR [rdx+0x30]
        movups  XMMWORD PTR [rdi+0x70], xmm7
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_unpack_sk (0x2360)

L2360:
        push    r13
        mov     r13, rcx
        push    r12
        mov     r12, r8
        push    rbp
        push    rbx
        mov     rbx, r9
        sub     rsp, 0x8
        mov     rbp, QWORD PTR [rsp+0x30]
        movdqu  xmm0, XMMWORD PTR [rbp+0x0]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rbp+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rbp+0x20]
        mov     rdi, r8
        movups  XMMWORD PTR [rdx], xmm2
        movdqu  xmm3, XMMWORD PTR [rbp+0x30]
        movups  XMMWORD PTR [rdx+0x10], xmm3
        movdqu  xmm4, XMMWORD PTR [rbp+0x40]
        movups  XMMWORD PTR [rsi], xmm4
        movdqu  xmm5, XMMWORD PTR [rbp+0x50]
        movups  XMMWORD PTR [rsi+0x10], xmm5
        movdqu  xmm6, XMMWORD PTR [rbp+0x60]
        movups  XMMWORD PTR [rsi+0x20], xmm6
        movdqu  xmm7, XMMWORD PTR [rbp+0x70]
        movups  XMMWORD PTR [rsi+0x30], xmm7
        lea     rsi, [rbp+0x80]
        call    L4170
        mov     rdi, r12
        mov     r12, r13
        call    L3f60
        lea     rsi, [rbp+0x200]
        mov     rdi, rbx
        call    L41f0
        mov     rdi, rbx
        lea     rbx, [rbp+0x380]
        add     rbp, 0xa00
        call    L4070
L23fc:
        mov     rsi, rbx
        mov     rdi, r12
        add     rbx, 0x1a0
        add     r12, 0x400
        call    L3020
        cmp     rbx, rbp
        jne     L23fc
        add     rsp, 0x8
        mov     rdi, r13
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        jmp     L4070
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_pack_sig_c (0x2430)

L2430:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_pack_sig_h (0x2450)

L2450:
        push    r15
        lea     r15, [rdi+0x920]
        xor     eax, eax
        push    r14
        mov     r14, rsi
        push    r13
        mov     r13, rcx
        mov     rcx, r15
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rdi
        lea     rdi, [rdi+0x928]
        push    rbx
        add     rbp, 0x970
        xor     ebx, ebx
        sub     rsp, 0x18
        mov     QWORD PTR [rdi-0x8], 0x0
        mov     QWORD PTR [rdi+0x44], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x54
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        lea     rax, [rdx+0x300]
        mov     QWORD PTR [rsp+0x8], rax
L24b2:
        mov     rsi, r12
        mov     rdi, r13
        call    L32b0
        xor     eax, eax
        jmp     L24dd
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L24c8:
        mov     ecx, ebx
        add     ebx, 0x1
        mov     BYTE PTR [r15+rcx*1], al
L24d1:
        add     rax, 0x1
        cmp     rax, 0x100
        je      L2519
L24dd:
        mov     ecx, DWORD PTR [r14+rax*4]
        mov     edi, DWORD PTR [r13+rax*4+0x0]
        lea     esi, [rcx+0x17400]
        cmp     esi, 0x2e800
        ja      L2500
        cmp     ecx, 0xfffe8c00
        jne     L24d1
        test    edi, edi
        je      L24d1
L2500:
        cmp     ebx, 0x50
        jne     L24c8
        mov     eax, 0xffffffff
L250a:
        add     rsp, 0x18
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
L2519:
        mov     rax, QWORD PTR [rsp+0x8]
        add     r12, 0xc0
        mov     BYTE PTR [rbp+0x0], bl
        add     r14, 0x400
        add     rbp, 0x1
        cmp     r12, rax
        jne     L24b2
        xor     eax, eax
        jmp     L250a

// mldsa44_pack_sig_z (0x2540)

L2540:
        lea     eax, [rdx+rdx*8]
        shl     eax, 0x6
        lea     rdi, [rax+rdi*1+0x20]
        jmp     L3b50

// mldsa44_sig_unpack_hints (0x2550)

L2550:
        push    rbp
        mov     r11, rsi
        mov     r8, rdi
        mov     ebp, edx
        push    rbx
        lea     rbx, [rsi+0x920]
        xor     esi, esi
        test    edx, edx
        je      L2573
        lea     eax, [rdx+0x4f]
        movzx   esi, BYTE PTR [r11+rax*1+0x920]
L2573:
        lea     eax, [rbp+0x50]
        movzx   r9d, BYTE PTR [r11+rax*1+0x920]
        mov     r10, r9
        cmp     r9d, esi
        jb      L25f6
        cmp     r9d, 0x50
        ja      L25f6
        lea     rdi, [r8+0x8]
        mov     rcx, r8
        xor     eax, eax
        mov     QWORD PTR [r8], 0x0
        mov     QWORD PTR [r8+0x3f8], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x400
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        cmp     esi, r9d
        jae     L2600
        lea     edx, [rsi+0x920]
        mov     eax, esi
        add     rdx, r11
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L25d0:
        movzx   ecx, BYTE PTR [rdx]
        add     rdx, 0x1
        mov     DWORD PTR [r8+rcx*4], 0x1
        mov     ecx, eax
        add     eax, 0x1
        cmp     eax, r9d
        jae     L2600
        cmp     esi, eax
        jae     L25d0
        movzx   edi, BYTE PTR [rdx]
        cmp     BYTE PTR [rbx+rcx*1], dil
        jb      L25d0
L25f6:
        mov     eax, 0xffffffff
        pop     rbx
        pop     rbp
        ret
        // xchg    ax, ax
        .byte   0x66,0x90
L2600:
        cmp     ebp, 0x3
        je      L2610
L2605:
        xor     eax, eax
        pop     rbx
        pop     rbp
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2610:
        cmp     r9d, 0x50
        je      L2605
        cmp     BYTE PTR [r11+r10*1+0x920], 0x0
        jne     L25f6
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L2628:
        add     r10, 0x1
        cmp     r10d, 0x50
        je      L2605
        cmp     BYTE PTR [r11+r10*1+0x920], 0x0
        je      L2628
        jmp     L25f6
        // nop
        .byte   0x90

// mld_rej_uniform_c.constprop.0 (0x2640)

L2640:
        mov     r8, rdi
        mov     r9d, ecx
        cmp     esi, 0xff
        ja      L26a8
        mov     r10d, 0x3
        sub     r10d, edx
        jmp     L266f
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L2660:
        mov     esi, ecx
L2662:
        add     rdx, 0x3
        lea     eax, [r10+rdx*1]
        cmp     r9d, eax
        jb      L26a8
L266f:
        movzx   eax, BYTE PTR [rdx+0x1]
        movzx   ecx, BYTE PTR [rdx+0x2]
        movzx   edi, BYTE PTR [rdx]
        shl     eax, 0x8
        shl     ecx, 0x10
        or      eax, ecx
        or      eax, edi
        and     eax, 0x7fffff
        cmp     eax, 0x7fe000
        ja      L2662
        mov     edi, esi
        lea     ecx, [rsi+0x1]
        mov     DWORD PTR [r8+rdi*4], eax
        cmp     esi, 0xff
        jne     L2660
        mov     eax, ecx
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L26a8:
        mov     ecx, esi
        mov     eax, ecx
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_poly_reduce (0x26b0)

L26b0:
        movdqa  xmm2, XMMWORD PTR [rip+Lc4c0]
        lea     rax, [rdi+0x400]
        // nop
        .byte   0x90
L26c0:
        movdqa  xmm1, XMMWORD PTR [rdi]
        add     rdi, 0x10
        paddd   xmm1, xmm2
        psrad   xmm1, 0x17
        movdqa  xmm0, xmm1
        pslld   xmm0, 0xa
        psubd   xmm0, xmm1
        pslld   xmm0, 0xd
        paddd   xmm0, xmm1
        movdqa  xmm1, XMMWORD PTR [rdi-0x10]
        psubd   xmm1, xmm0
        movaps  XMMWORD PTR [rdi-0x10], xmm1
        cmp     rax, rdi
        jne     L26c0
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa_poly_caddq (0x2700)

L2700:
        lea     rsi, [rdi+0x400]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L2710:
        movsxd  rax, DWORD PTR [rdi]
        mov     rcx, rax
        sar     rax, 0x1f
        lea     edx, [rcx+0x7fe001]
        add     rdi, 0x4
        xor     edx, ecx
        and     eax, edx
        xor     eax, ecx
        mov     DWORD PTR [rdi-0x4], eax
        cmp     rdi, rsi
        jne     L2710
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_poly_add (0x2740)

L2740:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2748:
        movdqa  xmm0, XMMWORD PTR [rdi+rax*1]
        paddd   xmm0, XMMWORD PTR [rsi+rax*1]
        movaps  XMMWORD PTR [rdi+rax*1], xmm0
        add     rax, 0x10
        cmp     rax, 0x400
        jne     L2748
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_poly_sub (0x2770)

L2770:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2778:
        movdqa  xmm0, XMMWORD PTR [rdi+rax*1]
        psubd   xmm0, XMMWORD PTR [rsi+rax*1]
        movaps  XMMWORD PTR [rdi+rax*1], xmm0
        add     rax, 0x10
        cmp     rax, 0x400
        jne     L2778
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_poly_shiftl (0x27a0)

L27a0:
        lea     rax, [rdi+0x400]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L27b0:
        movdqa  xmm0, XMMWORD PTR [rdi]
        add     rdi, 0x10
        pslld   xmm0, 0xd
        movaps  XMMWORD PTR [rdi-0x10], xmm0
        cmp     rdi, rax
        jne     L27b0
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_poly_ntt (0x27d0)

L27d0:
        push    r15
        xor     ecx, ecx
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        mov     edi, 0x64f7
        push    rbp
        lea     r14, [r12+0x4]
        lea     rbp, [rip+Lc0c0]
        mov     r13, r12
        push    rbx
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L27f8:
        lea     r8d, [rcx+0x1]
        mov     esi, 0x1
        mov     edx, 0x100
        xor     eax, eax
        shl     esi, cl
        mov     ecx, r8d
        mov     ebx, r8d
        shr     edx, cl
        lea     r9d, [rdx+rdx*1]
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L2820:
        add     esi, 0x1
        cmp     eax, edx
        jae     L289a
        mov     ecx, edx
        mov     r10d, eax
        sub     ecx, eax
        lea     r8, [r13+r10*4+0x0]
        sub     ecx, 0x1
        add     rcx, r10
        lea     r12, [r14+rcx*4]
        mov     ecx, edx
        sub     rcx, r10
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2848:
        movsxd  r10, DWORD PTR [r8+rcx*4]
        imul    r10, rdi
        mov     QWORD PTR [rsp-0x8], r10
        imul    r10d, DWORD PTR [rsp-0x8], 0x3802001
        movsxd  r10, r10d
        mov     r11, r10
        mov     r15, r10
        shl     r11, 0xa
        sub     r15, r11
        mov     r11, r15
        shl     r11, 0xd
        sub     r11, r10
        mov     r10, QWORD PTR [rsp-0x8]
        add     r11, r10
        mov     r10d, DWORD PTR [r8]
        sar     r11, 0x20
        sub     r10d, r11d
        mov     DWORD PTR [r8+rcx*4], r10d
        add     DWORD PTR [r8], r11d
        add     r8, 0x4
        cmp     r12, r8
        jne     L2848
L289a:
        add     eax, r9d
        add     edx, r9d
        cmp     eax, 0xff
        ja      L28b8
        mov     ecx, esi
        movsxd  rdi, DWORD PTR [rbp+rcx*4+0x0]
        jmp     L2820
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L28b8:
        cmp     ebx, 0x8
        je      L28d2
        mov     ecx, ebx
        mov     eax, 0x1
        shl     eax, cl
        mov     ecx, ebx
        movsxd  rdi, DWORD PTR [rbp+rax*4+0x0]
        jmp     L27f8
L28d2:
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_poly_invntt_tomont (0x28e0)

L28e0:
        push    r15
        mov     rax, rdi
        mov     ecx, 0x8
        push    r14
        push    r13
        lea     r13, [rip+Lc0c0]
        push    r12
        push    rbp
        lea     rbp, [rdi+0x4]
        push    rbx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L2900:
        mov     esi, 0x100
        mov     edi, 0x1
        xor     edx, edx
        mov     r15d, ecx
        shr     esi, cl
        shl     edi, cl
        sub     edi, 0x1
        lea     r8d, [rsi+rsi*1]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2920:
        mov     ecx, edi
        sub     edi, 0x1
        mov     ecx, DWORD PTR [r13+rcx*4+0x0]
        neg     ecx
        cmp     edx, esi
        jae     L29bd
        mov     r9d, esi
        mov     r10d, edx
        movsxd  rcx, ecx
        lea     r11, [rax+r9*4]
        mov     r9d, esi
        lea     rbx, [rax+r10*4]
        sub     r9d, edx
        sub     r9d, 0x1
        add     r9, r10
        lea     r14, [rbp+r9*4+0x0]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L2960:
        mov     r9d, DWORD PTR [rbx]
        mov     r10d, DWORD PTR [r11]
        add     rbx, 0x4
        add     r11, 0x4
        add     r10d, r9d
        mov     DWORD PTR [rbx-0x4], r10d
        sub     r9d, DWORD PTR [r11-0x4]
        movsxd  r9, r9d
        imul    r9, rcx
        mov     QWORD PTR [rsp-0x8], r9
        imul    r10d, DWORD PTR [rsp-0x8], 0x3802001
        movsxd  r10, r10d
        mov     r9, r10
        mov     r12, r10
        shl     r9, 0xa
        sub     r12, r9
        mov     r9, r12
        shl     r9, 0xd
        sub     r9, r10
        mov     r10, QWORD PTR [rsp-0x8]
        add     r9, r10
        sar     r9, 0x20
        mov     DWORD PTR [r11-0x4], r9d
        cmp     r14, rbx
        jne     L2960
L29bd:
        add     edx, r8d
        add     esi, r8d
        cmp     edx, 0xff
        jbe     L2920
        mov     ecx, r15d
        sub     ecx, 0x1
        jne     L2900
        lea     r8, [rax+0x400]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L29e8:
        movsxd  rsi, DWORD PTR [rax]
        add     rax, 0x4
        imul    rsi, rsi, 0xa3fa
        imul    ecx, esi, 0x3802001
        movsxd  rcx, ecx
        mov     rdi, rcx
        mov     rdx, rcx
        shl     rdi, 0xa
        sub     rdx, rdi
        shl     rdx, 0xd
        sub     rdx, rcx
        add     rdx, rsi
        sar     rdx, 0x20
        mov     DWORD PTR [rax-0x4], edx
        cmp     r8, rax
        jne     L29e8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_poly_pointwise_montgomery (0x2a30)

L2a30:
        mov     r8, rdi
        xor     edx, edx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L2a38:
        movsxd  rax, DWORD PTR [rsi+rdx*1]
        movsxd  rdi, DWORD PTR [r8+rdx*1]
        imul    rdi, rax
        imul    ecx, edi, 0x3802001
        movsxd  rcx, ecx
        mov     r9, rcx
        mov     rax, rcx
        shl     r9, 0xa
        sub     rax, r9
        shl     rax, 0xd
        sub     rax, rcx
        add     rax, rdi
        sar     rax, 0x20
        mov     DWORD PTR [r8+rdx*1], eax
        add     rdx, 0x4
        cmp     rdx, 0x400
        jne     L2a38
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa_poly_power2round (0x2a80)

L2a80:
        movdqa  xmm4, XMMWORD PTR [rip+Lc4d0]
        movdqa  xmm3, XMMWORD PTR [rip+Lc4e0]
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2a98:
        movdqa  xmm0, XMMWORD PTR [rdx+rax*1]
        movdqa  xmm1, xmm0
        paddd   xmm1, xmm4
        movdqa  xmm2, xmm1
        pand    xmm1, xmm3
        psrad   xmm2, 0xd
        psubd   xmm0, xmm1
        movaps  XMMWORD PTR [rdi+rax*1], xmm2
        movaps  XMMWORD PTR [rsi+rax*1], xmm0
        add     rax, 0x10
        cmp     rax, 0x400
        jne     L2a98
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa_poly_uniform (0x2ad0)

L2ad0:
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdi
        push    r13
        push    r12
        push    rbx
        mov     rbx, rsi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x440
        lea     r13, [rsp+0x10]
        lea     r12, [rsp+0xe0]
        mov     rdi, r13
        call    L1040
        mov     edx, 0x22
        mov     rsi, rbx
        mov     rdi, r13
        call    L1080
        mov     rdi, r13
        call    L1110
        mov     rdx, r13
        mov     esi, 0x348
        mov     rdi, r12
        call    L1160
        xor     esi, esi
        mov     ecx, 0x348
        mov     rdx, r12
        mov     rdi, r14
        call    L2640
        cmp     eax, 0xff
        ja      L2b73
        mov     ebx, eax
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L2b48:
        mov     rdx, r13
        mov     esi, 0xa8
        mov     rdi, r12
        call    L1160
        mov     esi, ebx
        mov     ecx, 0xa8
        mov     rdx, r12
        mov     rdi, r14
        call    L2640
        mov     ebx, eax
        cmp     eax, 0xff
        jbe     L2b48
L2b73:
        mov     rdi, r13
        call    L1200
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x69
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_poly_uniform_4x (0x2ba0)

L2ba0:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        push    rbx
        mov     rbx, r8
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x10e0
        lea     r15, [rsp+0x40]
        mov     QWORD PTR [rsp], rdi
        lea     r12, [rsp+0x6c0]
        mov     rdi, r15
        mov     QWORD PTR [rsp+0x20], rsi
        lea     r14, [rsp+0x360]
        mov     QWORD PTR [rsp+0x18], rdx
        mov     QWORD PTR [rsp+0x10], rcx
        mov     QWORD PTR [rsp+0x8], r15
        call    L1700
        lea     rdx, [rbx+0x40]
        mov     rsi, rbx
        mov     rdi, r15
        lea     rcx, [rbx+0x80]
        lea     r8, [rbx+0xc0]
        mov     rbx, r15
        mov     r9d, 0x22
        call    L1600
        mov     r9, rbx
        mov     rsi, r12
        mov     rdi, r14
        lea     rax, [rsp+0xa20]
        mov     r8d, 0x5
        mov     QWORD PTR [rsp+0x38], r12
        lea     r15, [rsp+0xd80]
        mov     rdx, rax
        mov     rcx, r15
        mov     rbx, rax
        mov     QWORD PTR [rsp+0x30], rax
        call    L1660
        xor     esi, esi
        mov     rdi, r13
        mov     ecx, 0x348
        mov     rdx, r14
        call    L2640
        mov     rdi, QWORD PTR [rsp+0x20]
        mov     rdx, r12
        xor     esi, esi
        mov     ecx, 0x348
        mov     r13d, eax
        call    L2640
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     rdx, rbx
        xor     esi, esi
        mov     ecx, 0x348
        mov     r12d, eax
        call    L2640
        mov     rdi, QWORD PTR [rsp+0x10]
        xor     esi, esi
        mov     rdx, r15
        mov     ecx, 0x348
        mov     ebx, eax
        call    L2640
        cmp     r12d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r13d, 0xff
        jmp     L2d58
        // nop
        .byte   0x90
L2cc0:
        mov     r9, QWORD PTR [rsp+0x8]
        mov     rdx, QWORD PTR [rsp+0x30]
        mov     rcx, r15
        mov     rdi, r14
        mov     rsi, QWORD PTR [rsp+0x38]
        mov     r8d, 0x1
        mov     DWORD PTR [rsp+0x2c], r10d
        call    L1660
        mov     rdi, QWORD PTR [rsp]
        mov     esi, r13d
        mov     rdx, r14
        mov     ecx, 0xa8
        call    L2640
        mov     rdx, QWORD PTR [rsp+0x38]
        mov     rdi, QWORD PTR [rsp+0x20]
        mov     esi, r12d
        mov     ecx, 0xa8
        mov     r13d, eax
        call    L2640
        mov     rdx, QWORD PTR [rsp+0x30]
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     esi, ebx
        mov     ecx, 0xa8
        mov     r12d, eax
        call    L2640
        mov     esi, DWORD PTR [rsp+0x2c]
        mov     rdi, QWORD PTR [rsp+0x10]
        mov     rdx, r15
        mov     ecx, 0xa8
        mov     ebx, eax
        call    L2640
        cmp     r13d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r12d, 0xff
L2d58:
        setbe   dl
        or      eax, edx
        cmp     ebx, 0xff
        setbe   dl
        or      al, dl
        jne     L2cc0
        cmp     r10d, 0xff
        jbe     L2cc0
        mov     rdi, QWORD PTR [rsp+0x8]
        call    L1710
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x1b0
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_polyt1_pack (0x2db0)

L2db0:
        lea     rcx, [rsi+0x400]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L2dc0:
        mov     eax, DWORD PTR [rsi]
        add     rsi, 0x10
        add     rdi, 0x5
        mov     BYTE PTR [rdi-0x5], al
        mov     eax, DWORD PTR [rsi-0xc]
        shl     eax, 0x2
        or      al, BYTE PTR [rsi-0xf]
        mov     BYTE PTR [rdi-0x4], al
        mov     eax, DWORD PTR [rsi-0xc]
        mov     edx, DWORD PTR [rsi-0x8]
        sar     eax, 0x6
        shl     edx, 0x4
        or      eax, edx
        mov     BYTE PTR [rdi-0x3], al
        mov     eax, DWORD PTR [rsi-0x8]
        mov     edx, DWORD PTR [rsi-0x4]
        sar     eax, 0x4
        shl     edx, 0x6
        or      eax, edx
        mov     BYTE PTR [rdi-0x2], al
        mov     eax, DWORD PTR [rsi-0x4]
        sar     eax, 0x2
        mov     BYTE PTR [rdi-0x1], al
        cmp     rsi, rcx
        jne     L2dc0
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa_polyt1_unpack (0x2e10)

L2e10:
        mov     rax, rsi
        mov     rcx, rdi
        lea     rsi, [rsi+0x140]
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L2e20:
        movzx   edx, BYTE PTR [rax+0x1]
        movzx   edi, BYTE PTR [rax]
        add     rax, 0x5
        add     rcx, 0x10
        shl     edx, 0x8
        or      edx, edi
        and     edx, 0x3ff
        mov     DWORD PTR [rcx-0x10], edx
        movzx   edx, BYTE PTR [rax-0x4]
        movzx   edi, BYTE PTR [rax-0x3]
        shr     dl, 0x2
        shl     edi, 0x6
        movzx   edx, dl
        or      edx, edi
        and     edx, 0x3ff
        mov     DWORD PTR [rcx-0xc], edx
        movzx   edx, BYTE PTR [rax-0x3]
        movzx   edi, BYTE PTR [rax-0x2]
        shr     dl, 0x4
        shl     edi, 0x4
        movzx   edx, dl
        or      edx, edi
        and     edx, 0x3ff
        mov     DWORD PTR [rcx-0x8], edx
        movzx   edx, BYTE PTR [rax-0x2]
        movzx   edi, BYTE PTR [rax-0x1]
        shr     dl, 0x6
        movzx   edx, dl
        shl     edi, 0x2
        or      edx, edi
        mov     DWORD PTR [rcx-0x4], edx
        cmp     rsi, rax
        jne     L2e20
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_polyt0_pack (0x2ea0)

L2ea0:
        push    r15
        lea     rax, [rsi+0x400]
        mov     rdx, rsi
        mov     ecx, 0x1000
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        mov     rbx, rdi
        mov     QWORD PTR [rsp-0x8], rax
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L2ec8:
        mov     r13d, ecx
        mov     r9d, ecx
        sub     r13d, DWORD PTR [rdx]
        sub     r9d, DWORD PTR [rdx+0x4]
        mov     r11d, r13d
        mov     r8d, r9d
        mov     r10d, ecx
        sub     r10d, DWORD PTR [rdx+0x8]
        shr     r11d, 0x8
        shl     r8d, 0x5
        mov     r14d, r9d
        mov     eax, ecx
        or      r8d, r11d
        sub     eax, DWORD PTR [rdx+0xc]
        lea     r11d, [r10*4+0x0]
        mov     edi, ecx
        shr     r9d, 0xb
        sub     edi, DWORD PTR [rdx+0x10]
        shr     r10d, 0x6
        mov     r15d, eax
        or      r9d, r11d
        mov     r11d, eax
        shr     eax, 0x9
        mov     r12d, ecx
        shl     r11d, 0x7
        shr     r15d, 1
        sub     r12d, DWORD PTR [rdx+0x14]
        mov     esi, ecx
        or      r10d, r11d
        mov     r11d, edi
        movzx   r15d, r15b
        shr     r14d, 0x3
        shl     r11d, 0x4
        sub     esi, DWORD PTR [rdx+0x18]
        mov     ebp, ecx
        sub     ebp, DWORD PTR [rdx+0x1c]
        or      r11d, eax
        mov     eax, edi
        shr     eax, 0x4
        movzx   r11d, r11b
        movzx   eax, al
        shl     rax, 0x8
        or      rax, r11
        movzx   r11d, r10b
        shl     rax, 0x8
        or      rax, r15
        shl     rax, 0x8
        mov     r10, rax
        movzx   eax, r9b
        or      r10, r11
        shl     r10, 0x8
        mov     r9, r10
        or      r9, rax
        movzx   eax, r14b
        mov     r14, r9
        mov     r9d, esi
        shl     r14, 0x8
        or      r14, rax
        movzx   eax, r8b
        shl     r14, 0x8
        shr     edi, 0xc
        add     rdx, 0x20
        add     rbx, 0xd
        mov     r8, r14
        shr     r9d, 0x2
        or      r8, rax
        movzx   eax, r13b
        shl     r8, 0x8
        mov     r13, r8
        mov     r8d, esi
        shr     esi, 0xa
        or      r13, rax
        lea     eax, [r12+r12*1]
        shl     r8d, 0x6
        or      eax, edi
        lea     edi, [rbp*8+0x0]
        shr     r12d, 0x7
        mov     QWORD PTR [rbx-0xd], r13
        or      edi, esi
        movzx   esi, r9b
        or      r8d, r12d
        movzx   eax, al
        movzx   edi, dil
        shr     ebp, 0x5
        shl     edi, 0x8
        mov     BYTE PTR [rbx-0x1], bpl
        or      edi, esi
        movzx   esi, r8b
        shl     edi, 0x8
        or      edi, esi
        shl     edi, 0x8
        or      edi, eax
        mov     DWORD PTR [rbx-0x5], edi
        cmp     QWORD PTR [rsp-0x8], rdx
        jne     L2ec8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_polyt0_unpack (0x3020)

L3020:
        push    r13
        mov     rdx, rsi
        mov     rax, rdi
        push    r12
        lea     r12, [rsi+0x1a0]
        push    rbp
        push    rbx
        mov     ebx, 0x1000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L3040:
        movzx   ecx, BYTE PTR [rdx]
        mov     DWORD PTR [rax], ecx
        movzx   r11d, BYTE PTR [rdx+0x1]
        shl     r11d, 0x8
        or      r11d, ecx
        and     r11d, 0x1fff
        mov     DWORD PTR [rax], r11d
        movzx   esi, BYTE PTR [rdx+0x1]
        shr     sil, 0x5
        movzx   esi, sil
        mov     DWORD PTR [rax+0x4], esi
        movzx   ecx, BYTE PTR [rdx+0x2]
        shl     ecx, 0x3
        or      ecx, esi
        mov     DWORD PTR [rax+0x4], ecx
        movzx   r10d, BYTE PTR [rdx+0x3]
        shl     r10d, 0xb
        or      r10d, ecx
        and     r10d, 0x1fff
        mov     DWORD PTR [rax+0x4], r10d
        movzx   ecx, BYTE PTR [rdx+0x3]
        shr     cl, 0x2
        movzx   ecx, cl
        mov     DWORD PTR [rax+0x8], ecx
        movzx   r9d, BYTE PTR [rdx+0x4]
        shl     r9d, 0x6
        or      r9d, ecx
        and     r9d, 0x1fff
        mov     DWORD PTR [rax+0x8], r9d
        movzx   esi, BYTE PTR [rdx+0x4]
        shr     sil, 0x7
        movzx   esi, sil
        mov     DWORD PTR [rax+0xc], esi
        movzx   ecx, BYTE PTR [rdx+0x5]
        add     ecx, ecx
        or      ecx, esi
        mov     DWORD PTR [rax+0xc], ecx
        movzx   r8d, BYTE PTR [rdx+0x6]
        shl     r8d, 0x9
        or      r8d, ecx
        and     r8d, 0x1fff
        mov     DWORD PTR [rax+0xc], r8d
        movzx   esi, BYTE PTR [rdx+0x6]
        shr     sil, 0x4
        movzx   esi, sil
        mov     DWORD PTR [rax+0x10], esi
        movzx   ecx, BYTE PTR [rdx+0x7]
        shl     ecx, 0x4
        or      ecx, esi
        mov     DWORD PTR [rax+0x10], ecx
        movzx   edi, BYTE PTR [rdx+0x8]
        shl     edi, 0xc
        or      edi, ecx
        and     edi, 0x1fff
        mov     DWORD PTR [rax+0x10], edi
        movzx   ecx, BYTE PTR [rdx+0x8]
        shr     cl, 1
        movzx   ecx, cl
        mov     DWORD PTR [rax+0x14], ecx
        movzx   esi, BYTE PTR [rdx+0x9]
        shl     esi, 0x7
        or      esi, ecx
        and     esi, 0x1fff
        mov     DWORD PTR [rax+0x14], esi
        movzx   ecx, BYTE PTR [rdx+0x9]
        shr     cl, 0x6
        movzx   ecx, cl
        mov     DWORD PTR [rax+0x18], ecx
        movzx   ebp, BYTE PTR [rdx+0xa]
        shl     ebp, 0x2
        or      ebp, ecx
        mov     DWORD PTR [rax+0x18], ebp
        movzx   ecx, BYTE PTR [rdx+0xb]
        shl     ecx, 0xa
        add     rdx, 0xd
        add     rax, 0x20
        or      ecx, ebp
        and     ecx, 0x1fff
        mov     DWORD PTR [rax-0x8], ecx
        movzx   ebp, BYTE PTR [rdx-0x2]
        shr     bpl, 0x3
        movzx   ebp, bpl
        mov     DWORD PTR [rax-0x4], ebp
        movzx   r13d, BYTE PTR [rdx-0x1]
        shl     r13d, 0x5
        or      ebp, r13d
        mov     r13d, ebx
        sub     r13d, r11d
        mov     r11d, ebx
        sub     r11d, r10d
        mov     r10d, ebx
        mov     DWORD PTR [rax-0x20], r13d
        sub     r10d, r9d
        mov     r9d, ebx
        mov     DWORD PTR [rax-0x1c], r11d
        sub     r9d, r8d
        mov     r8d, ebx
        mov     DWORD PTR [rax-0x18], r10d
        sub     r8d, edi
        mov     edi, ebx
        mov     DWORD PTR [rax-0x14], r9d
        sub     edi, esi
        mov     esi, ebx
        mov     DWORD PTR [rax-0x10], r8d
        sub     esi, ecx
        mov     ecx, ebx
        mov     DWORD PTR [rax-0xc], edi
        sub     ecx, ebp
        mov     DWORD PTR [rax-0x8], esi
        mov     DWORD PTR [rax-0x4], ecx
        cmp     r12, rdx
        jne     L3040
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_poly_chknorm (0x31e0)

L31e0:
        mov     rcx, rdi
        lea     edi, [rsi-0x1]
        xor     esi, esi
        lea     r8, [rcx+0x400]
        // nop
        .byte   0x90
L31f0:
        movsxd  rax, DWORD PTR [rcx]
        mov     r9, rax
        sar     rax, 0x1f
        mov     edx, r9d
        neg     edx
        xor     edx, r9d
        and     edx, eax
        mov     eax, edi
        xor     edx, r9d
        sub     eax, edx
        cdqe
        sar     rax, 0x1f
        add     rcx, 0x4
        or      esi, eax
        cmp     rcx, r8
        jne     L31f0
        mov     eax, esi
        ret
        // nop
        .byte   0x90

// mldsa_polyw1_pack_88 (0x3220)

L3220:
        lea     rcx, [rdi+0xc0]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L3230:
        mov     eax, DWORD PTR [rsi]
        add     rdi, 0x3
        add     rsi, 0x10
        mov     BYTE PTR [rdi-0x3], al
        mov     edx, DWORD PTR [rsi-0xc]
        shl     edx, 0x6
        or      eax, edx
        mov     BYTE PTR [rdi-0x3], al
        mov     eax, DWORD PTR [rsi-0xc]
        sar     eax, 0x2
        mov     BYTE PTR [rdi-0x2], al
        mov     edx, DWORD PTR [rsi-0x8]
        shl     edx, 0x4
        or      eax, edx
        mov     BYTE PTR [rdi-0x2], al
        mov     eax, DWORD PTR [rsi-0x8]
        sar     eax, 0x4
        mov     BYTE PTR [rdi-0x1], al
        mov     edx, DWORD PTR [rsi-0x4]
        shl     edx, 0x2
        or      eax, edx
        mov     BYTE PTR [rdi-0x1], al
        cmp     rdi, rcx
        jne     L3230
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_polyw1_pack_32 (0x3280)

L3280:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L3288:
        mov     edx, DWORD PTR [rsi+rax*8+0x4]
        shl     edx, 0x4
        or      dl, BYTE PTR [rsi+rax*8]
        mov     BYTE PTR [rdi+rax*1], dl
        add     rax, 0x1
        cmp     rax, 0x80
        jne     L3288
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_polyw1_unpack_88 (0x32b0)

L32b0:
        mov     rcx, rdi
        mov     rdx, rsi
        lea     rdi, [rsi+0xc0]
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L32c0:
        movzx   eax, BYTE PTR [rdx]
        add     rdx, 0x3
        add     rcx, 0x10
        and     eax, 0x3f
        mov     DWORD PTR [rcx-0x10], eax
        movzx   eax, BYTE PTR [rdx-0x3]
        movzx   esi, BYTE PTR [rdx-0x2]
        shr     al, 0x6
        shl     esi, 0x2
        movzx   eax, al
        or      eax, esi
        and     eax, 0x3f
        mov     DWORD PTR [rcx-0xc], eax
        movzx   eax, BYTE PTR [rdx-0x2]
        movzx   esi, BYTE PTR [rdx-0x1]
        shr     al, 0x4
        movzx   eax, al
        shl     esi, 0x4
        or      eax, esi
        and     eax, 0x3f
        mov     DWORD PTR [rcx-0x8], eax
        movzx   eax, BYTE PTR [rdx-0x1]
        shr     al, 0x2
        movzx   eax, al
        mov     DWORD PTR [rcx-0x4], eax
        cmp     rdx, rdi
        jne     L32c0
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_polyw1_unpack_32 (0x3320)

L3320:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L3328:
        movzx   edx, BYTE PTR [rsi+rax*1]
        and     edx, 0xf
        mov     DWORD PTR [rdi+rax*8], edx
        movzx   edx, BYTE PTR [rsi+rax*1]
        shr     dl, 0x4
        movzx   edx, dl
        mov     DWORD PTR [rdi+rax*8+0x4], edx
        add     rax, 0x1
        cmp     rax, 0x80
        jne     L3328
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mld_rej_eta_c44.constprop.0 (0x3350)

L3350:
        mov     r8, rdi
        cmp     esi, 0xff
        ja      L33f6
        mov     r9d, 0x1
        mov     r10d, 0x2
        sub     r9d, edx
        // xchg    ax, ax
        .byte   0x66,0x90
L3370:
        movzx   eax, BYTE PTR [rdx]
        mov     ecx, eax
        shr     al, 0x4
        and     ecx, 0xf
        movzx   eax, al
        cmp     cl, 0xf
        je      L33a5
        movzx   ecx, cl
        imul    edi, ecx, 0xcd
        shr     edi, 0xa
        lea     r11d, [rdi+rdi*4]
        mov     edi, esi
        add     esi, 0x1
        sub     ecx, r11d
        mov     r11d, r10d
        sub     r11d, ecx
        mov     DWORD PTR [r8+rdi*4], r11d
L33a5:
        cmp     esi, 0xff
        setbe   cl
        cmp     eax, 0xe
        ja      L33de
        test    cl, cl
        je      L33de
        imul    ecx, eax, 0xcd
        lea     edi, [rsi+0x1]
        mov     esi, esi
        shr     ecx, 0xa
        lea     ecx, [rcx+rcx*4]
        sub     eax, ecx
        mov     ecx, r10d
        sub     ecx, eax
        cmp     edi, 0xff
        mov     DWORD PTR [r8+rsi*4], ecx
        setbe   cl
        mov     esi, edi
L33de:
        lea     eax, [r9+rdx*1]
        cmp     eax, 0x87
        setbe   al
        add     rdx, 0x1
        test    al, cl
        jne     L3370
L33f6:
        mov     eax, esi
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa44_poly_decompose (0x3400)

L3400:
        xor     ecx, ecx
        mov     r9d, 0x2b
        mov     r8d, 0x3ff000
        // xchg    ax, ax
        .byte   0x66,0x90
L3410:
        mov     r10d, DWORD PTR [rsi+rcx*1]
        mov     eax, r9d
        lea     edx, [r10+0x7f]
        sar     edx, 0x7
        imul    edx, edx, 0x2c0b
        add     edx, 0x800000
        sar     edx, 0x18
        sub     eax, edx
        cdqe
        sar     rax, 0x1f
        not     eax
        and     eax, edx
        mov     edx, r8d
        mov     DWORD PTR [rdi+rcx*1], eax
        imul    eax, eax, 0xfffd1800
        add     eax, r10d
        sub     edx, eax
        movsxd  rdx, edx
        sar     rdx, 0x1f
        lea     r10d, [rax-0x7fe001]
        xor     r10d, eax
        and     edx, r10d
        xor     eax, edx
        mov     DWORD PTR [rsi+rcx*1], eax
        add     rcx, 0x4
        cmp     rcx, 0x400
        jne     L3410
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_poly_use_hint (0x3480)

L3480:
        mov     r8, rsi
        push    rbx
        xor     ecx, ecx
        mov     esi, 0x2b
        mov     r9d, 0x3ff000
        xor     r10d, r10d
        jmp     L34bc
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L34a0:
        lea     edx, [rax+0x1]
        cmp     eax, 0x2b
        mov     eax, edx
        cmove   eax, r10d
L34ac:
        mov     DWORD PTR [rdi+rcx*1], eax
        add     rcx, 0x4
        cmp     rcx, 0x400
        je      L3529
L34bc:
        mov     r11d, DWORD PTR [rdi+rcx*1]
        mov     eax, esi
        lea     edx, [r11+0x7f]
        sar     edx, 0x7
        imul    edx, edx, 0x2c0b
        add     edx, 0x800000
        sar     edx, 0x18
        sub     eax, edx
        cdqe
        sar     rax, 0x1f
        not     eax
        and     eax, edx
        imul    edx, eax, 0xfffd1800
        add     r11d, edx
        mov     edx, r9d
        sub     edx, r11d
        movsxd  rdx, edx
        sar     rdx, 0x1f
        mov     ebx, DWORD PTR [r8+rcx*1]
        test    ebx, ebx
        je      L34ac
        lea     ebx, [r11-0x7fe001]
        xor     ebx, r11d
        and     edx, ebx
        xor     edx, r11d
        jg      L34a0
        sub     eax, 0x1
        cmovb   eax, esi
        mov     DWORD PTR [rdi+rcx*1], eax
        add     rcx, 0x4
        cmp     rcx, 0x400
        jne     L34bc
L3529:
        pop     rbx
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa44_poly_uniform_eta_4x (0x3530)

L3530:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x780
        movdqu  xmm3, XMMWORD PTR [r8]
        movdqu  xmm2, XMMWORD PTR [r8+0x10]
        movdqu  xmm1, XMMWORD PTR [r8+0x20]
        movdqu  xmm0, XMMWORD PTR [r8+0x30]
        lea     r14, [rsp+0x60]
        mov     QWORD PTR [rsp+0x38], rsi
        movaps  XMMWORD PTR [rsp+0x60], xmm3
        lea     rbx, [rsp+0xc0]
        lea     r13, [rsp+0x120]
        movaps  XMMWORD PTR [rsp+0x70], xmm2
        lea     r12, [rsp+0x180]
        movaps  XMMWORD PTR [rsp+0x80], xmm1
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0xc0], xmm3
        movaps  XMMWORD PTR [rsp+0xd0], xmm2
        movaps  XMMWORD PTR [rsp+0xe0], xmm1
        movaps  XMMWORD PTR [rsp+0xf0], xmm0
        movaps  XMMWORD PTR [rsp+0x120], xmm3
        movaps  XMMWORD PTR [rsp+0x130], xmm2
        movaps  XMMWORD PTR [rsp+0x140], xmm1
        movaps  XMMWORD PTR [rsp+0x150], xmm0
        movaps  XMMWORD PTR [rsp+0x180], xmm3
        movaps  XMMWORD PTR [rsp+0x190], xmm2
        movaps  XMMWORD PTR [rsp+0x1a0], xmm1
        movaps  XMMWORD PTR [rsp+0x1b0], xmm0
        mov     QWORD PTR [rsp+0x30], rdx
        mov     QWORD PTR [rsp+0x28], rcx
        mov     QWORD PTR [rsp+0x40], rdi
        mov     QWORD PTR [rsp+0x18], r14
        mov     BYTE PTR [rsp+0xa0], r9b
        mov     eax, DWORD PTR [rbp+0x10]
        mov     BYTE PTR [rsp+0x100], al
        mov     eax, DWORD PTR [rbp+0x18]
        mov     BYTE PTR [rsp+0x160], al
        mov     eax, DWORD PTR [rbp+0x20]
        mov     BYTE PTR [rsp+0xa1], 0x0
        mov     BYTE PTR [rsp+0x1c0], al
        lea     rax, [rsp+0x460]
        mov     r15, rax
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x20], rax
        mov     BYTE PTR [rsp+0x101], 0x0
        mov     BYTE PTR [rsp+0x161], 0x0
        mov     BYTE PTR [rsp+0x1c1], 0x0
        call    L1850
        mov     r8, r12
        mov     rcx, r13
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r15
        mov     r9d, 0x42
        mov     rbx, r15
        call    L1750
        lea     r14, [rsp+0x1e0]
        lea     r11, [rsp+0x320]
        mov     r9, rbx
        mov     rdx, r11
        mov     r8d, 0x1
        mov     rdi, r14
        mov     rbx, r11
        lea     rax, [rsp+0x3c0]
        lea     r15, [rsp+0x280]
        mov     QWORD PTR [rsp+0x50], r11
        mov     rcx, rax
        mov     rsi, r15
        mov     QWORD PTR [rsp+0x58], rax
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x40]
        xor     esi, esi
        mov     rdx, r14
        call    L3350
        mov     rdi, QWORD PTR [rsp+0x38]
        xor     esi, esi
        mov     rdx, r15
        mov     r13d, eax
        call    L3350
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     rdx, rbx
        xor     esi, esi
        mov     r12d, eax
        call    L3350
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     rdi, QWORD PTR [rsp+0x28]
        xor     esi, esi
        mov     ebx, eax
        call    L3350
        cmp     r12d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r13d, 0xff
        jmp     L37b5
L3730:
        mov     r9, QWORD PTR [rsp+0x20]
        mov     rcx, QWORD PTR [rsp+0x58]
        mov     rsi, r15
        mov     rdi, r14
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     r8d, 0x1
        mov     DWORD PTR [rsp+0x4c], r10d
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x40]
        mov     esi, r13d
        mov     rdx, r14
        call    L3350
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     esi, r12d
        mov     rdx, r15
        mov     r13d, eax
        call    L3350
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     esi, ebx
        mov     r12d, eax
        call    L3350
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     esi, DWORD PTR [rsp+0x4c]
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     ebx, eax
        call    L3350
        cmp     r13d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r12d, 0xff
L37b5:
        setbe   dl
        or      eax, edx
        cmp     ebx, 0xff
        setbe   dl
        or      al, dl
        jne     L3730
        cmp     r10d, 0xff
        jbe     L3730
        mov     rdi, QWORD PTR [rsp+0x20]
        call    L1860
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x50
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     ecx, 0x30
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x18]
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret

// mldsa44_poly_challenge (0x3810)

L3810:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        mov     r14, rdi
        push    r13
        push    r12
        push    rbx
        mov     rbx, rsi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x180
        lea     r12, [rsp+0xb0]
        mov     rdi, r12
        call    L1240
        mov     rsi, rbx
        mov     edx, 0x20
        mov     rdi, r12
        call    L1280
        lea     rbx, [rsp+0x20]
        mov     rdi, r12
        call    L1310
        mov     esi, 0x88
        mov     rdi, rbx
        mov     rdx, r12
        call    L1360
        mov     rax, rbx
        lea     rdi, [rsp+0x28]
        xor     ecx, ecx
        xor     esi, esi
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L3880:
        movzx   edx, BYTE PTR [rax]
        add     rax, 0x1
        shl     rdx, cl
        add     ecx, 0x8
        or      rsi, rdx
        cmp     rax, rdi
        jne     L3880
        lea     rdi, [r14+0x8]
        mov     rcx, r14
        xor     eax, eax
        mov     QWORD PTR [rsp+0x18], rsi
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [r14], 0x0
        mov     r15d, 0xd9
        mov     r13d, 0x1
        mov     QWORD PTR [r14+0x3f8], 0x0
        sub     rcx, rdi
        add     ecx, 0x400
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x8
        jmp     L38ef
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L38e0:
        mov     eax, ecx
L38e2:
        movzx   edx, BYTE PTR [rsp+rax*1+0x20]
        lea     ecx, [rax+0x1]
        cmp     r15d, edx
        jae     L391b
L38ef:
        cmp     ecx, 0x88
        jne     L38e0
        mov     rdx, r12
        mov     esi, 0x88
        mov     rdi, rbx
        call    L1360
        movzx   edx, BYTE PTR [rsp+0x20]
        mov     eax, 0x1
        cmp     r15d, edx
        jb      L38e2
        mov     ecx, 0x1
L391b:
        mov     eax, DWORD PTR [r14+rdx*4]
        mov     edi, r13d
        mov     DWORD PTR [r14+r15*4], eax
        mov     rax, QWORD PTR [rsp+0x18]
        add     r15, 0x1
        mov     rsi, rax
        shr     rax, 1
        and     esi, 0x1
        mov     QWORD PTR [rsp+0x18], rax
        add     rsi, rsi
        sub     edi, esi
        mov     DWORD PTR [r14+rdx*4], edi
        cmp     r15, 0x100
        jne     L38ef
        mov     rdi, r12
        call    L1400
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x11
        rep stos QWORD PTR es:[rdi], rax
        mov     QWORD PTR [rsp+0x18], 0x0
        lea     rax, [rsp+0x18]
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_polyeta_pack (0x3990)

L3990:
        push    r12
        mov     rax, rsi
        mov     r8, rdi
        lea     r9, [rsi+0x400]
        push    rbp
        mov     edx, 0x2
        push    rbx
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L39b0:
        mov     r11d, edx
        sub     r11b, BYTE PTR [rax+0x8]
        mov     r12d, edx
        sub     r12b, BYTE PTR [rax+0x4]
        mov     edi, r11d
        shl     r12d, 0x3
        mov     ebp, edx
        mov     esi, edx
        shl     edi, 0x6
        sub     bpl, BYTE PTR [rax+0xc]
        sub     sil, BYTE PTR [rax+0x10]
        mov     r10d, edx
        or      edi, r12d
        mov     r12d, edx
        sub     r12b, BYTE PTR [rax]
        sub     r10b, BYTE PTR [rax+0x14]
        or      edi, r12d
        mov     ebx, edx
        mov     ecx, edx
        sub     bl, BYTE PTR [rax+0x18]
        sub     cl, BYTE PTR [rax+0x1c]
        shl     esi, 0x4
        mov     BYTE PTR [r8], dil
        lea     edi, [rbp+rbp*1+0x0]
        or      esi, edi
        shr     r11b, 0x2
        mov     edi, r10d
        add     rax, 0x20
        shl     ebx, 0x2
        shl     ecx, 0x5
        or      esi, r11d
        add     r8, 0x3
        shl     edi, 0x7
        or      ecx, ebx
        shr     r10b, 1
        or      esi, edi
        or      ecx, r10d
        mov     BYTE PTR [r8-0x2], sil
        mov     BYTE PTR [r8-0x1], cl
        cmp     r9, rax
        jne     L39b0
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mldsa44_polyeta_unpack (0x3a40)

L3a40:
        push    r13
        mov     rax, rdi
        lea     r11, [rdi+0x400]
        mov     rdx, rsi
        push    r12
        mov     edi, 0x2
        push    rbp
        push    rbx
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L3a60:
        movzx   r10d, BYTE PTR [rdx]
        mov     r13d, edi
        add     rax, 0x20
        add     rdx, 0x3
        and     r10d, 0x7
        mov     DWORD PTR [rax-0x20], r10d
        movzx   r9d, BYTE PTR [rdx-0x3]
        sub     r13d, r10d
        mov     r10d, edi
        shr     r9b, 0x3
        and     r9d, 0x7
        mov     DWORD PTR [rax-0x1c], r9d
        movzx   esi, BYTE PTR [rdx-0x3]
        sub     r10d, r9d
        mov     r9d, edi
        movzx   ecx, BYTE PTR [rdx-0x2]
        shr     sil, 0x6
        shl     ecx, 0x2
        movzx   esi, sil
        or      esi, ecx
        and     esi, 0x7
        mov     DWORD PTR [rax-0x18], esi
        movzx   ebp, BYTE PTR [rdx-0x2]
        sub     r9d, esi
        mov     esi, edi
        shr     bpl, 1
        and     ebp, 0x7
        mov     DWORD PTR [rax-0x14], ebp
        movzx   ebx, BYTE PTR [rdx-0x2]
        sub     esi, ebp
        shr     bl, 0x4
        and     ebx, 0x7
        mov     DWORD PTR [rax-0x10], ebx
        movzx   ecx, BYTE PTR [rdx-0x2]
        movzx   r8d, BYTE PTR [rdx-0x1]
        shr     cl, 0x7
        add     r8d, r8d
        movzx   ecx, cl
        or      ecx, r8d
        and     ecx, 0x7
        mov     DWORD PTR [rax-0xc], ecx
        movzx   r8d, BYTE PTR [rdx-0x1]
        shr     r8b, 0x2
        and     r8d, 0x7
        mov     DWORD PTR [rax-0x8], r8d
        movzx   r12d, BYTE PTR [rdx-0x1]
        mov     DWORD PTR [rax-0x14], esi
        mov     esi, edi
        sub     esi, ebx
        shr     r12b, 0x5
        mov     DWORD PTR [rax-0x20], r13d
        mov     DWORD PTR [rax-0x10], esi
        mov     esi, edi
        movzx   r12d, r12b
        sub     esi, ecx
        mov     ecx, edi
        mov     DWORD PTR [rax-0x1c], r10d
        sub     ecx, r8d
        mov     DWORD PTR [rax-0x18], r9d
        mov     DWORD PTR [rax-0x8], ecx
        mov     ecx, edi
        sub     ecx, r12d
        mov     DWORD PTR [rax-0xc], esi
        mov     DWORD PTR [rax-0x4], ecx
        cmp     r11, rax
        jne     L3a60
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_polyz_pack (0x3b50)

L3b50:
        push    r13
        mov     rdx, rsi
        mov     rsi, rdi
        mov     edi, 0x20000
        push    r12
        lea     r8, [rdx+0x400]
        push    rbp
        push    rbx
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L3b70:
        mov     r9d, edi
        sub     r9d, DWORD PTR [rdx]
        mov     ebp, edi
        mov     eax, edi
        sub     ebp, DWORD PTR [rdx+0x4]
        sub     eax, DWORD PTR [rdx+0x8]
        mov     ebx, r9d
        mov     ecx, edi
        shr     ebx, 0x10
        sub     ecx, DWORD PTR [rdx+0xc]
        mov     r12d, eax
        mov     r10d, r9d
        shl     r12d, 0x4
        mov     r13d, ecx
        shr     r10d, 0x8
        movzx   r9d, r9b
        lea     r11d, [rbp*4+0x0]
        shl     r13d, 0x6
        movzx   r10d, r10b
        add     rdx, 0x10
        or      r11d, ebx
        mov     ebx, ebp
        shr     ebp, 0xe
        or      ebp, r12d
        mov     r12d, eax
        shr     eax, 0xc
        movzx   r11d, r11b
        shr     r12d, 0x4
        or      r13d, eax
        mov     eax, ecx
        movzx   ebp, bpl
        shr     eax, 0x2
        movzx   r13d, r13b
        movzx   r12d, r12b
        shr     ebx, 0x6
        movzx   eax, al
        movzx   ebx, bl
        shr     ecx, 0xa
        shl     rax, 0x8
        mov     BYTE PTR [rsi+0x8], cl
        or      rax, r13
        shl     rax, 0x8
        or      rax, r12
        shl     rax, 0x8
        or      rax, rbp
        shl     rax, 0x8
        or      rax, rbx
        shl     rax, 0x8
        or      rax, r11
        shl     rax, 0x8
        or      rax, r10
        shl     rax, 0x8
        or      rax, r9
        add     rsi, 0x9
        mov     QWORD PTR [rsi-0x9], rax
        cmp     r8, rdx
        jne     L3b70
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa44_polyz_unpack (0x3c40)

L3c40:
        mov     rdx, rsi
        mov     rax, rdi
        lea     r11, [rdi+0x400]
        mov     r10d, 0x20000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L3c58:
        movzx   esi, BYTE PTR [rdx]
        add     rax, 0x10
        add     rdx, 0x9
        mov     DWORD PTR [rax-0x10], esi
        movzx   ecx, BYTE PTR [rdx-0x8]
        shl     ecx, 0x8
        or      ecx, esi
        mov     DWORD PTR [rax-0x10], ecx
        movzx   edi, BYTE PTR [rdx-0x7]
        shl     edi, 0x10
        or      edi, ecx
        and     edi, 0x3ffff
        mov     DWORD PTR [rax-0x10], edi
        movzx   esi, BYTE PTR [rdx-0x7]
        shr     sil, 0x2
        movzx   esi, sil
        mov     DWORD PTR [rax-0xc], esi
        movzx   ecx, BYTE PTR [rdx-0x6]
        shl     ecx, 0x6
        or      ecx, esi
        mov     DWORD PTR [rax-0xc], ecx
        movzx   esi, BYTE PTR [rdx-0x5]
        shl     esi, 0xe
        or      esi, ecx
        and     esi, 0x3ffff
        mov     DWORD PTR [rax-0xc], esi
        movzx   ecx, BYTE PTR [rdx-0x5]
        shr     cl, 0x4
        movzx   ecx, cl
        mov     DWORD PTR [rax-0x8], ecx
        movzx   r8d, BYTE PTR [rdx-0x4]
        shl     r8d, 0x4
        or      r8d, ecx
        mov     DWORD PTR [rax-0x8], r8d
        movzx   ecx, BYTE PTR [rdx-0x3]
        shl     ecx, 0xc
        or      ecx, r8d
        and     ecx, 0x3ffff
        mov     DWORD PTR [rax-0x8], ecx
        movzx   r9d, BYTE PTR [rdx-0x3]
        shr     r9b, 0x6
        movzx   r9d, r9b
        mov     DWORD PTR [rax-0x4], r9d
        movzx   r8d, BYTE PTR [rdx-0x2]
        shl     r8d, 0x2
        or      r8d, r9d
        mov     DWORD PTR [rax-0x4], r8d
        movzx   r9d, BYTE PTR [rdx-0x1]
        shl     r9d, 0xa
        or      r8d, r9d
        mov     r9d, r10d
        sub     r9d, edi
        mov     edi, r10d
        sub     edi, esi
        mov     esi, r10d
        mov     DWORD PTR [rax-0x10], r9d
        sub     esi, ecx
        mov     ecx, r10d
        mov     DWORD PTR [rax-0xc], edi
        sub     ecx, r8d
        mov     DWORD PTR [rax-0x8], esi
        mov     DWORD PTR [rax-0x4], ecx
        cmp     rax, r11
        jne     L3c58
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa44_poly_uniform_gamma1_4x (0x3d40)

L3d40:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xfe0
        movdqu  xmm3, XMMWORD PTR [r8]
        movdqu  xmm2, XMMWORD PTR [r8+0x10]
        movdqu  xmm1, XMMWORD PTR [r8+0x20]
        movdqu  xmm0, XMMWORD PTR [r8+0x30]
        mov     QWORD PTR [rsp+0x30], rsi
        lea     r12, [rsp+0x1c0]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        lea     r13, [rsp+0xa0]
        lea     r14, [rsp+0x100]
        movaps  XMMWORD PTR [rsp+0x50], xmm2
        lea     r15, [rsp+0x160]
        lea     rbx, [rsp+0x40]
        movaps  XMMWORD PTR [rsp+0x60], xmm1
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0xa0], xmm3
        movaps  XMMWORD PTR [rsp+0xb0], xmm2
        movaps  XMMWORD PTR [rsp+0xc0], xmm1
        movaps  XMMWORD PTR [rsp+0xd0], xmm0
        movaps  XMMWORD PTR [rsp+0x100], xmm3
        movaps  XMMWORD PTR [rsp+0x110], xmm2
        movaps  XMMWORD PTR [rsp+0x120], xmm1
        movaps  XMMWORD PTR [rsp+0x130], xmm0
        movaps  XMMWORD PTR [rsp+0x160], xmm3
        movaps  XMMWORD PTR [rsp+0x170], xmm2
        movaps  XMMWORD PTR [rsp+0x180], xmm1
        movaps  XMMWORD PTR [rsp+0x190], xmm0
        mov     QWORD PTR [rsp+0x28], rdx
        mov     QWORD PTR [rsp+0x20], rcx
        mov     WORD PTR [rsp+0x80], r9w
        mov     QWORD PTR [rsp+0x38], rdi
        mov     eax, DWORD PTR [rbp+0x10]
        mov     rdi, r12
        mov     WORD PTR [rsp+0xe0], ax
        mov     eax, DWORD PTR [rbp+0x18]
        mov     WORD PTR [rsp+0x140], ax
        mov     eax, DWORD PTR [rbp+0x20]
        mov     WORD PTR [rsp+0x1a0], ax
        call    L1850
        mov     r8, r15
        mov     rcx, r14
        mov     rdx, r13
        mov     rsi, rbx
        mov     rdi, r12
        mov     r9d, 0x42
        call    L1750
        lea     r13, [rsp+0x4e0]
        lea     r11, [rsp+0x7a0]
        mov     r9, r12
        lea     r14, [rsp+0xd20]
        mov     rsi, r11
        mov     r8d, 0x5
        mov     rdi, r13
        lea     r15, [rsp+0xa60]
        mov     rcx, r14
        mov     QWORD PTR [rsp+0x18], r11
        mov     rdx, r15
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     rsi, r13
        call    L3c40
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, QWORD PTR [rsp+0x30]
        call    L3c40
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     rsi, r15
        call    L3c40
        mov     rdi, QWORD PTR [rsp+0x20]
        mov     rsi, r14
        call    L3c40
        mov     rdi, r12
        call    L1860
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x160
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x30
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_polyvecl_uniform_gamma1 (0x3f10)

L3f10:
        lea     eax, [rdx+0x3]
        sub     rsp, 0x10
        mov     r8, rsi
        movzx   r9d, dx
        movzx   eax, ax
        lea     r10, [rdi+0x800]
        lea     rcx, [rdi+0xc00]
        push    rax
        lea     eax, [rdx+0x2]
        lea     rsi, [rdi+0x400]
        movzx   eax, ax
        push    rax
        lea     eax, [rdx+0x1]
        mov     rdx, r10
        movzx   eax, ax
        push    rax
        call    L3d40
        add     rsp, 0x28
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa44_polyvecl_ntt (0x3f60)

L3f60:
        push    rbx
        mov     rbx, rdi
        call    L27d0
        lea     rdi, [rbx+0x400]
        call    L27d0
        lea     rdi, [rbx+0x800]
        call    L27d0
        lea     rdi, [rbx+0xc00]
        pop     rbx
        jmp     L27d0
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyvecl_pointwise_acc_montgomery (0x3f90)

L3f90:
        mov     r10, rdx
        mov     r8, rdi
        mov     r9, rsi
        xor     edx, edx
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L3fa0:
        mov     rax, rdx
        xor     esi, esi
        lea     rcx, [rdx+0x1000]
L3fac:
        movsxd  rdi, DWORD PTR [r9+rax*1]
        movsxd  r11, DWORD PTR [r10+rax*1]
        add     rax, 0x400
        imul    rdi, r11
        add     rsi, rdi
        cmp     rcx, rax
        jne     L3fac
        imul    ecx, esi, 0x3802001
        movsxd  rcx, ecx
        mov     rdi, rcx
        mov     rax, rcx
        shl     rdi, 0xa
        sub     rax, rdi
        shl     rax, 0xd
        sub     rax, rcx
        add     rax, rsi
        sar     rax, 0x20
        mov     DWORD PTR [r8+rdx*1], eax
        add     rdx, 0x4
        cmp     rdx, 0x400
        jne     L3fa0
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_polyvecl_chknorm (0x4000)

L4000:
        push    r13
        lea     r13, [rdi+0x1000]
        push    r12
        mov     r12d, esi
        push    rbp
        xor     ebp, ebp
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L4019:
        mov     rdi, rbx
        mov     esi, r12d
        add     rbx, 0x400
        call    L31e0
        or      ebp, eax
        cmp     rbx, r13
        jne     L4019
        add     rsp, 0x8
        mov     eax, ebp
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop
        .byte   0x90

// mldsa44_polyveck_caddq (0x4040)

L4040:
        push    rbx
        mov     rbx, rdi
        call    L2700
        lea     rdi, [rbx+0x400]
        call    L2700
        lea     rdi, [rbx+0x800]
        call    L2700
        lea     rdi, [rbx+0xc00]
        pop     rbx
        jmp     L2700
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyveck_ntt (0x4070)

L4070:
        push    rbx
        mov     rbx, rdi
        call    L27d0
        lea     rdi, [rbx+0x400]
        call    L27d0
        lea     rdi, [rbx+0x800]
        call    L27d0
        lea     rdi, [rbx+0xc00]
        pop     rbx
        jmp     L27d0
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyveck_invntt_tomont (0x40a0)

L40a0:
        push    rbx
        mov     rbx, rdi
        call    L28e0
        lea     rdi, [rbx+0x400]
        call    L28e0
        lea     rdi, [rbx+0x800]
        call    L28e0
        lea     rdi, [rbx+0xc00]
        pop     rbx
        jmp     L28e0
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyveck_unpack_eta_chknorm (0x40d0)

L40d0:
        push    r14
        lea     r14, [rdi+0x180]
        push    r13
        mov     r13d, esi
        push    r12
        xor     r12d, r12d
        push    rbp
        mov     rbp, rdx
        push    rbx
        mov     rbx, rdi
L40eb:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        call    L3a40
        mov     esi, r13d
        mov     rdi, rbp
        call    L31e0
        or      r12d, eax
        cmp     rbx, r14
        jne     L40eb
        pop     rbx
        mov     eax, r12d
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa44_polyveck_decompose_pack_w1 (0x4120)

L4120:
        push    r13
        lea     r13, [rdi+0x300]
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L413a:
        mov     rsi, rbp
        mov     rdi, r12
        add     rbp, 0x400
        call    L3400
        mov     rdi, rbx
        mov     rsi, r12
        add     rbx, 0xc0
        call    L3220
        cmp     rbx, r13
        jne     L413a
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyvecl_unpack_eta (0x4170)

L4170:
        push    r12
        lea     r12, [rsi+0x180]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
L4181:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        add     rbp, 0x400
        call    L3a40
        cmp     rbx, r12
        jne     L4181
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_polyvecl_unpack_z (0x41b0)

L41b0:
        push    r12
        lea     r12, [rsi+0x900]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
L41c1:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x240
        add     rbp, 0x400
        call    L3c40
        cmp     rbx, r12
        jne     L41c1
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mldsa44_polyveck_unpack_eta (0x41f0)

L41f0:
        push    r12
        lea     r12, [rsi+0x180]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
L4201:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        add     rbp, 0x400
        call    L3a40
        cmp     rbx, r12
        jne     L4201
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa44_polyvec_matrix_expand_eager (0x4230)

L4230:
        push    rbp
        mov     rbp, rsp
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x100
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm0, XMMWORD PTR [rsi+0x10]
        mov     r14, rsp
        lea     r12, [rsp+0x100]
        mov     rax, r14
L4260:
        movaps  XMMWORD PTR [rax], xmm1
        add     rax, 0x40
        movaps  XMMWORD PTR [rax-0x30], xmm0
        cmp     r12, rax
        jne     L4260
        xor     ebx, ebx
L4272:
        mov     rax, r14
        mov     edx, ebx
L4277:
        mov     ecx, edx
        add     rax, 0x40
        and     ecx, 0x3
        mov     BYTE PTR [rax-0x20], cl
        mov     ecx, edx
        add     edx, 0x1
        shr     ecx, 0x2
        mov     BYTE PTR [rax-0x1f], cl
        cmp     r12, rax
        jne     L4277
        lea     eax, [rbx+0x3]
        mov     edi, ebx
        mov     r8, r14
        shr     eax, 0x2
        shr     edi, 0x2
        shl     rax, 0xc
        shl     rdi, 0xc
        lea     rcx, [r13+rax*1+0xc00]
        lea     eax, [rbx+0x2]
        add     rdi, r13
        shr     eax, 0x2
        shl     rax, 0xc
        lea     rdx, [r13+rax*1+0x800]
        lea     eax, [rbx+0x1]
        add     ebx, 0x4
        shr     eax, 0x2
        shl     rax, 0xc
        lea     rsi, [r13+rax*1+0x400]
        call    L2ba0
        cmp     ebx, 0x10
        jne     L4272
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // nop
        .byte   0x90

// mldsa44_polyvec_matrix_pointwise_montgomery_row_eager (0x4300)

L4300:
        mov     ecx, ecx
        shl     rcx, 0xc
        add     rsi, rcx
        jmp     L3f90
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager (0x4310)

L4310:
        push    r14
        mov     r14, rdi
        push    r13
        mov     r13, rsi
        mov     rsi, rdx
        push    r12
        mov     r12, rcx
        mov     ecx, 0x200
        push    rbp
        mov     rdi, r12
        mov     rbp, r14
        push    rbx
        xor     ebx, ebx
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rdi, r12
        call    L3f60
L433c:
        mov     ecx, ebx
        mov     rdi, rbp
        mov     rdx, r12
        mov     rsi, r13
        call    L4300
        add     ebx, 0x1
        add     rbp, 0x400
        cmp     ebx, 0x4
        jne     L433c
        pop     rbx
        mov     rdi, r14
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        jmp     L40a0
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mld_compute_pack_t0_t144 (0x4370)

L4370:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rcx
        push    r14
        mov     r14, rdi
        push    r13
        mov     r13, rsi
        mov     rsi, r8
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x4820
        lea     rax, [rsp+0x820]
        mov     QWORD PTR [rsp+0x8], rdx
        lea     rbx, [rsp+0x20]
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x10], rax
        lea     r12, [rsp+0x420]
        call    L4230
        xor     eax, eax
L43bd:
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     rsi, QWORD PTR [rsp+0x10]
        mov     ecx, eax
        mov     rdi, rbx
        mov     DWORD PTR [rsp+0x1c], eax
        call    L4300
        mov     rdi, rbx
        call    L28e0
        mov     rsi, r15
        mov     rdi, r12
        add     r15, 0x60
        call    L3a40
        mov     rsi, r12
        mov     rdi, rbx
        call    L2740
        mov     rdi, rbx
        call    L26b0
        mov     rdi, rbx
        call    L2700
        mov     rdx, rbx
        mov     rsi, rbx
        mov     rdi, r12
        call    L2a80
        mov     rdi, r14
        mov     rsi, r12
        add     r14, 0x140
        call    L2db0
        mov     rdi, r13
        mov     rsi, rbx
        add     r13, 0x1a0
        call    L2ea0
        mov     eax, DWORD PTR [rsp+0x1c]
        add     eax, 0x1
        cmp     eax, 0x4
        jne     L43bd
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rbx, QWORD PTR [rsp+0x10]
        mov     edx, 0x4000
        xor     esi, esi
        mov     rdi, rbx
        call    L1030
        lea     rsp, [rbp-0x28]
        xor     eax, eax
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mld_H44 (0x4490)

L4490:
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rsi
        push    rbp
        mov     rbp, rdi
        push    rbx
        sub     rsp, 0xe8
        lea     rbx, [rsp+0x10]
        mov     QWORD PTR [rsp+0x8], r8
        mov     rdi, rbx
        call    L1240
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, rbx
        call    L1280
        test    r15, r15
        jne     L4520
        cmp     QWORD PTR [rsp+0x128], 0x0
        jne     L453b
L44e0:
        mov     rdi, rbx
        call    L1310
        mov     rdx, rbx
        mov     rsi, r12
        mov     rdi, rbp
        call    L1360
        mov     rdi, rbx
        call    L1400
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        add     rsp, 0xe8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L4520:
        mov     rsi, QWORD PTR [rsp+0x8]
        mov     rdx, r15
        mov     rdi, rbx
        call    L1280
        cmp     QWORD PTR [rsp+0x128], 0x0
        je      L44e0
L453b:
        mov     rdx, QWORD PTR [rsp+0x128]
        mov     rsi, QWORD PTR [rsp+0x120]
        mov     rdi, rbx
        call    L1280
        jmp     L44e0
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_keypair_internal (0x4560)

L4560:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        mov     ecx, 0x22
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r15, [rbp-0xc30]
        lea     r14, [rbp-0x830]
        push    r13
        mov     r13, rdi
        push    r12
        lea     r12, [rbp-0x1030]
        push    r10
        push    rbx
        mov     rbx, rsi
        lea     rsi, [rbp-0x1130]
        sub     rsp, 0x1140
        movdqu  xmm1, XMMWORD PTR [rdx]
        movzx   eax, WORD PTR [rip+Lc600]
        mov     QWORD PTR [rbp-0x1150], rsi
        movdqu  xmm2, XMMWORD PTR [rdx+0x10]
        mov     rdx, rsi
        mov     esi, 0x80
        mov     WORD PTR [rbp-0x1110], ax
        lea     rax, [rbp-0x10b0]
        mov     rdi, rax
        movaps  XMMWORD PTR [rbp-0x1130], xmm1
        movaps  XMMWORD PTR [rbp-0x1120], xmm2
        mov     QWORD PTR [rbp-0x1138], rax
        call    L1440
        sub     rsp, 0x8
        mov     rsi, r15
        lea     rdx, [rbx+0x200]
        mov     QWORD PTR [rbp-0x1148], rdx
        lea     rax, [rbp-0x430]
        mov     rdx, r14
        mov     rdi, r12
        push    0x7
        mov     rcx, rax
        lea     r8, [rbp-0x1090]
        mov     r9d, 0x4
        push    0x6
        push    0x5
        mov     QWORD PTR [rbp-0x1140], rax
        mov     QWORD PTR [rbp-0x1158], r8
        call    L3530
        mov     rdi, QWORD PTR [rbp-0x1148]
        add     rsp, 0x20
        mov     rsi, r12
        call    L3990
        mov     rsi, r15
        lea     rdi, [rbx+0x260]
        call    L3990
        mov     rsi, r14
        lea     rdi, [rbx+0x2c0]
        call    L3990
        mov     rsi, QWORD PTR [rbp-0x1140]
        lea     rdi, [rbx+0x320]
        call    L3990
        sub     rsp, 0x8
        mov     rdx, r14
        xor     r9d, r9d
        push    0x3
        mov     r8, QWORD PTR [rbp-0x1158]
        mov     rsi, r15
        mov     rdi, r12
        push    0x2
        mov     rcx, QWORD PTR [rbp-0x1140]
        push    0x1
        call    L3530
        add     rsp, 0x20
        lea     rdi, [rbx+0x80]
        mov     rsi, r12
        call    L3990
        mov     rsi, r15
        lea     rdi, [rbx+0xe0]
        lea     r15, [rbp-0x10f0]
        call    L3990
        mov     rsi, r14
        lea     rdi, [rbx+0x140]
        call    L3990
        mov     rsi, QWORD PTR [rbp-0x1140]
        lea     rdi, [rbx+0x1a0]
        call    L3990
        mov     rdi, r12
        call    L3f60
        movdqa  xmm3, XMMWORD PTR [rbp-0x10b0]
        lea     rdi, [r13+0x20]
        movdqa  xmm4, XMMWORD PTR [rbp-0x10a0]
        mov     r8, QWORD PTR [rbp-0x1138]
        mov     rcx, QWORD PTR [rbp-0x1148]
        lea     rsi, [rbx+0x380]
        mov     rdx, r12
        movups  XMMWORD PTR [r13+0x0], xmm3
        movups  XMMWORD PTR [r13+0x10], xmm4
        call    L4370
        mov     r14d, eax
        test    eax, eax
        jne     L476f
        mov     ecx, 0x520
        mov     rdx, r13
        mov     esi, 0x40
        mov     rdi, r15
        call    L1440
        mov     rsi, QWORD PTR [rbp-0x1138]
        mov     rdx, r15
        mov     rdi, rbx
        lea     rcx, [rbp-0x1050]
        call    L2310
L476f:
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x200
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x10f0], xmm0
        movaps  XMMWORD PTR [rbp-0x10e0], xmm0
        movaps  XMMWORD PTR [rbp-0x10d0], xmm0
        movaps  XMMWORD PTR [rbp-0x10c0], xmm0
        xor     edx, edx
        movaps  XMMWORD PTR [rbp-0x1130], xmm0
        mov     WORD PTR [rbp-0x1110], dx
        mov     rdx, QWORD PTR [rbp-0x1150]
        movaps  XMMWORD PTR [rbp-0x1120], xmm0
        mov     rdi, QWORD PTR [rbp-0x1138]
        mov     ecx, 0x10
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1138]
        test    r14d, r14d
        jne     L47f0
L47d5:
        lea     rsp, [rbp-0x30]
        mov     eax, r14d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L47f0:
        lea     rdi, [r13+0x8]
        mov     rcx, r13
        mov     QWORD PTR [r13+0x0], 0x0
        mov     QWORD PTR [r13+0x518], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x520
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x9f8], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xa00
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        jmp     L47d5
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa44_keypair (0x4850)

L4850:
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1020
        test    eax, eax
        jne     L48a8
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    L4560
L4889:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     rsp, [rbp-0x18]
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L48a8:
        mov     eax, 0xfffffffd
        jmp     L4889
        // nop
        .byte   0x90

// mldsa44_signature_internal (0x48b0)

L48b0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     rax, [rbp-0xa030]
        lea     r15, [rbp-0xabd0]
        push    r13
        lea     r13, [rbp-0xac10]
        push    r12
        mov     r12, rsi
        lea     rsi, [rbp-0xac30]
        push    r10
        push    rbx
        mov     rbx, r9
        lea     r9, [rbp-0x8030]
        sub     rsp, 0xacc8
        mov     QWORD PTR [rbp-0xac60], rcx
        lea     rcx, [rbp-0x9030]
        mov     r14d, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0xac88], rdi
        mov     rdi, rsi
        mov     QWORD PTR [rbp-0xac58], rdx
        mov     rdx, r15
        mov     QWORD PTR [rbp-0xac68], r8
        mov     r8, rax
        mov     QWORD PTR [rbp-0xacd8], rsi
        mov     rsi, r13
        mov     QWORD PTR [rbp-0xaca8], r9
        mov     QWORD PTR [rbp-0xac98], rax
        mov     QWORD PTR [rbp-0xacb0], rcx
        push    QWORD PTR [r10]
        call    L2360
        pop     rdi
        pop     r8
        test    r14d, r14d
        jne     L4e90
        lea     rax, [rbp-0xabb0]
        mov     r9, QWORD PTR [rbp-0xac68]
        mov     ecx, 0x40
        mov     rdx, r13
        mov     QWORD PTR [rbp-0xacc0], rax
        mov     r8, QWORD PTR [rbp-0xac60]
        mov     esi, 0x40
        mov     rdi, rax
        push    QWORD PTR [rbp-0xac58]
        push    r12
        call    L4490
        pop     rcx
        pop     rsi
L499a:
        mov     rdx, r15
        mov     r8, rbx
        mov     ecx, 0x20
        mov     esi, 0x40
        lea     rax, [rbp-0xab70]
        mov     r9d, 0x20
        lea     rbx, [rbp-0x6030]
        mov     QWORD PTR [rbp-0xacd0], rax
        mov     rdi, rax
        lea     r14, [rbp-0xa830]
        lea     r15, [rbp-0xa430]
        push    0x40
        mov     r12, r15
        push    QWORD PTR [rbp-0xacc0]
        call    L4490
        lea     rax, [rbp-0x4030]
        mov     rsi, QWORD PTR [rbp-0xacd8]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0xacc8], rax
        call    L4230
        pop     rax
        lea     rax, [rbp-0x7030]
        pop     rdx
        mov     QWORD PTR [rbp-0xac70], rax
        lea     rax, [rbp-0x5030]
        mov     QWORD PTR [rbp-0xac78], rax
        lea     rax, [rbp-0xab30]
        mov     QWORD PTR [rbp-0xac90], rax
        lea     rax, [rbp-0xac50]
        mov     DWORD PTR [rbp-0xac7c], 0x0
        mov     QWORD PTR [rbp-0xac58], rbx
        mov     QWORD PTR [rbp-0xaca0], rax
        mov     QWORD PTR [rbp-0xac60], r14
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L4a58:
        mov     r14, QWORD PTR [rbp-0xac70]
        mov     edx, DWORD PTR [rbp-0xac7c]
        mov     rsi, QWORD PTR [rbp-0xacd0]
        mov     rdi, r14
        call    L3f10
        mov     r13, QWORD PTR [rbp-0xac58]
        mov     rdx, r14
        mov     r14, QWORD PTR [rbp-0xac78]
        mov     rsi, QWORD PTR [rbp-0xacc8]
        mov     rcx, r13
        mov     rdi, r14
        call    L4310
        mov     rdi, r14
        call    L4040
        mov     rsi, r14
        mov     r14, QWORD PTR [rbp-0xac90]
        mov     rdx, r13
        mov     rdi, r14
        call    L4120
        mov     rdi, r15
        call    L1240
        mov     rsi, QWORD PTR [rbp-0xacc0]
        mov     rdi, r15
        mov     edx, 0x40
        call    L1280
        mov     rsi, r14
        mov     edx, 0x300
        mov     rdi, r15
        call    L1280
        mov     rdi, r15
        call    L1310
        mov     r14, QWORD PTR [rbp-0xaca0]
        mov     rdx, r15
        mov     esi, 0x20
        mov     rdi, r14
        call    L1360
        mov     rdi, r15
        call    L1400
        mov     rdi, r15
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rsi, r14
        mov     r14, QWORD PTR [rbp-0xac60]
        xor     r13d, r13d
        mov     rdi, r14
        call    L3810
        mov     rdi, r14
        call    L27d0
L4b31:
        mov     rax, QWORD PTR [rbp-0xac98]
        mov     r14, r13
        mov     rdi, r15
        mov     ecx, 0x80
        shl     r14, 0xa
        mov     DWORD PTR [rbp-0xac68], r13d
        mov     r15, r12
        lea     rsi, [rax+r14*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, QWORD PTR [rbp-0xac60]
        mov     rdi, r12
        call    L2a30
        mov     rdi, r12
        call    L28e0
        mov     rax, QWORD PTR [rbp-0xac70]
        mov     ecx, 0x80
        mov     rdi, QWORD PTR [rbp-0xac58]
        mov     QWORD PTR [rbp-0xac58], rbx
        lea     rsi, [rax+r14*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, rbx
        mov     rdi, r12
        call    L2740
        mov     rdi, r12
        call    L26b0
        mov     esi, 0x1ffb2
        mov     rdi, r12
        call    L31e0
        test    eax, eax
        jne     L4e85
        mov     edx, DWORD PTR [rbp-0xac68]
        mov     rdi, QWORD PTR [rbp-0xac88]
        mov     rsi, r12
        add     r13, 0x1
        call    L2540
        cmp     r13, 0x4
        jne     L4b31
        mov     QWORD PTR [rbp-0xac68], r12
        xor     r13d, r13d
        mov     QWORD PTR [rbp-0xacb8], r12
        mov     r12, QWORD PTR [rbp-0xac60]
L4bf3:
        mov     rax, QWORD PTR [rbp-0xaca8]
        mov     ecx, 0x80
        mov     rdi, rbx
        mov     r15, rbx
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, r12
        mov     rdi, rbx
        call    L2a30
        mov     rdi, rbx
        call    L28e0
        mov     rax, QWORD PTR [rbp-0xac78]
        mov     rsi, rbx
        lea     r14, [rax+r13*1]
        mov     rdi, r14
        call    L2770
        mov     rdi, r14
        call    L26b0
        mov     esi, 0x173b2
        mov     rdi, r14
        call    L31e0
        test    eax, eax
        jne     L4e70
        mov     rax, QWORD PTR [rbp-0xacb0]
        mov     ecx, 0x80
        mov     rdi, rbx
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, r12
        mov     rdi, rbx
        call    L2a30
        mov     rdi, rbx
        call    L28e0
        mov     rdi, rbx
        call    L26b0
        mov     esi, 0x17400
        mov     rdi, rbx
        call    L31e0
        test    eax, eax
        jne     L4e70
        mov     rsi, rbx
        mov     rdi, r14
        add     r13, 0x400
        call    L2740
        cmp     r13, 0x1000
        jne     L4bf3
        mov     r14, QWORD PTR [rbp-0xac88]
        mov     rsi, QWORD PTR [rbp-0xaca0]
        mov     QWORD PTR [rbp-0xac58], rbx
        mov     r15, QWORD PTR [rbp-0xac68]
        mov     r12, QWORD PTR [rbp-0xacb8]
        mov     rdi, r14
        call    L2430
        mov     rdx, QWORD PTR [rbp-0xac90]
        mov     rcx, rbx
        mov     rdi, r14
        mov     rsi, QWORD PTR [rbp-0xac78]
        call    L2450
        mov     r13d, eax
L4cfe:
        mov     rdi, r12
        xor     eax, eax
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xac60]
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xac60]
        mov     rdi, QWORD PTR [rbp-0xac78]
        mov     ecx, 0x200
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xac78]
        mov     rdi, QWORD PTR [rbp-0xac90]
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xac90]
        mov     ecx, 0x200
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xac70]
        mov     ecx, 0x200
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xac70]
        mov     rax, QWORD PTR [rbp-0xaca0]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rax], xmm0
        movaps  XMMWORD PTR [rax+0x10], xmm0
        test    r13d, r13d
        je      L4dde
        cmp     r13d, 0xffffffff
        jne     L4da9
        add     DWORD PTR [rbp-0xac7c], 0x4
        mov     eax, DWORD PTR [rbp-0xac7c]
        cmp     eax, 0xfff8
        jne     L4a58
        mov     r13d, 0xfffffffc
L4da9:
        mov     rdx, QWORD PTR [rbp-0xac88]
        xor     eax, eax
        lea     rdi, [rdx+0x8]
        mov     rcx, rdx
        mov     QWORD PTR [rdx], 0x0
        mov     QWORD PTR [rdx+0x96c], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x974
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L4dde:
        mov     rdi, QWORD PTR [rbp-0xaca8]
        xor     ebx, ebx
        mov     ecx, 0x200
        mov     rax, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xaca8]
        mov     rdi, QWORD PTR [rbp-0xacb0]
        mov     ecx, 0x200
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xacb0]
        mov     rdi, QWORD PTR [rbp-0xac98]
        mov     ecx, 0x200
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xac98]
        mov     r15, QWORD PTR [rbp-0xacc8]
        mov     edx, 0x4000
        xor     esi, esi
        mov     rdi, r15
        call    L1030
        mov     rdi, QWORD PTR [rbp-0xacd8]
        mov     rax, rbx
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0xacd8]
        lea     rsp, [rbp-0x30]
        mov     eax, r13d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L4e70:
        mov     QWORD PTR [rbp-0xac58], r15
        mov     r12, QWORD PTR [rbp-0xacb8]
        mov     r15, QWORD PTR [rbp-0xac68]
L4e85:
        mov     r13d, 0xffffffff
        jmp     L4cfe
L4e90:
        movdqu  xmm1, XMMWORD PTR [r12]
        movdqu  xmm2, XMMWORD PTR [r12+0x10]
        lea     rax, [rbp-0xabb0]
        movdqu  xmm3, XMMWORD PTR [r12+0x20]
        movdqu  xmm4, XMMWORD PTR [r12+0x30]
        mov     QWORD PTR [rbp-0xacc0], rax
        movaps  XMMWORD PTR [rbp-0xabb0], xmm1
        movaps  XMMWORD PTR [rbp-0xaba0], xmm2
        movaps  XMMWORD PTR [rbp-0xab90], xmm3
        movaps  XMMWORD PTR [rbp-0xab80], xmm4
        jmp     L499a
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa44_signature_extmu (0x4ee0)

L4ee0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdx
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x50]
        mov     rdi, rbx
        sub     rsp, 0x28
        call    L1020
        test    eax, eax
        jne     L4f60
        push    0x1
        xor     ecx, ecx
        mov     edx, 0x40
        mov     r9, rbx
        push    r14
        xor     r8d, r8d
        mov     rsi, r13
        mov     rdi, r12
        call    L48b0
        pop     rdx
        pop     rcx
L4f3a:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L4f60:
        mov     eax, 0xfffffffd
        jmp     L4f3a
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_verify_internal (0x4f70)

L4f70:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rdx
        push    r14
        lea     rax, [rbp-0x5030]
        mov     r14, rdi
        push    r13
        mov     r13, rax
        push    r12
        mov     r12, rsi
        lea     rsi, [rdi+0x20]
        push    r10
        push    rbx
        sub     rsp, 0x60a0
        movdqu  xmm3, XMMWORD PTR [rdi]
        movdqu  xmm4, XMMWORD PTR [rdi+0x10]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x60a8], rcx
        mov     ebx, DWORD PTR [r10]
        mov     QWORD PTR [rbp-0x60b8], r8
        mov     QWORD PTR [rbp-0x60b0], r9
        mov     QWORD PTR [rbp-0x60a0], rax
        movaps  XMMWORD PTR [rbp-0x6090], xmm3
        movaps  XMMWORD PTR [rbp-0x6080], xmm4
        call    L41b0
        mov     esi, 0x1ffb2
        mov     rdi, r13
        call    L4000
        test    eax, eax
        jne     L5462
        mov     r13d, eax
        test    ebx, ebx
        je      L5380
        movdqu  xmm5, XMMWORD PTR [r12]
        lea     rax, [rbp-0x4030]
        movdqu  xmm6, XMMWORD PTR [r12+0x10]
        lea     rbx, [rbp-0x5430]
        mov     QWORD PTR [rbp-0x6098], rax
        lea     rax, [rbp-0x6050]
        movdqu  xmm7, XMMWORD PTR [r12+0x20]
        movaps  XMMWORD PTR [rbp-0x6050], xmm5
        movdqu  xmm5, XMMWORD PTR [r12+0x30]
        mov     QWORD PTR [rbp-0x60c8], rax
        movaps  XMMWORD PTR [rbp-0x6040], xmm6
        movaps  XMMWORD PTR [rbp-0x6030], xmm7
        movaps  XMMWORD PTR [rbp-0x6020], xmm5
L5062:
        mov     rdi, QWORD PTR [rbp-0x60a0]
        lea     r12, [rbp-0x5830]
        call    L3f60
        mov     rsi, QWORD PTR [rbp-0x60b0]
        mov     rdi, QWORD PTR [rbp-0x6098]
        call    L4230
        lea     rax, [rbp-0x5c30]
        lea     rsi, [rbp-0x6090]
        mov     r15, rax
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x60a8], rax
        mov     QWORD PTR [rbp-0x60d0], rsi
        call    L3810
        mov     rdi, r15
        call    L27d0
        lea     rax, [rbp-0x5f30]
        mov     QWORD PTR [rbp-0x60b8], r14
        mov     QWORD PTR [rbp-0x60c0], rax
        mov     r15, rax
L50cf:
        mov     rdx, QWORD PTR [rbp-0x60a0]
        mov     rsi, QWORD PTR [rbp-0x6098]
        mov     ecx, r13d
        mov     rdi, r12
        call    L4300
        mov     rsi, QWORD PTR [rbp-0x60b0]
        mov     edx, r13d
        mov     rdi, rbx
        call    L2300
        mov     rdi, rbx
        call    L27a0
        mov     rdi, rbx
        call    L27d0
        mov     rsi, QWORD PTR [rbp-0x60a8]
        mov     rdi, rbx
        call    L2a30
        mov     rsi, rbx
        mov     rdi, r12
        call    L2770
        mov     rdi, r12
        call    L26b0
        mov     rdi, r12
        call    L28e0
        mov     rdi, r12
        call    L2700
        mov     rsi, QWORD PTR [rbp-0x60b8]
        mov     edx, r13d
        mov     rdi, rbx
        call    L2550
        mov     r14d, eax
        test    eax, eax
        jne     L5450
        mov     rsi, rbx
        mov     rdi, r12
        add     r13d, 0x1
        call    L3480
        mov     rdi, r15
        mov     rsi, r12
        add     r15, 0xc0
        call    L3220
        cmp     r13d, 0x4
        jne     L50cf
        lea     r13, [rbp-0x6000]
        lea     r15, [rbp-0x6070]
        mov     rdi, r13
        call    L1240
        mov     rsi, QWORD PTR [rbp-0x60c8]
        mov     rdi, r13
        mov     edx, 0x40
        call    L1280
        mov     rsi, QWORD PTR [rbp-0x60c0]
        mov     edx, 0x300
        mov     rdi, r13
        call    L1280
        mov     rdi, r13
        call    L1310
        mov     rdx, r13
        mov     esi, 0x20
        mov     rdi, r15
        call    L1360
        mov     rdi, r13
        call    L1400
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        movdqa  xmm1, XMMWORD PTR [rbp-0x6090]
        movdqa  xmm2, XMMWORD PTR [rbp-0x6080]
        pxor    xmm1, XMMWORD PTR [rbp-0x6070]
        pxor    xmm2, XMMWORD PTR [rbp-0x6060]
        movdqa  xmm0, xmm1
        pxor    xmm1, xmm2
        por     xmm0, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    edx, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     rax
        sar     rax, 0x20
        xor     eax, edx
        cmp     al, dl
        jne     L5457
L529f:
        xor     r13d, r13d
        mov     rdi, rbx
        mov     ecx, 0x80
        mov     rax, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     rbx, QWORD PTR [rbp-0x6098]
        mov     edx, 0x4000
        xor     esi, esi
        mov     rdi, rbx
        call    L1030
        mov     rdi, QWORD PTR [rbp-0x60a8]
        mov     rax, r13
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x60a8]
        mov     rdi, QWORD PTR [rbp-0x60a0]
        mov     ecx, 0x200
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x60a0]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x6070], xmm0
        movaps  XMMWORD PTR [rbp-0x6060], xmm0
        mov     rax, QWORD PTR [rbp-0x60d0]
        movaps  XMMWORD PTR [rbp-0x6090], xmm0
        movaps  XMMWORD PTR [rbp-0x6080], xmm0
        mov     rax, QWORD PTR [rbp-0x60c8]
        movaps  XMMWORD PTR [rbp-0x6050], xmm0
        movaps  XMMWORD PTR [rbp-0x6040], xmm0
        movaps  XMMWORD PTR [rbp-0x6030], xmm0
        movaps  XMMWORD PTR [rbp-0x6020], xmm0
        mov     rdi, QWORD PTR [rbp-0x60c0]
        mov     rax, r13
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x60c0]
        lea     rsp, [rbp-0x30]
        mov     eax, r14d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L5380:
        lea     rax, [rbp-0x4030]
        mov     rdi, rax
        mov     rbx, rax
        call    L1240
        mov     rsi, QWORD PTR [rbp-0x60b0]
        mov     edx, 0x520
        mov     rdi, rbx
        call    L1280
        mov     rdi, rbx
        mov     QWORD PTR [rbp-0x6098], rbx
        lea     rbx, [rbp-0x5430]
        call    L1310
        mov     rdx, QWORD PTR [rbp-0x6098]
        mov     esi, 0x40
        mov     rdi, rbx
        call    L1360
        mov     rdi, QWORD PTR [rbp-0x6098]
        call    L1400
        mov     rdi, QWORD PTR [rbp-0x6098]
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x6098]
        lea     rax, [rbp-0x6050]
        mov     r9, QWORD PTR [rbp-0x60b8]
        mov     ecx, 0x40
        mov     rdx, rbx
        mov     QWORD PTR [rbp-0x60c8], rax
        mov     r8, QWORD PTR [rbp-0x60a8]
        mov     esi, 0x40
        mov     rdi, rax
        push    r15
        push    r12
        call    L4490
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x5430], xmm0
        movaps  XMMWORD PTR [rbp-0x5420], xmm0
        movaps  XMMWORD PTR [rbp-0x5410], xmm0
        movaps  XMMWORD PTR [rbp-0x5400], xmm0
        pop     rax
        pop     rdx
        jmp     L5062
L5450:
        lea     r15, [rbp-0x6070]
L5457:
        mov     r14d, 0xfffffffa
        jmp     L529f
L5462:
        lea     rax, [rbp-0x4030]
        lea     rbx, [rbp-0x5430]
        mov     QWORD PTR [rbp-0x6098], rax
        lea     rax, [rbp-0x6050]
        lea     r12, [rbp-0x5830]
        mov     QWORD PTR [rbp-0x60c8], rax
        lea     rax, [rbp-0x6090]
        lea     r15, [rbp-0x6070]
        mov     QWORD PTR [rbp-0x60d0], rax
        lea     rax, [rbp-0x5c30]
        mov     QWORD PTR [rbp-0x60a8], rax
        lea     rax, [rbp-0x5f30]
        mov     QWORD PTR [rbp-0x60c0], rax
        jmp     L5457
        // nop
        .byte   0x90

// mldsa44_verify_extmu (0x54c0)

L54c0:
        sub     rsp, 0x10
        mov     r9, rdx
        xor     r8d, r8d
        xor     ecx, ecx
        push    0x1
        mov     edx, 0x40
        call    L4f70
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa44_prepare_domain_separation_prefix (0x54e0)

L54e0:
        xor     eax, eax
        cmp     r8, 0xff
        ja      L5550
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbp
        mov     rbp, r8
        sub     rsp, 0x18
        test    r9d, r9d
        jne     L5528
        mov     BYTE PTR [rdi], 0x0
        mov     BYTE PTR [r12+0x1], r8b
        test    r8, r8
        jne     L5608
L5512:
        lea     rax, [rbp+0x2]
L5516:
        add     rsp, 0x18
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L5528:
        cmp     r9d, 0xc
        ja      L55be
        mov     r13, rdx
        mov     eax, r9d
        lea     rdx, [rip+Lc500]
        mov     r14, rsi
        movsxd  rax, DWORD PTR [rdx+rax*4]
        add     rax, rdx
        jmp     rax
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L5550:
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
        cmp     r13, 0x20
        jne     L55be
L555e:
        mov     BYTE PTR [r12], 0x1
        mov     BYTE PTR [r12+0x1], bpl
        test    rbp, rbp
        jne     L5620
L5571:
        lea     rcx, [rip+Lc540]
        xor     eax, eax
        mov     rdx, rcx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L5580:
        cmp     r9d, DWORD PTR [rdx]
        je      L55e8
        add     eax, 0x1
        add     rdx, 0x10
        cmp     eax, 0xc
        jne     L5580
L5591:
        lea     rdi, [r12+rbp*1+0xd]
        mov     rdx, r13
        mov     rsi, r14
        call    L1010
        add     rsp, 0x18
        lea     rax, [r13+rbp*1+0xd]
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
        cmp     r13, 0x1c
        je      L555e
L55be:
        xor     eax, eax
        jmp     L5516
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x40
        je      L555e
        xor     eax, eax
        jmp     L5516
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x30
        je      L555e
        xor     eax, eax
        jmp     L5516
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L55e8:
        shl     rax, 0x4
        lea     rdx, [r12+rbp*1+0x2]
        lea     rax, [rcx+rax*1+0x4]
        mov     rcx, QWORD PTR [rax]
        mov     QWORD PTR [rdx], rcx
        mov     eax, DWORD PTR [rax+0x7]
        mov     DWORD PTR [rdx+0x7], eax
        jmp     L5591
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L5608:
        lea     rdi, [rdi+0x2]
        mov     rdx, r8
        mov     rsi, rcx
        call    L1010
        jmp     L5512
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L5620:
        lea     rdi, [r12+0x2]
        mov     rdx, rbp
        mov     rsi, rcx
        mov     DWORD PTR [rsp+0xc], r9d
        call    L1010
        mov     r9d, DWORD PTR [rsp+0xc]
        jmp     L5571
        // nop
        .byte   0x90

// mldsa44_signature (0x5640)

L5640:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        xor     r9d, r9d
        push    r14
        mov     r14, rdx
        xor     edx, edx
        push    r13
        push    r12
        lea     r12, [rbp-0x190]
        push    r10
        push    rbx
        mov     rbx, rdi
        mov     rdi, r12
        sub     rsp, 0x1a0
        mov     QWORD PTR [rbp-0x1b8], rsi
        xor     esi, esi
        call    L54e0
        test    rax, rax
        mov     QWORD PTR [rbp-0x1c0], rax
        jne     L5710
        mov     edx, 0xfffffff7
        lea     r13, [rbp-0x1b0]
L56a1:
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        xor     eax, eax
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x96c], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x974
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L56cf:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x1b0], xmm0
        movaps  XMMWORD PTR [rbp-0x1a0], xmm0
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x30]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L5710:
        lea     r13, [rbp-0x1b0]
        mov     esi, 0x20
        mov     rdi, r13
        call    L1020
        mov     edx, 0xfffffffd
        test    eax, eax
        jne     L56a1
        push    0x0
        mov     r8, QWORD PTR [rbp-0x1c0]
        mov     rcx, r12
        mov     rdx, r14
        push    r15
        mov     rsi, QWORD PTR [rbp-0x1b8]
        mov     r9, r13
        mov     rdi, rbx
        call    L48b0
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      L56cf
        jmp     L56a1
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_verify (0x5770)

L5770:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        xor     r9d, r9d
        push    r14
        mov     r14, rdx
        xor     edx, edx
        push    r13
        mov     r13, rsi
        xor     esi, esi
        push    r12
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x190]
        mov     rdi, rbx
        sub     rsp, 0x160
        call    L54e0
        test    rax, rax
        je      L5808
        sub     rsp, 0x8
        mov     rcx, rbx
        mov     rdx, r14
        mov     r8, rax
        push    0x0
        mov     r9, r15
        mov     rsi, r13
        mov     rdi, r12
        call    L4f70
        mov     edx, eax
        pop     rax
        pop     rcx
L57db:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x30]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L5808:
        mov     edx, 0xfffffff7
        jmp     L57db
        // nop
        .byte   0x90

// mldsa44_signature_pre_hash_internal (0x5810)

L5810:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r14
        push    r13
        mov     r13, r9
        push    r12
        lea     r12, [rbp-0x190]
        push    r10
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x168
        mov     r9d, DWORD PTR [r10+0x8]
        mov     r14, QWORD PTR [r10]
        test    r9d, r9d
        jne     L58a8
L584a:
        mov     edx, 0xfffffff7
L584f:
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        xor     eax, eax
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x96c], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x974
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L587d:
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x28]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L58a8:
        mov     rdi, r12
        call    L54e0
        test    rax, rax
        je      L584a
        push    0x0
        xor     ecx, ecx
        mov     rdx, rax
        mov     r9, r13
        push    r14
        xor     r8d, r8d
        mov     rsi, r12
        mov     rdi, rbx
        call    L48b0
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      L587d
        jmp     L584f
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_signature_pre_hash_shake256 (0x58e0)

L58e0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rcx
        mov     rcx, rdx
        mov     rdx, rsi
        push    r12
        mov     esi, 0x40
        push    r10
        push    rbx
        lea     rbx, [rbp-0x70]
        sub     rsp, 0x60
        mov     r12, QWORD PTR [r10]
        mov     QWORD PTR [rbp-0x78], rdi
        mov     rdi, rbx
        call    L1440
        push    0xc
        mov     rdi, QWORD PTR [rbp-0x78]
        mov     r9, r15
        push    r12
        mov     r8, r14
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        call    L5810
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x70], xmm0
        movaps  XMMWORD PTR [rbp-0x60], xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        pop     rdx
        pop     rcx
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret

// mldsa44_verify_pre_hash_internal (0x5970)

L5970:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, r9
        push    r12
        push    r10
        push    rbx
        sub     rsp, 0x170
        mov     r9d, DWORD PTR [r10]
        test    r9d, r9d
        je      L5a00
        lea     rbx, [rbp-0x190]
        mov     r12, rdi
        mov     rdi, rbx
        call    L54e0
        mov     rdx, rax
        test    rax, rax
        je      L5a07
        sub     rsp, 0x8
        xor     ecx, ecx
        mov     r9, r13
        xor     r8d, r8d
        push    0x0
        mov     rsi, rbx
        mov     rdi, r12
        call    L4f70
        mov     edx, eax
        pop     rax
        pop     rcx
L59d1:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x20]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L5a00:
        lea     rbx, [rbp-0x190]
L5a07:
        mov     edx, 0xfffffff7
        jmp     L59d1
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_verify_pre_hash_shake256 (0x5a10)

L5a10:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rcx
        mov     rcx, rdx
        mov     rdx, rsi
        push    r12
        mov     esi, 0x40
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x70]
        mov     rdi, rbx
        sub     rsp, 0x40
        call    L1440
        sub     rsp, 0x8
        mov     r9, r15
        mov     r8, r14
        push    0xc
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        mov     rdi, r12
        call    L5970
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x70], xmm0
        movaps  XMMWORD PTR [rbp-0x60], xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        pop     rdx
        pop     rcx
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa44_pk_from_sk (0x5aa0)

L5aa0:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbx
        mov     rbx, rsi
        sub     rsi, 0xffffffffffffff80
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x1b80
        movdqu  xmm3, XMMWORD PTR [rsi-0x80]
        movdqu  xmm4, XMMWORD PTR [rsi-0x70]
        movdqu  xmm5, XMMWORD PTR [rsi-0x60]
        movdqu  xmm6, XMMWORD PTR [rsi-0x50]
        lea     r14, [rsp+0xb80]
        lea     r15, [rsp+0x100]
        movdqu  xmm7, XMMWORD PTR [rsi-0x40]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        movdqu  xmm3, XMMWORD PTR [rsi-0x30]
        mov     rdi, r14
        movaps  XMMWORD PTR [rsp+0x50], xmm4
        movdqu  xmm4, XMMWORD PTR [rsi-0x20]
        movaps  XMMWORD PTR [rsp+0x60], xmm5
        movdqu  xmm5, XMMWORD PTR [rsi-0x10]
        movaps  XMMWORD PTR [rsp+0x70], xmm6
        movaps  XMMWORD PTR [rsp+0x80], xmm7
        movaps  XMMWORD PTR [rsp+0x90], xmm3
        movaps  XMMWORD PTR [rsp+0xa0], xmm4
        movaps  XMMWORD PTR [rsp+0xb0], xmm5
        call    L4170
        mov     esi, 0x3
        mov     rdi, r14
        call    L4000
        lea     rcx, [rbx+0x200]
        mov     rdx, r15
        mov     esi, 0x3
        mov     rdi, rcx
        mov     QWORD PTR [rsp+0x38], rcx
        mov     r13d, eax
        call    L40d0
        mov     rdi, r14
        mov     DWORD PTR [rsp+0x2c], eax
        call    L3f60
        movdqa  xmm6, XMMWORD PTR [rsp+0x40]
        movdqa  xmm7, XMMWORD PTR [rsp+0x50]
        lea     r9, [rsp+0x500]
        mov     rcx, QWORD PTR [rsp+0x38]
        lea     r8, [rsp+0x40]
        mov     rsi, r9
        mov     rdx, r14
        movups  XMMWORD PTR [r12], xmm6
        lea     rdi, [r12+0x20]
        movups  XMMWORD PTR [r12+0x10], xmm7
        mov     QWORD PTR [rsp+0x30], r8
        mov     QWORD PTR [rsp+0x38], r9
        call    L4370
        mov     r9, QWORD PTR [rsp+0x38]
        mov     r8, QWORD PTR [rsp+0x30]
        test    eax, eax
        mov     r11d, eax
        je      L5ca0
        lea     rbx, [rsp+0xc0]
        lea     rdx, [rsp+0x80]
L5bd6:
        lea     rdi, [r12+0x8]
        mov     rcx, r12
        xor     eax, eax
        mov     QWORD PTR [r12], 0x0
        mov     QWORD PTR [r12+0x518], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x520
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L5c07:
        xor     eax, eax
        mov     rdi, r9
        mov     ecx, 0xd0
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x200
        mov     rdi, r14
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        lea     rax, [rsp+0x60]
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0xc0], xmm0
        movaps  XMMWORD PTR [rsp+0xd0], xmm0
        movaps  XMMWORD PTR [rsp+0xe0], xmm0
        movaps  XMMWORD PTR [rsp+0xf0], xmm0
        movaps  XMMWORD PTR [rsp+0x80], xmm0
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0xa0], xmm0
        movaps  XMMWORD PTR [rsp+0xb0], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        lea     rsp, [rbp-0x28]
        mov     eax, r11d
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L5ca0:
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L5cb0:
        movdqu  xmm1, XMMWORD PTR [rbx+rax*1+0x380]
        pxor    xmm1, XMMWORD PTR [r9+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x680
        jne     L5cb0
        movdqa  xmm1, xmm2
        mov     QWORD PTR [rsp+0x18], r8
        psrldq  xmm1, 0x8
        mov     QWORD PTR [rsp+0x20], r9
        pxor    xmm2, xmm1
        mov     DWORD PTR [rsp+0x30], r11d
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    edx, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     rax
        sar     rax, 0x20
        xor     eax, edx
        lea     rbx, [rsp+0xc0]
        xor     eax, edx
        mov     ecx, 0x520
        mov     rdx, r12
        mov     esi, 0x40
        mov     rdi, rbx
        mov     BYTE PTR [rsp+0x38], al
        call    L1440
        pxor    xmm1, xmm1
        mov     r8, QWORD PTR [rsp+0x18]
        xor     eax, eax
        mov     r9, QWORD PTR [rsp+0x20]
        mov     r11d, DWORD PTR [rsp+0x30]
        movdqa  xmm0, xmm1
        lea     rdx, [rsp+0x80]
L5da2:
        movdqa  xmm2, XMMWORD PTR [rbx+rax*1]
        pxor    xmm2, XMMWORD PTR [rdx+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x40
        jne     L5da2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    esi, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    ecx, xmm0
        movzx   ecx, cl
        neg     rcx
        mov     rax, rcx
        sar     rax, 0x20
        xor     eax, esi
        or      r13b, BYTE PTR [rsp+0x2c]
        xor     eax, esi
        or      r13b, BYTE PTR [rsp+0x38]
        or      r13d, eax
        test    r13b, r13b
        je      L5c07
        mov     r11d, 0xfffffff9
        jmp     L5bd6

// mldsa65_unpack_pk_t1 (0x5e60)

L5e60:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x6
        lea     rsi, [rax+rsi*1+0x20]
        jmp     L2e10

// mldsa65_pack_sk_rho_key_tr (0x5e70)

L5e70:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rcx]
        movups  XMMWORD PTR [rdi+0x20], xmm2
        movdqu  xmm3, XMMWORD PTR [rcx+0x10]
        movups  XMMWORD PTR [rdi+0x30], xmm3
        movdqu  xmm4, XMMWORD PTR [rdx]
        movups  XMMWORD PTR [rdi+0x40], xmm4
        movdqu  xmm5, XMMWORD PTR [rdx+0x10]
        movups  XMMWORD PTR [rdi+0x50], xmm5
        movdqu  xmm6, XMMWORD PTR [rdx+0x20]
        movups  XMMWORD PTR [rdi+0x60], xmm6
        movdqu  xmm7, XMMWORD PTR [rdx+0x30]
        movups  XMMWORD PTR [rdi+0x70], xmm7
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_unpack_sk (0x5ec0)

L5ec0:
        push    r13
        mov     r13, rcx
        push    r12
        push    rbp
        mov     rbp, r8
        push    rbx
        mov     rbx, r9
        sub     rsp, 0x8
        mov     r12, QWORD PTR [rsp+0x30]
        movdqu  xmm0, XMMWORD PTR [r12]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [r12+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [r12+0x20]
        mov     rdi, r8
        movups  XMMWORD PTR [rdx], xmm2
        movdqu  xmm3, XMMWORD PTR [r12+0x30]
        movups  XMMWORD PTR [rdx+0x10], xmm3
        movdqu  xmm4, XMMWORD PTR [r12+0x40]
        movups  XMMWORD PTR [rsi], xmm4
        movdqu  xmm5, XMMWORD PTR [r12+0x50]
        movups  XMMWORD PTR [rsi+0x10], xmm5
        movdqu  xmm6, XMMWORD PTR [r12+0x60]
        movups  XMMWORD PTR [rsi+0x20], xmm6
        movdqu  xmm7, XMMWORD PTR [r12+0x70]
        movups  XMMWORD PTR [rsi+0x30], xmm7
        lea     rsi, [r12+0x80]
        call    L6ea0
        mov     rdi, rbp
        mov     rbp, r13
        call    L6c70
        lea     rsi, [r12+0x300]
        mov     rdi, rbx
        call    L6f20
        mov     rdi, rbx
        lea     rbx, [r12+0x600]
        add     r12, 0xfc0
        call    L6d90
        // xchg    ax, ax
        .byte   0x66,0x90
L5f70:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x1a0
        add     rbp, 0x400
        call    L3020
        cmp     rbx, r12
        jne     L5f70
        add     rsp, 0x8
        mov     rdi, r13
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        jmp     L6d90

// mldsa65_pack_sig_c (0x5fa0)

L5fa0:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rsi+0x20]
        movups  XMMWORD PTR [rdi+0x20], xmm2
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa65_pack_sig_h (0x5fc0)

L5fc0:
        push    r15
        lea     rax, [rdx+0x300]
        pxor    xmm0, xmm0
        lea     r15, [rdi+0xcb0]
        push    r14
        mov     r14, rsi
        push    r13
        mov     r13, rcx
        push    r12
        mov     r12, rdx
        push    rbp
        lea     rbp, [rdi+0xce7]
        push    rbx
        xor     ebx, ebx
        sub     rsp, 0x18
        movups  XMMWORD PTR [rdi+0xcb0], xmm0
        mov     QWORD PTR [rsp+0x8], rax
        movups  XMMWORD PTR [r15+0x20], xmm0
        movups  XMMWORD PTR [r15+0x10], xmm0
        movups  XMMWORD PTR [r15+0x2d], xmm0
L600d:
        mov     rsi, r12
        mov     rdi, r13
        call    L3320
        xor     eax, eax
        jmp     L6035
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L6020:
        mov     ecx, ebx
        add     ebx, 0x1
        mov     BYTE PTR [r15+rcx*1], al
L6029:
        add     rax, 0x1
        cmp     rax, 0x100
        je      L6071
L6035:
        mov     ecx, DWORD PTR [r14+rax*4]
        mov     edi, DWORD PTR [r13+rax*4+0x0]
        lea     esi, [rcx+0x3ff00]
        cmp     esi, 0x7fe00
        ja      L6058
        cmp     ecx, 0xfffc0100
        jne     L6029
        test    edi, edi
        je      L6029
L6058:
        cmp     ebx, 0x37
        jne     L6020
        mov     eax, 0xffffffff
L6062:
        add     rsp, 0x18
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
L6071:
        mov     rax, QWORD PTR [rsp+0x8]
        sub     r12, 0xffffffffffffff80
        mov     BYTE PTR [rbp+0x0], bl
        add     rbp, 0x1
        add     r14, 0x400
        cmp     r12, rax
        jne     L600d
        xor     eax, eax
        jmp     L6062
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_pack_sig_z (0x60a0)

L60a0:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x7
        lea     rdi, [rax+rdi*1+0x30]
        jmp     L6860

// mldsa65_sig_unpack_hints (0x60b0)

L60b0:
        push    rbp
        mov     r11, rsi
        mov     r8, rdi
        mov     ebp, edx
        push    rbx
        lea     rbx, [rsi+0xcb0]
        xor     esi, esi
        test    edx, edx
        je      L60d3
        lea     eax, [rdx+0x36]
        movzx   esi, BYTE PTR [r11+rax*1+0xcb0]
L60d3:
        lea     eax, [rbp+0x37]
        movzx   r9d, BYTE PTR [r11+rax*1+0xcb0]
        mov     r10, r9
        cmp     r9d, esi
        jb      L6156
        cmp     r9d, 0x37
        ja      L6156
        lea     rdi, [r8+0x8]
        mov     rcx, r8
        xor     eax, eax
        mov     QWORD PTR [r8], 0x0
        mov     QWORD PTR [r8+0x3f8], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x400
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        cmp     esi, r9d
        jae     L6160
        lea     edx, [rsi+0xcb0]
        mov     eax, esi
        add     rdx, r11
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L6130:
        movzx   ecx, BYTE PTR [rdx]
        add     rdx, 0x1
        mov     DWORD PTR [r8+rcx*4], 0x1
        mov     ecx, eax
        add     eax, 0x1
        cmp     eax, r9d
        jae     L6160
        cmp     esi, eax
        jae     L6130
        movzx   edi, BYTE PTR [rdx]
        cmp     BYTE PTR [rbx+rcx*1], dil
        jb      L6130
L6156:
        mov     eax, 0xffffffff
        pop     rbx
        pop     rbp
        ret
        // xchg    ax, ax
        .byte   0x66,0x90
L6160:
        cmp     ebp, 0x5
        je      L6170
L6165:
        xor     eax, eax
        pop     rbx
        pop     rbp
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L6170:
        cmp     r9d, 0x37
        je      L6165
        cmp     BYTE PTR [r11+r10*1+0xcb0], 0x0
        jne     L6156
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L6188:
        add     r10, 0x1
        cmp     r10d, 0x37
        je      L6165
        cmp     BYTE PTR [r11+r10*1+0xcb0], 0x0
        je      L6188
        jmp     L6156
        // nop
        .byte   0x90

// mld_rej_eta_c65.constprop.0 (0x61a0)

L61a0:
        cmp     esi, 0xff
        ja      L6230
        push    rbx
        mov     r10d, 0x1
        mov     r8, rdi
        mov     r9d, ecx
        mov     r11d, 0x4
        sub     r10d, edx
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L61c8:
        movzx   eax, BYTE PTR [rdx]
        mov     ecx, eax
        shr     al, 0x4
        and     ecx, 0xf
        cmp     cl, 0x8
        ja      L61e9
        movzx   ecx, cl
        mov     ebx, r11d
        mov     edi, esi
        add     esi, 0x1
        sub     ebx, ecx
        mov     DWORD PTR [r8+rdi*4], ebx
L61e9:
        cmp     esi, 0xff
        setbe   cl
        cmp     al, 0x8
        ja      L6216
        test    cl, cl
        je      L6216
        lea     edi, [rsi+0x1]
        movzx   eax, al
        mov     ecx, r11d
        mov     esi, esi
        sub     ecx, eax
        cmp     edi, 0xff
        mov     DWORD PTR [r8+rsi*4], ecx
        setbe   cl
        mov     esi, edi
L6216:
        lea     eax, [r10+rdx*1]
        cmp     eax, r9d
        setb    al
        add     rdx, 0x1
        test    al, cl
        jne     L61c8
        mov     eax, esi
        pop     rbx
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L6230:
        mov     eax, esi
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_poly_decompose (0x6240)

L6240:
        xor     ecx, ecx
        mov     r8d, 0x3ff000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L6250:
        mov     edx, DWORD PTR [rsi+rcx*1]
        lea     eax, [rdx+0x7f]
        sar     eax, 0x7
        mov     r9d, eax
        shl     r9d, 0xa
        lea     eax, [rax+r9*1+0x200000]
        sar     eax, 0x16
        and     eax, 0xf
        mov     r9d, eax
        mov     DWORD PTR [rdi+rcx*1], eax
        shl     r9d, 0xa
        sub     eax, r9d
        shl     eax, 0x9
        add     eax, edx
        mov     edx, r8d
        sub     edx, eax
        movsxd  rdx, edx
        sar     rdx, 0x1f
        lea     r9d, [rax-0x7fe001]
        xor     r9d, eax
        and     edx, r9d
        xor     eax, edx
        mov     DWORD PTR [rsi+rcx*1], eax
        add     rcx, 0x4
        cmp     rcx, 0x400
        jne     L6250
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_poly_use_hint (0x62b0)

L62b0:
        mov     r8, rsi
        mov     r9d, 0x3ff000
        xor     esi, esi
        jmp     L62d6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L62c0:
        add     edx, 0x1
        and     edx, 0xf
L62c6:
        mov     DWORD PTR [rdi+rsi*1], edx
        add     rsi, 0x4
        cmp     rsi, 0x400
        je      L633d
L62d6:
        mov     r10d, DWORD PTR [rdi+rsi*1]
        lea     eax, [r10+0x7f]
        sar     eax, 0x7
        mov     edx, eax
        shl     edx, 0xa
        lea     edx, [rax+rdx*1+0x200000]
        sar     edx, 0x16
        and     edx, 0xf
        mov     eax, edx
        mov     ecx, edx
        shl     eax, 0xa
        sub     ecx, eax
        mov     eax, r9d
        shl     ecx, 0x9
        add     ecx, r10d
        sub     eax, ecx
        cdqe
        sar     rax, 0x1f
        mov     r10d, DWORD PTR [r8+rsi*1]
        test    r10d, r10d
        je      L62c6
        lea     r10d, [rcx-0x7fe001]
        xor     r10d, ecx
        and     eax, r10d
        xor     eax, ecx
        jg      L62c0
        sub     edx, 0x1
        and     edx, 0xf
        mov     DWORD PTR [rdi+rsi*1], edx
        add     rsi, 0x4
        cmp     rsi, 0x400
        jne     L62d6
L633d:
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_poly_uniform_eta_4x (0x6340)

L6340:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x980
        movdqu  xmm3, XMMWORD PTR [r8]
        movdqu  xmm2, XMMWORD PTR [r8+0x10]
        movdqu  xmm1, XMMWORD PTR [r8+0x20]
        movdqu  xmm0, XMMWORD PTR [r8+0x30]
        lea     r14, [rsp+0x60]
        mov     QWORD PTR [rsp+0x38], rsi
        movaps  XMMWORD PTR [rsp+0x60], xmm3
        lea     rbx, [rsp+0xc0]
        lea     r13, [rsp+0x120]
        movaps  XMMWORD PTR [rsp+0x70], xmm2
        lea     r12, [rsp+0x180]
        movaps  XMMWORD PTR [rsp+0x80], xmm1
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0xc0], xmm3
        movaps  XMMWORD PTR [rsp+0xd0], xmm2
        movaps  XMMWORD PTR [rsp+0xe0], xmm1
        movaps  XMMWORD PTR [rsp+0xf0], xmm0
        movaps  XMMWORD PTR [rsp+0x120], xmm3
        movaps  XMMWORD PTR [rsp+0x130], xmm2
        movaps  XMMWORD PTR [rsp+0x140], xmm1
        movaps  XMMWORD PTR [rsp+0x150], xmm0
        movaps  XMMWORD PTR [rsp+0x180], xmm3
        movaps  XMMWORD PTR [rsp+0x190], xmm2
        movaps  XMMWORD PTR [rsp+0x1a0], xmm1
        movaps  XMMWORD PTR [rsp+0x1b0], xmm0
        mov     QWORD PTR [rsp+0x30], rdx
        mov     QWORD PTR [rsp+0x28], rcx
        mov     QWORD PTR [rsp+0x40], rdi
        mov     QWORD PTR [rsp+0x18], r14
        mov     BYTE PTR [rsp+0xa0], r9b
        mov     eax, DWORD PTR [rbp+0x10]
        mov     BYTE PTR [rsp+0x100], al
        mov     eax, DWORD PTR [rbp+0x18]
        mov     BYTE PTR [rsp+0x160], al
        mov     eax, DWORD PTR [rbp+0x20]
        mov     BYTE PTR [rsp+0xa1], 0x0
        mov     BYTE PTR [rsp+0x1c0], al
        lea     rax, [rsp+0x1e0]
        mov     r15, rax
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x20], rax
        mov     BYTE PTR [rsp+0x101], 0x0
        mov     BYTE PTR [rsp+0x161], 0x0
        mov     BYTE PTR [rsp+0x1c1], 0x0
        call    L1850
        mov     r8, r12
        mov     rcx, r13
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r15
        mov     r9d, 0x42
        mov     rbx, r15
        call    L1750
        lea     r14, [rsp+0x500]
        lea     r11, [rsp+0x620]
        mov     r9, rbx
        mov     rsi, r11
        mov     r8d, 0x2
        mov     rdi, r14
        mov     rbx, r11
        lea     rax, [rsp+0x860]
        lea     r15, [rsp+0x740]
        mov     QWORD PTR [rsp+0x50], r11
        mov     rcx, rax
        mov     rdx, r15
        mov     QWORD PTR [rsp+0x58], rax
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x40]
        xor     esi, esi
        mov     rdx, r14
        mov     ecx, 0x110
        call    L61a0
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     rdx, rbx
        xor     esi, esi
        mov     ecx, 0x110
        mov     r13d, eax
        call    L61a0
        mov     rdi, QWORD PTR [rsp+0x30]
        xor     esi, esi
        mov     rdx, r15
        mov     ecx, 0x110
        mov     r12d, eax
        call    L61a0
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     rdi, QWORD PTR [rsp+0x28]
        xor     esi, esi
        mov     ecx, 0x110
        mov     ebx, eax
        call    L61a0
        cmp     r12d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r13d, 0xff
        jmp     L65f1
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L6558:
        mov     r9, QWORD PTR [rsp+0x20]
        mov     rcx, QWORD PTR [rsp+0x58]
        mov     rdx, r15
        mov     rdi, r14
        mov     rsi, QWORD PTR [rsp+0x50]
        mov     r8d, 0x1
        mov     DWORD PTR [rsp+0x4c], r10d
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x40]
        mov     esi, r13d
        mov     rdx, r14
        mov     ecx, 0x88
        call    L61a0
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     esi, r12d
        mov     ecx, 0x88
        mov     r13d, eax
        call    L61a0
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     esi, ebx
        mov     rdx, r15
        mov     ecx, 0x88
        mov     r12d, eax
        call    L61a0
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     esi, DWORD PTR [rsp+0x4c]
        mov     ecx, 0x88
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     ebx, eax
        call    L61a0
        cmp     r13d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r12d, 0xff
L65f1:
        setbe   dl
        or      eax, edx
        cmp     ebx, 0xff
        setbe   dl
        or      al, dl
        jne     L6558
        cmp     r10d, 0xff
        jbe     L6558
        mov     rdi, QWORD PTR [rsp+0x20]
        call    L1860
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x90
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     ecx, 0x30
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x18]
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_poly_challenge (0x6650)

L6650:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        mov     r14, rdi
        push    r13
        push    r12
        push    rbx
        mov     rbx, rsi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x180
        lea     r12, [rsp+0xb0]
        mov     rdi, r12
        call    L1240
        mov     rsi, rbx
        mov     edx, 0x30
        mov     rdi, r12
        call    L1280
        lea     rbx, [rsp+0x20]
        mov     rdi, r12
        call    L1310
        mov     esi, 0x88
        mov     rdi, rbx
        mov     rdx, r12
        call    L1360
        mov     rax, rbx
        lea     rdi, [rsp+0x28]
        xor     ecx, ecx
        xor     esi, esi
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L66c0:
        movzx   edx, BYTE PTR [rax]
        add     rax, 0x1
        shl     rdx, cl
        add     ecx, 0x8
        or      rsi, rdx
        cmp     rax, rdi
        jne     L66c0
        lea     rdi, [r14+0x8]
        mov     rcx, r14
        xor     eax, eax
        mov     QWORD PTR [rsp+0x18], rsi
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [r14], 0x0
        mov     r15d, 0xcf
        mov     r13d, 0x1
        mov     QWORD PTR [r14+0x3f8], 0x0
        sub     rcx, rdi
        add     ecx, 0x400
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x8
        jmp     L672f
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L6720:
        mov     eax, ecx
L6722:
        movzx   edx, BYTE PTR [rsp+rax*1+0x20]
        lea     ecx, [rax+0x1]
        cmp     r15d, edx
        jae     L675b
L672f:
        cmp     ecx, 0x88
        jne     L6720
        mov     rdx, r12
        mov     esi, 0x88
        mov     rdi, rbx
        call    L1360
        movzx   edx, BYTE PTR [rsp+0x20]
        mov     eax, 0x1
        cmp     r15d, edx
        jb      L6722
        mov     ecx, 0x1
L675b:
        mov     eax, DWORD PTR [r14+rdx*4]
        mov     edi, r13d
        mov     DWORD PTR [r14+r15*4], eax
        mov     rax, QWORD PTR [rsp+0x18]
        add     r15, 0x1
        mov     rsi, rax
        shr     rax, 1
        and     esi, 0x1
        mov     QWORD PTR [rsp+0x18], rax
        add     rsi, rsi
        sub     edi, esi
        mov     DWORD PTR [r14+rdx*4], edi
        cmp     r15, 0x100
        jne     L672f
        mov     rdi, r12
        call    L1400
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x11
        rep stos QWORD PTR es:[rdi], rax
        mov     QWORD PTR [rsp+0x18], 0x0
        lea     rax, [rsp+0x18]
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_polyeta_pack (0x67d0)

L67d0:
        xor     eax, eax
        mov     ecx, 0x4
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L67e0:
        mov     edx, ecx
        sub     dl, BYTE PTR [rsi+rax*8+0x4]
        mov     r8d, ecx
        sub     r8b, BYTE PTR [rsi+rax*8]
        shl     edx, 0x4
        or      edx, r8d
        mov     BYTE PTR [rdi+rax*1], dl
        add     rax, 0x1
        cmp     rax, 0x80
        jne     L67e0
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_polyeta_unpack (0x6810)

L6810:
        lea     rdx, [rdi+0x4]
        lea     r9, [rsi+0x80]
        mov     edi, 0x4
L6820:
        movzx   ecx, BYTE PTR [rsi]
        mov     r8d, edi
        add     rsi, 0x1
        add     rdx, 0x8
        and     ecx, 0xf
        mov     DWORD PTR [rdx-0xc], ecx
        movzx   eax, BYTE PTR [rsi-0x1]
        sub     r8d, ecx
        mov     ecx, edi
        mov     DWORD PTR [rdx-0xc], r8d
        shr     al, 0x4
        movzx   eax, al
        sub     ecx, eax
        mov     DWORD PTR [rdx-0x8], ecx
        cmp     rsi, r9
        jne     L6820
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa65_polyz_pack (0x6860)

L6860:
        push    rbx
        mov     rax, rdi
        mov     r8d, 0x80000
        mov     rdi, rsi
        lea     r9, [rax+0x280]
        mov     rsi, rax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L6880:
        mov     ecx, r8d
        mov     edx, r8d
        sub     ecx, DWORD PTR [rdi]
        sub     edx, DWORD PTR [rdi+0x4]
        mov     eax, ecx
        mov     r10d, edx
        movzx   ebx, ch
        movzx   ecx, cl
        shr     eax, 0x10
        shl     r10d, 0x4
        add     rsi, 0x5
        add     rdi, 0x8
        or      r10d, eax
        mov     eax, edx
        shr     edx, 0xc
        shl     eax, 0x4
        movzx   r10d, r10b
        mov     BYTE PTR [rsi-0x1], dl
        and     eax, 0xff00
        or      eax, r10d
        shl     eax, 0x8
        or      eax, ebx
        shl     eax, 0x8
        or      eax, ecx
        mov     DWORD PTR [rsi-0x5], eax
        cmp     r9, rsi
        jne     L6880
        pop     rbx
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_polyz_unpack (0x68e0)

L68e0:
        mov     rax, rsi
        mov     rdx, rdi
        lea     r9, [rsi+0x280]
        mov     r8d, 0x80000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L68f8:
        movzx   ecx, BYTE PTR [rax]
        add     rax, 0x5
        add     rdx, 0x8
        mov     DWORD PTR [rdx-0x8], ecx
        movzx   esi, BYTE PTR [rax-0x4]
        shl     esi, 0x8
        or      esi, ecx
        mov     DWORD PTR [rdx-0x8], esi
        movzx   ecx, BYTE PTR [rax-0x3]
        shl     ecx, 0x10
        or      ecx, esi
        and     ecx, 0xfffff
        mov     DWORD PTR [rdx-0x8], ecx
        movzx   edi, BYTE PTR [rax-0x3]
        shr     dil, 0x4
        movzx   edi, dil
        mov     DWORD PTR [rdx-0x4], edi
        movzx   esi, BYTE PTR [rax-0x2]
        shl     esi, 0x4
        or      esi, edi
        mov     DWORD PTR [rdx-0x4], esi
        movzx   edi, BYTE PTR [rax-0x1]
        shl     edi, 0xc
        or      esi, edi
        mov     edi, r8d
        sub     edi, ecx
        mov     ecx, r8d
        sub     ecx, esi
        mov     DWORD PTR [rdx-0x8], edi
        mov     DWORD PTR [rdx-0x4], ecx
        cmp     r9, rax
        jne     L68f8
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_poly_uniform_gamma1 (0x6960)

L6960:
        push    rbp
        mov     rbp, rsp
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x3e0
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm2, XMMWORD PTR [rsi+0x10]
        movdqu  xmm3, XMMWORD PTR [rsi+0x20]
        movdqu  xmm4, XMMWORD PTR [rsi+0x30]
        lea     r12, [rsp+0x50]
        mov     r14, rsp
        mov     rdi, r12
        movaps  XMMWORD PTR [rsp], xmm1
        lea     rbx, [rsp+0x120]
        movaps  XMMWORD PTR [rsp+0x10], xmm2
        movaps  XMMWORD PTR [rsp+0x20], xmm3
        movaps  XMMWORD PTR [rsp+0x30], xmm4
        mov     WORD PTR [rsp+0x40], dx
        call    L1240
        mov     rsi, r14
        mov     edx, 0x42
        mov     rdi, r12
        call    L1280
        mov     rdi, r12
        call    L1310
        mov     rdx, r12
        mov     rdi, rbx
        mov     esi, 0x2a8
        call    L1360
        mov     rsi, rbx
        mov     rdi, r13
        call    L68e0
        mov     rdi, r12
        call    L1400
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x55
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        xor     eax, eax
        mov     WORD PTR [rsp+0x40], ax
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // nop
        .byte   0x90

// mldsa65_poly_uniform_gamma1_4x (0x6a30)

L6a30:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xfe0
        movdqu  xmm3, XMMWORD PTR [r8]
        movdqu  xmm2, XMMWORD PTR [r8+0x10]
        movdqu  xmm1, XMMWORD PTR [r8+0x20]
        movdqu  xmm0, XMMWORD PTR [r8+0x30]
        mov     QWORD PTR [rsp+0x30], rsi
        lea     r12, [rsp+0x1c0]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        lea     r13, [rsp+0xa0]
        lea     r14, [rsp+0x100]
        movaps  XMMWORD PTR [rsp+0x50], xmm2
        lea     r15, [rsp+0x160]
        lea     rbx, [rsp+0x40]
        movaps  XMMWORD PTR [rsp+0x60], xmm1
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0xa0], xmm3
        movaps  XMMWORD PTR [rsp+0xb0], xmm2
        movaps  XMMWORD PTR [rsp+0xc0], xmm1
        movaps  XMMWORD PTR [rsp+0xd0], xmm0
        movaps  XMMWORD PTR [rsp+0x100], xmm3
        movaps  XMMWORD PTR [rsp+0x110], xmm2
        movaps  XMMWORD PTR [rsp+0x120], xmm1
        movaps  XMMWORD PTR [rsp+0x130], xmm0
        movaps  XMMWORD PTR [rsp+0x160], xmm3
        movaps  XMMWORD PTR [rsp+0x170], xmm2
        movaps  XMMWORD PTR [rsp+0x180], xmm1
        movaps  XMMWORD PTR [rsp+0x190], xmm0
        mov     QWORD PTR [rsp+0x28], rdx
        mov     QWORD PTR [rsp+0x20], rcx
        mov     WORD PTR [rsp+0x80], r9w
        mov     QWORD PTR [rsp+0x38], rdi
        mov     eax, DWORD PTR [rbp+0x10]
        mov     rdi, r12
        mov     WORD PTR [rsp+0xe0], ax
        mov     eax, DWORD PTR [rbp+0x18]
        mov     WORD PTR [rsp+0x140], ax
        mov     eax, DWORD PTR [rbp+0x20]
        mov     WORD PTR [rsp+0x1a0], ax
        call    L1850
        mov     r8, r15
        mov     rcx, r14
        mov     rdx, r13
        mov     rsi, rbx
        mov     rdi, r12
        mov     r9d, 0x42
        call    L1750
        lea     r13, [rsp+0x4e0]
        lea     r11, [rsp+0x7a0]
        mov     r9, r12
        lea     r14, [rsp+0xd20]
        mov     rsi, r11
        mov     r8d, 0x5
        mov     rdi, r13
        lea     r15, [rsp+0xa60]
        mov     rcx, r14
        mov     QWORD PTR [rsp+0x18], r11
        mov     rdx, r15
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     rsi, r13
        call    L68e0
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, QWORD PTR [rsp+0x30]
        call    L68e0
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     rsi, r15
        call    L68e0
        mov     rdi, QWORD PTR [rsp+0x20]
        mov     rsi, r14
        call    L68e0
        mov     rdi, r12
        call    L1860
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x160
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x30
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_polyvecl_uniform_gamma1 (0x6c00)

L6c00:
        push    r12
        mov     r12, rsi
        lea     rcx, [rdi+0xc00]
        lea     rsi, [rdi+0x400]
        push    rbp
        mov     r8, r12
        mov     rbp, rdi
        push    rbx
        mov     ebx, edx
        lea     rdx, [rdi+0x800]
        lea     eax, [rbx+0x3]
        movzx   r9d, bx
        movzx   eax, ax
        sub     rsp, 0x8
        push    rax
        lea     eax, [rbx+0x2]
        movzx   eax, ax
        push    rax
        lea     eax, [rbx+0x1]
        movzx   eax, ax
        push    rax
        call    L6a30
        add     rsp, 0x20
        lea     edx, [rbx+0x4]
        mov     rsi, r12
        pop     rbx
        lea     rdi, [rbp+0x1000]
        movzx   edx, dx
        pop     rbp
        pop     r12
        jmp     L6960
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_polyvecl_ntt (0x6c70)

L6c70:
        push    rbp
        lea     rbp, [rdi+0x1400]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L6c80:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L27d0
        cmp     rbx, rbp
        jne     L6c80
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyvecl_pointwise_acc_montgomery (0x6ca0)

L6ca0:
        mov     r9, rdx
        mov     r8, rsi
        xor     edx, edx
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L6cb0:
        mov     rax, rdx
        xor     esi, esi
        lea     r11, [rdx+0x1400]
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L6cc0:
        movsxd  rcx, DWORD PTR [r8+rax*1]
        movsxd  r10, DWORD PTR [r9+rax*1]
        add     rax, 0x400
        imul    rcx, r10
        add     rsi, rcx
        cmp     r11, rax
        jne     L6cc0
        imul    ecx, esi, 0x3802001
        movsxd  rcx, ecx
        mov     r10, rcx
        mov     rax, rcx
        shl     r10, 0xa
        sub     rax, r10
        shl     rax, 0xd
        sub     rax, rcx
        add     rax, rsi
        sar     rax, 0x20
        mov     DWORD PTR [rdi+rdx*1], eax
        add     rdx, 0x4
        cmp     rdx, 0x400
        jne     L6cb0
        ret
        // nop
        .byte   0x90

// mldsa65_polyvecl_chknorm (0x6d10)

L6d10:
        push    r13
        lea     r13, [rdi+0x1400]
        push    r12
        mov     r12d, esi
        push    rbp
        xor     ebp, ebp
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L6d30:
        mov     rdi, rbx
        mov     esi, r12d
        add     rbx, 0x400
        call    L31e0
        or      ebp, eax
        cmp     rbx, r13
        jne     L6d30
        add     rsp, 0x8
        mov     eax, ebp
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_polyveck_caddq (0x6d60)

L6d60:
        push    rbp
        lea     rbp, [rdi+0x1800]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L6d70:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L2700
        cmp     rbx, rbp
        jne     L6d70
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyveck_ntt (0x6d90)

L6d90:
        push    rbp
        lea     rbp, [rdi+0x1800]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L6da0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L27d0
        cmp     rbx, rbp
        jne     L6da0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyveck_invntt_tomont (0x6dc0)

L6dc0:
        push    rbp
        lea     rbp, [rdi+0x1800]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L6dd0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L28e0
        cmp     rbx, rbp
        jne     L6dd0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyveck_unpack_eta_chknorm (0x6df0)

L6df0:
        push    r14
        lea     r14, [rdi+0x300]
        push    r13
        mov     r13d, esi
        push    r12
        xor     r12d, r12d
        push    rbp
        mov     rbp, rdx
        push    rbx
        mov     rbx, rdi
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L6e10:
        mov     rsi, rbx
        mov     rdi, rbp
        sub     rbx, 0xffffffffffffff80
        call    L6810
        mov     esi, r13d
        mov     rdi, rbp
        call    L31e0
        or      r12d, eax
        cmp     rbx, r14
        jne     L6e10
        pop     rbx
        mov     eax, r12d
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_polyveck_decompose_pack_w1 (0x6e40)

L6e40:
        push    r13
        lea     r13, [rsi+0x1800]
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        sub     rsp, 0x8
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L6e60:
        mov     rsi, rbx
        mov     rdi, r12
        add     rbx, 0x400
        call    L6240
        mov     rdi, rbp
        mov     rsi, r12
        sub     rbp, 0xffffffffffffff80
        call    L3280
        cmp     rbx, r13
        jne     L6e60
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_polyvecl_unpack_eta (0x6ea0)

L6ea0:
        push    r12
        lea     r12, [rdi+0x1400]
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L6eb8:
        mov     rsi, rbp
        mov     rdi, rbx
        add     rbx, 0x400
        sub     rbp, 0xffffffffffffff80
        call    L6810
        cmp     rbx, r12
        jne     L6eb8
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_polyvecl_unpack_z (0x6ee0)

L6ee0:
        push    r12
        lea     r12, [rsi+0xc80]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L6ef8:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x280
        add     rbp, 0x400
        call    L68e0
        cmp     rbx, r12
        jne     L6ef8
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyveck_unpack_eta (0x6f20)

L6f20:
        push    r12
        lea     r12, [rdi+0x1800]
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L6f38:
        mov     rsi, rbp
        mov     rdi, rbx
        add     rbx, 0x400
        sub     rbp, 0xffffffffffffff80
        call    L6810
        cmp     rbx, r12
        jne     L6f38
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_polyvec_matrix_expand_eager (0x6f60)

L6f60:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        mov     r14, rdi
        push    r13
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x100
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm0, XMMWORD PTR [rsi+0x10]
        mov     rbx, rsp
        lea     r15, [rsp+0x100]
        mov     rax, rbx
L6f92:
        movaps  XMMWORD PTR [rax], xmm1
        add     rax, 0x40
        movaps  XMMWORD PTR [rax-0x30], xmm0
        cmp     r15, rax
        jne     L6f92
        xor     r12d, r12d
        mov     r13d, 0xcccccccd
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L6fb0:
        mov     rdx, rbx
        mov     ecx, r12d
L6fb6:
        mov     eax, ecx
        mov     esi, ecx
        add     rdx, 0x40
        add     ecx, 0x1
        imul    rax, r13
        shr     rax, 0x22
        lea     edi, [rax+rax*4]
        mov     BYTE PTR [rdx-0x1f], al
        sub     esi, edi
        mov     BYTE PTR [rdx-0x20], sil
        cmp     r15, rdx
        jne     L6fb6
        lea     eax, [r12+0x3]
        lea     esi, [r12+0x2]
        mov     rdx, rax
        imul    rax, r13
        lea     edi, [r12+0x1]
        shr     rax, 0x22
        mov     ecx, eax
        lea     eax, [rax+rax*4]
        sub     edx, eax
        mov     eax, esi
        lea     rcx, [rcx+rcx*4]
        imul    rax, r13
        add     rcx, rdx
        shl     rcx, 0xa
        add     rcx, r14
        shr     rax, 0x22
        mov     edx, eax
        lea     eax, [rax+rax*4]
        sub     esi, eax
        mov     eax, edi
        lea     rdx, [rdx+rdx*4]
        imul    rax, r13
        add     rdx, rsi
        shl     rdx, 0xa
        add     rdx, r14
        shr     rax, 0x22
        mov     esi, eax
        lea     eax, [rax+rax*4]
        sub     edi, eax
        mov     eax, r12d
        lea     rsi, [rsi+rsi*4]
        imul    rax, r13
        add     rsi, rdi
        shl     rsi, 0xa
        add     rsi, r14
        shr     rax, 0x22
        lea     r8d, [rax+rax*4]
        mov     edi, eax
        mov     eax, r12d
        add     r12d, 0x4
        sub     eax, r8d
        lea     rdi, [rdi+rdi*4]
        mov     r8, rbx
        add     rdi, rax
        shl     rdi, 0xa
        add     rdi, r14
        call    L2ba0
        cmp     r12d, 0x1c
        jne     L6fb0
        movzx   eax, WORD PTR [rip+Lc602]
        lea     rdi, [r14+0x7000]
        mov     rsi, rbx
        mov     WORD PTR [rsp+0x20], ax
        call    L2ad0
        movzx   eax, WORD PTR [rip+Lc604]
        lea     rdi, [r14+0x7400]
        mov     rsi, rbx
        mov     WORD PTR [rsp+0x20], ax
        call    L2ad0
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mldsa65_polyvec_matrix_pointwise_montgomery_row_eager (0x70e0)

L70e0:
        mov     ecx, ecx
        lea     rax, [rcx+rcx*4]
        shl     rax, 0xa
        add     rsi, rax
        jmp     L6ca0
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager (0x7100)

L7100:
        push    r14
        mov     r14, rdi
        push    r13
        mov     r13, rsi
        mov     rsi, rdx
        push    r12
        mov     r12, rcx
        mov     ecx, 0x280
        push    rbp
        mov     rdi, r12
        mov     rbp, r14
        push    rbx
        xor     ebx, ebx
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rdi, r12
        call    L6c70
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L7130:
        mov     ecx, ebx
        mov     rdi, rbp
        mov     rdx, r12
        mov     rsi, r13
        call    L70e0
        add     ebx, 0x1
        add     rbp, 0x400
        cmp     ebx, 0x6
        jne     L7130
        pop     rbx
        mov     rdi, r14
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        jmp     L6dc0
        // nop
        .byte   0x90

// mld_compute_pack_t0_t165 (0x7160)

L7160:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rcx
        push    r14
        mov     r14, rdi
        push    r13
        mov     r13, rsi
        mov     rsi, r8
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x8020
        lea     rax, [rsp+0x820]
        mov     QWORD PTR [rsp+0x8], rdx
        lea     rbx, [rsp+0x20]
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x10], rax
        lea     r12, [rsp+0x420]
        call    L6f60
        xor     eax, eax
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L71b0:
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     rsi, QWORD PTR [rsp+0x10]
        mov     ecx, eax
        mov     rdi, rbx
        mov     DWORD PTR [rsp+0x1c], eax
        call    L70e0
        mov     rdi, rbx
        call    L28e0
        mov     rsi, r15
        mov     rdi, r12
        sub     r15, 0xffffffffffffff80
        call    L6810
        mov     rsi, r12
        mov     rdi, rbx
        call    L2740
        mov     rdi, rbx
        call    L26b0
        mov     rdi, rbx
        call    L2700
        mov     rdx, rbx
        mov     rsi, rbx
        mov     rdi, r12
        call    L2a80
        mov     rdi, r14
        mov     rsi, r12
        add     r14, 0x140
        call    L2db0
        mov     rdi, r13
        mov     rsi, rbx
        add     r13, 0x1a0
        call    L2ea0
        mov     eax, DWORD PTR [rsp+0x1c]
        add     eax, 0x1
        cmp     eax, 0x6
        jne     L71b0
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rbx, QWORD PTR [rsp+0x10]
        mov     edx, 0x7800
        xor     esi, esi
        mov     rdi, rbx
        call    L1030
        lea     rsp, [rbp-0x28]
        xor     eax, eax
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mld_H65 (0x7280)

L7280:
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, rdx
        push    r12
        mov     r12, rsi
        push    rbp
        mov     rbp, rdi
        push    rbx
        sub     rsp, 0xe8
        lea     rbx, [rsp+0x10]
        mov     QWORD PTR [rsp+0x8], r8
        mov     rdi, rbx
        call    L1240
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, rbx
        call    L1280
        test    r15, r15
        jne     L7310
        cmp     QWORD PTR [rsp+0x128], 0x0
        jne     L732b
L72d0:
        mov     rdi, rbx
        call    L1310
        mov     rdx, rbx
        mov     rsi, r12
        mov     rdi, rbp
        call    L1360
        mov     rdi, rbx
        call    L1400
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        add     rsp, 0xe8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L7310:
        mov     rsi, QWORD PTR [rsp+0x8]
        mov     rdx, r15
        mov     rdi, rbx
        call    L1280
        cmp     QWORD PTR [rsp+0x128], 0x0
        je      L72d0
L732b:
        mov     rdx, QWORD PTR [rsp+0x128]
        mov     rsi, QWORD PTR [rsp+0x120]
        mov     rdi, rbx
        call    L1280
        jmp     L72d0
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_keypair_internal (0x7350)

L7350:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        mov     ecx, 0x22
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        mov     r14, rdi
        lea     r15, [rbp-0xc30]
        push    r13
        lea     r13, [rbp-0x1030]
        push    r12
        lea     r12, [rbp-0x1430]
        push    r10
        push    rbx
        mov     rbx, rsi
        lea     rsi, [rbp-0x1530]
        sub     rsp, 0x1540
        movdqu  xmm1, XMMWORD PTR [rdx]
        movzx   eax, WORD PTR [rip+Lc606]
        mov     QWORD PTR [rbp-0x1550], rsi
        movdqu  xmm2, XMMWORD PTR [rdx+0x10]
        mov     rdx, rsi
        mov     esi, 0x80
        mov     WORD PTR [rbp-0x1510], ax
        lea     rax, [rbp-0x14b0]
        mov     rdi, rax
        movaps  XMMWORD PTR [rbp-0x1530], xmm1
        movaps  XMMWORD PTR [rbp-0x1520], xmm2
        mov     QWORD PTR [rbp-0x1538], rax
        call    L1440
        sub     rsp, 0x8
        mov     rsi, r13
        lea     rdx, [rbx+0x300]
        mov     QWORD PTR [rbp-0x1548], rdx
        lea     rax, [rbp-0x830]
        mov     rdx, r15
        mov     rdi, r12
        push    0xa
        lea     r8, [rbp-0x1490]
        mov     rcx, rax
        mov     r9d, 0x7
        push    0x9
        push    0x8
        mov     QWORD PTR [rbp-0x1558], r8
        mov     QWORD PTR [rbp-0x1540], rax
        call    L6340
        add     rsp, 0x20
        lea     rdi, [rbx+0x400]
        mov     rsi, r12
        call    L67d0
        mov     rsi, r13
        lea     rdi, [rbx+0x480]
        call    L67d0
        mov     rsi, r15
        lea     rdi, [rbx+0x500]
        call    L67d0
        mov     rsi, QWORD PTR [rbp-0x1540]
        lea     rdi, [rbx+0x580]
        call    L67d0
        sub     rsp, 0x8
        mov     rcx, r15
        mov     rdx, r13
        push    0xff
        lea     rax, [rbp-0x430]
        mov     r8, QWORD PTR [rbp-0x1558]
        mov     rsi, r12
        push    0x6
        mov     rdi, rax
        mov     r9d, 0x4
        push    0x5
        mov     QWORD PTR [rbp-0x1558], rax
        mov     QWORD PTR [rbp-0x1560], r8
        call    L6340
        mov     rsi, QWORD PTR [rbp-0x1558]
        add     rsp, 0x20
        lea     rdi, [rbx+0x280]
        call    L67d0
        mov     rdi, QWORD PTR [rbp-0x1548]
        mov     rsi, r12
        call    L67d0
        mov     rsi, r13
        lea     rdi, [rbx+0x380]
        call    L67d0
        sub     rsp, 0x8
        mov     rdx, r15
        xor     r9d, r9d
        push    0x3
        mov     r8, QWORD PTR [rbp-0x1560]
        mov     rsi, r13
        mov     rdi, r12
        push    0x2
        mov     rcx, QWORD PTR [rbp-0x1540]
        push    0x1
        call    L6340
        add     rsp, 0x20
        lea     rdi, [rbx+0x80]
        mov     rsi, r12
        call    L67d0
        mov     rsi, r13
        lea     rdi, [rbx+0x100]
        call    L67d0
        mov     rsi, r15
        lea     rdi, [rbx+0x180]
        lea     r15, [rbp-0x14f0]
        call    L67d0
        mov     rsi, QWORD PTR [rbp-0x1540]
        lea     rdi, [rbx+0x200]
        call    L67d0
        mov     rdi, r12
        call    L6c70
        movdqa  xmm3, XMMWORD PTR [rbp-0x14b0]
        lea     rdi, [r14+0x20]
        movdqa  xmm4, XMMWORD PTR [rbp-0x14a0]
        mov     r8, QWORD PTR [rbp-0x1538]
        mov     rcx, QWORD PTR [rbp-0x1548]
        lea     rsi, [rbx+0x600]
        mov     rdx, r12
        movups  XMMWORD PTR [r14], xmm3
        movups  XMMWORD PTR [r14+0x10], xmm4
        call    L7160
        mov     r13d, eax
        test    eax, eax
        jne     L75d3
        mov     ecx, 0x7a0
        mov     rdx, r14
        mov     esi, 0x40
        mov     rdi, r15
        call    L1440
        mov     rsi, QWORD PTR [rbp-0x1538]
        mov     rdx, r15
        mov     rdi, rbx
        lea     rcx, [rbp-0x1450]
        call    L5e70
L75d3:
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x280
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x14f0], xmm0
        movaps  XMMWORD PTR [rbp-0x14e0], xmm0
        movaps  XMMWORD PTR [rbp-0x14d0], xmm0
        movaps  XMMWORD PTR [rbp-0x14c0], xmm0
        xor     edx, edx
        movaps  XMMWORD PTR [rbp-0x1530], xmm0
        mov     WORD PTR [rbp-0x1510], dx
        mov     rdx, QWORD PTR [rbp-0x1550]
        movaps  XMMWORD PTR [rbp-0x1520], xmm0
        mov     rdi, QWORD PTR [rbp-0x1538]
        mov     ecx, 0x10
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1538]
        test    r13d, r13d
        jne     L7658
L7639:
        lea     rsp, [rbp-0x30]
        mov     eax, r13d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L7658:
        lea     rdi, [r14+0x8]
        mov     rcx, r14
        mov     QWORD PTR [r14], 0x0
        mov     QWORD PTR [r14+0x798], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x7a0
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0xfb8], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xfc0
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        jmp     L7639
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa65_keypair (0x76c0)

L76c0:
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1020
        test    eax, eax
        jne     L7718
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    L7350
L76f9:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     rsp, [rbp-0x18]
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L7718:
        mov     eax, 0xfffffffd
        jmp     L76f9
        // nop
        .byte   0x90

// mldsa65_signature_internal (0x7720)

L7720:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     rax, [rbp-0xfc30]
        lea     r14, [rbp-0x107d0]
        push    r13
        lea     r15, [rbp-0x10810]
        push    r12
        mov     r12, rsi
        lea     rsi, [rbp-0x10830]
        push    r10
        push    rbx
        mov     rbx, r9
        lea     r9, [rbp-0xa830]
        sub     rsp, 0x108c8
        mov     QWORD PTR [rbp-0x10880], rcx
        lea     rcx, [rbp-0xc030]
        mov     r13d, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x108a0], rdi
        mov     rdi, rsi
        mov     QWORD PTR [rbp-0x10878], rdx
        mov     rdx, r14
        mov     QWORD PTR [rbp-0x10888], r8
        mov     r8, rax
        mov     QWORD PTR [rbp-0x108f0], rsi
        mov     rsi, r15
        mov     QWORD PTR [rbp-0x108c0], r9
        mov     QWORD PTR [rbp-0x108a8], rax
        mov     QWORD PTR [rbp-0x108c8], rcx
        push    QWORD PTR [r10]
        call    L5ec0
        pop     rdi
        pop     r8
        test    r13d, r13d
        jne     L7d07
        lea     rax, [rbp-0x107b0]
        mov     r9, QWORD PTR [rbp-0x10888]
        mov     ecx, 0x40
        mov     rdx, r15
        mov     QWORD PTR [rbp-0x108e0], rax
        mov     r8, QWORD PTR [rbp-0x10880]
        mov     esi, 0x40
        mov     rdi, rax
        push    QWORD PTR [rbp-0x10878]
        push    r12
        call    L7280
        pop     rcx
        pop     rsi
L780a:
        mov     rdx, r14
        mov     r8, rbx
        mov     ecx, 0x20
        mov     esi, 0x40
        lea     rax, [rbp-0x10770]
        mov     r9d, 0x20
        lea     rbx, [rbp-0xd430]
        mov     QWORD PTR [rbp-0x108e8], rax
        mov     rdi, rax
        lea     r15, [rbp-0x10030]
        lea     r14, [rbp-0x10430]
        push    0x40
        mov     r12, r15
        push    QWORD PTR [rbp-0x108e0]
        call    L7280
        lea     rax, [rbp-0x7830]
        mov     rsi, QWORD PTR [rbp-0x108f0]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x108d8], rax
        call    L6f60
        pop     rax
        lea     rax, [rbp-0xe830]
        pop     rdx
        mov     QWORD PTR [rbp-0x10888], rax
        lea     rax, [rbp-0x9030]
        mov     QWORD PTR [rbp-0x10890], rax
        lea     rax, [rbp-0x10730]
        mov     QWORD PTR [rbp-0x108b8], rax
        lea     rax, [rbp-0x10870]
        mov     DWORD PTR [rbp-0x108ac], 0x0
        mov     QWORD PTR [rbp-0x10878], rbx
        mov     QWORD PTR [rbp-0x108d0], rax
        // xchg    ax, ax
        .byte   0x66,0x90
L78c0:
        mov     r13, QWORD PTR [rbp-0x10888]
        mov     edx, DWORD PTR [rbp-0x108ac]
        mov     rsi, QWORD PTR [rbp-0x108e8]
        mov     rdi, r13
        call    L6c00
        mov     rdx, r13
        mov     r13, QWORD PTR [rbp-0x10890]
        mov     rcx, QWORD PTR [rbp-0x10878]
        mov     rsi, QWORD PTR [rbp-0x108d8]
        mov     rdi, r13
        call    L7100
        mov     rdi, r13
        call    L6d60
        mov     rsi, r13
        mov     r13, QWORD PTR [rbp-0x108b8]
        mov     rdx, QWORD PTR [rbp-0x10878]
        mov     rdi, r13
        call    L6e40
        mov     rdi, r15
        call    L1240
        mov     rsi, QWORD PTR [rbp-0x108e0]
        mov     rdi, r15
        mov     edx, 0x40
        call    L1280
        mov     rsi, r13
        mov     edx, 0x300
        mov     rdi, r15
        call    L1280
        mov     rdi, r15
        call    L1310
        mov     r13, QWORD PTR [rbp-0x108d0]
        mov     rdx, r15
        mov     esi, 0x30
        mov     rdi, r13
        call    L1360
        mov     rdi, r15
        call    L1400
        mov     rdi, r15
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rsi, r13
        mov     rdi, r14
        xor     r13d, r13d
        call    L6650
        mov     rdi, r14
        call    L27d0
        mov     QWORD PTR [rbp-0x10898], r14
        mov     r14, r13
L799d:
        mov     rax, QWORD PTR [rbp-0x108a8]
        mov     r13, r14
        mov     rdi, r15
        mov     ecx, 0x80
        shl     r13, 0xa
        mov     DWORD PTR [rbp-0x10880], r14d
        mov     r15, r12
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, QWORD PTR [rbp-0x10898]
        mov     rdi, r12
        call    L2a30
        mov     rdi, r12
        call    L28e0
        mov     rax, QWORD PTR [rbp-0x10888]
        mov     ecx, 0x80
        mov     rdi, QWORD PTR [rbp-0x10878]
        mov     QWORD PTR [rbp-0x10878], rbx
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, rbx
        mov     rdi, r12
        call    L2740
        mov     rdi, r12
        call    L26b0
        mov     esi, 0x7ff3c
        mov     rdi, r12
        call    L31e0
        test    eax, eax
        jne     L7cd8
        mov     edx, DWORD PTR [rbp-0x10880]
        mov     rdi, QWORD PTR [rbp-0x108a0]
        mov     rsi, r12
        add     r14, 0x1
        call    L60a0
        cmp     r14, 0x5
        jne     L799d
        mov     QWORD PTR [rbp-0x10878], r12
        mov     r14, QWORD PTR [rbp-0x10898]
        xor     r13d, r13d
        mov     QWORD PTR [rbp-0x10880], r12
L7a5f:
        mov     rax, QWORD PTR [rbp-0x108c0]
        mov     ecx, 0x80
        mov     rdi, rbx
        mov     r12, rbx
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, r14
        mov     rdi, rbx
        call    L2a30
        mov     rdi, rbx
        call    L28e0
        mov     rax, QWORD PTR [rbp-0x10890]
        mov     rsi, rbx
        lea     r15, [rax+r13*1]
        mov     rdi, r15
        call    L2770
        mov     rdi, r15
        call    L26b0
        mov     esi, 0x3fe3c
        mov     rdi, r15
        call    L31e0
        test    eax, eax
        jne     L7cf0
        mov     rax, QWORD PTR [rbp-0x108c8]
        mov     ecx, 0x80
        mov     rdi, rbx
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, r14
        mov     rdi, rbx
        call    L2a30
        mov     rdi, rbx
        call    L28e0
        mov     rdi, rbx
        call    L26b0
        mov     esi, 0x3ff00
        mov     rdi, rbx
        call    L31e0
        test    eax, eax
        jne     L7cf0
        mov     rsi, rbx
        mov     rdi, r15
        add     r13, 0x400
        call    L2740
        cmp     r13, 0x1800
        jne     L7a5f
        mov     r13, QWORD PTR [rbp-0x108a0]
        mov     rsi, QWORD PTR [rbp-0x108d0]
        mov     r15, QWORD PTR [rbp-0x10878]
        mov     r12, QWORD PTR [rbp-0x10880]
        mov     QWORD PTR [rbp-0x10878], rbx
        mov     rdi, r13
        call    L5fa0
        mov     rdx, QWORD PTR [rbp-0x108b8]
        mov     rdi, r13
        mov     rcx, rbx
        mov     rsi, QWORD PTR [rbp-0x10890]
        call    L5fc0
        mov     r13d, eax
L7b6a:
        mov     rdi, r12
        xor     eax, eax
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r14
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x10890]
        mov     ecx, 0x300
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x10890]
        mov     rdi, QWORD PTR [rbp-0x108b8]
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x108b8]
        mov     ecx, 0x280
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x10888]
        mov     ecx, 0x280
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x10888]
        mov     rax, QWORD PTR [rbp-0x108d0]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rax], xmm0
        movaps  XMMWORD PTR [rax+0x10], xmm0
        movaps  XMMWORD PTR [rax+0x20], xmm0
        test    r13d, r13d
        je      L7c43
        cmp     r13d, 0xffffffff
        jne     L7c0e
        add     DWORD PTR [rbp-0x108ac], 0x5
        mov     eax, DWORD PTR [rbp-0x108ac]
        cmp     eax, 0xfffa
        jne     L78c0
        mov     r13d, 0xfffffffc
L7c0e:
        mov     rdx, QWORD PTR [rbp-0x108a0]
        xor     eax, eax
        lea     rdi, [rdx+0x8]
        mov     rcx, rdx
        mov     QWORD PTR [rdx], 0x0
        mov     QWORD PTR [rdx+0xce5], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xced
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L7c43:
        mov     rdi, QWORD PTR [rbp-0x108c0]
        xor     ebx, ebx
        mov     ecx, 0x300
        mov     rax, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x108c0]
        mov     rdi, QWORD PTR [rbp-0x108c8]
        mov     ecx, 0x300
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x108c8]
        mov     rdi, QWORD PTR [rbp-0x108a8]
        mov     ecx, 0x280
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x108a8]
        mov     r14, QWORD PTR [rbp-0x108d8]
        mov     edx, 0x7800
        xor     esi, esi
        mov     rdi, r14
        call    L1030
        mov     rdi, QWORD PTR [rbp-0x108f0]
        mov     rax, rbx
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x108f0]
        lea     rsp, [rbp-0x30]
        mov     eax, r13d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L7cd8:
        mov     r14, QWORD PTR [rbp-0x10898]
L7cdf:
        mov     r13d, 0xffffffff
        jmp     L7b6a
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L7cf0:
        mov     r15, QWORD PTR [rbp-0x10878]
        mov     QWORD PTR [rbp-0x10878], r12
        mov     r12, QWORD PTR [rbp-0x10880]
        jmp     L7cdf
L7d07:
        movdqu  xmm1, XMMWORD PTR [r12]
        movdqu  xmm2, XMMWORD PTR [r12+0x10]
        lea     rax, [rbp-0x107b0]
        movdqu  xmm3, XMMWORD PTR [r12+0x20]
        movdqu  xmm4, XMMWORD PTR [r12+0x30]
        mov     QWORD PTR [rbp-0x108e0], rax
        movaps  XMMWORD PTR [rbp-0x107b0], xmm1
        movaps  XMMWORD PTR [rbp-0x107a0], xmm2
        movaps  XMMWORD PTR [rbp-0x10790], xmm3
        movaps  XMMWORD PTR [rbp-0x10780], xmm4
        jmp     L780a
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_signature_extmu (0x7d60)

L7d60:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdx
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x50]
        mov     rdi, rbx
        sub     rsp, 0x28
        call    L1020
        test    eax, eax
        jne     L7de0
        push    0x1
        xor     ecx, ecx
        mov     edx, 0x40
        mov     r9, rbx
        push    r14
        xor     r8d, r8d
        mov     rsi, r13
        mov     rdi, r12
        call    L7720
        pop     rdx
        pop     rcx
L7dba:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L7de0:
        mov     eax, 0xfffffffd
        jmp     L7dba
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_verify_internal (0x7df0)

L7df0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rdx
        push    r14
        lea     rax, [rbp-0x8c30]
        mov     r14, rcx
        push    r13
        mov     r13, rax
        push    r12
        mov     r12, rsi
        lea     rsi, [rdi+0x30]
        push    r10
        push    rbx
        sub     rsp, 0x9ce0
        movdqu  xmm3, XMMWORD PTR [rdi]
        movdqu  xmm4, XMMWORD PTR [rdi+0x10]
        mov     QWORD PTR [rbp-0x9cd8], rdi
        movdqu  xmm5, XMMWORD PTR [rdi+0x20]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x9ce8], r8
        mov     QWORD PTR [rbp-0x9cf0], r9
        mov     ebx, DWORD PTR [r10]
        mov     QWORD PTR [rbp-0x9ce0], rax
        movaps  XMMWORD PTR [rbp-0x9cd0], xmm3
        movaps  XMMWORD PTR [rbp-0x9cc0], xmm4
        movaps  XMMWORD PTR [rbp-0x9cb0], xmm5
        call    L6ee0
        mov     esi, 0x7ff3c
        mov     rdi, r13
        call    L6d10
        mov     r11, QWORD PTR [rbp-0x9cd8]
        test    eax, eax
        jne     L8312
        mov     r13d, eax
        test    ebx, ebx
        je      L8220
        movdqu  xmm6, XMMWORD PTR [r12]
        movdqu  xmm7, XMMWORD PTR [r12+0x10]
        lea     rax, [rbp-0x7830]
        lea     rbx, [rbp-0x9030]
        mov     QWORD PTR [rbp-0x9cd8], rax
        lea     rax, [rbp-0x9c50]
        movaps  XMMWORD PTR [rbp-0x9c50], xmm6
        movdqu  xmm6, XMMWORD PTR [r12+0x20]
        movaps  XMMWORD PTR [rbp-0x9c40], xmm7
        movdqu  xmm7, XMMWORD PTR [r12+0x30]
        mov     QWORD PTR [rbp-0x9d10], rax
        movaps  XMMWORD PTR [rbp-0x9c30], xmm6
        movaps  XMMWORD PTR [rbp-0x9c20], xmm7
L7ef5:
        mov     rdi, QWORD PTR [rbp-0x9ce0]
        mov     QWORD PTR [rbp-0x9cf8], r11
        lea     r12, [rbp-0x9430]
        call    L6c70
        mov     rsi, QWORD PTR [rbp-0x9cf0]
        mov     rdi, QWORD PTR [rbp-0x9cd8]
        call    L6f60
        lea     rax, [rbp-0x9830]
        lea     rsi, [rbp-0x9cd0]
        mov     r14, rax
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x9ce8], rax
        mov     QWORD PTR [rbp-0x9d08], rsi
        call    L6650
        mov     rdi, r14
        call    L27d0
        lea     rax, [rbp-0x9b30]
        mov     QWORD PTR [rbp-0x9d00], rax
        mov     r15, rax
L7f62:
        mov     rdx, QWORD PTR [rbp-0x9ce0]
        mov     rsi, QWORD PTR [rbp-0x9cd8]
        mov     ecx, r13d
        mov     rdi, r12
        call    L70e0
        mov     rsi, QWORD PTR [rbp-0x9cf0]
        mov     edx, r13d
        mov     rdi, rbx
        call    L5e60
        mov     rdi, rbx
        call    L27a0
        mov     rdi, rbx
        call    L27d0
        mov     rsi, QWORD PTR [rbp-0x9ce8]
        mov     rdi, rbx
        call    L2a30
        mov     rsi, rbx
        mov     rdi, r12
        call    L2770
        mov     rdi, r12
        call    L26b0
        mov     rdi, r12
        call    L28e0
        mov     rdi, r12
        call    L2700
        mov     rsi, QWORD PTR [rbp-0x9cf8]
        mov     edx, r13d
        mov     rdi, rbx
        call    L60b0
        mov     r14d, eax
        test    eax, eax
        jne     L8300
        mov     rsi, rbx
        mov     rdi, r12
        add     r13d, 0x1
        call    L62b0
        mov     rdi, r15
        mov     rsi, r12
        sub     r15, 0xffffffffffffff80
        call    L3280
        cmp     r13d, 0x6
        jne     L7f62
        lea     r13, [rbp-0x9c00]
        lea     r15, [rbp-0x9c90]
        mov     rdi, r13
        call    L1240
        mov     rsi, QWORD PTR [rbp-0x9d10]
        mov     rdi, r13
        mov     edx, 0x40
        call    L1280
        mov     rsi, QWORD PTR [rbp-0x9d00]
        mov     edx, 0x300
        mov     rdi, r13
        call    L1280
        mov     rdi, r13
        call    L1310
        mov     rdx, r13
        mov     esi, 0x30
        mov     rdi, r15
        call    L1360
        mov     rdi, r13
        call    L1400
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm1, xmm1
        mov     rdx, QWORD PTR [rbp-0x9d08]
        movdqa  xmm0, xmm1
L808e:
        movdqa  xmm2, XMMWORD PTR [rdx+rax*1]
        pxor    xmm2, XMMWORD PTR [r15+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x30
        jne     L808e
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    edx, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     rax
        sar     rax, 0x20
        xor     eax, edx
        cmp     al, dl
        jne     L8307
L812f:
        xor     r13d, r13d
        mov     rdi, rbx
        mov     ecx, 0x80
        mov     rax, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     rbx, QWORD PTR [rbp-0x9cd8]
        mov     edx, 0x7800
        xor     esi, esi
        mov     rdi, rbx
        call    L1030
        mov     rdi, QWORD PTR [rbp-0x9ce8]
        mov     rax, r13
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x9ce8]
        mov     rdi, QWORD PTR [rbp-0x9ce0]
        mov     ecx, 0x280
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x9ce0]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x9c90], xmm0
        movaps  XMMWORD PTR [rbp-0x9c80], xmm0
        movaps  XMMWORD PTR [rbp-0x9c70], xmm0
        mov     rax, QWORD PTR [rbp-0x9d08]
        movaps  XMMWORD PTR [rbp-0x9cd0], xmm0
        movaps  XMMWORD PTR [rbp-0x9cc0], xmm0
        movaps  XMMWORD PTR [rbp-0x9cb0], xmm0
        mov     rax, QWORD PTR [rbp-0x9d10]
        movaps  XMMWORD PTR [rbp-0x9c50], xmm0
        movaps  XMMWORD PTR [rbp-0x9c40], xmm0
        movaps  XMMWORD PTR [rbp-0x9c30], xmm0
        movaps  XMMWORD PTR [rbp-0x9c20], xmm0
        mov     rdi, QWORD PTR [rbp-0x9d00]
        mov     rax, r13
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x9d00]
        lea     rsp, [rbp-0x30]
        mov     eax, r14d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L8220:
        lea     rax, [rbp-0x7830]
        mov     QWORD PTR [rbp-0x9cf8], r11
        mov     rdi, rax
        mov     rbx, rax
        call    L1240
        mov     rsi, QWORD PTR [rbp-0x9cf0]
        mov     edx, 0x7a0
        mov     rdi, rbx
        call    L1280
        mov     rdi, rbx
        mov     QWORD PTR [rbp-0x9cd8], rbx
        lea     rbx, [rbp-0x9030]
        call    L1310
        mov     rdx, QWORD PTR [rbp-0x9cd8]
        mov     esi, 0x40
        mov     rdi, rbx
        call    L1360
        mov     rdi, QWORD PTR [rbp-0x9cd8]
        call    L1400
        mov     rdi, QWORD PTR [rbp-0x9cd8]
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x9cd8]
        mov     ecx, 0x40
        mov     r8, r14
        mov     rdx, rbx
        mov     esi, 0x40
        lea     rax, [rbp-0x9c50]
        mov     r9, QWORD PTR [rbp-0x9ce8]
        mov     QWORD PTR [rbp-0x9d10], rax
        mov     rdi, rax
        push    r15
        push    r12
        call    L7280
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x9030], xmm0
        movaps  XMMWORD PTR [rbp-0x9020], xmm0
        movaps  XMMWORD PTR [rbp-0x9010], xmm0
        movaps  XMMWORD PTR [rbp-0x9000], xmm0
        pop     rax
        mov     r11, QWORD PTR [rbp-0x9cf8]
        pop     rdx
        jmp     L7ef5
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L8300:
        lea     r15, [rbp-0x9c90]
L8307:
        mov     r14d, 0xfffffffa
        jmp     L812f
L8312:
        lea     rax, [rbp-0x7830]
        lea     rbx, [rbp-0x9030]
        mov     QWORD PTR [rbp-0x9cd8], rax
        lea     rax, [rbp-0x9c50]
        lea     r12, [rbp-0x9430]
        mov     QWORD PTR [rbp-0x9d10], rax
        lea     rax, [rbp-0x9cd0]
        lea     r15, [rbp-0x9c90]
        mov     QWORD PTR [rbp-0x9d08], rax
        lea     rax, [rbp-0x9830]
        mov     QWORD PTR [rbp-0x9ce8], rax
        lea     rax, [rbp-0x9b30]
        mov     QWORD PTR [rbp-0x9d00], rax
        jmp     L8307
        // nop
        .byte   0x90

// mldsa65_verify_extmu (0x8370)

L8370:
        sub     rsp, 0x10
        mov     r9, rdx
        xor     r8d, r8d
        xor     ecx, ecx
        push    0x1
        mov     edx, 0x40
        call    L7df0
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa65_prepare_domain_separation_prefix (0x8390)

L8390:
        xor     eax, eax
        cmp     r8, 0xff
        ja      L8400
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbp
        mov     rbp, r8
        sub     rsp, 0x18
        test    r9d, r9d
        jne     L83d8
        mov     BYTE PTR [rdi], 0x0
        mov     BYTE PTR [r12+0x1], r8b
        test    r8, r8
        jne     L84b8
L83c2:
        lea     rax, [rbp+0x2]
L83c6:
        add     rsp, 0x18
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L83d8:
        cmp     r9d, 0xc
        ja      L846e
        mov     r13, rdx
        mov     eax, r9d
        lea     rdx, [rip+Lc620]
        mov     r14, rsi
        movsxd  rax, DWORD PTR [rdx+rax*4]
        add     rax, rdx
        jmp     rax
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L8400:
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
        cmp     r13, 0x20
        jne     L846e
L840e:
        mov     BYTE PTR [r12], 0x1
        mov     BYTE PTR [r12+0x1], bpl
        test    rbp, rbp
        jne     L84d0
L8421:
        lea     rcx, [rip+Lc660]
        xor     eax, eax
        mov     rdx, rcx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L8430:
        cmp     r9d, DWORD PTR [rdx]
        je      L8498
        add     eax, 0x1
        add     rdx, 0x10
        cmp     eax, 0xc
        jne     L8430
L8441:
        lea     rdi, [r12+rbp*1+0xd]
        mov     rdx, r13
        mov     rsi, r14
        call    L1010
        add     rsp, 0x18
        lea     rax, [r13+rbp*1+0xd]
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
        cmp     r13, 0x1c
        je      L840e
L846e:
        xor     eax, eax
        jmp     L83c6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x40
        je      L840e
        xor     eax, eax
        jmp     L83c6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x30
        je      L840e
        xor     eax, eax
        jmp     L83c6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L8498:
        shl     rax, 0x4
        lea     rdx, [r12+rbp*1+0x2]
        lea     rax, [rcx+rax*1+0x4]
        mov     rcx, QWORD PTR [rax]
        mov     QWORD PTR [rdx], rcx
        mov     eax, DWORD PTR [rax+0x7]
        mov     DWORD PTR [rdx+0x7], eax
        jmp     L8441
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L84b8:
        lea     rdi, [rdi+0x2]
        mov     rdx, r8
        mov     rsi, rcx
        call    L1010
        jmp     L83c2
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L84d0:
        lea     rdi, [r12+0x2]
        mov     rdx, rbp
        mov     rsi, rcx
        mov     DWORD PTR [rsp+0xc], r9d
        call    L1010
        mov     r9d, DWORD PTR [rsp+0xc]
        jmp     L8421
        // nop
        .byte   0x90

// mldsa65_signature (0x84f0)

L84f0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        xor     r9d, r9d
        push    r14
        mov     r14, rdx
        xor     edx, edx
        push    r13
        push    r12
        lea     r12, [rbp-0x190]
        push    r10
        push    rbx
        mov     rbx, rdi
        mov     rdi, r12
        sub     rsp, 0x1a0
        mov     QWORD PTR [rbp-0x1b8], rsi
        xor     esi, esi
        call    L8390
        test    rax, rax
        mov     QWORD PTR [rbp-0x1c0], rax
        jne     L85c0
        mov     edx, 0xfffffff7
        lea     r13, [rbp-0x1b0]
L8551:
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        xor     eax, eax
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0xce5], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xced
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L857f:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x1b0], xmm0
        movaps  XMMWORD PTR [rbp-0x1a0], xmm0
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x30]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L85c0:
        lea     r13, [rbp-0x1b0]
        mov     esi, 0x20
        mov     rdi, r13
        call    L1020
        mov     edx, 0xfffffffd
        test    eax, eax
        jne     L8551
        push    0x0
        mov     r8, QWORD PTR [rbp-0x1c0]
        mov     rcx, r12
        mov     rdx, r14
        push    r15
        mov     rsi, QWORD PTR [rbp-0x1b8]
        mov     r9, r13
        mov     rdi, rbx
        call    L7720
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      L857f
        jmp     L8551
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_verify (0x8620)

L8620:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        xor     r9d, r9d
        push    r14
        mov     r14, rdx
        xor     edx, edx
        push    r13
        mov     r13, rsi
        xor     esi, esi
        push    r12
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x190]
        mov     rdi, rbx
        sub     rsp, 0x160
        call    L8390
        test    rax, rax
        je      L86b8
        sub     rsp, 0x8
        mov     rcx, rbx
        mov     rdx, r14
        mov     r8, rax
        push    0x0
        mov     r9, r15
        mov     rsi, r13
        mov     rdi, r12
        call    L7df0
        mov     edx, eax
        pop     rax
        pop     rcx
L868b:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x30]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L86b8:
        mov     edx, 0xfffffff7
        jmp     L868b
        // nop
        .byte   0x90

// mldsa65_signature_pre_hash_internal (0x86c0)

L86c0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r14
        push    r13
        mov     r13, r9
        push    r12
        lea     r12, [rbp-0x190]
        push    r10
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x168
        mov     r9d, DWORD PTR [r10+0x8]
        mov     r14, QWORD PTR [r10]
        test    r9d, r9d
        jne     L8758
L86fa:
        mov     edx, 0xfffffff7
L86ff:
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        xor     eax, eax
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0xce5], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xced
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L872d:
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x28]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L8758:
        mov     rdi, r12
        call    L8390
        test    rax, rax
        je      L86fa
        push    0x0
        xor     ecx, ecx
        mov     rdx, rax
        mov     r9, r13
        push    r14
        xor     r8d, r8d
        mov     rsi, r12
        mov     rdi, rbx
        call    L7720
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      L872d
        jmp     L86ff
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_signature_pre_hash_shake256 (0x8790)

L8790:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rcx
        mov     rcx, rdx
        mov     rdx, rsi
        push    r12
        mov     esi, 0x40
        push    r10
        push    rbx
        lea     rbx, [rbp-0x70]
        sub     rsp, 0x60
        mov     r12, QWORD PTR [r10]
        mov     QWORD PTR [rbp-0x78], rdi
        mov     rdi, rbx
        call    L1440
        push    0xc
        mov     rdi, QWORD PTR [rbp-0x78]
        mov     r9, r15
        push    r12
        mov     r8, r14
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        call    L86c0
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x70], xmm0
        movaps  XMMWORD PTR [rbp-0x60], xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        pop     rdx
        pop     rcx
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret

// mldsa65_verify_pre_hash_internal (0x8820)

L8820:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, r9
        push    r12
        push    r10
        push    rbx
        sub     rsp, 0x170
        mov     r9d, DWORD PTR [r10]
        test    r9d, r9d
        je      L88b0
        lea     rbx, [rbp-0x190]
        mov     r12, rdi
        mov     rdi, rbx
        call    L8390
        mov     rdx, rax
        test    rax, rax
        je      L88b7
        sub     rsp, 0x8
        xor     ecx, ecx
        mov     r9, r13
        xor     r8d, r8d
        push    0x0
        mov     rsi, rbx
        mov     rdi, r12
        call    L7df0
        mov     edx, eax
        pop     rax
        pop     rcx
L8881:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x20]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L88b0:
        lea     rbx, [rbp-0x190]
L88b7:
        mov     edx, 0xfffffff7
        jmp     L8881
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_verify_pre_hash_shake256 (0x88c0)

L88c0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rcx
        mov     rcx, rdx
        mov     rdx, rsi
        push    r12
        mov     esi, 0x40
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x70]
        mov     rdi, rbx
        sub     rsp, 0x40
        call    L1440
        sub     rsp, 0x8
        mov     r9, r15
        mov     r8, r14
        push    0xc
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        mov     rdi, r12
        call    L8820
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x70], xmm0
        movaps  XMMWORD PTR [rbp-0x60], xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        pop     rdx
        pop     rcx
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa65_pk_from_sk (0x8950)

L8950:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbx
        mov     rbx, rsi
        sub     rsi, 0xffffffffffffff80
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x22c0
        movdqu  xmm3, XMMWORD PTR [rsi-0x80]
        movdqu  xmm4, XMMWORD PTR [rsi-0x70]
        movdqu  xmm5, XMMWORD PTR [rsi-0x60]
        movdqu  xmm6, XMMWORD PTR [rsi-0x50]
        lea     r14, [rsp+0xec0]
        lea     r15, [rsp+0x100]
        movdqu  xmm7, XMMWORD PTR [rsi-0x40]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        movdqu  xmm3, XMMWORD PTR [rsi-0x30]
        mov     rdi, r14
        movaps  XMMWORD PTR [rsp+0x50], xmm4
        movdqu  xmm4, XMMWORD PTR [rsi-0x20]
        movaps  XMMWORD PTR [rsp+0x60], xmm5
        movdqu  xmm5, XMMWORD PTR [rsi-0x10]
        movaps  XMMWORD PTR [rsp+0x70], xmm6
        movaps  XMMWORD PTR [rsp+0x80], xmm7
        movaps  XMMWORD PTR [rsp+0x90], xmm3
        movaps  XMMWORD PTR [rsp+0xa0], xmm4
        movaps  XMMWORD PTR [rsp+0xb0], xmm5
        call    L6ea0
        mov     esi, 0x5
        mov     rdi, r14
        call    L6d10
        lea     rcx, [rbx+0x300]
        mov     rdx, r15
        mov     esi, 0x5
        mov     rdi, rcx
        mov     QWORD PTR [rsp+0x38], rcx
        mov     r13d, eax
        call    L6df0
        mov     rdi, r14
        mov     DWORD PTR [rsp+0x2c], eax
        call    L6c70
        movdqa  xmm6, XMMWORD PTR [rsp+0x40]
        movdqa  xmm7, XMMWORD PTR [rsp+0x50]
        lea     r9, [rsp+0x500]
        mov     rcx, QWORD PTR [rsp+0x38]
        lea     r8, [rsp+0x40]
        mov     rsi, r9
        mov     rdx, r14
        movups  XMMWORD PTR [r12], xmm6
        lea     rdi, [r12+0x20]
        movups  XMMWORD PTR [r12+0x10], xmm7
        mov     QWORD PTR [rsp+0x30], r8
        mov     QWORD PTR [rsp+0x38], r9
        call    L7160
        mov     r9, QWORD PTR [rsp+0x38]
        mov     r8, QWORD PTR [rsp+0x30]
        test    eax, eax
        mov     r11d, eax
        je      L8b50
        lea     rbx, [rsp+0xc0]
        lea     rdx, [rsp+0x80]
L8a86:
        lea     rdi, [r12+0x8]
        mov     rcx, r12
        xor     eax, eax
        mov     QWORD PTR [r12], 0x0
        mov     QWORD PTR [r12+0x798], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x7a0
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L8ab7:
        xor     eax, eax
        mov     rdi, r9
        mov     ecx, 0x138
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x280
        mov     rdi, r14
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        lea     rax, [rsp+0x60]
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0xc0], xmm0
        movaps  XMMWORD PTR [rsp+0xd0], xmm0
        movaps  XMMWORD PTR [rsp+0xe0], xmm0
        movaps  XMMWORD PTR [rsp+0xf0], xmm0
        movaps  XMMWORD PTR [rsp+0x80], xmm0
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0xa0], xmm0
        movaps  XMMWORD PTR [rsp+0xb0], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        lea     rsp, [rbp-0x28]
        mov     eax, r11d
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L8b50:
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L8b60:
        movdqu  xmm1, XMMWORD PTR [rbx+rax*1+0x600]
        pxor    xmm1, XMMWORD PTR [r9+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x9c0
        jne     L8b60
        movdqa  xmm1, xmm2
        mov     QWORD PTR [rsp+0x18], r9
        psrldq  xmm1, 0x8
        mov     QWORD PTR [rsp+0x20], r8
        pxor    xmm2, xmm1
        mov     DWORD PTR [rsp+0x30], r11d
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    edx, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     rax
        sar     rax, 0x20
        xor     eax, edx
        lea     rbx, [rsp+0xc0]
        xor     eax, edx
        mov     ecx, 0x7a0
        mov     rdx, r12
        mov     esi, 0x40
        mov     rdi, rbx
        mov     BYTE PTR [rsp+0x38], al
        call    L1440
        pxor    xmm1, xmm1
        mov     r9, QWORD PTR [rsp+0x18]
        xor     eax, eax
        mov     r8, QWORD PTR [rsp+0x20]
        mov     r11d, DWORD PTR [rsp+0x30]
        movdqa  xmm0, xmm1
        lea     rdx, [rsp+0x80]
L8c52:
        movdqa  xmm2, XMMWORD PTR [rbx+rax*1]
        pxor    xmm2, XMMWORD PTR [rdx+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x40
        jne     L8c52
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    esi, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    ecx, xmm0
        movzx   ecx, cl
        neg     rcx
        mov     rax, rcx
        sar     rax, 0x20
        xor     eax, esi
        or      r13b, BYTE PTR [rsp+0x2c]
        xor     eax, esi
        or      r13b, BYTE PTR [rsp+0x38]
        or      r13d, eax
        test    r13b, r13b
        je      L8ab7
        mov     r11d, 0xfffffff9
        jmp     L8a86

// mldsa87_unpack_pk_t1 (0x8d10)

L8d10:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x6
        lea     rsi, [rax+rsi*1+0x20]
        jmp     L2e10

// mldsa87_pack_sk_rho_key_tr (0x8d20)

L8d20:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rcx]
        movups  XMMWORD PTR [rdi+0x20], xmm2
        movdqu  xmm3, XMMWORD PTR [rcx+0x10]
        movups  XMMWORD PTR [rdi+0x30], xmm3
        movdqu  xmm4, XMMWORD PTR [rdx]
        movups  XMMWORD PTR [rdi+0x40], xmm4
        movdqu  xmm5, XMMWORD PTR [rdx+0x10]
        movups  XMMWORD PTR [rdi+0x50], xmm5
        movdqu  xmm6, XMMWORD PTR [rdx+0x20]
        movups  XMMWORD PTR [rdi+0x60], xmm6
        movdqu  xmm7, XMMWORD PTR [rdx+0x30]
        movups  XMMWORD PTR [rdi+0x70], xmm7
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_unpack_sk (0x8d70)

L8d70:
        push    r13
        mov     r13, rcx
        push    r12
        push    rbp
        mov     rbp, r8
        push    rbx
        mov     rbx, r9
        sub     rsp, 0x8
        mov     r12, QWORD PTR [rsp+0x30]
        movdqu  xmm0, XMMWORD PTR [r12]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [r12+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [r12+0x20]
        mov     rdi, r8
        movups  XMMWORD PTR [rdx], xmm2
        movdqu  xmm3, XMMWORD PTR [r12+0x30]
        movups  XMMWORD PTR [rdx+0x10], xmm3
        movdqu  xmm4, XMMWORD PTR [r12+0x40]
        movups  XMMWORD PTR [rsi], xmm4
        movdqu  xmm5, XMMWORD PTR [r12+0x50]
        movups  XMMWORD PTR [rsi+0x10], xmm5
        movdqu  xmm6, XMMWORD PTR [r12+0x60]
        movups  XMMWORD PTR [rsi+0x20], xmm6
        movdqu  xmm7, XMMWORD PTR [r12+0x70]
        movups  XMMWORD PTR [rsi+0x30], xmm7
        lea     rsi, [r12+0x80]
        call    L9df0
        mov     rdi, rbp
        mov     rbp, r13
        call    L9bb0
        lea     rsi, [r12+0x320]
        mov     rdi, rbx
        call    L9e70
        mov     rdi, rbx
        lea     rbx, [r12+0x620]
        add     r12, 0x1320
        call    L9ce0
        // xchg    ax, ax
        .byte   0x66,0x90
L8e20:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x1a0
        add     rbp, 0x400
        call    L3020
        cmp     rbx, r12
        jne     L8e20
        add     rsp, 0x8
        mov     rdi, r13
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        jmp     L9ce0

// mldsa87_pack_sig_c (0x8e50)

L8e50:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rsi+0x20]
        movups  XMMWORD PTR [rdi+0x20], xmm2
        movdqu  xmm3, XMMWORD PTR [rsi+0x30]
        movups  XMMWORD PTR [rdi+0x30], xmm3
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_pack_sig_h (0x8e80)

L8e80:
        push    r15
        lea     r15, [rdi+0x11c0]
        xor     eax, eax
        push    r14
        mov     r14, rsi
        push    r13
        mov     r13, rcx
        mov     rcx, r15
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rdi
        lea     rdi, [rdi+0x11c8]
        push    rbx
        add     rbp, 0x120b
        xor     ebx, ebx
        sub     rsp, 0x18
        mov     QWORD PTR [rdi-0x8], 0x0
        mov     QWORD PTR [rdi+0x43], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x53
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        lea     rax, [rdx+0x400]
        mov     QWORD PTR [rsp+0x8], rax
L8ee2:
        mov     rsi, r12
        mov     rdi, r13
        call    L3320
        xor     eax, eax
        jmp     L8f0d
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L8ef8:
        mov     ecx, ebx
        add     ebx, 0x1
        mov     BYTE PTR [r15+rcx*1], al
L8f01:
        add     rax, 0x1
        cmp     rax, 0x100
        je      L8f49
L8f0d:
        mov     ecx, DWORD PTR [r14+rax*4]
        mov     edi, DWORD PTR [r13+rax*4+0x0]
        lea     esi, [rcx+0x3ff00]
        cmp     esi, 0x7fe00
        ja      L8f30
        cmp     ecx, 0xfffc0100
        jne     L8f01
        test    edi, edi
        je      L8f01
L8f30:
        cmp     ebx, 0x4b
        jne     L8ef8
        mov     eax, 0xffffffff
L8f3a:
        add     rsp, 0x18
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
L8f49:
        mov     rax, QWORD PTR [rsp+0x8]
        sub     r12, 0xffffffffffffff80
        mov     BYTE PTR [rbp+0x0], bl
        add     rbp, 0x1
        add     r14, 0x400
        cmp     r12, rax
        jne     L8ee2
        xor     eax, eax
        jmp     L8f3a
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_pack_sig_z (0x8f70)

L8f70:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x7
        lea     rdi, [rax+rdi*1+0x40]
        jmp     L9840

// mldsa87_sig_unpack_hints (0x8f80)

L8f80:
        push    rbp
        mov     r11, rsi
        mov     r8, rdi
        mov     ebp, edx
        push    rbx
        lea     rbx, [rsi+0x11c0]
        xor     esi, esi
        test    edx, edx
        je      L8fa3
        lea     eax, [rdx+0x4a]
        movzx   esi, BYTE PTR [r11+rax*1+0x11c0]
L8fa3:
        lea     eax, [rbp+0x4b]
        movzx   r9d, BYTE PTR [r11+rax*1+0x11c0]
        mov     r10, r9
        cmp     r9d, esi
        jb      L9026
        cmp     r9d, 0x4b
        ja      L9026
        lea     rdi, [r8+0x8]
        mov     rcx, r8
        xor     eax, eax
        mov     QWORD PTR [r8], 0x0
        mov     QWORD PTR [r8+0x3f8], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x400
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        cmp     esi, r9d
        jae     L9030
        lea     edx, [rsi+0x11c0]
        mov     eax, esi
        add     rdx, r11
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L9000:
        movzx   ecx, BYTE PTR [rdx]
        add     rdx, 0x1
        mov     DWORD PTR [r8+rcx*4], 0x1
        mov     ecx, eax
        add     eax, 0x1
        cmp     eax, r9d
        jae     L9030
        cmp     esi, eax
        jae     L9000
        movzx   edi, BYTE PTR [rdx]
        cmp     BYTE PTR [rbx+rcx*1], dil
        jb      L9000
L9026:
        mov     eax, 0xffffffff
        pop     rbx
        pop     rbp
        ret
        // xchg    ax, ax
        .byte   0x66,0x90
L9030:
        cmp     ebp, 0x7
        je      L9040
L9035:
        xor     eax, eax
        pop     rbx
        pop     rbp
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L9040:
        cmp     r9d, 0x4b
        je      L9035
        cmp     BYTE PTR [r11+r10*1+0x11c0], 0x0
        jne     L9026
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L9058:
        add     r10, 0x1
        cmp     r10d, 0x4b
        je      L9035
        cmp     BYTE PTR [r11+r10*1+0x11c0], 0x0
        je      L9058
        jmp     L9026
        // nop
        .byte   0x90

// mld_rej_eta_c87.constprop.0 (0x9070)

L9070:
        mov     r8, rdi
        cmp     esi, 0xff
        ja      L9116
        mov     r9d, 0x1
        mov     r10d, 0x2
        sub     r9d, edx
        // xchg    ax, ax
        .byte   0x66,0x90
L9090:
        movzx   eax, BYTE PTR [rdx]
        mov     ecx, eax
        shr     al, 0x4
        and     ecx, 0xf
        movzx   eax, al
        cmp     cl, 0xf
        je      L90c5
        movzx   ecx, cl
        imul    edi, ecx, 0xcd
        shr     edi, 0xa
        lea     r11d, [rdi+rdi*4]
        mov     edi, esi
        add     esi, 0x1
        sub     ecx, r11d
        mov     r11d, r10d
        sub     r11d, ecx
        mov     DWORD PTR [r8+rdi*4], r11d
L90c5:
        cmp     esi, 0xff
        setbe   cl
        cmp     eax, 0xe
        ja      L90fe
        test    cl, cl
        je      L90fe
        imul    ecx, eax, 0xcd
        lea     edi, [rsi+0x1]
        mov     esi, esi
        shr     ecx, 0xa
        lea     ecx, [rcx+rcx*4]
        sub     eax, ecx
        mov     ecx, r10d
        sub     ecx, eax
        cmp     edi, 0xff
        mov     DWORD PTR [r8+rsi*4], ecx
        setbe   cl
        mov     esi, edi
L90fe:
        lea     eax, [r9+rdx*1]
        cmp     eax, 0x87
        setbe   al
        add     rdx, 0x1
        test    al, cl
        jne     L9090
L9116:
        mov     eax, esi
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa87_poly_decompose (0x9120)

L9120:
        xor     ecx, ecx
        mov     r8d, 0x3ff000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L9130:
        mov     edx, DWORD PTR [rsi+rcx*1]
        lea     eax, [rdx+0x7f]
        sar     eax, 0x7
        mov     r9d, eax
        shl     r9d, 0xa
        lea     eax, [rax+r9*1+0x200000]
        sar     eax, 0x16
        and     eax, 0xf
        mov     r9d, eax
        mov     DWORD PTR [rdi+rcx*1], eax
        shl     r9d, 0xa
        sub     eax, r9d
        shl     eax, 0x9
        add     eax, edx
        mov     edx, r8d
        sub     edx, eax
        movsxd  rdx, edx
        sar     rdx, 0x1f
        lea     r9d, [rax-0x7fe001]
        xor     r9d, eax
        and     edx, r9d
        xor     eax, edx
        mov     DWORD PTR [rsi+rcx*1], eax
        add     rcx, 0x4
        cmp     rcx, 0x400
        jne     L9130
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_poly_use_hint (0x9190)

L9190:
        mov     r8, rsi
        mov     r9d, 0x3ff000
        xor     esi, esi
        jmp     L91b6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L91a0:
        add     edx, 0x1
        and     edx, 0xf
L91a6:
        mov     DWORD PTR [rdi+rsi*1], edx
        add     rsi, 0x4
        cmp     rsi, 0x400
        je      L921d
L91b6:
        mov     r10d, DWORD PTR [rdi+rsi*1]
        lea     eax, [r10+0x7f]
        sar     eax, 0x7
        mov     edx, eax
        shl     edx, 0xa
        lea     edx, [rax+rdx*1+0x200000]
        sar     edx, 0x16
        and     edx, 0xf
        mov     eax, edx
        mov     ecx, edx
        shl     eax, 0xa
        sub     ecx, eax
        mov     eax, r9d
        shl     ecx, 0x9
        add     ecx, r10d
        sub     eax, ecx
        cdqe
        sar     rax, 0x1f
        mov     r10d, DWORD PTR [r8+rsi*1]
        test    r10d, r10d
        je      L91a6
        lea     r10d, [rcx-0x7fe001]
        xor     r10d, ecx
        and     eax, r10d
        xor     eax, ecx
        jg      L91a0
        sub     edx, 0x1
        and     edx, 0xf
        mov     DWORD PTR [rdi+rsi*1], edx
        add     rsi, 0x4
        cmp     rsi, 0x400
        jne     L91b6
L921d:
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_poly_uniform_eta_4x (0x9220)

L9220:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x780
        movdqu  xmm3, XMMWORD PTR [r8]
        movdqu  xmm2, XMMWORD PTR [r8+0x10]
        movdqu  xmm1, XMMWORD PTR [r8+0x20]
        movdqu  xmm0, XMMWORD PTR [r8+0x30]
        lea     r14, [rsp+0x60]
        mov     QWORD PTR [rsp+0x38], rsi
        movaps  XMMWORD PTR [rsp+0x60], xmm3
        lea     rbx, [rsp+0xc0]
        lea     r13, [rsp+0x120]
        movaps  XMMWORD PTR [rsp+0x70], xmm2
        lea     r12, [rsp+0x180]
        movaps  XMMWORD PTR [rsp+0x80], xmm1
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0xc0], xmm3
        movaps  XMMWORD PTR [rsp+0xd0], xmm2
        movaps  XMMWORD PTR [rsp+0xe0], xmm1
        movaps  XMMWORD PTR [rsp+0xf0], xmm0
        movaps  XMMWORD PTR [rsp+0x120], xmm3
        movaps  XMMWORD PTR [rsp+0x130], xmm2
        movaps  XMMWORD PTR [rsp+0x140], xmm1
        movaps  XMMWORD PTR [rsp+0x150], xmm0
        movaps  XMMWORD PTR [rsp+0x180], xmm3
        movaps  XMMWORD PTR [rsp+0x190], xmm2
        movaps  XMMWORD PTR [rsp+0x1a0], xmm1
        movaps  XMMWORD PTR [rsp+0x1b0], xmm0
        mov     QWORD PTR [rsp+0x30], rdx
        mov     QWORD PTR [rsp+0x28], rcx
        mov     QWORD PTR [rsp+0x40], rdi
        mov     QWORD PTR [rsp+0x18], r14
        mov     BYTE PTR [rsp+0xa0], r9b
        mov     eax, DWORD PTR [rbp+0x10]
        mov     BYTE PTR [rsp+0x100], al
        mov     eax, DWORD PTR [rbp+0x18]
        mov     BYTE PTR [rsp+0x160], al
        mov     eax, DWORD PTR [rbp+0x20]
        mov     BYTE PTR [rsp+0xa1], 0x0
        mov     BYTE PTR [rsp+0x1c0], al
        lea     rax, [rsp+0x460]
        mov     r15, rax
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x20], rax
        mov     BYTE PTR [rsp+0x101], 0x0
        mov     BYTE PTR [rsp+0x161], 0x0
        mov     BYTE PTR [rsp+0x1c1], 0x0
        call    L1850
        mov     r8, r12
        mov     rcx, r13
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r15
        mov     r9d, 0x42
        mov     rbx, r15
        call    L1750
        lea     r14, [rsp+0x1e0]
        lea     r11, [rsp+0x320]
        mov     r9, rbx
        mov     rdx, r11
        mov     r8d, 0x1
        mov     rdi, r14
        mov     rbx, r11
        lea     rax, [rsp+0x3c0]
        lea     r15, [rsp+0x280]
        mov     QWORD PTR [rsp+0x50], r11
        mov     rcx, rax
        mov     rsi, r15
        mov     QWORD PTR [rsp+0x58], rax
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x40]
        xor     esi, esi
        mov     rdx, r14
        call    L9070
        mov     rdi, QWORD PTR [rsp+0x38]
        xor     esi, esi
        mov     rdx, r15
        mov     r13d, eax
        call    L9070
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     rdx, rbx
        xor     esi, esi
        mov     r12d, eax
        call    L9070
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     rdi, QWORD PTR [rsp+0x28]
        xor     esi, esi
        mov     ebx, eax
        call    L9070
        cmp     r12d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r13d, 0xff
        jmp     L94a5
L9420:
        mov     r9, QWORD PTR [rsp+0x20]
        mov     rcx, QWORD PTR [rsp+0x58]
        mov     rsi, r15
        mov     rdi, r14
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     r8d, 0x1
        mov     DWORD PTR [rsp+0x4c], r10d
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x40]
        mov     esi, r13d
        mov     rdx, r14
        call    L9070
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     esi, r12d
        mov     rdx, r15
        mov     r13d, eax
        call    L9070
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     esi, ebx
        mov     r12d, eax
        call    L9070
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     esi, DWORD PTR [rsp+0x4c]
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     ebx, eax
        call    L9070
        cmp     r13d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r12d, 0xff
L94a5:
        setbe   dl
        or      eax, edx
        cmp     ebx, 0xff
        setbe   dl
        or      al, dl
        jne     L9420
        cmp     r10d, 0xff
        jbe     L9420
        mov     rdi, QWORD PTR [rsp+0x20]
        call    L1860
        xor     eax, eax
        mov     rdi, r14
        mov     ecx, 0x50
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x18]
        mov     ecx, 0x30
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x18]
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret

// mldsa87_poly_challenge (0x9500)

L9500:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        mov     r14, rdi
        push    r13
        push    r12
        push    rbx
        mov     rbx, rsi
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x180
        lea     r12, [rsp+0xb0]
        mov     rdi, r12
        call    L1240
        mov     rsi, rbx
        mov     edx, 0x40
        mov     rdi, r12
        call    L1280
        lea     rbx, [rsp+0x20]
        mov     rdi, r12
        call    L1310
        mov     esi, 0x88
        mov     rdi, rbx
        mov     rdx, r12
        call    L1360
        mov     rax, rbx
        lea     rdi, [rsp+0x28]
        xor     ecx, ecx
        xor     esi, esi
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L9570:
        movzx   edx, BYTE PTR [rax]
        add     rax, 0x1
        shl     rdx, cl
        add     ecx, 0x8
        or      rsi, rdx
        cmp     rax, rdi
        jne     L9570
        lea     rdi, [r14+0x8]
        mov     rcx, r14
        xor     eax, eax
        mov     QWORD PTR [rsp+0x18], rsi
        and     rdi, 0xfffffffffffffff8
        mov     QWORD PTR [r14], 0x0
        mov     r15d, 0xc4
        mov     r13d, 0x1
        mov     QWORD PTR [r14+0x3f8], 0x0
        sub     rcx, rdi
        add     ecx, 0x400
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x8
        jmp     L95df
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L95d0:
        mov     eax, ecx
L95d2:
        movzx   edx, BYTE PTR [rsp+rax*1+0x20]
        lea     ecx, [rax+0x1]
        cmp     r15d, edx
        jae     L960b
L95df:
        cmp     ecx, 0x88
        jne     L95d0
        mov     rdx, r12
        mov     esi, 0x88
        mov     rdi, rbx
        call    L1360
        movzx   edx, BYTE PTR [rsp+0x20]
        mov     eax, 0x1
        cmp     r15d, edx
        jb      L95d2
        mov     ecx, 0x1
L960b:
        mov     eax, DWORD PTR [r14+rdx*4]
        mov     edi, r13d
        mov     DWORD PTR [r14+r15*4], eax
        mov     rax, QWORD PTR [rsp+0x18]
        add     r15, 0x1
        mov     rsi, rax
        shr     rax, 1
        and     esi, 0x1
        mov     QWORD PTR [rsp+0x18], rax
        add     rsi, rsi
        sub     edi, esi
        mov     DWORD PTR [r14+rdx*4], edi
        cmp     r15, 0x100
        jne     L95df
        mov     rdi, r12
        call    L1400
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x11
        rep stos QWORD PTR es:[rdi], rax
        mov     QWORD PTR [rsp+0x18], 0x0
        lea     rax, [rsp+0x18]
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_polyeta_pack (0x9680)

L9680:
        push    r12
        mov     rax, rsi
        mov     r8, rdi
        lea     r9, [rsi+0x400]
        push    rbp
        mov     edx, 0x2
        push    rbx
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L96a0:
        mov     r11d, edx
        sub     r11b, BYTE PTR [rax+0x8]
        mov     r12d, edx
        sub     r12b, BYTE PTR [rax+0x4]
        mov     edi, r11d
        shl     r12d, 0x3
        mov     ebp, edx
        mov     esi, edx
        shl     edi, 0x6
        sub     bpl, BYTE PTR [rax+0xc]
        sub     sil, BYTE PTR [rax+0x10]
        mov     r10d, edx
        or      edi, r12d
        mov     r12d, edx
        sub     r12b, BYTE PTR [rax]
        sub     r10b, BYTE PTR [rax+0x14]
        or      edi, r12d
        mov     ebx, edx
        mov     ecx, edx
        sub     bl, BYTE PTR [rax+0x18]
        sub     cl, BYTE PTR [rax+0x1c]
        shl     esi, 0x4
        mov     BYTE PTR [r8], dil
        lea     edi, [rbp+rbp*1+0x0]
        or      esi, edi
        shr     r11b, 0x2
        mov     edi, r10d
        add     rax, 0x20
        shl     ebx, 0x2
        shl     ecx, 0x5
        or      esi, r11d
        add     r8, 0x3
        shl     edi, 0x7
        or      ecx, ebx
        shr     r10b, 1
        or      esi, edi
        or      ecx, r10d
        mov     BYTE PTR [r8-0x2], sil
        mov     BYTE PTR [r8-0x1], cl
        cmp     r9, rax
        jne     L96a0
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop
        .byte   0x90

// mldsa87_polyeta_unpack (0x9730)

L9730:
        push    r13
        mov     rax, rdi
        lea     r11, [rdi+0x400]
        mov     rdx, rsi
        push    r12
        mov     edi, 0x2
        push    rbp
        push    rbx
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L9750:
        movzx   r10d, BYTE PTR [rdx]
        mov     r13d, edi
        add     rax, 0x20
        add     rdx, 0x3
        and     r10d, 0x7
        mov     DWORD PTR [rax-0x20], r10d
        movzx   r9d, BYTE PTR [rdx-0x3]
        sub     r13d, r10d
        mov     r10d, edi
        shr     r9b, 0x3
        and     r9d, 0x7
        mov     DWORD PTR [rax-0x1c], r9d
        movzx   esi, BYTE PTR [rdx-0x3]
        sub     r10d, r9d
        mov     r9d, edi
        movzx   ecx, BYTE PTR [rdx-0x2]
        shr     sil, 0x6
        shl     ecx, 0x2
        movzx   esi, sil
        or      esi, ecx
        and     esi, 0x7
        mov     DWORD PTR [rax-0x18], esi
        movzx   ebp, BYTE PTR [rdx-0x2]
        sub     r9d, esi
        mov     esi, edi
        shr     bpl, 1
        and     ebp, 0x7
        mov     DWORD PTR [rax-0x14], ebp
        movzx   ebx, BYTE PTR [rdx-0x2]
        sub     esi, ebp
        shr     bl, 0x4
        and     ebx, 0x7
        mov     DWORD PTR [rax-0x10], ebx
        movzx   ecx, BYTE PTR [rdx-0x2]
        movzx   r8d, BYTE PTR [rdx-0x1]
        shr     cl, 0x7
        add     r8d, r8d
        movzx   ecx, cl
        or      ecx, r8d
        and     ecx, 0x7
        mov     DWORD PTR [rax-0xc], ecx
        movzx   r8d, BYTE PTR [rdx-0x1]
        shr     r8b, 0x2
        and     r8d, 0x7
        mov     DWORD PTR [rax-0x8], r8d
        movzx   r12d, BYTE PTR [rdx-0x1]
        mov     DWORD PTR [rax-0x14], esi
        mov     esi, edi
        sub     esi, ebx
        shr     r12b, 0x5
        mov     DWORD PTR [rax-0x20], r13d
        mov     DWORD PTR [rax-0x10], esi
        mov     esi, edi
        movzx   r12d, r12b
        sub     esi, ecx
        mov     ecx, edi
        mov     DWORD PTR [rax-0x1c], r10d
        sub     ecx, r8d
        mov     DWORD PTR [rax-0x18], r9d
        mov     DWORD PTR [rax-0x8], ecx
        mov     ecx, edi
        sub     ecx, r12d
        mov     DWORD PTR [rax-0xc], esi
        mov     DWORD PTR [rax-0x4], ecx
        cmp     r11, rax
        jne     L9750
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyz_pack (0x9840)

L9840:
        push    rbx
        mov     rax, rdi
        mov     r8d, 0x80000
        mov     rdi, rsi
        lea     r9, [rax+0x280]
        mov     rsi, rax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L9860:
        mov     ecx, r8d
        mov     edx, r8d
        sub     ecx, DWORD PTR [rdi]
        sub     edx, DWORD PTR [rdi+0x4]
        mov     eax, ecx
        mov     r10d, edx
        movzx   ebx, ch
        movzx   ecx, cl
        shr     eax, 0x10
        shl     r10d, 0x4
        add     rsi, 0x5
        add     rdi, 0x8
        or      r10d, eax
        mov     eax, edx
        shr     edx, 0xc
        shl     eax, 0x4
        movzx   r10d, r10b
        mov     BYTE PTR [rsi-0x1], dl
        and     eax, 0xff00
        or      eax, r10d
        shl     eax, 0x8
        or      eax, ebx
        shl     eax, 0x8
        or      eax, ecx
        mov     DWORD PTR [rsi-0x5], eax
        cmp     r9, rsi
        jne     L9860
        pop     rbx
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_polyz_unpack (0x98c0)

L98c0:
        mov     rax, rsi
        mov     rdx, rdi
        lea     r9, [rsi+0x280]
        mov     r8d, 0x80000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L98d8:
        movzx   ecx, BYTE PTR [rax]
        add     rax, 0x5
        add     rdx, 0x8
        mov     DWORD PTR [rdx-0x8], ecx
        movzx   esi, BYTE PTR [rax-0x4]
        shl     esi, 0x8
        or      esi, ecx
        mov     DWORD PTR [rdx-0x8], esi
        movzx   ecx, BYTE PTR [rax-0x3]
        shl     ecx, 0x10
        or      ecx, esi
        and     ecx, 0xfffff
        mov     DWORD PTR [rdx-0x8], ecx
        movzx   edi, BYTE PTR [rax-0x3]
        shr     dil, 0x4
        movzx   edi, dil
        mov     DWORD PTR [rdx-0x4], edi
        movzx   esi, BYTE PTR [rax-0x2]
        shl     esi, 0x4
        or      esi, edi
        mov     DWORD PTR [rdx-0x4], esi
        movzx   edi, BYTE PTR [rax-0x1]
        shl     edi, 0xc
        or      esi, edi
        mov     edi, r8d
        sub     edi, ecx
        mov     ecx, r8d
        sub     ecx, esi
        mov     DWORD PTR [rdx-0x8], edi
        mov     DWORD PTR [rdx-0x4], ecx
        cmp     r9, rax
        jne     L98d8
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_poly_uniform_gamma1_4x (0x9940)

L9940:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xfe0
        movdqu  xmm3, XMMWORD PTR [r8]
        movdqu  xmm2, XMMWORD PTR [r8+0x10]
        movdqu  xmm1, XMMWORD PTR [r8+0x20]
        movdqu  xmm0, XMMWORD PTR [r8+0x30]
        mov     QWORD PTR [rsp+0x30], rsi
        lea     r12, [rsp+0x1c0]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        lea     r13, [rsp+0xa0]
        lea     r14, [rsp+0x100]
        movaps  XMMWORD PTR [rsp+0x50], xmm2
        lea     r15, [rsp+0x160]
        lea     rbx, [rsp+0x40]
        movaps  XMMWORD PTR [rsp+0x60], xmm1
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0xa0], xmm3
        movaps  XMMWORD PTR [rsp+0xb0], xmm2
        movaps  XMMWORD PTR [rsp+0xc0], xmm1
        movaps  XMMWORD PTR [rsp+0xd0], xmm0
        movaps  XMMWORD PTR [rsp+0x100], xmm3
        movaps  XMMWORD PTR [rsp+0x110], xmm2
        movaps  XMMWORD PTR [rsp+0x120], xmm1
        movaps  XMMWORD PTR [rsp+0x130], xmm0
        movaps  XMMWORD PTR [rsp+0x160], xmm3
        movaps  XMMWORD PTR [rsp+0x170], xmm2
        movaps  XMMWORD PTR [rsp+0x180], xmm1
        movaps  XMMWORD PTR [rsp+0x190], xmm0
        mov     QWORD PTR [rsp+0x28], rdx
        mov     QWORD PTR [rsp+0x20], rcx
        mov     WORD PTR [rsp+0x80], r9w
        mov     QWORD PTR [rsp+0x38], rdi
        mov     eax, DWORD PTR [rbp+0x10]
        mov     rdi, r12
        mov     WORD PTR [rsp+0xe0], ax
        mov     eax, DWORD PTR [rbp+0x18]
        mov     WORD PTR [rsp+0x140], ax
        mov     eax, DWORD PTR [rbp+0x20]
        mov     WORD PTR [rsp+0x1a0], ax
        call    L1850
        mov     r8, r15
        mov     rcx, r14
        mov     rdx, r13
        mov     rsi, rbx
        mov     rdi, r12
        mov     r9d, 0x42
        call    L1750
        lea     r13, [rsp+0x4e0]
        lea     r11, [rsp+0x7a0]
        mov     r9, r12
        lea     r14, [rsp+0xd20]
        mov     rsi, r11
        mov     r8d, 0x5
        mov     rdi, r13
        lea     r15, [rsp+0xa60]
        mov     rcx, r14
        mov     QWORD PTR [rsp+0x18], r11
        mov     rdx, r15
        call    L17b0
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     rsi, r13
        call    L98c0
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, QWORD PTR [rsp+0x30]
        call    L98c0
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     rsi, r15
        call    L98c0
        mov     rdi, QWORD PTR [rsp+0x20]
        mov     rsi, r14
        call    L98c0
        mov     rdi, r12
        call    L1860
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x160
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x30
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_polyvecl_uniform_gamma1 (0x9b10)

L9b10:
        push    r13
        lea     r13, [rdi+0xc00]
        push    r12
        mov     r12, rsi
        mov     rcx, r13
        lea     rsi, [rdi+0x400]
        push    rbp
        mov     r8, r12
        mov     rbp, rdi
        push    rbx
        mov     ebx, edx
        lea     rdx, [rdi+0x800]
        lea     eax, [rbx+0x2]
        movzx   r9d, bx
        movzx   eax, ax
        sub     rsp, 0x10
        push    0xff
        push    rax
        lea     eax, [rbx+0x1]
        movzx   eax, ax
        push    rax
        call    L9940
        lea     eax, [rbx+0x6]
        add     rsp, 0x18
        lea     r9d, [rbx+0x3]
        movzx   eax, ax
        lea     rcx, [rbp+0x1800]
        mov     r8, r12
        mov     rdi, r13
        push    rax
        lea     eax, [rbx+0x5]
        add     ebx, 0x4
        movzx   r9d, r9w
        movzx   eax, ax
        movzx   ebx, bx
        lea     rdx, [rbp+0x1400]
        push    rax
        lea     rsi, [rbp+0x1000]
        push    rbx
        call    L9940
        add     rsp, 0x28
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyvecl_ntt (0x9bb0)

L9bb0:
        push    rbp
        lea     rbp, [rdi+0x1c00]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L9bc0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L27d0
        cmp     rbx, rbp
        jne     L9bc0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyvecl_pointwise_acc_montgomery (0x9be0)

L9be0:
        push    rbx
        mov     r9, rdx
        mov     r8, rsi
        xor     edx, edx
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L9bf0:
        xor     eax, eax
        lea     r11, [r8+rdx*1]
        lea     r10, [r9+rdx*1]
        xor     esi, esi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L9c00:
        movsxd  rcx, DWORD PTR [r11+rax*1]
        movsxd  rbx, DWORD PTR [r10+rax*1]
        add     rax, 0x400
        imul    rcx, rbx
        add     rsi, rcx
        cmp     rax, 0x1c00
        jne     L9c00
        imul    ecx, esi, 0x3802001
        movsxd  rcx, ecx
        mov     r10, rcx
        mov     rax, rcx
        shl     r10, 0xa
        sub     rax, r10
        shl     rax, 0xd
        sub     rax, rcx
        add     rax, rsi
        sar     rax, 0x20
        mov     DWORD PTR [rdi+rdx*1], eax
        add     rdx, 0x4
        cmp     rdx, 0x400
        jne     L9bf0
        pop     rbx
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_polyvecl_chknorm (0x9c60)

L9c60:
        push    r13
        lea     r13, [rdi+0x1c00]
        push    r12
        mov     r12d, esi
        push    rbp
        xor     ebp, ebp
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L9c80:
        mov     rdi, rbx
        mov     esi, r12d
        add     rbx, 0x400
        call    L31e0
        or      ebp, eax
        cmp     rbx, r13
        jne     L9c80
        add     rsp, 0x8
        mov     eax, ebp
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyveck_caddq (0x9cb0)

L9cb0:
        push    rbp
        lea     rbp, [rdi+0x2000]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L9cc0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L2700
        cmp     rbx, rbp
        jne     L9cc0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyveck_ntt (0x9ce0)

L9ce0:
        push    rbp
        lea     rbp, [rdi+0x2000]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L9cf0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L27d0
        cmp     rbx, rbp
        jne     L9cf0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyveck_invntt_tomont (0x9d10)

L9d10:
        push    rbp
        lea     rbp, [rdi+0x2000]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L9d20:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L28e0
        cmp     rbx, rbp
        jne     L9d20
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyveck_unpack_eta_chknorm (0x9d40)

L9d40:
        push    r14
        lea     r14, [rdi+0x300]
        push    r13
        mov     r13d, esi
        push    r12
        xor     r12d, r12d
        push    rbp
        mov     rbp, rdx
        push    rbx
        mov     rbx, rdi
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L9d60:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        call    L9730
        mov     esi, r13d
        mov     rdi, rbp
        call    L31e0
        or      r12d, eax
        cmp     rbx, r14
        jne     L9d60
        pop     rbx
        mov     eax, r12d
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_polyveck_decompose_pack_w1 (0x9d90)

L9d90:
        push    r13
        lea     r13, [rsi+0x2000]
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        sub     rsp, 0x8
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L9db0:
        mov     rsi, rbx
        mov     rdi, r12
        add     rbx, 0x400
        call    L9120
        mov     rdi, rbp
        mov     rsi, r12
        sub     rbp, 0xffffffffffffff80
        call    L3280
        cmp     rbx, r13
        jne     L9db0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_polyvecl_unpack_eta (0x9df0)

L9df0:
        push    r12
        lea     r12, [rsi+0x2a0]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L9e08:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        add     rbp, 0x400
        call    L9730
        cmp     rbx, r12
        jne     L9e08
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyvecl_unpack_z (0x9e30)

L9e30:
        push    r12
        lea     r12, [rsi+0x1180]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L9e48:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x280
        add     rbp, 0x400
        call    L98c0
        cmp     rbx, r12
        jne     L9e48
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyveck_unpack_eta (0x9e70)

L9e70:
        push    r12
        lea     r12, [rsi+0x300]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L9e88:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        add     rbp, 0x400
        call    L9730
        cmp     rbx, r12
        jne     L9e88
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyvec_matrix_expand_eager (0x9eb0)

L9eb0:
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdi
        push    r13
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x100
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm0, XMMWORD PTR [rsi+0x10]
        mov     rbx, rsp
        lea     r13, [rsp+0x100]
        mov     rax, rbx
L9ee0:
        movaps  XMMWORD PTR [rax], xmm1
        add     rax, 0x40
        movaps  XMMWORD PTR [rax-0x30], xmm0
        cmp     r13, rax
        jne     L9ee0
        xor     r12d, r12d
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L9ef8:
        mov     rsi, rbx
        mov     ecx, r12d
L9efe:
        mov     edx, ecx
        mov     eax, ecx
        mov     edi, ecx
        add     rsi, 0x40
        imul    rdx, rdx, 0x24924925
        add     ecx, 0x1
        shr     rdx, 0x20
        sub     eax, edx
        shr     eax, 1
        add     eax, edx
        shr     eax, 0x2
        lea     edx, [rax*8+0x0]
        mov     BYTE PTR [rsi-0x1f], al
        sub     edx, eax
        sub     edi, edx
        mov     BYTE PTR [rsi-0x20], dil
        cmp     r13, rsi
        jne     L9efe
        lea     edx, [r12+0x3]
        lea     esi, [r12+0x2]
        mov     r8, rdx
        imul    rdx, rdx, 0x24924925
        lea     edi, [r12+0x1]
        mov     eax, r8d
        shr     rdx, 0x20
        sub     eax, edx
        shr     eax, 1
        add     eax, edx
        shr     eax, 0x2
        mov     edx, eax
        lea     rcx, [rdx*8+0x0]
        sub     rcx, rdx
        lea     edx, [rax*8+0x0]
        sub     edx, eax
        mov     eax, esi
        sub     r8d, edx
        mov     edx, esi
        imul    rdx, rdx, 0x24924925
        add     rcx, r8
        shl     rcx, 0xa
        add     rcx, r14
        shr     rdx, 0x20
        sub     eax, edx
        shr     eax, 1
        add     eax, edx
        shr     eax, 0x2
        mov     r8d, eax
        lea     rdx, [r8*8+0x0]
        sub     rdx, r8
        lea     r8d, [rax*8+0x0]
        sub     r8d, eax
        mov     eax, edi
        sub     esi, r8d
        add     rdx, rsi
        mov     esi, edi
        imul    rsi, rsi, 0x24924925
        shl     rdx, 0xa
        add     rdx, r14
        shr     rsi, 0x20
        sub     eax, esi
        shr     eax, 1
        add     eax, esi
        shr     eax, 0x2
        mov     r8d, eax
        lea     rsi, [r8*8+0x0]
        sub     rsi, r8
        lea     r8d, [rax*8+0x0]
        sub     r8d, eax
        mov     eax, r12d
        sub     edi, r8d
        add     rsi, rdi
        mov     edi, r12d
        imul    rdi, rdi, 0x24924925
        shl     rsi, 0xa
        add     rsi, r14
        shr     rdi, 0x20
        sub     eax, edi
        shr     eax, 1
        add     eax, edi
        shr     eax, 0x2
        mov     r8d, eax
        lea     rdi, [r8*8+0x0]
        sub     rdi, r8
        lea     r8d, [rax*8+0x0]
        sub     r8d, eax
        mov     eax, r12d
        add     r12d, 0x4
        sub     eax, r8d
        mov     r8, rbx
        add     rdi, rax
        shl     rdi, 0xa
        add     rdi, r14
        call    L2ba0
        cmp     r12d, 0x38
        jne     L9ef8
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        lea     rsp, [rbp-0x20]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_polyvec_matrix_pointwise_montgomery_row_eager (0xa080)

La080:
        mov     ecx, ecx
        lea     rax, [rcx*8+0x0]
        sub     rax, rcx
        shl     rax, 0xa
        add     rsi, rax
        jmp     L9be0
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager (0xa0a0)

La0a0:
        push    r14
        mov     r14, rdi
        push    r13
        mov     r13, rsi
        mov     rsi, rdx
        push    r12
        mov     r12, rcx
        mov     ecx, 0x380
        push    rbp
        mov     rdi, r12
        mov     rbp, r14
        push    rbx
        xor     ebx, ebx
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rdi, r12
        call    L9bb0
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
La0d0:
        mov     ecx, ebx
        mov     rdi, rbp
        mov     rdx, r12
        mov     rsi, r13
        call    La080
        add     ebx, 0x1
        add     rbp, 0x400
        cmp     ebx, 0x8
        jne     La0d0
        pop     rbx
        mov     rdi, r14
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        jmp     L9d10
        // nop
        .byte   0x90

// mld_compute_pack_t0_t187 (0xa100)

La100:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rcx
        push    r14
        mov     r14, rdi
        push    r13
        mov     r13, rsi
        mov     rsi, r8
        push    r12
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0xe820
        lea     rax, [rsp+0x820]
        mov     QWORD PTR [rsp+0x8], rdx
        lea     rbx, [rsp+0x20]
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x10], rax
        lea     r12, [rsp+0x420]
        call    L9eb0
        xor     eax, eax
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
La150:
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     rsi, QWORD PTR [rsp+0x10]
        mov     ecx, eax
        mov     rdi, rbx
        mov     DWORD PTR [rsp+0x1c], eax
        call    La080
        mov     rdi, rbx
        call    L28e0
        mov     rsi, r15
        mov     rdi, r12
        add     r15, 0x60
        call    L9730
        mov     rsi, r12
        mov     rdi, rbx
        call    L2740
        mov     rdi, rbx
        call    L26b0
        mov     rdi, rbx
        call    L2700
        mov     rdx, rbx
        mov     rsi, rbx
        mov     rdi, r12
        call    L2a80
        mov     rdi, r14
        mov     rsi, r12
        add     r14, 0x140
        call    L2db0
        mov     rdi, r13
        mov     rsi, rbx
        add     r13, 0x1a0
        call    L2ea0
        mov     eax, DWORD PTR [rsp+0x1c]
        add     eax, 0x1
        cmp     eax, 0x8
        jne     La150
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rbx, QWORD PTR [rsp+0x10]
        mov     edx, 0xe000
        xor     esi, esi
        mov     rdi, rbx
        call    L1030
        lea     rsp, [rbp-0x28]
        xor     eax, eax
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mld_H87.constprop.0 (0xa220)

La220:
        push    r15
        mov     r15, r8
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, r9
        push    r12
        mov     r12, rsi
        push    rbp
        mov     rbp, rdi
        push    rbx
        sub     rsp, 0xe8
        lea     rbx, [rsp+0x10]
        mov     QWORD PTR [rsp+0x8], rdx
        mov     rdi, rbx
        call    L1240
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     rsi, r12
        mov     rdi, rbx
        call    L1280
        test    r15, r15
        jne     La2b8
        cmp     QWORD PTR [rsp+0x120], 0x0
        jne     La2d1
La272:
        mov     rdi, rbx
        call    L1310
        mov     rdx, rbx
        mov     esi, 0x40
        mov     rdi, rbp
        call    L1360
        mov     rdi, rbx
        call    L1400
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        add     rsp, 0xe8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
La2b8:
        mov     rdx, r15
        mov     rsi, r14
        mov     rdi, rbx
        call    L1280
        cmp     QWORD PTR [rsp+0x120], 0x0
        je      La272
La2d1:
        mov     rdx, QWORD PTR [rsp+0x120]
        mov     rsi, r13
        mov     rdi, rbx
        call    L1280
        jmp     La272
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_keypair_internal (0xa2f0)

La2f0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        mov     ecx, 0x22
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     r15, [rbp-0x1cb0]
        lea     r14, [rbp-0x1430]
        push    r13
        lea     r13, [rbp-0x1030]
        push    r12
        lea     r12, [rbp-0x1c30]
        push    r10
        push    rbx
        mov     rbx, rsi
        lea     rsi, [rbp-0x1d30]
        sub     rsp, 0x1d40
        movdqu  xmm1, XMMWORD PTR [rdx]
        movdqu  xmm2, XMMWORD PTR [rdx+0x10]
        mov     QWORD PTR [rbp-0x1d70], rdi
        movzx   eax, WORD PTR [rip+Lc608]
        mov     rdx, rsi
        mov     rdi, r15
        mov     QWORD PTR [rbp-0x1d58], rsi
        mov     esi, 0x80
        movaps  XMMWORD PTR [rbp-0x1d30], xmm1
        movaps  XMMWORD PTR [rbp-0x1d20], xmm2
        mov     WORD PTR [rbp-0x1d10], ax
        mov     QWORD PTR [rbp-0x1d40], r15
        lea     r15, [rbp-0x1830]
        call    L1440
        sub     rsp, 0x8
        mov     rcx, r13
        mov     rdx, r14
        lea     rax, [rbx+0x320]
        mov     r9d, 0xb
        mov     rsi, r15
        mov     rdi, r12
        mov     QWORD PTR [rbp-0x1d48], rax
        lea     rax, [rbp-0x1c90]
        push    0xe
        mov     r8, rax
        push    0xd
        push    0xc
        mov     QWORD PTR [rbp-0x1d38], rax
        call    L9220
        add     rsp, 0x20
        lea     rdi, [rbx+0x4a0]
        mov     rsi, r12
        call    L9680
        mov     rsi, r15
        lea     rdi, [rbx+0x500]
        call    L9680
        mov     rsi, r14
        lea     rdi, [rbx+0x560]
        call    L9680
        mov     rsi, r13
        lea     rdi, [rbx+0x5c0]
        call    L9680
        sub     rsp, 0x8
        mov     rcx, r13
        mov     rdx, r14
        push    0xa
        mov     r8, QWORD PTR [rbp-0x1d38]
        mov     rsi, r15
        mov     rdi, r12
        push    0x9
        mov     r9d, 0x7
        push    0x8
        call    L9220
        mov     rdi, QWORD PTR [rbp-0x1d48]
        add     rsp, 0x20
        mov     rsi, r12
        call    L9680
        mov     rsi, r15
        lea     rdi, [rbx+0x380]
        call    L9680
        mov     rsi, r14
        lea     rdi, [rbx+0x3e0]
        call    L9680
        mov     rsi, r13
        lea     rdi, [rbx+0x440]
        call    L9680
        sub     rsp, 0x8
        mov     rcx, r12
        lea     rax, [rbp-0x430]
        push    0xff
        mov     rdx, rax
        mov     r9d, 0x4
        lea     r11, [rbp-0x830]
        push    0x6
        lea     r10, [rbp-0xc30]
        mov     r8, QWORD PTR [rbp-0x1d38]
        mov     rsi, r11
        push    0x5
        mov     rdi, r10
        mov     QWORD PTR [rbp-0x1d68], rax
        mov     QWORD PTR [rbp-0x1d60], r11
        mov     QWORD PTR [rbp-0x1d50], r10
        call    L9220
        mov     rsi, QWORD PTR [rbp-0x1d50]
        add     rsp, 0x20
        lea     rdi, [rbx+0x200]
        call    L9680
        mov     rsi, QWORD PTR [rbp-0x1d60]
        lea     rdi, [rbx+0x260]
        call    L9680
        mov     rsi, QWORD PTR [rbp-0x1d68]
        lea     rdi, [rbx+0x2c0]
        call    L9680
        sub     rsp, 0x8
        mov     rcx, r13
        mov     rdx, r14
        push    0x3
        mov     r8, QWORD PTR [rbp-0x1d38]
        xor     r9d, r9d
        mov     rsi, r15
        push    0x2
        mov     rdi, r12
        push    0x1
        call    L9220
        add     rsp, 0x20
        lea     rdi, [rbx+0x80]
        mov     rsi, r12
        call    L9680
        mov     rsi, r15
        lea     rdi, [rbx+0xe0]
        call    L9680
        mov     rsi, r14
        lea     rdi, [rbx+0x140]
        lea     r14, [rbp-0x1cf0]
        call    L9680
        mov     rsi, r13
        lea     rdi, [rbx+0x1a0]
        call    L9680
        mov     rdi, r12
        call    L9bb0
        mov     r10, QWORD PTR [rbp-0x1d70]
        mov     rdx, r12
        movdqa  xmm3, XMMWORD PTR [rbp-0x1cb0]
        movdqa  xmm4, XMMWORD PTR [rbp-0x1ca0]
        mov     r15, QWORD PTR [rbp-0x1d40]
        lea     rsi, [rbx+0x620]
        mov     rcx, QWORD PTR [rbp-0x1d48]
        movups  XMMWORD PTR [r10], xmm3
        lea     rdi, [r10+0x20]
        movups  XMMWORD PTR [r10+0x10], xmm4
        mov     r8, r15
        mov     QWORD PTR [rbp-0x1d38], r10
        call    La100
        mov     r10, QWORD PTR [rbp-0x1d38]
        test    eax, eax
        mov     r13d, eax
        jne     La607
        mov     rdx, r10
        mov     ecx, 0xa20
        mov     esi, 0x40
        mov     rdi, r14
        call    L1440
        mov     rdx, r14
        mov     rsi, r15
        mov     rdi, rbx
        lea     rcx, [rbp-0x1c50]
        call    L8d20
        mov     r10, QWORD PTR [rbp-0x1d38]
La607:
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x380
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x1cf0], xmm0
        movaps  XMMWORD PTR [rbp-0x1ce0], xmm0
        movaps  XMMWORD PTR [rbp-0x1cd0], xmm0
        movaps  XMMWORD PTR [rbp-0x1cc0], xmm0
        xor     edx, edx
        movaps  XMMWORD PTR [rbp-0x1d30], xmm0
        mov     WORD PTR [rbp-0x1d10], dx
        mov     rdx, QWORD PTR [rbp-0x1d58]
        movaps  XMMWORD PTR [rbp-0x1d20], xmm0
        mov     rdi, QWORD PTR [rbp-0x1d40]
        mov     ecx, 0x10
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1d40]
        test    r13d, r13d
        jne     La688
La66d:
        lea     rsp, [rbp-0x30]
        mov     eax, r13d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
La688:
        lea     rdi, [r10+0x8]
        mov     rcx, r10
        mov     QWORD PTR [r10], 0x0
        mov     QWORD PTR [r10+0xa18], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xa20
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x1318], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x1320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        jmp     La66d
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_keypair (0xa6f0)

La6f0:
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x20
        mov     rbx, rsp
        mov     rdi, rbx
        call    L1020
        test    eax, eax
        jne     La748
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    La2f0
La729:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp], xmm0
        movaps  XMMWORD PTR [rsp+0x10], xmm0
        lea     rsp, [rbp-0x18]
        pop     rbx
        pop     r12
        pop     r13
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
La748:
        mov     eax, 0xfffffffd
        jmp     La729
        // nop
        .byte   0x90

// mldsa87_signature_internal (0xa750)

La750:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     rax, [rbp-0x19430]
        lea     r15, [rbp-0x1a110]
        push    r13
        lea     r13, [rbp-0x1a0d0]
        push    r12
        mov     r12, rsi
        lea     rsi, [rbp-0x14030]
        push    r10
        push    rbx
        mov     rbx, r9
        lea     r9, [rbp-0x12030]
        sub     rsp, 0x1a1c8
        mov     QWORD PTR [rbp-0x1a1a8], rdi
        lea     rdi, [rbp-0x1a130]
        mov     r14d, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x1a178], rdx
        mov     rdx, r13
        mov     QWORD PTR [rbp-0x1a180], rcx
        mov     rcx, rsi
        mov     QWORD PTR [rbp-0x1a188], r8
        mov     r8, rax
        mov     QWORD PTR [rbp-0x1a1c8], rsi
        mov     rsi, r15
        mov     QWORD PTR [rbp-0x1a1f0], rdi
        mov     QWORD PTR [rbp-0x1a1b8], r9
        mov     QWORD PTR [rbp-0x1a1a0], rax
        push    QWORD PTR [r10]
        call    L8d70
        pop     rdi
        pop     r8
        test    r14d, r14d
        jne     Lad3f
        sub     rsp, 0x8
        mov     rsi, r15
        mov     r9, r12
        mov     edx, 0x40
        lea     rax, [rbp-0x1a0b0]
        mov     rcx, QWORD PTR [rbp-0x1a180]
        mov     r8, QWORD PTR [rbp-0x1a188]
        mov     QWORD PTR [rbp-0x1a1d8], rax
        mov     rdi, rax
        push    QWORD PTR [rbp-0x1a178]
        call    La220
        pop     rcx
        pop     rsi
La83a:
        sub     rsp, 0x8
        mov     rcx, rbx
        mov     edx, 0x20
        mov     rsi, r13
        lea     rax, [rbp-0x1a070]
        mov     r9, QWORD PTR [rbp-0x1a1d8]
        mov     r8d, 0x20
        lea     rbx, [rbp-0x15c30]
        mov     QWORD PTR [rbp-0x1a1e8], rax
        mov     rdi, rax
        lea     r15, [rbp-0x19830]
        lea     r14, [rbp-0x19c30]
        push    0x40
        mov     r12, r15
        call    La220
        lea     rax, [rbp-0xe030]
        mov     rsi, QWORD PTR [rbp-0x1a1f0]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x1a1e0], rax
        call    L9eb0
        pop     rax
        lea     rax, [rbp-0x17830]
        pop     rdx
        mov     QWORD PTR [rbp-0x1a188], rax
        lea     rax, [rbp-0x10030]
        mov     QWORD PTR [rbp-0x1a198], rax
        lea     rax, [rbp-0x1a030]
        mov     QWORD PTR [rbp-0x1a1c0], rax
        lea     rax, [rbp-0x1a170]
        mov     DWORD PTR [rbp-0x1a1ac], 0x0
        mov     QWORD PTR [rbp-0x1a178], rbx
        mov     QWORD PTR [rbp-0x1a1d0], rax
        // xchg    ax, ax
        .byte   0x66,0x90
La8f0:
        mov     r13, QWORD PTR [rbp-0x1a188]
        mov     edx, DWORD PTR [rbp-0x1a1ac]
        mov     rsi, QWORD PTR [rbp-0x1a1e8]
        mov     rdi, r13
        call    L9b10
        mov     rdx, r13
        mov     r13, QWORD PTR [rbp-0x1a198]
        mov     rcx, QWORD PTR [rbp-0x1a178]
        mov     rsi, QWORD PTR [rbp-0x1a1e0]
        mov     rdi, r13
        call    La0a0
        mov     rdi, r13
        call    L9cb0
        mov     rsi, r13
        mov     r13, QWORD PTR [rbp-0x1a1c0]
        mov     rdx, QWORD PTR [rbp-0x1a178]
        mov     rdi, r13
        call    L9d90
        mov     rdi, r15
        call    L1240
        mov     rsi, QWORD PTR [rbp-0x1a1d8]
        mov     rdi, r15
        mov     edx, 0x40
        call    L1280
        mov     rsi, r13
        mov     edx, 0x400
        mov     rdi, r15
        call    L1280
        mov     rdi, r15
        call    L1310
        mov     r13, QWORD PTR [rbp-0x1a1d0]
        mov     rdx, r15
        mov     esi, 0x40
        mov     rdi, r13
        call    L1360
        mov     rdi, r15
        call    L1400
        mov     rdi, r15
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rsi, r13
        mov     rdi, r14
        xor     r13d, r13d
        call    L9500
        mov     rdi, r14
        call    L27d0
        mov     QWORD PTR [rbp-0x1a190], r14
        mov     r14, r13
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
La9d0:
        mov     rax, QWORD PTR [rbp-0x1a1a0]
        mov     r13, r14
        mov     rdi, r15
        mov     ecx, 0x80
        shl     r13, 0xa
        mov     DWORD PTR [rbp-0x1a180], r14d
        mov     r15, r12
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, QWORD PTR [rbp-0x1a190]
        mov     rdi, r12
        call    L2a30
        mov     rdi, r12
        call    L28e0
        mov     rax, QWORD PTR [rbp-0x1a188]
        mov     ecx, 0x80
        mov     rdi, QWORD PTR [rbp-0x1a178]
        mov     QWORD PTR [rbp-0x1a178], rbx
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, rbx
        mov     rdi, r12
        call    L2740
        mov     rdi, r12
        call    L26b0
        mov     esi, 0x7ff88
        mov     rdi, r12
        call    L31e0
        test    eax, eax
        jne     Lad10
        mov     edx, DWORD PTR [rbp-0x1a180]
        mov     rdi, QWORD PTR [rbp-0x1a1a8]
        mov     rsi, r12
        add     r14, 0x1
        call    L8f70
        cmp     r14, 0x7
        jne     La9d0
        mov     r14, QWORD PTR [rbp-0x1a190]
        mov     QWORD PTR [rbp-0x1a180], r12
        xor     r13d, r13d
        mov     QWORD PTR [rbp-0x1a190], r12
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Laa98:
        mov     rax, QWORD PTR [rbp-0x1a1b8]
        mov     ecx, 0x80
        mov     rdi, rbx
        mov     r12, rbx
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, r14
        mov     rdi, rbx
        call    L2a30
        mov     rdi, rbx
        call    L28e0
        mov     rax, QWORD PTR [rbp-0x1a198]
        mov     rsi, rbx
        lea     r15, [rax+r13*1]
        mov     rdi, r15
        call    L2770
        mov     rdi, r15
        call    L26b0
        mov     esi, 0x3fe88
        mov     rdi, r15
        call    L31e0
        test    eax, eax
        jne     Lad28
        mov     rax, QWORD PTR [rbp-0x1a1c8]
        mov     ecx, 0x80
        mov     rdi, rbx
        lea     rsi, [rax+r13*1]
        rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
        mov     rsi, r14
        mov     rdi, rbx
        call    L2a30
        mov     rdi, rbx
        call    L28e0
        mov     rdi, rbx
        call    L26b0
        mov     esi, 0x3ff00
        mov     rdi, rbx
        call    L31e0
        test    eax, eax
        jne     Lad28
        mov     rsi, rbx
        mov     rdi, r15
        add     r13, 0x400
        call    L2740
        cmp     r13, 0x2000
        jne     Laa98
        mov     r13, QWORD PTR [rbp-0x1a1a8]
        mov     rsi, QWORD PTR [rbp-0x1a1d0]
        mov     QWORD PTR [rbp-0x1a178], rbx
        mov     r15, QWORD PTR [rbp-0x1a180]
        mov     r12, QWORD PTR [rbp-0x1a190]
        mov     rdi, r13
        call    L8e50
        mov     rdx, QWORD PTR [rbp-0x1a1c0]
        mov     rdi, r13
        mov     rcx, rbx
        mov     rsi, QWORD PTR [rbp-0x1a198]
        call    L8e80
        mov     r13d, eax
Laba3:
        mov     rdi, r12
        xor     eax, eax
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r14
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a198]
        mov     ecx, 0x400
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a198]
        mov     rdi, QWORD PTR [rbp-0x1a1c0]
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a1c0]
        mov     ecx, 0x380
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a188]
        mov     ecx, 0x380
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a188]
        mov     rax, QWORD PTR [rbp-0x1a1d0]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rax], xmm0
        movaps  XMMWORD PTR [rax+0x10], xmm0
        movaps  XMMWORD PTR [rax+0x20], xmm0
        movaps  XMMWORD PTR [rax+0x30], xmm0
        test    r13d, r13d
        je      Lac80
        cmp     r13d, 0xffffffff
        jne     Lac4b
        add     DWORD PTR [rbp-0x1a1ac], 0x7
        mov     eax, DWORD PTR [rbp-0x1a1ac]
        cmp     eax, 0xfff7
        jne     La8f0
        mov     r13d, 0xfffffffc
Lac4b:
        mov     rdx, QWORD PTR [rbp-0x1a1a8]
        xor     eax, eax
        lea     rdi, [rdx+0x8]
        mov     rcx, rdx
        mov     QWORD PTR [rdx], 0x0
        mov     QWORD PTR [rdx+0x120b], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x1213
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
Lac80:
        mov     rdi, QWORD PTR [rbp-0x1a1b8]
        xor     ebx, ebx
        mov     ecx, 0x400
        mov     rax, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a1b8]
        mov     rdi, QWORD PTR [rbp-0x1a1c8]
        mov     ecx, 0x400
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a1c8]
        mov     rdi, QWORD PTR [rbp-0x1a1a0]
        mov     ecx, 0x380
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a1a0]
        mov     r14, QWORD PTR [rbp-0x1a1e0]
        mov     edx, 0xe000
        xor     esi, esi
        mov     rdi, r14
        call    L1030
        mov     rdi, QWORD PTR [rbp-0x1a1f0]
        mov     rax, rbx
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x1a1f0]
        lea     rsp, [rbp-0x30]
        mov     eax, r13d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // xchg    ax, ax
        .byte   0x66,0x90
Lad10:
        mov     r14, QWORD PTR [rbp-0x1a190]
Lad17:
        mov     r13d, 0xffffffff
        jmp     Laba3
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Lad28:
        mov     QWORD PTR [rbp-0x1a178], r12
        mov     r15, QWORD PTR [rbp-0x1a180]
        mov     r12, QWORD PTR [rbp-0x1a190]
        jmp     Lad17
Lad3f:
        movdqu  xmm1, XMMWORD PTR [r12]
        movdqu  xmm2, XMMWORD PTR [r12+0x10]
        lea     rax, [rbp-0x1a0b0]
        movdqu  xmm3, XMMWORD PTR [r12+0x20]
        movdqu  xmm4, XMMWORD PTR [r12+0x30]
        mov     QWORD PTR [rbp-0x1a1d8], rax
        movaps  XMMWORD PTR [rbp-0x1a0b0], xmm1
        movaps  XMMWORD PTR [rbp-0x1a0a0], xmm2
        movaps  XMMWORD PTR [rbp-0x1a090], xmm3
        movaps  XMMWORD PTR [rbp-0x1a080], xmm4
        jmp     La83a
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa87_signature_extmu (0xad90)

Lad90:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r14
        mov     r14, rdx
        push    r13
        mov     r13, rsi
        mov     esi, 0x20
        push    r12
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x50]
        mov     rdi, rbx
        sub     rsp, 0x28
        call    L1020
        test    eax, eax
        jne     Lae10
        push    0x1
        xor     ecx, ecx
        mov     edx, 0x40
        mov     r9, rbx
        push    r14
        xor     r8d, r8d
        mov     rsi, r13
        mov     rdi, r12
        call    La750
        pop     rdx
        pop     rcx
Ladea:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
Lae10:
        mov     eax, 0xfffffffd
        jmp     Ladea
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_verify_internal (0xae20)

Lae20:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rcx
        push    r14
        lea     rax, [rbp-0xfc30]
        mov     r14, rsi
        lea     rsi, [rdi+0x40]
        push    r13
        mov     r13, rax
        push    r12
        mov     r12, rdx
        push    r10
        push    rbx
        sub     rsp, 0x10de0
        movdqu  xmm3, XMMWORD PTR [rdi]
        mov     ebx, DWORD PTR [r10]
        mov     QWORD PTR [rbp-0x10dd8], rdi
        movdqu  xmm4, XMMWORD PTR [rdi+0x10]
        movdqu  xmm5, XMMWORD PTR [rdi+0x20]
        mov     QWORD PTR [rbp-0x10de8], r8
        movdqu  xmm6, XMMWORD PTR [rdi+0x30]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x10df0], r9
        mov     QWORD PTR [rbp-0x10de0], rax
        movaps  XMMWORD PTR [rbp-0x10d90], xmm3
        movaps  XMMWORD PTR [rbp-0x10d80], xmm4
        movaps  XMMWORD PTR [rbp-0x10d70], xmm5
        movaps  XMMWORD PTR [rbp-0x10d60], xmm6
        call    L9e30
        mov     esi, 0x7ff88
        mov     rdi, r13
        call    L9c60
        mov     r11, QWORD PTR [rbp-0x10dd8]
        test    eax, eax
        jne     Lb379
        mov     r13d, eax
        test    ebx, ebx
        je      Lb280
        movdqu  xmm7, XMMWORD PTR [r14]
        lea     rax, [rbp-0xe030]
        movdqu  xmm3, XMMWORD PTR [r14+0x20]
        lea     rbx, [rbp-0x10030]
        mov     QWORD PTR [rbp-0x10dd8], rax
        lea     rax, [rbp-0x10dd0]
        movdqu  xmm4, XMMWORD PTR [r14+0x30]
        movaps  XMMWORD PTR [rbp-0x10dd0], xmm7
        movdqu  xmm7, XMMWORD PTR [r14+0x10]
        mov     QWORD PTR [rbp-0x10e08], rax
        movaps  XMMWORD PTR [rbp-0x10dc0], xmm7
        movaps  XMMWORD PTR [rbp-0x10db0], xmm3
        movaps  XMMWORD PTR [rbp-0x10da0], xmm4
Laf2d:
        mov     rdi, QWORD PTR [rbp-0x10de0]
        mov     QWORD PTR [rbp-0x10df8], r11
        lea     r12, [rbp-0x10430]
        call    L9bb0
        mov     rsi, QWORD PTR [rbp-0x10df0]
        mov     rdi, QWORD PTR [rbp-0x10dd8]
        call    L9eb0
        lea     rax, [rbp-0x10830]
        lea     r8, [rbp-0x10d90]
        mov     r14, rax
        mov     rdi, rax
        mov     rsi, r8
        mov     QWORD PTR [rbp-0x10de8], rax
        mov     QWORD PTR [rbp-0x10e10], r8
        call    L9500
        mov     rdi, r14
        call    L27d0
        lea     rax, [rbp-0x10c30]
        mov     QWORD PTR [rbp-0x10e00], rax
        mov     r15, rax
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
Lafa0:
        mov     rdx, QWORD PTR [rbp-0x10de0]
        mov     rsi, QWORD PTR [rbp-0x10dd8]
        mov     ecx, r13d
        mov     rdi, r12
        call    La080
        mov     rsi, QWORD PTR [rbp-0x10df0]
        mov     edx, r13d
        mov     rdi, rbx
        call    L8d10
        mov     rdi, rbx
        call    L27a0
        mov     rdi, rbx
        call    L27d0
        mov     rsi, QWORD PTR [rbp-0x10de8]
        mov     rdi, rbx
        call    L2a30
        mov     rsi, rbx
        mov     rdi, r12
        call    L2770
        mov     rdi, r12
        call    L26b0
        mov     rdi, r12
        call    L28e0
        mov     rdi, r12
        call    L2700
        mov     rsi, QWORD PTR [rbp-0x10df8]
        mov     edx, r13d
        mov     rdi, rbx
        call    L8f80
        mov     r14d, eax
        test    eax, eax
        jne     Lb360
        mov     rsi, rbx
        mov     rdi, r12
        add     r13d, 0x1
        call    L9190
        mov     rdi, r15
        mov     rsi, r12
        sub     r15, 0xffffffffffffff80
        call    L3280
        cmp     r13d, 0x8
        jne     Lafa0
        mov     r8, QWORD PTR [rbp-0x10e10]
        lea     r13, [rbp-0x10d00]
        lea     r15, [rbp-0x10d50]
        mov     rdi, r13
        mov     QWORD PTR [rbp-0x10df0], r8
        call    L1240
        mov     rsi, QWORD PTR [rbp-0x10e08]
        mov     rdi, r13
        mov     edx, 0x40
        call    L1280
        mov     rsi, QWORD PTR [rbp-0x10e00]
        mov     edx, 0x400
        mov     rdi, r13
        call    L1280
        mov     rdi, r13
        call    L1310
        mov     rdx, r13
        mov     esi, 0x40
        mov     rdi, r15
        call    L1360
        mov     rdi, r13
        call    L1400
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm1, xmm1
        mov     r8, QWORD PTR [rbp-0x10df0]
        movdqa  xmm0, xmm1
Lb0da:
        movdqa  xmm2, XMMWORD PTR [r8+rax*1]
        pxor    xmm2, XMMWORD PTR [r15+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x40
        jne     Lb0da
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    edx, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     rax
        sar     rax, 0x20
        xor     eax, edx
        cmp     al, dl
        jne     Lb36e
Lb17c:
        xor     r13d, r13d
        mov     rdi, rbx
        mov     ecx, 0x80
        mov     QWORD PTR [rbp-0x10df0], r8
        mov     rax, r13
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     rbx, QWORD PTR [rbp-0x10dd8]
        mov     edx, 0xe000
        xor     esi, esi
        mov     rdi, rbx
        call    L1030
        mov     rdi, QWORD PTR [rbp-0x10de8]
        mov     rax, r13
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x10de8]
        mov     rdi, QWORD PTR [rbp-0x10de0]
        mov     ecx, 0x380
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x10de0]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x10d50], xmm0
        movaps  XMMWORD PTR [rbp-0x10d40], xmm0
        movaps  XMMWORD PTR [rbp-0x10d30], xmm0
        movaps  XMMWORD PTR [rbp-0x10d20], xmm0
        mov     r8, QWORD PTR [rbp-0x10df0]
        movaps  XMMWORD PTR [rbp-0x10d90], xmm0
        movaps  XMMWORD PTR [rbp-0x10d80], xmm0
        movaps  XMMWORD PTR [rbp-0x10d70], xmm0
        movaps  XMMWORD PTR [rbp-0x10d60], xmm0
        mov     rax, QWORD PTR [rbp-0x10e08]
        movaps  XMMWORD PTR [rbp-0x10dd0], xmm0
        movaps  XMMWORD PTR [rbp-0x10dc0], xmm0
        movaps  XMMWORD PTR [rbp-0x10db0], xmm0
        movaps  XMMWORD PTR [rbp-0x10da0], xmm0
        mov     rdi, QWORD PTR [rbp-0x10e00]
        mov     rax, r13
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x10e00]
        lea     rsp, [rbp-0x30]
        mov     eax, r14d
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
Lb280:
        lea     rax, [rbp-0xe030]
        mov     QWORD PTR [rbp-0x10df8], r11
        mov     rdi, rax
        mov     rbx, rax
        call    L1240
        mov     rsi, QWORD PTR [rbp-0x10df0]
        mov     edx, 0xa20
        mov     rdi, rbx
        call    L1280
        mov     rdi, rbx
        mov     QWORD PTR [rbp-0x10dd8], rbx
        lea     rbx, [rbp-0x10030]
        call    L1310
        mov     rdx, QWORD PTR [rbp-0x10dd8]
        mov     esi, 0x40
        mov     rdi, rbx
        call    L1360
        mov     rdi, QWORD PTR [rbp-0x10dd8]
        call    L1400
        mov     rdi, QWORD PTR [rbp-0x10dd8]
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x10dd8]
        lea     rax, [rbp-0x10dd0]
        mov     r9, r14
        mov     rcx, r15
        mov     rsi, rbx
        sub     rsp, 0x8
        mov     QWORD PTR [rbp-0x10e08], rax
        mov     edx, 0x40
        mov     rdi, rax
        push    r12
        mov     r8, QWORD PTR [rbp-0x10de8]
        call    La220
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x10030], xmm0
        movaps  XMMWORD PTR [rbp-0x10020], xmm0
        movaps  XMMWORD PTR [rbp-0x10010], xmm0
        movaps  XMMWORD PTR [rbp-0x10000], xmm0
        pop     rax
        mov     r11, QWORD PTR [rbp-0x10df8]
        pop     rdx
        jmp     Laf2d
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Lb360:
        mov     r8, QWORD PTR [rbp-0x10e10]
        lea     r15, [rbp-0x10d50]
Lb36e:
        mov     r14d, 0xfffffffa
        jmp     Lb17c
Lb379:
        lea     rax, [rbp-0xe030]
        lea     rbx, [rbp-0x10030]
        mov     QWORD PTR [rbp-0x10dd8], rax
        lea     rax, [rbp-0x10dd0]
        lea     r8, [rbp-0x10d90]
        mov     QWORD PTR [rbp-0x10e08], rax
        lea     rax, [rbp-0x10830]
        lea     r12, [rbp-0x10430]
        mov     QWORD PTR [rbp-0x10de8], rax
        lea     rax, [rbp-0x10c30]
        lea     r15, [rbp-0x10d50]
        mov     QWORD PTR [rbp-0x10e00], rax
        jmp     Lb36e
        // nop
        .byte   0x90

// mldsa87_verify_extmu (0xb3d0)

Lb3d0:
        sub     rsp, 0x10
        mov     r9, rdx
        xor     r8d, r8d
        xor     ecx, ecx
        push    0x1
        mov     edx, 0x40
        call    Lae20
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_prepare_domain_separation_prefix (0xb3f0)

Lb3f0:
        xor     eax, eax
        cmp     r8, 0xff
        ja      Lb460
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbp
        mov     rbp, r8
        sub     rsp, 0x18
        test    r9d, r9d
        jne     Lb438
        mov     BYTE PTR [rdi], 0x0
        mov     BYTE PTR [r12+0x1], r8b
        test    r8, r8
        jne     Lb518
Lb422:
        lea     rax, [rbp+0x2]
Lb426:
        add     rsp, 0x18
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Lb438:
        cmp     r9d, 0xc
        ja      Lb4ce
        mov     r13, rdx
        mov     eax, r9d
        lea     rdx, [rip+Lc720]
        mov     r14, rsi
        movsxd  rax, DWORD PTR [rdx+rax*4]
        add     rax, rdx
        jmp     rax
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
Lb460:
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
        cmp     r13, 0x20
        jne     Lb4ce
Lb46e:
        mov     BYTE PTR [r12], 0x1
        mov     BYTE PTR [r12+0x1], bpl
        test    rbp, rbp
        jne     Lb530
Lb481:
        lea     rcx, [rip+Lc760]
        xor     eax, eax
        mov     rdx, rcx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
Lb490:
        cmp     r9d, DWORD PTR [rdx]
        je      Lb4f8
        add     eax, 0x1
        add     rdx, 0x10
        cmp     eax, 0xc
        jne     Lb490
Lb4a1:
        lea     rdi, [r12+rbp*1+0xd]
        mov     rdx, r13
        mov     rsi, r14
        call    L1010
        add     rsp, 0x18
        lea     rax, [r13+rbp*1+0xd]
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
        cmp     r13, 0x1c
        je      Lb46e
Lb4ce:
        xor     eax, eax
        jmp     Lb426
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x40
        je      Lb46e
        xor     eax, eax
        jmp     Lb426
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x30
        je      Lb46e
        xor     eax, eax
        jmp     Lb426
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
Lb4f8:
        shl     rax, 0x4
        lea     rdx, [r12+rbp*1+0x2]
        lea     rax, [rcx+rax*1+0x4]
        mov     rcx, QWORD PTR [rax]
        mov     QWORD PTR [rdx], rcx
        mov     eax, DWORD PTR [rax+0x7]
        mov     DWORD PTR [rdx+0x7], eax
        jmp     Lb4a1
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
Lb518:
        lea     rdi, [rdi+0x2]
        mov     rdx, r8
        mov     rsi, rcx
        call    L1010
        jmp     Lb422
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
Lb530:
        lea     rdi, [r12+0x2]
        mov     rdx, rbp
        mov     rsi, rcx
        mov     DWORD PTR [rsp+0xc], r9d
        call    L1010
        mov     r9d, DWORD PTR [rsp+0xc]
        jmp     Lb481
        // nop
        .byte   0x90

// mldsa87_signature (0xb550)

Lb550:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        xor     r9d, r9d
        push    r14
        mov     r14, rdx
        xor     edx, edx
        push    r13
        push    r12
        lea     r12, [rbp-0x190]
        push    r10
        push    rbx
        mov     rbx, rdi
        mov     rdi, r12
        sub     rsp, 0x1a0
        mov     QWORD PTR [rbp-0x1b8], rsi
        xor     esi, esi
        call    Lb3f0
        test    rax, rax
        mov     QWORD PTR [rbp-0x1c0], rax
        jne     Lb620
        mov     edx, 0xfffffff7
        lea     r13, [rbp-0x1b0]
Lb5b1:
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        xor     eax, eax
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x120b], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x1213
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
Lb5df:
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x1b0], xmm0
        movaps  XMMWORD PTR [rbp-0x1a0], xmm0
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x30]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
Lb620:
        lea     r13, [rbp-0x1b0]
        mov     esi, 0x20
        mov     rdi, r13
        call    L1020
        mov     edx, 0xfffffffd
        test    eax, eax
        jne     Lb5b1
        push    0x0
        mov     r8, QWORD PTR [rbp-0x1c0]
        mov     rcx, r12
        mov     rdx, r14
        push    r15
        mov     rsi, QWORD PTR [rbp-0x1b8]
        mov     r9, r13
        mov     rdi, rbx
        call    La750
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      Lb5df
        jmp     Lb5b1
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_verify (0xb680)

Lb680:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        xor     r9d, r9d
        push    r14
        mov     r14, rdx
        xor     edx, edx
        push    r13
        mov     r13, rsi
        xor     esi, esi
        push    r12
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x190]
        mov     rdi, rbx
        sub     rsp, 0x160
        call    Lb3f0
        test    rax, rax
        je      Lb718
        sub     rsp, 0x8
        mov     rcx, rbx
        mov     rdx, r14
        mov     r8, rax
        push    0x0
        mov     r9, r15
        mov     rsi, r13
        mov     rdi, r12
        call    Lae20
        mov     edx, eax
        pop     rax
        pop     rcx
Lb6eb:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x30]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
Lb718:
        mov     edx, 0xfffffff7
        jmp     Lb6eb
        // nop
        .byte   0x90

// mldsa87_signature_pre_hash_internal (0xb720)

Lb720:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r14
        push    r13
        mov     r13, r9
        push    r12
        lea     r12, [rbp-0x190]
        push    r10
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x168
        mov     r9d, DWORD PTR [r10+0x8]
        mov     r14, QWORD PTR [r10]
        test    r9d, r9d
        jne     Lb7b8
Lb75a:
        mov     edx, 0xfffffff7
Lb75f:
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        xor     eax, eax
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x120b], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x1213
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
Lb78d:
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x28]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
Lb7b8:
        mov     rdi, r12
        call    Lb3f0
        test    rax, rax
        je      Lb75a
        push    0x0
        xor     ecx, ecx
        mov     rdx, rax
        mov     r9, r13
        push    r14
        xor     r8d, r8d
        mov     rsi, r12
        mov     rdi, rbx
        call    La750
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      Lb78d
        jmp     Lb75f
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_signature_pre_hash_shake256 (0xb7f0)

Lb7f0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rcx
        mov     rcx, rdx
        mov     rdx, rsi
        push    r12
        mov     esi, 0x40
        push    r10
        push    rbx
        lea     rbx, [rbp-0x70]
        sub     rsp, 0x60
        mov     r12, QWORD PTR [r10]
        mov     QWORD PTR [rbp-0x78], rdi
        mov     rdi, rbx
        call    L1440
        push    0xc
        mov     rdi, QWORD PTR [rbp-0x78]
        mov     r9, r15
        push    r12
        mov     r8, r14
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        call    Lb720
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x70], xmm0
        movaps  XMMWORD PTR [rbp-0x60], xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        pop     rdx
        pop     rcx
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret

// mldsa87_verify_pre_hash_internal (0xb880)

Lb880:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r13
        mov     r13, r9
        push    r12
        push    r10
        push    rbx
        sub     rsp, 0x170
        mov     r9d, DWORD PTR [r10]
        test    r9d, r9d
        je      Lb910
        lea     rbx, [rbp-0x190]
        mov     r12, rdi
        mov     rdi, rbx
        call    Lb3f0
        mov     rdx, rax
        test    rax, rax
        je      Lb917
        sub     rsp, 0x8
        xor     ecx, ecx
        mov     r9, r13
        xor     r8d, r8d
        push    0x0
        mov     rsi, rbx
        mov     rdi, r12
        call    Lae20
        mov     edx, eax
        pop     rax
        pop     rcx
Lb8e1:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x29
        rep stos QWORD PTR es:[rdi], rax
        mov     DWORD PTR [rdi], 0x0
        lea     rsp, [rbp-0x20]
        mov     eax, edx
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
Lb910:
        lea     rbx, [rbp-0x190]
Lb917:
        mov     edx, 0xfffffff7
        jmp     Lb8e1
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_verify_pre_hash_shake256 (0xb920)

Lb920:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, r9
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rcx
        mov     rcx, rdx
        mov     rdx, rsi
        push    r12
        mov     esi, 0x40
        mov     r12, rdi
        push    r10
        push    rbx
        lea     rbx, [rbp-0x70]
        mov     rdi, rbx
        sub     rsp, 0x40
        call    L1440
        sub     rsp, 0x8
        mov     r9, r15
        mov     r8, r14
        push    0xc
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        mov     rdi, r12
        call    Lb880
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x70], xmm0
        movaps  XMMWORD PTR [rbp-0x60], xmm0
        movaps  XMMWORD PTR [rbp-0x50], xmm0
        movaps  XMMWORD PTR [rbp-0x40], xmm0
        pop     rdx
        pop     rcx
        lea     rsp, [rbp-0x30]
        pop     rbx
        pop     r10
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        lea     rsp, [r10-0x8]
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_pk_from_sk (0xb9b0)

Lb9b0:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbx
        mov     rbx, rsi
        sub     rsi, 0xffffffffffffff80
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x2e00
        movdqu  xmm3, XMMWORD PTR [rsi-0x80]
        movdqu  xmm4, XMMWORD PTR [rsi-0x70]
        movdqu  xmm5, XMMWORD PTR [rsi-0x60]
        movdqu  xmm6, XMMWORD PTR [rsi-0x50]
        lea     r14, [rsp+0x1200]
        lea     r15, [rsp+0x100]
        movdqu  xmm7, XMMWORD PTR [rsi-0x40]
        movaps  XMMWORD PTR [rsp+0x40], xmm3
        movdqu  xmm3, XMMWORD PTR [rsi-0x30]
        mov     rdi, r14
        movaps  XMMWORD PTR [rsp+0x50], xmm4
        movdqu  xmm4, XMMWORD PTR [rsi-0x20]
        movaps  XMMWORD PTR [rsp+0x60], xmm5
        movdqu  xmm5, XMMWORD PTR [rsi-0x10]
        movaps  XMMWORD PTR [rsp+0x70], xmm6
        movaps  XMMWORD PTR [rsp+0x80], xmm7
        movaps  XMMWORD PTR [rsp+0x90], xmm3
        movaps  XMMWORD PTR [rsp+0xa0], xmm4
        movaps  XMMWORD PTR [rsp+0xb0], xmm5
        call    L9df0
        mov     esi, 0x3
        mov     rdi, r14
        call    L9c60
        lea     rcx, [rbx+0x320]
        mov     rdx, r15
        mov     esi, 0x3
        mov     rdi, rcx
        mov     QWORD PTR [rsp+0x38], rcx
        mov     r13d, eax
        call    L9d40
        mov     rdi, r14
        mov     DWORD PTR [rsp+0x2c], eax
        call    L9bb0
        movdqa  xmm6, XMMWORD PTR [rsp+0x40]
        movdqa  xmm7, XMMWORD PTR [rsp+0x50]
        lea     r9, [rsp+0x500]
        mov     rcx, QWORD PTR [rsp+0x38]
        lea     r8, [rsp+0x40]
        mov     rsi, r9
        mov     rdx, r14
        movups  XMMWORD PTR [r12], xmm6
        lea     rdi, [r12+0x20]
        movups  XMMWORD PTR [r12+0x10], xmm7
        mov     QWORD PTR [rsp+0x30], r8
        mov     QWORD PTR [rsp+0x38], r9
        call    La100
        mov     r9, QWORD PTR [rsp+0x38]
        mov     r8, QWORD PTR [rsp+0x30]
        test    eax, eax
        mov     r11d, eax
        je      Lbbb0
        lea     rbx, [rsp+0xc0]
        lea     rdx, [rsp+0x80]
Lbae6:
        lea     rdi, [r12+0x8]
        mov     rcx, r12
        xor     eax, eax
        mov     QWORD PTR [r12], 0x0
        mov     QWORD PTR [r12+0xa18], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xa20
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
Lbb17:
        xor     eax, eax
        mov     rdi, r9
        mov     ecx, 0x1a0
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x380
        mov     rdi, r14
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm0, xmm0
        lea     rax, [rsp+0x60]
        movaps  XMMWORD PTR [rsp+0x60], xmm0
        movaps  XMMWORD PTR [rsp+0x70], xmm0
        movaps  XMMWORD PTR [rsp+0xc0], xmm0
        movaps  XMMWORD PTR [rsp+0xd0], xmm0
        movaps  XMMWORD PTR [rsp+0xe0], xmm0
        movaps  XMMWORD PTR [rsp+0xf0], xmm0
        movaps  XMMWORD PTR [rsp+0x80], xmm0
        movaps  XMMWORD PTR [rsp+0x90], xmm0
        movaps  XMMWORD PTR [rsp+0xa0], xmm0
        movaps  XMMWORD PTR [rsp+0xb0], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        lea     rsp, [rbp-0x28]
        mov     eax, r11d
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
Lbbb0:
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Lbbc0:
        movdqu  xmm1, XMMWORD PTR [rbx+rax*1+0x620]
        pxor    xmm1, XMMWORD PTR [r9+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0xd00
        jne     Lbbc0
        movdqa  xmm1, xmm2
        mov     QWORD PTR [rsp+0x18], r8
        psrldq  xmm1, 0x8
        mov     QWORD PTR [rsp+0x20], r9
        pxor    xmm2, xmm1
        mov     DWORD PTR [rsp+0x30], r11d
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x4
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x2
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm2
        psrldq  xmm1, 0x1
        pxor    xmm2, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        movd    edx, xmm2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    eax, xmm0
        movzx   eax, al
        neg     rax
        sar     rax, 0x20
        xor     eax, edx
        lea     rbx, [rsp+0xc0]
        xor     eax, edx
        mov     ecx, 0xa20
        mov     rdx, r12
        mov     esi, 0x40
        mov     rdi, rbx
        mov     BYTE PTR [rsp+0x38], al
        call    L1440
        pxor    xmm1, xmm1
        mov     r8, QWORD PTR [rsp+0x18]
        xor     eax, eax
        mov     r9, QWORD PTR [rsp+0x20]
        mov     r11d, DWORD PTR [rsp+0x30]
        movdqa  xmm0, xmm1
        lea     rdx, [rsp+0x80]
Lbcb2:
        movdqa  xmm2, XMMWORD PTR [rbx+rax*1]
        pxor    xmm2, XMMWORD PTR [rdx+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x40
        jne     Lbcb2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x8
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x4
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x2
        pxor    xmm1, xmm2
        movdqa  xmm2, xmm1
        psrldq  xmm2, 0x1
        pxor    xmm1, xmm2
        movd    esi, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x8
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x4
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x2
        por     xmm0, xmm1
        movdqa  xmm1, xmm0
        psrldq  xmm1, 0x1
        por     xmm0, xmm1
        movd    ecx, xmm0
        movzx   ecx, cl
        neg     rcx
        mov     rax, rcx
        sar     rax, 0x20
        xor     eax, esi
        or      r13b, BYTE PTR [rsp+0x2c]
        xor     eax, esi
        or      r13b, BYTE PTR [rsp+0x38]
        or      r13d, eax
        test    r13b, r13b
        je      Lbb17
        mov     r11d, 0xfffffff9
        jmp     Lbae6

// Padding (0xbd70 to 0xc000)

        .zero   656

// The read-only data (0xc000 to 0xc820)

// mld_KeccakF_RoundConstants (0xc0 bytes)
Lc000:
        .quad   0x0000000000000001
        .quad   0x0000000000008082
        .quad   0x800000000000808a
        .quad   0x8000000080008000
        .quad   0x000000000000808b
        .quad   0x0000000080000001
        .quad   0x8000000080008081
        .quad   0x8000000000008009
        .quad   0x000000000000008a
        .quad   0x0000000000000088
        .quad   0x0000000080008009
        .quad   0x000000008000000a
        .quad   0x000000008000808b
        .quad   0x800000000000008b
        .quad   0x8000000000008089
        .quad   0x8000000000008003
        .quad   0x8000000000008002
        .quad   0x8000000000000080
        .quad   0x000000000000800a
        .quad   0x800000008000000a
        .quad   0x8000000080008081
        .quad   0x8000000000008080
        .quad   0x0000000080000001
        .quad   0x8000000080008008
// mld_zetas (0x400 bytes)
Lc0c0:
        .quad   0x000064f700000000
        .quad   0xfff81503ffd83102
        .quad   0xfff4211800039e44
        .quad   0x00071e24fff2a128
        .quad   0x0023e92b001bde2b
        .quad   0xffe0147ffffa84ad
        .quad   0xffd3fb09002f9a75
        .quad   0x0028e527002f7a49
        .quad   0x000fa07000299658
        .quad   0x0036b788ffef85a4
        .quad   0xffeeeaa0fff79d90
        .quad   0xffdfd37b0027f968
        .quad   0xffc51ae7ffdfadd6
        .quad   0xffcdfc98ffeaa4f7
        .quad   0xffffb422001ad035
        .quad   0x000445c5003d3201
        .quad   0x0001762000294a67
        .quad   0x0035dec5002ef4cd
        .quad   0xffc9302cffe6a503
        .quad   0x003bbeafffd947d4
        .quad   0xffd18e7cffc51585
        .quad   0xffd43e4100368a96
        .quad   0xfffb6a4d00360400
        .quad   0xfff7c55d0023d69c
        .quad   0xffe6ead6ffe6123d
        .quad   0xffc5af5900357e1e
        .quad   0xffdf56170035843f
        .quad   0x0038738cffe7945c
        .quad   0x00081b9a000c63a8
        .quad   0x003b3853000e8f76
        .quad   0xffd8fc30003b8534
        .quad   0xffd54f2d001f9d54
        .quad   0xffe8ac81ffc406e5
        .quad   0xffd19819ffc7e1cf
        .quad   0x003509eeffe9d65d
        .quad   0xffe7cfbb002135c7
        .quad   0x001d9772ffeccf75
        .quad   0xfff0bcf6ffc1b072
        .quad   0xffcfd2aeffcf5280
        .quad   0x0001efcaffc890e0
        .quad   0xfff0fe85003410f2
        .quad   0x00296e9f0020c638
        .quad   0xffc7a44bffd2b7a3
        .quad   0xffda3409fff9ba6d
        .quad   0xffed4113fff5c282
        .quad   0xffec09f7ffffa63b
        .quad   0x001495d4fffa2bdd
        .quad   0xffea2c62001c4563
        .quad   0x00040af0ffccfbe9
        .quad   0x002f45880007c417
        .quad   0xffef36be0000ad00
        .quad   0x003c675a000dcd44
        .quad   0xffffde7effc72bca
        .quad   0xffce69c000193948
        .quad   0xfffcc7df0024756c
        .quad   0xffebe808000b98a1
        .quad   0xffc9c8080002e46c
        .quad   0xffe3bff6003036c2
        .quad   0xfffd4ae0ffdb3c93
        .quad   0x0014779200141305
        .quad   0xffe7d0e000139e25
        .quad   0xffea0802fff39944
        .quad   0xffc4c79cffd1eea2
        .quad   0x003a97d9ffc8a057
        .quad   0x0033ff5a001fea93
        .quad   0x003a41f8002358d4
        .quad   0x00223dfbffccff72
        .quad   0xffc9a422ffdaab9f
        .quad   0x00252587000412f5
        .quad   0x00359b5dffed24f0
        .quad   0xffc6a2fcffca48a0
        .quad   0xffcf45deffedbb56
        .quad   0x001c5e1a000dbe5e
        .quad   0x000c7f5a000de0e6
        .quad   0xffe7628a00078f83
        .quad   0xfff806fcffff5704
        .quad   0xffd05af6fff60021
        .quad   0x0030ef86001f0084
        .quad   0xfff7fcd6ffc9b97d
        .quad   0xffc921c2fff44592
        .quad   0x0004610c00053919
        .quad   0x003eb01bffdacd41
        .quad   0xffcd003b003472e7
        .quad   0x00031924001a7cc7
        .quad   0x00291199002b5ee5
        .quad   0x00134d71ffd87a3a
        .quad   0x00130984003de11c
        .quad   0x00185a460025f051
        .quad   0x001314beffc68518
        .quad   0xffc9db9000283891
        .quad   0x001c853fffd25089
        .quad   0xffeff6a6001d0b4b
        .quad   0x0012e11bffeba8be
        .quad   0xffea2d2fffcd5e3e
        .quad   0x001406c7fff91de4
        .quad   0xffe20d6e00327283
        .quad   0x001d4099ffec7953
        .quad   0xffeb05adffd92578
        .quad   0x000bdbe70016e405
        .quad   0x0033f8cf00221de8
        .quad   0xffd4ca0cfff7b934
        .quad   0xffe3d157ffe67ff8
        .quad   0xffc72c12ffd8911b
        .quad   0xffc65e1f000910d8
        .quad   0x00251d8bffe14658
        .quad   0xfffd7c8f002573b7
        .quad   0x00336898001ddd98
        .quad   0xffed93a70002d4bb
        .quad   0x00027c1cffcf6cbe
        .quad   0x002dfd710018aa08
        .quad   0x0019379a000c5ca5
        .quad   0xffe48c3dffc7a167
        .quad   0x0035c539ffd1a13c
        .quad   0x00041dc0003b0115
        .quad   0xfff11bf40021c4f7
        .quad   0x0007340e001a35e7
        .quad   0x001a4cd0fff97d45
        .quad   0x001d2668ffe47cae
        .quad   0xffef2633ffe68e98
        .quad   0xffc57fdbfffc05da
        .quad   0xffdde1afffd32764
        .quad   0xffdd1d09fff993dd
        .quad   0xfff118050002cc93
        .quad   0xffc9e5a900189c2a
        .quad   0x003bcf2cfff78a50
        .quad   0xffeb36dfffff434e
        .quad   0x00155e68003c15ca
        .quad   0x001e29cefff316b6
Lc4c0:
        .quad   0x0040000000400000
        .quad   0x0040000000400000
Lc4d0:
        .quad   0x00000fff00000fff
        .quad   0x00000fff00000fff
Lc4e0:
        .quad   0xffffe000ffffe000
        .quad   0xffffe000ffffe000
        .zero   16
Lc500:
        .quad   0xffff90b8ffff90be
        .quad   0xffff90d8ffff9058
        .quad   0xffff90b8ffff90c8
        .quad   0xffff90b8ffff9058
        .quad   0xffff90d8ffff9058
        .quad   0xffff9058ffff90c8
        .quad   0x00000000ffff90c8
        .quad   0x0000000000000000
// oid_map.0 (0xc0 bytes)
Lc540:
        .quad   0x8660090600000001
        .quad   0x0004020403650148
        .quad   0x8660090600000002
        .quad   0x0001020403650148
        .quad   0x8660090600000003
        .quad   0x0002020403650148
        .quad   0x8660090600000004
        .quad   0x0003020403650148
        .quad   0x8660090600000005
        .quad   0x0005020403650148
        .quad   0x8660090600000006
        .quad   0x0006020403650148
        .quad   0x8660090600000007
        .quad   0x0007020403650148
        .quad   0x8660090600000008
        .quad   0x0008020403650148
        .quad   0x8660090600000009
        .quad   0x0009020403650148
        .quad   0x866009060000000a
        .quad   0x000a020403650148
        .quad   0x866009060000000b
        .quad   0x000b020403650148
        .quad   0x866009060000000c
        .quad   0x000c020403650148
Lc600:
        .byte   0x04
        .byte   0x04
Lc602:
        .byte   0x03
        .byte   0x05
Lc604:
        .byte   0x04
        .byte   0x05
Lc606:
        .byte   0x06
        .byte   0x05
Lc608:
        .quad   0x0000000000000708
        .zero   16
Lc620:
        .quad   0xffffbe48ffffbe4e
        .quad   0xffffbe68ffffbde8
        .quad   0xffffbe48ffffbe58
        .quad   0xffffbe48ffffbde8
        .quad   0xffffbe68ffffbde8
        .quad   0xffffbde8ffffbe58
        .quad   0x00000000ffffbe58
        .quad   0x0000000000000000
// oid_map.0 (0xc0 bytes)
Lc660:
        .quad   0x8660090600000001
        .quad   0x0004020403650148
        .quad   0x8660090600000002
        .quad   0x0001020403650148
        .quad   0x8660090600000003
        .quad   0x0002020403650148
        .quad   0x8660090600000004
        .quad   0x0003020403650148
        .quad   0x8660090600000005
        .quad   0x0005020403650148
        .quad   0x8660090600000006
        .quad   0x0006020403650148
        .quad   0x8660090600000007
        .quad   0x0007020403650148
        .quad   0x8660090600000008
        .quad   0x0008020403650148
        .quad   0x8660090600000009
        .quad   0x0009020403650148
        .quad   0x866009060000000a
        .quad   0x000a020403650148
        .quad   0x866009060000000b
        .quad   0x000b020403650148
        .quad   0x866009060000000c
        .quad   0x000c020403650148
Lc720:
        .quad   0xffffeda8ffffedae
        .quad   0xffffedc8ffffed48
        .quad   0xffffeda8ffffedb8
        .quad   0xffffeda8ffffed48
        .quad   0xffffedc8ffffed48
        .quad   0xffffed48ffffedb8
        .quad   0x00000000ffffedb8
        .quad   0x0000000000000000
// oid_map.0 (0xc0 bytes)
Lc760:
        .quad   0x8660090600000001
        .quad   0x0004020403650148
        .quad   0x8660090600000002
        .quad   0x0001020403650148
        .quad   0x8660090600000003
        .quad   0x0002020403650148
        .quad   0x8660090600000004
        .quad   0x0003020403650148
        .quad   0x8660090600000005
        .quad   0x0005020403650148
        .quad   0x8660090600000006
        .quad   0x0006020403650148
        .quad   0x8660090600000007
        .quad   0x0007020403650148
        .quad   0x8660090600000008
        .quad   0x0008020403650148
        .quad   0x8660090600000009
        .quad   0x0009020403650148
        .quad   0x866009060000000a
        .quad   0x000a020403650148
        .quad   0x866009060000000b
        .quad   0x000b020403650148
        .quad   0x866009060000000c
        .quad   0x000c020403650148

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
