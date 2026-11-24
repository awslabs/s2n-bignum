// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mldsa-native's libmldsa.so (gcc 12, -O2,
// MLD_CONFIG_REDUCE_RAM)
//
// This is a transcription of the binary
// reduced-ram/multilevel/gcc12/O2/libmldsa.so for x86-64 (see README.md), as
// loaded at an address that is a multiple of 4096: its bytes from address 0 up
// to the end of the read-only data, which are its first two loadable segments
// and the start of the third, with the padding between them. The ELF header
// and dynamic linking information at the start, the padding and the read-only
// data are given as data, while the procedure linkage table and the code are
// given as instructions. The instructions that refer to the global offset
// table, which is outside the image, are given as bytes, as are the NOPs and
// any instruction that the assembler would encode differently. The labels are
// named after the addresses in the binary.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(
          mldsa_native_libmldsa_gcc12_O2_reduced_ram)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(
          mldsa_native_libmldsa_gcc12_O2_reduced_ram)
        .text
        .balign 16

S2N_BN_SYMBOL(mldsa_native_libmldsa_gcc12_O2_reduced_ram):

// ELF header and dynamic linking information, and padding
// (0x0 to 0x1000)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x00000001003e0003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x000000000002e108
        .quad   0x0038004000000000
        .quad   0x0019001a00400009
        .quad   0x0000000400000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000e20
        .quad   0x0000000000000e20
        .quad   0x0000000000001000
        .quad   0x0000000500000001
        .quad   0x0000000000001000
        .quad   0x0000000000001000
        .quad   0x0000000000001000
        .quad   0x000000000000a1a0
        .quad   0x000000000000a1a0
        .quad   0x0000000000001000
        .quad   0x0000000400000001
        .quad   0x000000000000c000
        .quad   0x000000000000c000
        .quad   0x000000000000c000
        .quad   0x0000000000002808
        .quad   0x0000000000002808
        .quad   0x0000000000001000
        .quad   0x0000000600000001
        .quad   0x000000000000ee88
        .quad   0x000000000000fe88
        .quad   0x000000000000fe88
        .quad   0x0000000000000178
        .quad   0x0000000000000178
        .quad   0x0000000000001000
        .quad   0x0000000600000002
        .quad   0x000000000000ee88
        .quad   0x000000000000fe88
        .quad   0x000000000000fe88
        .quad   0x0000000000000150
        .quad   0x0000000000000150
        .quad   0x0000000000000008
        .quad   0x0000000400000004
        .quad   0x000000000000e7d8
        .quad   0x000000000000e7d8
        .quad   0x000000000000e7d8
        .quad   0x0000000000000030
        .quad   0x0000000000000030
        .quad   0x0000000000000008
        .quad   0x000000046474e553
        .quad   0x000000000000e7d8
        .quad   0x000000000000e7d8
        .quad   0x000000000000e7d8
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
        .quad   0x000000000000ee88
        .quad   0x000000000000fe88
        .quad   0x000000000000fe88
        .quad   0x0000000000000178
        .quad   0x0000000000000178
        .quad   0x0000000000000001
        .quad   0x0000002d00000025
        .quad   0x0000000000000010
        .quad   0x0000002800000022
        .quad   0x0000000000000000
        .quad   0x000000000000001c
        .quad   0x0000000900000020
        .quad   0x0000001600000017
        .quad   0x0000002300000008
        .quad   0x0000000000000014
        .quad   0x0000001b00000027
        .quad   0x000000000000000c
        .quad   0x0000001300000000
        .quad   0x0000002400000003
        .quad   0x0000001a00000006
        .quad   0x0000001500000019
        .quad   0x0000000000000000
        .quad   0x0000000b00000026
        .quad   0x0000001f00000018
        .quad   0x000000110000000e
        .quad   0x000000000000002c
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001d00000000
        .quad   0x0000000500000000
        .quad   0x0000002b00000021
        .quad   0x0000000000000000
        .quad   0x0000001e00000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000a00000000
        .quad   0x000000000000000f
        .quad   0x0000000000000002
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000000000000d
        .quad   0x0000000100000000
        .quad   0x0000000000000029
        .quad   0x0000002500000007
        .quad   0x0000002a00000000
        .quad   0x0000000000000012
        .quad   0x0000000000000004
        .quad   0x0000000300000025
        .quad   0x0000000800000004
        .quad   0x0a6340a0460288d5
        .quad   0x10a640204e3c180a
        .quad   0x087445801d011110
        .quad   0x00a4c96828348108
        .quad   0x0000000400000003
        .quad   0x0000000800000007
        .quad   0x0000000000000009
        .quad   0x0000000d0000000a
        .quad   0x0000000f0000000e
        .quad   0x0000001000000000
        .quad   0x0000000000000012
        .quad   0x0000001400000013
        .quad   0x0000001700000015
        .quad   0x0000001a00000000
        .quad   0x0000001d0000001c
        .quad   0x000000210000001f
        .quad   0x0000002400000022
        .quad   0x0000002600000025
        .quad   0x0000002700000000
        .quad   0x0000000000000000
        .quad   0x0000000000000028
        .quad   0x0000002900000000
        .quad   0x28bfc2110000002a
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
        .quad   0x00000010000000bf
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000002a
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0007001200000184
        .quad   0x0000000000006b20
        .quad   0x0000000000000362
        .quad   0x00070012000001c8
        .quad   0x00000000000074c0
        .quad   0x0000000000000087
        .quad   0x00070012000000c6
        .quad   0x0000000000005110
        .quad   0x0000000000000125
        .quad   0x0007001200000051
        .quad   0x00000000000049b0
        .quad   0x0000000000000087
        .quad   0x00070012000003c7
        .quad   0x000000000000ab50
        .quad   0x00000000000000cc
        .quad   0x0007001200000036
        .quad   0x00000000000043f0
        .quad   0x00000000000005b7
        .quad   0x0007001200000350
        .quad   0x000000000000a260
        .quad   0x0000000000000597
        .quad   0x000700120000040f
        .quad   0x000000000000acb0
        .quad   0x000000000000009e
        .quad   0x000700120000031d
        .quad   0x0000000000009c00
        .quad   0x00000000000005c8
        .quad   0x00070012000001e0
        .quad   0x0000000000007550
        .quad   0x000000000000057f
        .quad   0x000700120000027b
        .quad   0x0000000000007ef0
        .quad   0x0000000000000090
        .quad   0x00070012000002f4
        .quad   0x00000000000097a0
        .quad   0x00000000000003f2
        .quad   0x00070012000002c0
        .quad   0x0000000000008020
        .quad   0x000000000000008d
        .quad   0x0007001200000248
        .quad   0x0000000000007d80
        .quad   0x000000000000009f
        .quad   0x000700120000001a
        .quad   0x0000000000004390
        .quad   0x000000000000005f
        .quad   0x00070012000000e7
        .quad   0x00000000000052e0
        .quad   0x00000000000000cc
        .quad   0x00070012000003eb
        .quad   0x000000000000ac20
        .quad   0x0000000000000090
        .quad   0x0007001200000368
        .quad   0x000000000000a800
        .quad   0x000000000000001d
        .quad   0x0007001200000081
        .quad   0x0000000000004f90
        .quad   0x000000000000001d
        .quad   0x00070012000000d8
        .quad   0x0000000000005240
        .quad   0x000000000000009f
        .quad   0x00070012000001ad
        .quad   0x0000000000006ef0
        .quad   0x00000000000005ce
        .quad   0x000700120000012f
        .quad   0x0000000000005440
        .quad   0x000000000000009e
        .quad   0x00070012000003b8
        .quad   0x000000000000aab0
        .quad   0x000000000000009f
        .quad   0x00070012000003a6
        .quad   0x000000000000a980
        .quad   0x0000000000000125
        .quad   0x0007001200000451
        .quad   0x000000000000ade0
        .quad   0x00000000000003c0
        .quad   0x0007001200000171
        .quad   0x0000000000005570
        .quad   0x00000000000003c0
        .quad   0x0007001200000096
        .quad   0x0000000000004fb0
        .quad   0x000000000000015f
        .quad   0x0007001200000236
        .quad   0x0000000000007c50
        .quad   0x0000000000000125
        .quad   0x000700120000020d
        .quad   0x0000000000007af0
        .quad   0x000000000000015f
        .quad   0x0007001200000001
        .quad   0x00000000000040a0
        .quad   0x00000000000002eb
        .quad   0x000700120000037d
        .quad   0x000000000000a820
        .quad   0x000000000000015f
        .quad   0x000700120000010b
        .quad   0x00000000000053b0
        .quad   0x0000000000000090
        .quad   0x000700120000030d
        .quad   0x0000000000009ba0
        .quad   0x000000000000005f
        .quad   0x0007001200000430
        .quad   0x000000000000ad50
        .quad   0x000000000000008d
        .quad   0x00070012000001f8
        .quad   0x0000000000007ad0
        .quad   0x000000000000001d
        .quad   0x000700120000029f
        .quad   0x0000000000007f80
        .quad   0x000000000000009e
        .quad   0x000700120000019d
        .quad   0x0000000000006e90
        .quad   0x000000000000005f
        .quad   0x0007001200000257
        .quad   0x0000000000007e20
        .quad   0x00000000000000cc
        .quad   0x00070012000002e1
        .quad   0x00000000000080b0
        .quad   0x00000000000003c0
        .quad   0x0007001200000338
        .quad   0x000000000000a1d0
        .quad   0x0000000000000087
        .quad   0x0007001200000069
        .quad   0x0000000000004a40
        .quad   0x000000000000054f
        .quad   0x0007001200000150
        .quad   0x00000000000054e0
        .quad   0x000000000000008d
        .quad   0x34346173646c6d00
        .quad   0x7269617079656b5f
        .quad   0x616e7265746e695f
        .quad   0x346173646c6d006c
        .quad   0x69617079656b5f34
        .quad   0x6d6f646e61720072
        .quad   0x6c6d007365747962
        .quad   0x69735f3434617364
        .quad   0x5f65727574616e67
        .quad   0x6c616e7265746e69
        .quad   0x34346173646c6d00
        .quad   0x7574616e6769735f
        .quad   0x756d7478655f6572
        .quad   0x34346173646c6d00
        .quad   0x5f7966697265765f
        .quad   0x6c616e7265746e69
        .quad   0x34346173646c6d00
        .quad   0x5f7966697265765f
        .quad   0x6c6d00756d747865
        .quad   0x72705f3434617364
        .quad   0x6f645f6572617065
        .quad   0x7065735f6e69616d
        .quad   0x5f6e6f6974617261
        .quad   0x6d00786966657270
        .quad   0x6c6d007970636d65
        .quad   0x69735f3434617364
        .quad   0x0065727574616e67
        .quad   0x5f34346173646c6d
        .quad   0x6d00796669726576
        .quad   0x735f34346173646c
        .quad   0x65727574616e6769
        .quad   0x7361685f6572705f
        .quad   0x6e7265746e695f68
        .quad   0x6173646c6d006c61
        .quad   0x616e6769735f3434
        .quad   0x6572705f65727574
        .quad   0x68735f687361685f
        .quad   0x6d00363532656b61
        .quad   0x765f34346173646c
        .quad   0x72705f7966697265
        .quad   0x695f687361685f65
        .quad   0x006c616e7265746e
        .quad   0x5f34346173646c6d
        .quad   0x705f796669726576
        .quad   0x5f687361685f6572
        .quad   0x363532656b616873
        .quad   0x34346173646c6d00
        .quad   0x6d6f72665f6b705f
        .quad   0x73646c6d006b735f
        .quad   0x7079656b5f353661
        .quad   0x65746e695f726961
        .quad   0x646c6d006c616e72
        .quad   0x79656b5f35366173
        .quad   0x646c6d0072696170
        .quad   0x6769735f35366173
        .quad   0x695f65727574616e
        .quad   0x006c616e7265746e
        .quad   0x5f35366173646c6d
        .quad   0x727574616e676973
        .quad   0x00756d7478655f65
        .quad   0x5f35366173646c6d
        .quad   0x695f796669726576
        .quad   0x006c616e7265746e
        .quad   0x5f35366173646c6d
        .quad   0x655f796669726576
        .quad   0x646c6d00756d7478
        .quad   0x6572705f35366173
        .quad   0x6d6f645f65726170
        .quad   0x617065735f6e6961
        .quad   0x705f6e6f69746172
        .quad   0x6c6d007869666572
        .quad   0x69735f3536617364
        .quad   0x0065727574616e67
        .quad   0x5f35366173646c6d
        .quad   0x6d00796669726576
        .quad   0x735f35366173646c
        .quad   0x65727574616e6769
        .quad   0x7361685f6572705f
        .quad   0x6e7265746e695f68
        .quad   0x6173646c6d006c61
        .quad   0x616e6769735f3536
        .quad   0x6572705f65727574
        .quad   0x68735f687361685f
        .quad   0x6d00363532656b61
        .quad   0x765f35366173646c
        .quad   0x72705f7966697265
        .quad   0x695f687361685f65
        .quad   0x006c616e7265746e
        .quad   0x5f35366173646c6d
        .quad   0x705f796669726576
        .quad   0x5f687361685f6572
        .quad   0x363532656b616873
        .quad   0x35366173646c6d00
        .quad   0x6d6f72665f6b705f
        .quad   0x73646c6d006b735f
        .quad   0x7079656b5f373861
        .quad   0x65746e695f726961
        .quad   0x646c6d006c616e72
        .quad   0x79656b5f37386173
        .quad   0x646c6d0072696170
        .quad   0x6769735f37386173
        .quad   0x695f65727574616e
        .quad   0x006c616e7265746e
        .quad   0x5f37386173646c6d
        .quad   0x727574616e676973
        .quad   0x00756d7478655f65
        .quad   0x5f37386173646c6d
        .quad   0x695f796669726576
        .quad   0x006c616e7265746e
        .quad   0x5f37386173646c6d
        .quad   0x655f796669726576
        .quad   0x646c6d00756d7478
        .quad   0x6572705f37386173
        .quad   0x6d6f645f65726170
        .quad   0x617065735f6e6961
        .quad   0x705f6e6f69746172
        .quad   0x6c6d007869666572
        .quad   0x69735f3738617364
        .quad   0x0065727574616e67
        .quad   0x5f37386173646c6d
        .quad   0x6d00796669726576
        .quad   0x735f37386173646c
        .quad   0x65727574616e6769
        .quad   0x7361685f6572705f
        .quad   0x6e7265746e695f68
        .quad   0x6173646c6d006c61
        .quad   0x616e6769735f3738
        .quad   0x6572705f65727574
        .quad   0x68735f687361685f
        .quad   0x6d00363532656b61
        .quad   0x765f37386173646c
        .quad   0x72705f7966697265
        .quad   0x695f687361685f65
        .quad   0x006c616e7265746e
        .quad   0x5f37386173646c6d
        .quad   0x705f796669726576
        .quad   0x5f687361685f6572
        .quad   0x363532656b616873
        .quad   0x37386173646c6d00
        .quad   0x6d6f72665f6b705f
        .quad   0x6d62696c006b735f
        .quad   0x006f732e6173646c
        .quad   0x74616e2f706d742f
        .quad   0x2d3638782d657669
        .quad   0x6b636174732d6f6e
        .quad   0x746365746f72702d
        .quad   0x43586c36312e726f
        .quad   0x73646c6d2f4e7355
        .quad   0x656372756f732d61
        .quad   0x7374757074756f2f
        .quad   0x62696c2f74756f2f
        .quad   0x0000000000000000
        .quad   0x000000000000fff0
        .quad   0x0000000100000007
        .quad   0x0000000000000000
        .quad   0x000000000000fff8
        .quad   0x0000000200000007
        .zero   488

// The procedure linkage table (0x1000 to 0x1030)

L1000:
        // push    QWORD PTR [rip+0xefda]
        .byte   0xff,0x35,0xda,0xef,0x00,0x00
        // jmp     QWORD PTR [rip+0xefdc]
        .byte   0xff,0x25,0xdc,0xef,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L1010:
        // jmp     QWORD PTR [rip+0xefda]
        .byte   0xff,0x25,0xda,0xef,0x00,0x00
        // push    0x0
        .byte   0x68,0x00,0x00,0x00,0x00
        {disp32} jmp     L1000
L1020:
        // jmp     QWORD PTR [rip+0xefd2]
        .byte   0xff,0x25,0xd2,0xef,0x00,0x00
        // push    0x1
        .byte   0x68,0x01,0x00,0x00,0x00
        {disp32} jmp     L1000

// The code (0x1030 to 0xb1a0)

// mldsa_shake128_init (0x1030)

L1030:
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

// mldsa_shake128_absorb (0x1070)

L1070:
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
        jb      L10cf
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L10a0:
        mov     rsi, rbp
        mov     rdi, r13
        sub     rbx, r12
        add     rbp, r12
        call    L1750
        mov     rdi, r13
        mov     r12d, 0xa8
        call    L1880
        xor     edx, edx
        mov     ecx, 0xa8
        cmp     rbx, 0xa7
        ja      L10a0
L10cf:
        mov     ecx, ebx
        mov     rsi, rbp
        mov     rdi, r13
        mov     DWORD PTR [rsp+0xc], edx
        call    L1750
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

// mldsa_shake128_finalize (0x1100)

L1100:
        push    rbx
        mov     ecx, 0x1
        mov     rbx, rdi
        sub     rsp, 0x10
        mov     edx, DWORD PTR [rdi+0xc8]
        lea     rsi, [rsp+0xf]
        mov     BYTE PTR [rsp+0xf], 0x1f
        mov     BYTE PTR [rsp+0xe], 0x80
        call    L1750
        lea     rsi, [rsp+0xe]
        mov     rdi, rbx
        mov     ecx, 0x1
        mov     edx, 0xa7
        call    L1750
        mov     DWORD PTR [rbx+0xc8], 0xa8
        add     rsp, 0x10
        pop     rbx
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_shake128_squeeze (0x1150)

L1150:
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
        je      L11d8
        mov     r14, rdi
        mov     rbx, rsi
        xor     r15d, r15d
        jmp     L11b5
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L1180:
        mov     ecx, 0xa8
        mov     edx, r12d
        sub     ecx, r12d
        mov     ebp, ecx
L118d:
        mov     r12d, 0xa8
        cmp     rbx, rbp
        jae     L11a1
        mov     ecx, ebx
        lea     r12d, [rdx+rbx*1]
        mov     rbp, rbx
L11a1:
        lea     rsi, [r14+r15*1]
        mov     rdi, r13
        add     r15, rbp
        call    L1720
        sub     rbx, rbp
        je      L11d8
L11b5:
        cmp     r12d, 0xa8
        jne     L1180
        mov     rdi, r13
        mov     ebp, 0xa8
        call    L1880
        mov     ecx, 0xa8
        xor     edx, edx
        jmp     L118d
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L11d8:
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

// mldsa_shake128_release (0x11f0)

L11f0:
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

// mldsa_shake256_init (0x1230)

L1230:
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

// mldsa_shake256_absorb (0x1270)

L1270:
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
        jb      L12cf
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L12a0:
        mov     rsi, rbp
        mov     rdi, r13
        sub     rbx, r12
        add     rbp, r12
        call    L1750
        mov     rdi, r13
        mov     r12d, 0x88
        call    L1880
        xor     edx, edx
        mov     ecx, 0x88
        cmp     rbx, 0x87
        ja      L12a0
L12cf:
        mov     ecx, ebx
        mov     rsi, rbp
        mov     rdi, r13
        mov     DWORD PTR [rsp+0xc], edx
        call    L1750
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

// mldsa_shake256_finalize (0x1300)

L1300:
        push    rbx
        mov     ecx, 0x1
        mov     rbx, rdi
        sub     rsp, 0x10
        mov     edx, DWORD PTR [rdi+0xc8]
        lea     rsi, [rsp+0xf]
        mov     BYTE PTR [rsp+0xf], 0x1f
        mov     BYTE PTR [rsp+0xe], 0x80
        call    L1750
        lea     rsi, [rsp+0xe]
        mov     rdi, rbx
        mov     ecx, 0x1
        mov     edx, 0x87
        call    L1750
        mov     DWORD PTR [rbx+0xc8], 0x88
        add     rsp, 0x10
        pop     rbx
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_shake256_squeeze (0x1350)

L1350:
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
        je      L13d8
        mov     r14, rdi
        mov     rbx, rsi
        xor     r15d, r15d
        jmp     L13b5
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L1380:
        mov     ecx, 0x88
        mov     edx, r12d
        sub     ecx, r12d
        mov     ebp, ecx
L138d:
        mov     r12d, 0x88
        cmp     rbx, rbp
        jae     L13a1
        mov     ecx, ebx
        lea     r12d, [rdx+rbx*1]
        mov     rbp, rbx
L13a1:
        lea     rsi, [r14+r15*1]
        mov     rdi, r13
        add     r15, rbp
        call    L1720
        sub     rbx, rbp
        je      L13d8
L13b5:
        cmp     r12d, 0x88
        jne     L1380
        mov     rdi, r13
        mov     ebp, 0x88
        call    L1880
        mov     ecx, 0x88
        xor     edx, edx
        jmp     L138d
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L13d8:
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

// mldsa_shake256_release (0x13f0)

L13f0:
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

// mldsa_shake256 (0x1430)

L1430:
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
        call    L1230
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, rbx
        call    L1270
        mov     rdi, rbx
        call    L1300
        mov     rdx, rbx
        mov     rsi, r12
        mov     rdi, rbp
        call    L1350
        mov     rdi, rbx
        call    L13f0
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

// mldsa_shake256x4_absorb_once (0x14a0)

L14a0:
        push    r15
        mov     r15, rdi
        add     rdi, 0x8
        xor     eax, eax
        push    r14
        mov     r14, r8
        push    r13
        mov     r13, rcx
        mov     rcx, r15
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, r9
        sub     rsp, 0x28
        mov     QWORD PTR [rdi-0x8], 0x0
        mov     QWORD PTR [rdi+0x310], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x320
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
        mov     BYTE PTR [rsp+0x1f], 0x1f
        cmp     r9, 0x87
        jbe     L1558
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L1500:
        sub     rsp, 0x8
        xor     r9d, r9d
        mov     r8, r14
        mov     rcx, r13
        push    0x88
        mov     rdx, r12
        mov     rsi, rbp
        mov     rdi, r15
        sub     rbx, 0x88
        add     rbp, 0x88
        add     r12, 0x88
        add     r13, 0x88
        add     r14, 0x88
        call    L1800
        mov     rdi, r15
        call    L2150
        pop     r9
        pop     r10
        cmp     rbx, 0x87
        ja      L1500
L1558:
        mov     eax, ebx
        test    rbx, rbx
        jne     L15c0
L155f:
        lea     rbx, [rsp+0x1f]
        sub     rsp, 0x8
        mov     r9d, eax
        mov     rdi, r15
        push    0x1
        mov     r8, rbx
        mov     rcx, rbx
        mov     rdx, rbx
        mov     rsi, rbx
        call    L1800
        mov     rdx, rbx
        mov     r8, rbx
        mov     rcx, rbx
        mov     rsi, rbx
        mov     rdi, r15
        mov     r9d, 0x87
        mov     BYTE PTR [rsp+0x2f], 0x80
        mov     DWORD PTR [rsp], 0x1
        call    L1800
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
L15c0:
        mov     DWORD PTR [rsp+0xc], ebx
        sub     rsp, 0x8
        xor     r9d, r9d
        mov     r8, r14
        push    rbx
        mov     rdi, r15
        mov     rcx, r13
        mov     rdx, r12
        mov     rsi, rbp
        call    L1800
        cmp     rbx, 0x87
        pop     rdi
        pop     r8
        mov     eax, DWORD PTR [rsp+0xc]
        jne     L155f
        lea     rsi, [rsp+0x1f]
        or      BYTE PTR [rsp+0x1f], 0x80
        sub     rsp, 0x8
        mov     rdi, r15
        push    0x1
        mov     rcx, rsi
        mov     r8, rsi
        mov     rdx, rsi
        mov     r9d, 0x87
        call    L1800
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
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake256x4_squeezeblocks (0x1630)

L1630:
        test    r8, r8
        je      L16c0
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
L1660:
        mov     rdi, r15
        call    L2150
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
        call    L1780
        pop     rax
        pop     rdx
        sub     r14, 0x1
        jne     L1660
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
L16c0:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake256x4_init (0x16d0)

L16d0:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_shake256x4_release (0x16e0)

L16e0:
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

// mldsa_keccakf1600_extract_bytes (0x1720)

L1720:
        mov     edx, edx
        test    ecx, ecx
        je      L1740
        mov     ecx, ecx
        xor     eax, eax
        add     rdi, rdx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L1730:
        movzx   edx, BYTE PTR [rdi+rax*1]
        mov     BYTE PTR [rsi+rax*1], dl
        add     rax, 0x1
        cmp     rcx, rax
        jne     L1730
L1740:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_keccakf1600_xor_bytes (0x1750)

L1750:
        mov     edx, edx
        test    ecx, ecx
        je      L1772
        mov     ecx, ecx
        add     rdi, rdx
        lea     rdx, [rsi+rcx*1]
        // nop
        .byte   0x90
L1760:
        movzx   eax, BYTE PTR [rsi]
        add     rsi, 0x1
        xor     BYTE PTR [rdi], al
        add     rdi, 0x1
        cmp     rsi, rdx
        jne     L1760
L1772:
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_keccakf1600x4_extract_bytes (0x1780)

L1780:
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
        call    L1720
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r15
        lea     rdi, [rbx+0xc8]
        call    L1720
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r14
        lea     rdi, [rbx+0x190]
        call    L1720
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
        jmp     L1720
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_keccakf1600x4_xor_bytes (0x1800)

L1800:
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
        call    L1750
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r15
        lea     rdi, [rbx+0xc8]
        call    L1750
        mov     ecx, r12d
        mov     edx, ebp
        mov     rsi, r14
        lea     rdi, [rbx+0x190]
        call    L1750
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
        jmp     L1750
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_keccakf1600_permute (0x1880)

L1880:
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
L1980:
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
        jne     L1980
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

// mldsa_keccakf1600x4_permute (0x2150)

L2150:
        push    rbx
        mov     rbx, rdi
        call    L1880
        lea     rdi, [rbx+0xc8]
        call    L1880
        lea     rdi, [rbx+0x190]
        call    L1880
        lea     rdi, [rbx+0x258]
        pop     rbx
        jmp     L1880
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_unpack_pk_t1 (0x2180)

L2180:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x6
        lea     rsi, [rax+rsi*1+0x20]
        jmp     L2a20

// mldsa44_pack_sk_rho_key_tr (0x2190)

L2190:
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

// mldsa44_unpack_sk (0x21e0)

L21e0:
        mov     rax, QWORD PTR [rsp+0x8]
        movdqu  xmm0, XMMWORD PTR [rax]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rax+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rax+0x20]
        movups  XMMWORD PTR [rdx], xmm2
        movdqu  xmm3, XMMWORD PTR [rax+0x30]
        movups  XMMWORD PTR [rdx+0x10], xmm3
        movdqu  xmm4, XMMWORD PTR [rax+0x40]
        lea     rdx, [rax+0x80]
        movups  XMMWORD PTR [rsi], xmm4
        movdqu  xmm5, XMMWORD PTR [rax+0x50]
        movups  XMMWORD PTR [rsi+0x10], xmm5
        movdqu  xmm6, XMMWORD PTR [rax+0x60]
        movups  XMMWORD PTR [rsi+0x20], xmm6
        movdqu  xmm7, XMMWORD PTR [rax+0x70]
        movups  XMMWORD PTR [rsi+0x30], xmm7
        mov     QWORD PTR [r8], rdx
        lea     rdx, [rax+0x200]
        add     rax, 0x380
        mov     QWORD PTR [r9], rdx
        mov     QWORD PTR [rcx], rax
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_pack_sig_c (0x2250)

L2250:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_pack_sig_h (0x2270)

L2270:
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
L22d2:
        mov     rsi, r12
        mov     rdi, r13
        call    L2ed0
        xor     eax, eax
        jmp     L22fd
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L22e8:
        mov     ecx, ebx
        add     ebx, 0x1
        mov     BYTE PTR [r15+rcx*1], al
L22f1:
        add     rax, 0x1
        cmp     rax, 0x100
        je      L2339
L22fd:
        mov     ecx, DWORD PTR [r14+rax*4]
        mov     edi, DWORD PTR [r13+rax*4+0x0]
        lea     esi, [rcx+0x17400]
        cmp     esi, 0x2e800
        ja      L2320
        cmp     ecx, 0xfffe8c00
        jne     L22f1
        test    edi, edi
        je      L22f1
L2320:
        cmp     ebx, 0x50
        jne     L22e8
        mov     eax, 0xffffffff
L232a:
        add     rsp, 0x18
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
L2339:
        mov     rax, QWORD PTR [rsp+0x8]
        add     r12, 0xc0
        mov     BYTE PTR [rbp+0x0], bl
        add     r14, 0x400
        add     rbp, 0x1
        cmp     r12, rax
        jne     L22d2
        xor     eax, eax
        jmp     L232a

// mldsa44_pack_sig_z (0x2360)

L2360:
        lea     eax, [rdx+rdx*8]
        shl     eax, 0x6
        lea     rdi, [rax+rdi*1+0x20]
        jmp     L3780

// mldsa44_sig_unpack_hints (0x2370)

L2370:
        push    rbp
        mov     r11, rsi
        mov     r8, rdi
        mov     ebp, edx
        push    rbx
        lea     rbx, [rsi+0x920]
        xor     esi, esi
        test    edx, edx
        je      L2393
        lea     eax, [rdx+0x4f]
        movzx   esi, BYTE PTR [r11+rax*1+0x920]
L2393:
        lea     eax, [rbp+0x50]
        movzx   r9d, BYTE PTR [r11+rax*1+0x920]
        mov     r10, r9
        cmp     r9d, esi
        jb      L2416
        cmp     r9d, 0x50
        ja      L2416
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
        jae     L2420
        lea     edx, [rsi+0x920]
        mov     eax, esi
        add     rdx, r11
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L23f0:
        movzx   ecx, BYTE PTR [rdx]
        add     rdx, 0x1
        mov     DWORD PTR [r8+rcx*4], 0x1
        mov     ecx, eax
        add     eax, 0x1
        cmp     eax, r9d
        jae     L2420
        cmp     esi, eax
        jae     L23f0
        movzx   edi, BYTE PTR [rdx]
        cmp     BYTE PTR [rbx+rcx*1], dil
        jb      L23f0
L2416:
        mov     eax, 0xffffffff
        pop     rbx
        pop     rbp
        ret
        // xchg    ax, ax
        .byte   0x66,0x90
L2420:
        cmp     ebp, 0x3
        je      L2430
L2425:
        xor     eax, eax
        pop     rbx
        pop     rbp
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2430:
        cmp     r9d, 0x50
        je      L2425
        cmp     BYTE PTR [r11+r10*1+0x920], 0x0
        jne     L2416
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L2448:
        add     r10, 0x1
        cmp     r10d, 0x50
        je      L2425
        cmp     BYTE PTR [r11+r10*1+0x920], 0x0
        je      L2448
        jmp     L2416
        // nop
        .byte   0x90

// mld_rej_uniform_c.constprop.0 (0x2460)

L2460:
        mov     r8, rdi
        mov     r9d, ecx
        cmp     esi, 0xff
        ja      L24c8
        mov     r10d, 0x3
        sub     r10d, edx
        jmp     L248f
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L2480:
        mov     esi, ecx
L2482:
        add     rdx, 0x3
        lea     eax, [r10+rdx*1]
        cmp     r9d, eax
        jb      L24c8
L248f:
        movzx   eax, BYTE PTR [rdx+0x1]
        movzx   ecx, BYTE PTR [rdx+0x2]
        movzx   edi, BYTE PTR [rdx]
        shl     eax, 0x8
        shl     ecx, 0x10
        or      eax, ecx
        or      eax, edi
        and     eax, 0x7fffff
        cmp     eax, 0x7fe000
        ja      L2482
        mov     edi, esi
        lea     ecx, [rsi+0x1]
        mov     DWORD PTR [r8+rdi*4], eax
        cmp     esi, 0xff
        jne     L2480
        mov     eax, ecx
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L24c8:
        mov     ecx, esi
        mov     eax, ecx
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_poly_reduce (0x24d0)

L24d0:
        movdqa  xmm2, XMMWORD PTR [rip+Lc4c0]
        lea     rax, [rdi+0x400]
        // nop
        .byte   0x90
L24e0:
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
        jne     L24e0
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa_poly_caddq (0x2520)

L2520:
        lea     rsi, [rdi+0x400]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L2530:
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
        jne     L2530
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_poly_add (0x2560)

L2560:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2568:
        movdqa  xmm0, XMMWORD PTR [rdi+rax*1]
        paddd   xmm0, XMMWORD PTR [rsi+rax*1]
        movaps  XMMWORD PTR [rdi+rax*1], xmm0
        add     rax, 0x10
        cmp     rax, 0x400
        jne     L2568
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_poly_sub (0x2590)

L2590:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2598:
        movdqa  xmm0, XMMWORD PTR [rdi+rax*1]
        psubd   xmm0, XMMWORD PTR [rsi+rax*1]
        movaps  XMMWORD PTR [rdi+rax*1], xmm0
        add     rax, 0x10
        cmp     rax, 0x400
        jne     L2598
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa_poly_shiftl (0x25c0)

L25c0:
        lea     rax, [rdi+0x400]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L25d0:
        movdqa  xmm0, XMMWORD PTR [rdi]
        add     rdi, 0x10
        pslld   xmm0, 0xd
        movaps  XMMWORD PTR [rdi-0x10], xmm0
        cmp     rdi, rax
        jne     L25d0
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_poly_ntt (0x25f0)

L25f0:
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
L2618:
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
L2640:
        add     esi, 0x1
        cmp     eax, edx
        jae     L26ba
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
L2668:
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
        jne     L2668
L26ba:
        add     eax, r9d
        add     edx, r9d
        cmp     eax, 0xff
        ja      L26d8
        mov     ecx, esi
        movsxd  rdi, DWORD PTR [rbp+rcx*4+0x0]
        jmp     L2640
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L26d8:
        cmp     ebx, 0x8
        je      L26f2
        mov     ecx, ebx
        mov     eax, 0x1
        shl     eax, cl
        mov     ecx, ebx
        movsxd  rdi, DWORD PTR [rbp+rax*4+0x0]
        jmp     L2618
L26f2:
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_poly_invntt_tomont (0x2700)

L2700:
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
L2720:
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
L2740:
        mov     ecx, edi
        sub     edi, 0x1
        mov     ecx, DWORD PTR [r13+rcx*4+0x0]
        neg     ecx
        cmp     edx, esi
        jae     L27dd
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
L2780:
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
        jne     L2780
L27dd:
        add     edx, r8d
        add     esi, r8d
        cmp     edx, 0xff
        jbe     L2740
        mov     ecx, r15d
        sub     ecx, 0x1
        jne     L2720
        lea     r8, [rax+0x400]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2808:
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
        jne     L2808
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_poly_pointwise_montgomery (0x2850)

L2850:
        mov     r8, rdi
        xor     edx, edx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L2858:
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
        jne     L2858
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa_poly_power2round (0x28a0)

L28a0:
        movdqa  xmm4, XMMWORD PTR [rip+Lc4d0]
        movdqa  xmm3, XMMWORD PTR [rip+Lc4e0]
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L28b8:
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
        jne     L28b8
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa_poly_uniform (0x28f0)

L28f0:
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
        call    L1030
        mov     edx, 0x22
        mov     rsi, rbx
        mov     rdi, r13
        call    L1070
        mov     rdi, r13
        call    L1100
        mov     rdx, r13
        mov     esi, 0x348
        mov     rdi, r12
        call    L1150
        xor     esi, esi
        mov     ecx, 0x348
        mov     rdx, r12
        mov     rdi, r14
        call    L2460
        cmp     eax, 0xff
        ja      L2993
        mov     ebx, eax
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L2968:
        mov     rdx, r13
        mov     esi, 0xa8
        mov     rdi, r12
        call    L1150
        mov     esi, ebx
        mov     ecx, 0xa8
        mov     rdx, r12
        mov     rdi, r14
        call    L2460
        mov     ebx, eax
        cmp     eax, 0xff
        jbe     L2968
L2993:
        mov     rdi, r13
        call    L11f0
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

// mldsa_polyt1_pack (0x29c0)

L29c0:
        lea     rcx, [rsi+0x400]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L29d0:
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
        jne     L29d0
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa_polyt1_unpack (0x2a20)

L2a20:
        mov     rax, rsi
        mov     rcx, rdi
        lea     rsi, [rsi+0x140]
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L2a30:
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
        jne     L2a30
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa_polyt0_pack (0x2ab0)

L2ab0:
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
        mov     QWORD PTR [rsp-0x30], rax
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L2ad8:
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
        cmp     QWORD PTR [rsp-0x30], rdx
        jne     L2ad8
        pxor    xmm0, xmm0
        lea     rax, [rsp-0x28]
        movaps  XMMWORD PTR [rsp-0x28], xmm0
        movaps  XMMWORD PTR [rsp-0x18], xmm0
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa_polyt0_unpack (0x2c40)

L2c40:
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
L2c60:
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
        jne     L2c60
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_poly_chknorm (0x2e00)

L2e00:
        mov     rcx, rdi
        lea     edi, [rsi-0x1]
        xor     esi, esi
        lea     r8, [rcx+0x400]
        // nop
        .byte   0x90
L2e10:
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
        jne     L2e10
        mov     eax, esi
        ret
        // nop
        .byte   0x90

// mldsa_polyw1_pack_88 (0x2e40)

L2e40:
        lea     rcx, [rdi+0xc0]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L2e50:
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
        jne     L2e50
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_polyw1_pack_32 (0x2ea0)

L2ea0:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2ea8:
        mov     edx, DWORD PTR [rsi+rax*8+0x4]
        shl     edx, 0x4
        or      dl, BYTE PTR [rsi+rax*8]
        mov     BYTE PTR [rdi+rax*1], dl
        add     rax, 0x1
        cmp     rax, 0x80
        jne     L2ea8
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa_polyw1_unpack_88 (0x2ed0)

L2ed0:
        mov     rcx, rdi
        mov     rdx, rsi
        lea     rdi, [rsi+0xc0]
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L2ee0:
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
        jne     L2ee0
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa_polyw1_unpack_32 (0x2f40)

L2f40:
        xor     eax, eax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L2f48:
        movzx   edx, BYTE PTR [rsi+rax*1]
        and     edx, 0xf
        mov     DWORD PTR [rdi+rax*8], edx
        movzx   edx, BYTE PTR [rsi+rax*1]
        shr     dl, 0x4
        movzx   edx, dl
        mov     DWORD PTR [rdi+rax*8+0x4], edx
        add     rax, 0x1
        cmp     rax, 0x80
        jne     L2f48
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mld_rej_eta_c44.constprop.0 (0x2f70)

L2f70:
        mov     r8, rdi
        cmp     esi, 0xff
        ja      L3016
        mov     r9d, 0x1
        mov     r10d, 0x2
        sub     r9d, edx
        // xchg    ax, ax
        .byte   0x66,0x90
L2f90:
        movzx   eax, BYTE PTR [rdx]
        mov     ecx, eax
        shr     al, 0x4
        and     ecx, 0xf
        movzx   eax, al
        cmp     cl, 0xf
        je      L2fc5
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
L2fc5:
        cmp     esi, 0xff
        setbe   cl
        cmp     eax, 0xe
        ja      L2ffe
        test    cl, cl
        je      L2ffe
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
L2ffe:
        lea     eax, [r9+rdx*1]
        cmp     eax, 0x87
        setbe   al
        add     rdx, 0x1
        test    al, cl
        jne     L2f90
L3016:
        mov     eax, esi
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa44_poly_decompose (0x3020)

L3020:
        xor     ecx, ecx
        mov     r9d, 0x2b
        mov     r8d, 0x3ff000
        // xchg    ax, ax
        .byte   0x66,0x90
L3030:
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
        jne     L3030
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_poly_use_hint (0x30a0)

L30a0:
        mov     r8, rsi
        push    rbx
        xor     ecx, ecx
        mov     esi, 0x2b
        mov     r9d, 0x3ff000
        xor     r10d, r10d
        jmp     L30dc
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L30c0:
        lea     edx, [rax+0x1]
        cmp     eax, 0x2b
        mov     eax, edx
        cmove   eax, r10d
L30cc:
        mov     DWORD PTR [rdi+rcx*1], eax
        add     rcx, 0x4
        cmp     rcx, 0x400
        je      L3149
L30dc:
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
        je      L30cc
        lea     ebx, [r11-0x7fe001]
        xor     ebx, r11d
        and     edx, ebx
        xor     edx, r11d
        jg      L30c0
        sub     eax, 0x1
        cmovb   eax, esi
        mov     DWORD PTR [rdi+rcx*1], eax
        add     rcx, 0x4
        cmp     rcx, 0x400
        jne     L30dc
L3149:
        pop     rbx
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa44_poly_uniform_eta_4x (0x3150)

L3150:
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
        call    L16d0
        mov     r8, r12
        mov     rcx, r13
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r15
        mov     r9d, 0x42
        mov     rbx, r15
        call    L14a0
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
        call    L1630
        mov     rdi, QWORD PTR [rsp+0x40]
        xor     esi, esi
        mov     rdx, r14
        call    L2f70
        mov     rdi, QWORD PTR [rsp+0x38]
        xor     esi, esi
        mov     rdx, r15
        mov     r13d, eax
        call    L2f70
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     rdx, rbx
        xor     esi, esi
        mov     r12d, eax
        call    L2f70
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     rdi, QWORD PTR [rsp+0x28]
        xor     esi, esi
        mov     ebx, eax
        call    L2f70
        cmp     r12d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r13d, 0xff
        jmp     L33d5
L3350:
        mov     r9, QWORD PTR [rsp+0x20]
        mov     rcx, QWORD PTR [rsp+0x58]
        mov     rsi, r15
        mov     rdi, r14
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     r8d, 0x1
        mov     DWORD PTR [rsp+0x4c], r10d
        call    L1630
        mov     rdi, QWORD PTR [rsp+0x40]
        mov     esi, r13d
        mov     rdx, r14
        call    L2f70
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     esi, r12d
        mov     rdx, r15
        mov     r13d, eax
        call    L2f70
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     esi, ebx
        mov     r12d, eax
        call    L2f70
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     esi, DWORD PTR [rsp+0x4c]
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     ebx, eax
        call    L2f70
        cmp     r13d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r12d, 0xff
L33d5:
        setbe   dl
        or      eax, edx
        cmp     ebx, 0xff
        setbe   dl
        or      al, dl
        jne     L3350
        cmp     r10d, 0xff
        jbe     L3350
        mov     rdi, QWORD PTR [rsp+0x20]
        call    L16e0
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

// mldsa44_poly_challenge (0x3430)

L3430:
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
        call    L1230
        mov     rsi, rbx
        mov     edx, 0x20
        mov     rdi, r12
        call    L1270
        lea     rbx, [rsp+0x20]
        mov     rdi, r12
        call    L1300
        mov     esi, 0x88
        mov     rdi, rbx
        mov     rdx, r12
        call    L1350
        mov     rax, rbx
        lea     rdi, [rsp+0x28]
        xor     ecx, ecx
        xor     esi, esi
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L34a0:
        movzx   edx, BYTE PTR [rax]
        add     rax, 0x1
        shl     rdx, cl
        add     ecx, 0x8
        or      rsi, rdx
        cmp     rax, rdi
        jne     L34a0
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
        jmp     L350f
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L3500:
        mov     eax, ecx
L3502:
        movzx   edx, BYTE PTR [rsp+rax*1+0x20]
        lea     ecx, [rax+0x1]
        cmp     r15d, edx
        jae     L353b
L350f:
        cmp     ecx, 0x88
        jne     L3500
        mov     rdx, r12
        mov     esi, 0x88
        mov     rdi, rbx
        call    L1350
        movzx   edx, BYTE PTR [rsp+0x20]
        mov     eax, 0x1
        cmp     r15d, edx
        jb      L3502
        mov     ecx, 0x1
L353b:
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
        jne     L350f
        mov     rdi, r12
        call    L13f0
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

// mldsa44_polyeta_pack (0x35b0)

L35b0:
        push    r12
        mov     rax, rsi
        mov     r8, rdi
        lea     r9, [rsi+0x400]
        push    rbp
        mov     edx, 0x2
        push    rbx
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L35d0:
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
        jne     L35d0
        mov     QWORD PTR [rsp-0x8], 0x0
        lea     rax, [rsp-0x8]
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa44_polyeta_unpack (0x3670)

L3670:
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
L3690:
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
        jne     L3690
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_polyz_pack (0x3780)

L3780:
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
L37a0:
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
        jne     L37a0
        pxor    xmm0, xmm0
        lea     rax, [rsp-0x18]
        movaps  XMMWORD PTR [rsp-0x18], xmm0
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_polyz_unpack (0x3880)

L3880:
        mov     rdx, rsi
        mov     rax, rdi
        lea     r11, [rdi+0x400]
        mov     r10d, 0x20000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L3898:
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
        jne     L3898
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa44_poly_uniform_gamma1 (0x3980)

L3980:
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
        call    L1230
        mov     rsi, r14
        mov     edx, 0x42
        mov     rdi, r12
        call    L1270
        mov     rdi, r12
        call    L1300
        mov     rdx, r12
        mov     rdi, rbx
        mov     esi, 0x2a8
        call    L1350
        mov     rsi, rbx
        mov     rdi, r13
        call    L3880
        mov     rdi, r12
        call    L13f0
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

// mldsa44_polyvecl_ntt (0x3a50)

L3a50:
        push    rbx
        mov     rbx, rdi
        call    L25f0
        lea     rdi, [rbx+0x400]
        call    L25f0
        lea     rdi, [rbx+0x800]
        call    L25f0
        lea     rdi, [rbx+0xc00]
        pop     rbx
        jmp     L25f0
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyvecl_chknorm (0x3a80)

L3a80:
        push    r13
        lea     r13, [rdi+0x1000]
        push    r12
        mov     r12d, esi
        push    rbp
        xor     ebp, ebp
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L3a99:
        mov     rdi, rbx
        mov     esi, r12d
        add     rbx, 0x400
        call    L2e00
        or      ebp, eax
        cmp     rbx, r13
        jne     L3a99
        add     rsp, 0x8
        mov     eax, ebp
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // nop
        .byte   0x90

// mldsa44_polyveck_reduce (0x3ac0)

L3ac0:
        push    rbx
        mov     rbx, rdi
        call    L24d0
        lea     rdi, [rbx+0x400]
        call    L24d0
        lea     rdi, [rbx+0x800]
        call    L24d0
        lea     rdi, [rbx+0xc00]
        pop     rbx
        jmp     L24d0
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyveck_caddq (0x3af0)

L3af0:
        push    rbx
        mov     rbx, rdi
        call    L2520
        lea     rdi, [rbx+0x400]
        call    L2520
        lea     rdi, [rbx+0x800]
        call    L2520
        lea     rdi, [rbx+0xc00]
        pop     rbx
        jmp     L2520
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyveck_invntt_tomont (0x3b20)

L3b20:
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

// mldsa44_polyveck_unpack_eta_chknorm (0x3b50)

L3b50:
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
L3b6b:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        call    L3670
        mov     esi, r13d
        mov     rdi, rbp
        call    L2e00
        or      r12d, eax
        cmp     rbx, r14
        jne     L3b6b
        pop     rbx
        mov     eax, r12d
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa44_polyveck_decompose_pack_w1 (0x3ba0)

L3ba0:
        push    r13
        lea     r13, [rdi+0x300]
        push    r12
        mov     r12, rdx
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L3bba:
        mov     rsi, rbp
        mov     rdi, r12
        add     rbp, 0x400
        call    L3020
        mov     rdi, rbx
        mov     rsi, r12
        add     rbx, 0xc0
        call    L2e40
        cmp     rbx, r13
        jne     L3bba
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyvecl_unpack_eta (0x3bf0)

L3bf0:
        push    r12
        lea     r12, [rsi+0x180]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
L3c01:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        add     rbp, 0x400
        call    L3670
        cmp     rbx, r12
        jne     L3c01
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_polyvecl_unpack_z (0x3c30)

L3c30:
        push    r12
        lea     r12, [rsi+0x900]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
L3c41:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x240
        add     rbp, 0x400
        call    L3880
        cmp     rbx, r12
        jne     L3c41
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_polyvec_matrix_expand_lazy (0x3c70)

L3c70:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi+0x400], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x410], xmm1
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy (0x3c90)

L3c90:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15d, 0x1
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12, rsi
        push    rbx
        mov     rbx, rdx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x60
        movdqu  xmm1, XMMWORD PTR [rsi+0x400]
        movdqu  xmm2, XMMWORD PTR [rsi+0x410]
        lea     r14, [rsp+0x20]
        mov     BYTE PTR [rsp+0x1f], cl
        mov     rsi, r14
        mov     BYTE PTR [rsp+0x41], cl
        movaps  XMMWORD PTR [rsp+0x20], xmm1
        movaps  XMMWORD PTR [rsp+0x30], xmm2
        mov     BYTE PTR [rsp+0x40], 0x0
        call    L28f0
        mov     rsi, rbx
        mov     rdi, r13
        add     rbx, 0x400
        call    L2850
L3cfa:
        movzx   eax, BYTE PTR [rsp+0x1f]
        mov     rsi, r14
        mov     rdi, r12
        mov     BYTE PTR [rsp+0x40], r15b
        add     r15d, 0x1
        mov     BYTE PTR [rsp+0x41], al
        call    L28f0
        mov     rsi, rbx
        mov     rdi, r12
        add     rbx, 0x400
        call    L2850
        mov     rsi, r12
        mov     rdi, r13
        call    L2560
        cmp     r15d, 0x4
        jne     L3cfa
        mov     rdi, r13
        call    L24d0
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy (0x3d70)

L3d70:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        xor     r14d, r14d
        push    r13
        mov     r13, rcx
        push    r12
        mov     r12, rsi
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x60
        movdqu  xmm1, XMMWORD PTR [rsi+0x400]
        movdqu  xmm2, XMMWORD PTR [rsi+0x410]
        lea     rax, [rsp+0x20]
        mov     QWORD PTR [rsp+0x10], rdi
        mov     QWORD PTR [rsp+0x8], rdx
        mov     QWORD PTR [rsp+0x18], rax
        movaps  XMMWORD PTR [rsp+0x20], xmm1
        movaps  XMMWORD PTR [rsp+0x30], xmm2
L3dbc:
        mov     rax, QWORD PTR [rsp+0x8]
        mov     rdi, r13
        xor     r15d, r15d
        movzx   edx, WORD PTR [rax+0x8]
        mov     rsi, QWORD PTR [rax]
        add     edx, r14d
        movzx   edx, dx
        call    L3980
        mov     rdi, r13
        call    L25f0
        mov     rbx, QWORD PTR [rsp+0x10]
L3de6:
        test    r14d, r14d
        je      L3e80
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, r12
        mov     BYTE PTR [rsp+0x40], r14b
        mov     BYTE PTR [rsp+0x41], r15b
        call    L28f0
        mov     rsi, r13
        mov     rdi, r12
        call    L2850
        mov     rsi, r12
        mov     rdi, rbx
        call    L2560
L3e1c:
        add     r15d, 0x1
        add     rbx, 0x400
        cmp     r15d, 0x4
        jne     L3de6
        add     r14d, 0x1
        cmp     r14d, 0x4
        jne     L3dbc
        pxor    xmm0, xmm0
        mov     rax, QWORD PTR [rsp+0x18]
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        mov     rbx, QWORD PTR [rsp+0x10]
        mov     rdi, rbx
        call    L3ac0
        mov     rdi, rbx
        call    L3b20
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L3e80:
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, rbx
        mov     BYTE PTR [rsp+0x40], 0x0
        mov     BYTE PTR [rsp+0x41], r15b
        call    L28f0
        mov     rsi, r13
        mov     rdi, rbx
        call    L2850
        jmp     L3e1c
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mld_compute_pack_t0_t144 (0x3eb0)

L3eb0:
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
        sub     rsp, 0xc40
        lea     rax, [rsp+0x820]
        mov     QWORD PTR [rsp+0x8], rdx
        lea     rbx, [rsp+0x20]
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x10], rax
        lea     r12, [rsp+0x420]
        call    L3c70
        xor     eax, eax
L3efd:
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     rsi, QWORD PTR [rsp+0x10]
        mov     ecx, eax
        mov     rdi, rbx
        mov     DWORD PTR [rsp+0x1c], eax
        call    L3c90
        mov     rdi, rbx
        call    L2700
        mov     rsi, r15
        mov     rdi, r12
        add     r15, 0x60
        call    L3670
        mov     rsi, r12
        mov     rdi, rbx
        call    L2560
        mov     rdi, rbx
        call    L24d0
        mov     rdi, rbx
        call    L2520
        mov     rdx, rbx
        mov     rsi, rbx
        mov     rdi, r12
        call    L28a0
        mov     rdi, r14
        mov     rsi, r12
        add     r14, 0x140
        call    L29c0
        mov     rdi, r13
        mov     rsi, rbx
        add     r13, 0x1a0
        call    L2ab0
        mov     eax, DWORD PTR [rsp+0x1c]
        add     eax, 0x1
        cmp     eax, 0x4
        jne     L3efd
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x10]
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x10]
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
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mld_H44 (0x3fd0)

L3fd0:
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
        call    L1230
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, rbx
        call    L1270
        test    r15, r15
        jne     L4060
        cmp     QWORD PTR [rsp+0x128], 0x0
        jne     L407b
L4020:
        mov     rdi, rbx
        call    L1300
        mov     rdx, rbx
        mov     rsi, r12
        mov     rdi, rbp
        call    L1350
        mov     rdi, rbx
        call    L13f0
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
L4060:
        mov     rsi, QWORD PTR [rsp+0x8]
        mov     rdx, r15
        mov     rdi, rbx
        call    L1270
        cmp     QWORD PTR [rsp+0x128], 0x0
        je      L4020
L407b:
        mov     rdx, QWORD PTR [rsp+0x128]
        mov     rsi, QWORD PTR [rsp+0x120]
        mov     rdi, rbx
        call    L1270
        jmp     L4020
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_keypair_internal (0x40a0)

L40a0:
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
        call    L1430
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
        call    L3150
        mov     rdi, QWORD PTR [rbp-0x1148]
        add     rsp, 0x20
        mov     rsi, r12
        call    L35b0
        mov     rsi, r15
        lea     rdi, [rbx+0x260]
        call    L35b0
        mov     rsi, r14
        lea     rdi, [rbx+0x2c0]
        call    L35b0
        mov     rsi, QWORD PTR [rbp-0x1140]
        lea     rdi, [rbx+0x320]
        call    L35b0
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
        call    L3150
        add     rsp, 0x20
        lea     rdi, [rbx+0x80]
        mov     rsi, r12
        call    L35b0
        mov     rsi, r15
        lea     rdi, [rbx+0xe0]
        lea     r15, [rbp-0x10f0]
        call    L35b0
        mov     rsi, r14
        lea     rdi, [rbx+0x140]
        call    L35b0
        mov     rsi, QWORD PTR [rbp-0x1140]
        lea     rdi, [rbx+0x1a0]
        call    L35b0
        mov     rdi, r12
        call    L3a50
        movdqa  xmm3, XMMWORD PTR [rbp-0x10b0]
        lea     rdi, [r13+0x20]
        movdqa  xmm4, XMMWORD PTR [rbp-0x10a0]
        mov     r8, QWORD PTR [rbp-0x1138]
        mov     rcx, QWORD PTR [rbp-0x1148]
        lea     rsi, [rbx+0x380]
        mov     rdx, r12
        movups  XMMWORD PTR [r13+0x0], xmm3
        movups  XMMWORD PTR [r13+0x10], xmm4
        call    L3eb0
        mov     r14d, eax
        test    eax, eax
        jne     L42af
        mov     ecx, 0x520
        mov     rdx, r13
        mov     esi, 0x40
        mov     rdi, r15
        call    L1430
        mov     rsi, QWORD PTR [rbp-0x1138]
        mov     rdx, r15
        mov     rdi, rbx
        lea     rcx, [rbp-0x1050]
        call    L2190
L42af:
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
        jne     L4330
L4315:
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
L4330:
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
        jmp     L4315
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa44_keypair (0x4390)

L4390:
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
        jne     L43e8
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    L40a0
L43c9:
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
L43e8:
        mov     eax, 0xfffffffd
        jmp     L43c9
        // nop
        .byte   0x90

// mldsa44_signature_internal (0x43f0)

L43f0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rsi
        push    r14
        lea     rax, [rbp-0x24f0]
        lea     rsi, [rbp-0x2450]
        push    r13
        lea     r13, [rbp-0x23f0]
        push    r12
        lea     r12, [rbp-0x2430]
        push    r10
        push    rbx
        mov     rbx, r9
        lea     r9, [rbp-0x24b0]
        sub     rsp, 0x2548
        mov     QWORD PTR [rbp-0x2500], rcx
        lea     rcx, [rbp-0x24d0]
        mov     r14d, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x2508], rdi
        mov     rdi, rsi
        mov     QWORD PTR [rbp-0x24f8], rdx
        mov     rdx, r13
        mov     QWORD PTR [rbp-0x2510], r8
        mov     r8, rax
        mov     QWORD PTR [rbp-0x2550], r9
        mov     QWORD PTR [rbp-0x2548], rsi
        mov     rsi, r12
        mov     QWORD PTR [rbp-0x2558], rax
        mov     QWORD PTR [rbp-0x2560], rcx
        push    QWORD PTR [r10]
        call    L21e0
        pop     r8
        pop     r9
        test    r14d, r14d
        jne     L4961
        lea     rax, [rbp-0x23d0]
        mov     r9, QWORD PTR [rbp-0x2510]
        mov     esi, 0x40
        mov     rdx, r12
        mov     QWORD PTR [rbp-0x2538], rax
        mov     r8, QWORD PTR [rbp-0x2500]
        mov     rdi, rax
        mov     ecx, 0x40
        push    QWORD PTR [rbp-0x24f8]
        push    r15
        call    L3fd0
        pop     rsi
        pop     rdi
L44db:
        mov     r8, rbx
        mov     ecx, 0x20
        mov     rdx, r13
        mov     esi, 0x40
        lea     rax, [rbp-0x2390]
        mov     r9d, 0x20
        lea     r12, [rbp-0x2050]
        mov     QWORD PTR [rbp-0x2540], rax
        mov     rdi, rax
        lea     rbx, [rbp-0x1850]
        lea     r15, [rbp-0x1c50]
        push    0x40
        push    QWORD PTR [rbp-0x2538]
        call    L3fd0
        lea     rax, [rbp-0x1450]
        mov     rsi, QWORD PTR [rbp-0x2548]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x2530], rax
        call    L3c70
        pop     rax
        lea     rax, [rbp-0x2490]
        pop     rdx
        mov     QWORD PTR [rbp-0x2520], rax
        lea     rax, [rbp-0x1030]
        xor     ecx, ecx
        mov     QWORD PTR [rbp-0x24f8], rax
        lea     rax, [rbp-0x2350]
        mov     QWORD PTR [rbp-0x2510], rax
        lea     rax, [rbp-0x2470]
        mov     WORD PTR [rbp-0x2500], cx
        mov     QWORD PTR [rbp-0x2518], rax
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L4588:
        mov     rax, QWORD PTR [rbp-0x2540]
        mov     r14, QWORD PTR [rbp-0x24f8]
        mov     rcx, r12
        mov     rdx, QWORD PTR [rbp-0x2520]
        mov     rsi, QWORD PTR [rbp-0x2530]
        mov     QWORD PTR [rbp-0x2490], rax
        movzx   eax, WORD PTR [rbp-0x2500]
        mov     rdi, r14
        mov     WORD PTR [rbp-0x2488], ax
        call    L3d70
        mov     rdi, r14
        call    L3af0
        mov     rsi, r14
        mov     r14, QWORD PTR [rbp-0x2510]
        mov     rdx, r12
        mov     rdi, r14
        call    L3ba0
        mov     rdi, rbx
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x2538]
        mov     rdi, rbx
        mov     edx, 0x40
        call    L1270
        mov     rsi, r14
        mov     edx, 0x300
        mov     rdi, rbx
        call    L1270
        mov     rdi, rbx
        call    L1300
        mov     r14, QWORD PTR [rbp-0x2518]
        mov     rdx, rbx
        mov     esi, 0x20
        mov     rdi, r14
        call    L1350
        mov     rdi, rbx
        call    L13f0
        mov     rdi, rbx
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rsi, r14
        mov     rdi, r15
        xor     r14d, r14d
        call    L3430
        mov     rdi, r15
        call    L25f0
L4657:
        lea     rsi, [r14+r14*2]
        mov     rdi, rbx
        shl     rsi, 0x5
        add     rsi, QWORD PTR [rbp-0x24f0]
        call    L3670
        mov     rdi, rbx
        call    L25f0
        mov     rsi, r15
        mov     rdi, rbx
        call    L2850
        mov     rdi, rbx
        call    L2700
        movzx   edx, WORD PTR [rbp-0x2488]
        mov     rsi, QWORD PTR [rbp-0x2490]
        mov     rdi, r12
        add     edx, r14d
        movzx   edx, dx
        call    L3980
        mov     rsi, r12
        mov     rdi, rbx
        call    L2560
        mov     rdi, rbx
        call    L24d0
        mov     esi, 0x1ffb2
        mov     rdi, rbx
        call    L2e00
        test    eax, eax
        jne     L4957
        mov     rdi, QWORD PTR [rbp-0x2508]
        mov     edx, r14d
        mov     rsi, rbx
        add     r14, 0x1
        call    L2360
        cmp     r14, 0x4
        jne     L4657
        xor     eax, eax
        mov     r13, QWORD PTR [rbp-0x24f8]
        mov     QWORD PTR [rbp-0x2528], rbx
        xor     r14d, r14d
        mov     rbx, rax
L4703:
        mov     rsi, QWORD PTR [rbp-0x24b0]
        mov     rdi, r12
        add     rsi, r14
        call    L3670
        mov     rdi, r12
        call    L25f0
        mov     rsi, r15
        mov     rdi, r12
        call    L2850
        mov     rdi, r12
        call    L2700
        mov     rsi, r12
        mov     rdi, r13
        call    L2590
        mov     rdi, r13
        call    L24d0
        mov     esi, 0x173b2
        mov     rdi, r13
        call    L2e00
        test    eax, eax
        jne     L4950
        mov     rsi, QWORD PTR [rbp-0x24d0]
        mov     rdi, r12
        add     rsi, rbx
        call    L2c40
        mov     rdi, r12
        call    L25f0
        mov     rsi, r15
        mov     rdi, r12
        call    L2850
        mov     rdi, r12
        call    L2700
        mov     rdi, r12
        call    L24d0
        mov     esi, 0x17400
        mov     rdi, r12
        call    L2e00
        test    eax, eax
        jne     L4950
        mov     rdi, r13
        mov     rsi, r12
        add     r14, 0x60
        add     r13, 0x400
        call    L2560
        add     rbx, 0x1a0
        cmp     r14, 0x180
        jne     L4703
        mov     r14, QWORD PTR [rbp-0x2508]
        mov     rsi, QWORD PTR [rbp-0x2518]
        mov     rbx, QWORD PTR [rbp-0x2528]
        mov     rdi, r14
        call    L2250
        mov     rdx, QWORD PTR [rbp-0x2510]
        mov     rcx, r12
        mov     rdi, r14
        mov     rsi, QWORD PTR [rbp-0x24f8]
        call    L2270
        mov     edx, eax
L4804:
        mov     rdi, rbx
        xor     eax, eax
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x24f8]
        mov     ecx, 0x200
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x24f8]
        mov     rdi, QWORD PTR [rbp-0x2510]
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2510]
        mov     ecx, 0x80
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     rax, QWORD PTR [rbp-0x2520]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rax], xmm0
        mov     rax, QWORD PTR [rbp-0x2518]
        movaps  XMMWORD PTR [rax], xmm0
        movaps  XMMWORD PTR [rax+0x10], xmm0
        test    edx, edx
        je      L48cb
        cmp     edx, 0xffffffff
        jne     L4896
        add     WORD PTR [rbp-0x2500], 0x4
        movzx   eax, WORD PTR [rbp-0x2500]
        cmp     ax, 0xfff8
        jne     L4588
        mov     edx, 0xfffffffc
L4896:
        mov     rbx, QWORD PTR [rbp-0x2508]
        xor     eax, eax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x96c], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x974
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L48cb:
        mov     QWORD PTR [rbp-0x24b0], 0x0
        mov     rax, QWORD PTR [rbp-0x2550]
        mov     QWORD PTR [rbp-0x24d0], 0x0
        mov     rax, QWORD PTR [rbp-0x2560]
        mov     QWORD PTR [rbp-0x24f0], 0x0
        mov     rax, QWORD PTR [rbp-0x2558]
        mov     rdi, QWORD PTR [rbp-0x2530]
        xor     eax, eax
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2530]
        mov     rdi, QWORD PTR [rbp-0x2548]
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2548]
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
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L4950:
        mov     rbx, QWORD PTR [rbp-0x2528]
L4957:
        mov     edx, 0xffffffff
        jmp     L4804
L4961:
        movdqu  xmm1, XMMWORD PTR [r15]
        movdqu  xmm2, XMMWORD PTR [r15+0x10]
        lea     rax, [rbp-0x23d0]
        movdqu  xmm3, XMMWORD PTR [r15+0x20]
        movdqu  xmm4, XMMWORD PTR [r15+0x30]
        mov     QWORD PTR [rbp-0x2538], rax
        movaps  XMMWORD PTR [rbp-0x23d0], xmm1
        movaps  XMMWORD PTR [rbp-0x23c0], xmm2
        movaps  XMMWORD PTR [rbp-0x23b0], xmm3
        movaps  XMMWORD PTR [rbp-0x23a0], xmm4
        jmp     L44db
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_signature_extmu (0x49b0)

L49b0:
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
        jne     L4a30
        push    0x1
        xor     ecx, ecx
        mov     edx, 0x40
        mov     r9, rbx
        push    r14
        xor     r8d, r8d
        mov     rsi, r13
        mov     rdi, r12
        call    L43f0
        pop     rdx
        pop     rcx
L4a0a:
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
L4a30:
        mov     eax, 0xfffffffd
        jmp     L4a0a
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_verify_internal (0x4a40)

L4a40:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rdx
        push    r14
        lea     rax, [rbp-0x1030]
        mov     r14, rdi
        push    r13
        mov     r13, rax
        push    r12
        mov     r12, rsi
        lea     rsi, [rdi+0x20]
        push    r10
        push    rbx
        sub     rsp, 0x24c0
        movdqu  xmm3, XMMWORD PTR [rdi]
        movdqu  xmm4, XMMWORD PTR [rdi+0x10]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x24c8], rcx
        mov     ebx, DWORD PTR [r10]
        mov     QWORD PTR [rbp-0x24d8], r8
        mov     QWORD PTR [rbp-0x24d0], r9
        mov     QWORD PTR [rbp-0x24c0], rax
        movaps  XMMWORD PTR [rbp-0x24b0], xmm3
        movaps  XMMWORD PTR [rbp-0x24a0], xmm4
        call    L3c30
        mov     esi, 0x1ffb2
        mov     rdi, r13
        call    L3a80
        test    eax, eax
        jne     L4f32
        mov     r13d, eax
        test    ebx, ebx
        je      L4e48
        movdqu  xmm5, XMMWORD PTR [r12]
        lea     rax, [rbp-0x1450]
        movdqu  xmm6, XMMWORD PTR [r12+0x10]
        lea     rbx, [rbp-0x1850]
        mov     QWORD PTR [rbp-0x24b8], rax
        lea     rax, [rbp-0x2470]
        movdqu  xmm7, XMMWORD PTR [r12+0x20]
        movaps  XMMWORD PTR [rbp-0x2470], xmm5
        movdqu  xmm5, XMMWORD PTR [r12+0x30]
        mov     QWORD PTR [rbp-0x24e8], rax
        movaps  XMMWORD PTR [rbp-0x2460], xmm6
        movaps  XMMWORD PTR [rbp-0x2450], xmm7
        movaps  XMMWORD PTR [rbp-0x2440], xmm5
L4b32:
        mov     rdi, QWORD PTR [rbp-0x24c0]
        lea     r12, [rbp-0x1c50]
        call    L3a50
        mov     rsi, QWORD PTR [rbp-0x24d0]
        mov     rdi, QWORD PTR [rbp-0x24b8]
        call    L3c70
        lea     rax, [rbp-0x2050]
        lea     rsi, [rbp-0x24b0]
        mov     r15, rax
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x24c8], rax
        mov     QWORD PTR [rbp-0x24f0], rsi
        call    L3430
        mov     rdi, r15
        call    L25f0
        lea     rax, [rbp-0x2350]
        mov     QWORD PTR [rbp-0x24d8], r14
        mov     QWORD PTR [rbp-0x24e0], rax
        mov     r15, rax
L4b9f:
        mov     rdx, QWORD PTR [rbp-0x24c0]
        mov     rsi, QWORD PTR [rbp-0x24b8]
        mov     ecx, r13d
        mov     rdi, r12
        call    L3c90
        mov     rsi, QWORD PTR [rbp-0x24d0]
        mov     edx, r13d
        mov     rdi, rbx
        call    L2180
        mov     rdi, rbx
        call    L25c0
        mov     rdi, rbx
        call    L25f0
        mov     rsi, QWORD PTR [rbp-0x24c8]
        mov     rdi, rbx
        call    L2850
        mov     rsi, rbx
        mov     rdi, r12
        call    L2590
        mov     rdi, r12
        call    L24d0
        mov     rdi, r12
        call    L2700
        mov     rdi, r12
        call    L2520
        mov     rsi, QWORD PTR [rbp-0x24d8]
        mov     edx, r13d
        mov     rdi, rbx
        call    L2370
        mov     r14d, eax
        test    eax, eax
        jne     L4f20
        mov     rsi, rbx
        mov     rdi, r12
        add     r13d, 0x1
        call    L30a0
        mov     rdi, r15
        mov     rsi, r12
        add     r15, 0xc0
        call    L2e40
        cmp     r13d, 0x4
        jne     L4b9f
        lea     r13, [rbp-0x2420]
        lea     r15, [rbp-0x2490]
        mov     rdi, r13
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x24e8]
        mov     rdi, r13
        mov     edx, 0x40
        call    L1270
        mov     rsi, QWORD PTR [rbp-0x24e0]
        mov     edx, 0x300
        mov     rdi, r13
        call    L1270
        mov     rdi, r13
        call    L1300
        mov     rdx, r13
        mov     esi, 0x20
        mov     rdi, r15
        call    L1350
        mov     rdi, r13
        call    L13f0
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        movdqa  xmm1, XMMWORD PTR [rbp-0x24b0]
        movdqa  xmm2, XMMWORD PTR [rbp-0x24a0]
        pxor    xmm1, XMMWORD PTR [rbp-0x2490]
        pxor    xmm2, XMMWORD PTR [rbp-0x2480]
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
        jne     L4f27
L4d6f:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x24b8]
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x24b8]
        mov     rdi, QWORD PTR [rbp-0x24c8]
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x24c8]
        mov     rdi, QWORD PTR [rbp-0x24c0]
        mov     ecx, 0x200
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x24c0]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x2490], xmm0
        movaps  XMMWORD PTR [rbp-0x2480], xmm0
        mov     rdx, QWORD PTR [rbp-0x24f0]
        movaps  XMMWORD PTR [rbp-0x24b0], xmm0
        movaps  XMMWORD PTR [rbp-0x24a0], xmm0
        mov     rdx, QWORD PTR [rbp-0x24e8]
        movaps  XMMWORD PTR [rbp-0x2470], xmm0
        movaps  XMMWORD PTR [rbp-0x2460], xmm0
        movaps  XMMWORD PTR [rbp-0x2450], xmm0
        movaps  XMMWORD PTR [rbp-0x2440], xmm0
        mov     rdi, QWORD PTR [rbp-0x24e0]
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x24e0]
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
L4e48:
        lea     rax, [rbp-0x1450]
        mov     rdi, rax
        mov     rbx, rax
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x24d0]
        mov     edx, 0x520
        mov     rdi, rbx
        call    L1270
        mov     rdi, rbx
        mov     QWORD PTR [rbp-0x24b8], rbx
        lea     rbx, [rbp-0x1850]
        call    L1300
        mov     rdx, QWORD PTR [rbp-0x24b8]
        mov     esi, 0x40
        mov     rdi, rbx
        call    L1350
        mov     rdi, QWORD PTR [rbp-0x24b8]
        call    L13f0
        mov     rdi, QWORD PTR [rbp-0x24b8]
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x24b8]
        lea     rax, [rbp-0x2470]
        mov     r9, QWORD PTR [rbp-0x24d8]
        mov     ecx, 0x40
        mov     rdx, rbx
        mov     QWORD PTR [rbp-0x24e8], rax
        mov     r8, QWORD PTR [rbp-0x24c8]
        mov     esi, 0x40
        mov     rdi, rax
        push    r15
        push    r12
        call    L3fd0
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x1850], xmm0
        movaps  XMMWORD PTR [rbp-0x1840], xmm0
        movaps  XMMWORD PTR [rbp-0x1830], xmm0
        movaps  XMMWORD PTR [rbp-0x1820], xmm0
        pop     rax
        pop     rdx
        jmp     L4b32
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L4f20:
        lea     r15, [rbp-0x2490]
L4f27:
        mov     r14d, 0xfffffffa
        jmp     L4d6f
L4f32:
        lea     rax, [rbp-0x1450]
        lea     rbx, [rbp-0x1850]
        mov     QWORD PTR [rbp-0x24b8], rax
        lea     rax, [rbp-0x2470]
        lea     r12, [rbp-0x1c50]
        mov     QWORD PTR [rbp-0x24e8], rax
        lea     rax, [rbp-0x24b0]
        lea     r15, [rbp-0x2490]
        mov     QWORD PTR [rbp-0x24f0], rax
        lea     rax, [rbp-0x2050]
        mov     QWORD PTR [rbp-0x24c8], rax
        lea     rax, [rbp-0x2350]
        mov     QWORD PTR [rbp-0x24e0], rax
        jmp     L4f27
        // nop
        .byte   0x90

// mldsa44_verify_extmu (0x4f90)

L4f90:
        sub     rsp, 0x10
        mov     r9, rdx
        xor     r8d, r8d
        xor     ecx, ecx
        push    0x1
        mov     edx, 0x40
        call    L4a40
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa44_prepare_domain_separation_prefix (0x4fb0)

L4fb0:
        xor     eax, eax
        cmp     r8, 0xff
        ja      L5020
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbp
        mov     rbp, r8
        sub     rsp, 0x18
        test    r9d, r9d
        jne     L4ff8
        mov     BYTE PTR [rdi], 0x0
        mov     BYTE PTR [r12+0x1], r8b
        test    r8, r8
        jne     L50d8
L4fe2:
        lea     rax, [rbp+0x2]
L4fe6:
        add     rsp, 0x18
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L4ff8:
        cmp     r9d, 0xc
        ja      L508e
        mov     r13, rdx
        mov     eax, r9d
        lea     rdx, [rip+Lc500]
        mov     r14, rsi
        movsxd  rax, DWORD PTR [rdx+rax*4]
        add     rax, rdx
        jmp     rax
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L5020:
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
        cmp     r13, 0x20
        jne     L508e
L502e:
        mov     BYTE PTR [r12], 0x1
        mov     BYTE PTR [r12+0x1], bpl
        test    rbp, rbp
        jne     L50f0
L5041:
        lea     rcx, [rip+Lc540]
        xor     eax, eax
        mov     rdx, rcx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L5050:
        cmp     r9d, DWORD PTR [rdx]
        je      L50b8
        add     eax, 0x1
        add     rdx, 0x10
        cmp     eax, 0xc
        jne     L5050
L5061:
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
        je      L502e
L508e:
        xor     eax, eax
        jmp     L4fe6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x40
        je      L502e
        xor     eax, eax
        jmp     L4fe6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x30
        je      L502e
        xor     eax, eax
        jmp     L4fe6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L50b8:
        shl     rax, 0x4
        lea     rdx, [r12+rbp*1+0x2]
        lea     rax, [rcx+rax*1+0x4]
        mov     rcx, QWORD PTR [rax]
        mov     QWORD PTR [rdx], rcx
        mov     eax, DWORD PTR [rax+0x7]
        mov     DWORD PTR [rdx+0x7], eax
        jmp     L5061
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L50d8:
        lea     rdi, [rdi+0x2]
        mov     rdx, r8
        mov     rsi, rcx
        call    L1010
        jmp     L4fe2
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L50f0:
        lea     rdi, [r12+0x2]
        mov     rdx, rbp
        mov     rsi, rcx
        mov     DWORD PTR [rsp+0xc], r9d
        call    L1010
        mov     r9d, DWORD PTR [rsp+0xc]
        jmp     L5041
        // nop
        .byte   0x90

// mldsa44_signature (0x5110)

L5110:
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
        call    L4fb0
        test    rax, rax
        mov     QWORD PTR [rbp-0x1c0], rax
        jne     L51e0
        mov     edx, 0xfffffff7
        lea     r13, [rbp-0x1b0]
L5171:
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
L519f:
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
L51e0:
        lea     r13, [rbp-0x1b0]
        mov     esi, 0x20
        mov     rdi, r13
        call    L1020
        mov     edx, 0xfffffffd
        test    eax, eax
        jne     L5171
        push    0x0
        mov     r8, QWORD PTR [rbp-0x1c0]
        mov     rcx, r12
        mov     rdx, r14
        push    r15
        mov     rsi, QWORD PTR [rbp-0x1b8]
        mov     r9, r13
        mov     rdi, rbx
        call    L43f0
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      L519f
        jmp     L5171
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa44_verify (0x5240)

L5240:
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
        call    L4fb0
        test    rax, rax
        je      L52d8
        sub     rsp, 0x8
        mov     rcx, rbx
        mov     rdx, r14
        mov     r8, rax
        push    0x0
        mov     r9, r15
        mov     rsi, r13
        mov     rdi, r12
        call    L4a40
        mov     edx, eax
        pop     rax
        pop     rcx
L52ab:
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
L52d8:
        mov     edx, 0xfffffff7
        jmp     L52ab
        // nop
        .byte   0x90

// mldsa44_signature_pre_hash_internal (0x52e0)

L52e0:
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
        jne     L5378
L531a:
        mov     edx, 0xfffffff7
L531f:
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
L534d:
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
L5378:
        mov     rdi, r12
        call    L4fb0
        test    rax, rax
        je      L531a
        push    0x0
        xor     ecx, ecx
        mov     rdx, rax
        mov     r9, r13
        push    r14
        xor     r8d, r8d
        mov     rsi, r12
        mov     rdi, rbx
        call    L43f0
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      L534d
        jmp     L531f
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa44_signature_pre_hash_shake256 (0x53b0)

L53b0:
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
        call    L1430
        push    0xc
        mov     rdi, QWORD PTR [rbp-0x78]
        mov     r9, r15
        push    r12
        mov     r8, r14
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        call    L52e0
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

// mldsa44_verify_pre_hash_internal (0x5440)

L5440:
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
        je      L54d0
        lea     rbx, [rbp-0x190]
        mov     r12, rdi
        mov     rdi, rbx
        call    L4fb0
        mov     rdx, rax
        test    rax, rax
        je      L54d7
        sub     rsp, 0x8
        xor     ecx, ecx
        mov     r9, r13
        xor     r8d, r8d
        push    0x0
        mov     rsi, rbx
        mov     rdi, r12
        call    L4a40
        mov     edx, eax
        pop     rax
        pop     rcx
L54a1:
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
L54d0:
        lea     rbx, [rbp-0x190]
L54d7:
        mov     edx, 0xfffffff7
        jmp     L54a1
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa44_verify_pre_hash_shake256 (0x54e0)

L54e0:
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
        call    L1430
        sub     rsp, 0x8
        mov     r9, r15
        mov     r8, r14
        push    0xc
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        mov     rdi, r12
        call    L5440
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

// mldsa44_pk_from_sk (0x5570)

L5570:
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
        call    L3bf0
        mov     esi, 0x3
        mov     rdi, r14
        call    L3a80
        lea     rcx, [rbx+0x200]
        mov     rdx, r15
        mov     esi, 0x3
        mov     rdi, rcx
        mov     QWORD PTR [rsp+0x38], rcx
        mov     r13d, eax
        call    L3b50
        mov     rdi, r14
        mov     DWORD PTR [rsp+0x2c], eax
        call    L3a50
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
        call    L3eb0
        mov     r9, QWORD PTR [rsp+0x38]
        mov     r8, QWORD PTR [rsp+0x30]
        test    eax, eax
        mov     r11d, eax
        je      L5770
        lea     rbx, [rsp+0xc0]
        lea     rdx, [rsp+0x80]
L56a6:
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
L56d7:
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
L5770:
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L5780:
        movdqu  xmm1, XMMWORD PTR [rbx+rax*1+0x380]
        pxor    xmm1, XMMWORD PTR [r9+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x680
        jne     L5780
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
        call    L1430
        pxor    xmm1, xmm1
        mov     r8, QWORD PTR [rsp+0x18]
        xor     eax, eax
        mov     r9, QWORD PTR [rsp+0x20]
        mov     r11d, DWORD PTR [rsp+0x30]
        movdqa  xmm0, xmm1
        lea     rdx, [rsp+0x80]
L5872:
        movdqa  xmm2, XMMWORD PTR [rbx+rax*1]
        pxor    xmm2, XMMWORD PTR [rdx+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x40
        jne     L5872
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
        je      L56d7
        mov     r11d, 0xfffffff9
        jmp     L56a6

// mldsa65_unpack_pk_t1 (0x5930)

L5930:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x6
        lea     rsi, [rax+rsi*1+0x20]
        jmp     L2a20

// mldsa65_pack_sk_rho_key_tr (0x5940)

L5940:
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

// mldsa65_unpack_sk (0x5990)

L5990:
        mov     rax, QWORD PTR [rsp+0x8]
        movdqu  xmm0, XMMWORD PTR [rax]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rax+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rax+0x20]
        movups  XMMWORD PTR [rdx], xmm2
        movdqu  xmm3, XMMWORD PTR [rax+0x30]
        movups  XMMWORD PTR [rdx+0x10], xmm3
        movdqu  xmm4, XMMWORD PTR [rax+0x40]
        lea     rdx, [rax+0x80]
        movups  XMMWORD PTR [rsi], xmm4
        movdqu  xmm5, XMMWORD PTR [rax+0x50]
        movups  XMMWORD PTR [rsi+0x10], xmm5
        movdqu  xmm6, XMMWORD PTR [rax+0x60]
        movups  XMMWORD PTR [rsi+0x20], xmm6
        movdqu  xmm7, XMMWORD PTR [rax+0x70]
        movups  XMMWORD PTR [rsi+0x30], xmm7
        mov     QWORD PTR [r8], rdx
        lea     rdx, [rax+0x300]
        add     rax, 0x600
        mov     QWORD PTR [r9], rdx
        mov     QWORD PTR [rcx], rax
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_pack_sig_c (0x5a00)

L5a00:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rsi+0x20]
        movups  XMMWORD PTR [rdi+0x20], xmm2
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00

// mldsa65_pack_sig_h (0x5a20)

L5a20:
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
L5a6d:
        mov     rsi, r12
        mov     rdi, r13
        call    L2f40
        xor     eax, eax
        jmp     L5a95
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L5a80:
        mov     ecx, ebx
        add     ebx, 0x1
        mov     BYTE PTR [r15+rcx*1], al
L5a89:
        add     rax, 0x1
        cmp     rax, 0x100
        je      L5ad1
L5a95:
        mov     ecx, DWORD PTR [r14+rax*4]
        mov     edi, DWORD PTR [r13+rax*4+0x0]
        lea     esi, [rcx+0x3ff00]
        cmp     esi, 0x7fe00
        ja      L5ab8
        cmp     ecx, 0xfffc0100
        jne     L5a89
        test    edi, edi
        je      L5a89
L5ab8:
        cmp     ebx, 0x37
        jne     L5a80
        mov     eax, 0xffffffff
L5ac2:
        add     rsp, 0x18
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
L5ad1:
        mov     rax, QWORD PTR [rsp+0x8]
        sub     r12, 0xffffffffffffff80
        mov     BYTE PTR [rbp+0x0], bl
        add     rbp, 0x1
        add     r14, 0x400
        cmp     r12, rax
        jne     L5a6d
        xor     eax, eax
        jmp     L5ac2
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_pack_sig_z (0x5b00)

L5b00:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x7
        lea     rdi, [rax+rdi*1+0x30]
        jmp     L62d0

// mldsa65_sig_unpack_hints (0x5b10)

L5b10:
        push    rbp
        mov     r11, rsi
        mov     r8, rdi
        mov     ebp, edx
        push    rbx
        lea     rbx, [rsi+0xcb0]
        xor     esi, esi
        test    edx, edx
        je      L5b33
        lea     eax, [rdx+0x36]
        movzx   esi, BYTE PTR [r11+rax*1+0xcb0]
L5b33:
        lea     eax, [rbp+0x37]
        movzx   r9d, BYTE PTR [r11+rax*1+0xcb0]
        mov     r10, r9
        cmp     r9d, esi
        jb      L5bb6
        cmp     r9d, 0x37
        ja      L5bb6
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
        jae     L5bc0
        lea     edx, [rsi+0xcb0]
        mov     eax, esi
        add     rdx, r11
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L5b90:
        movzx   ecx, BYTE PTR [rdx]
        add     rdx, 0x1
        mov     DWORD PTR [r8+rcx*4], 0x1
        mov     ecx, eax
        add     eax, 0x1
        cmp     eax, r9d
        jae     L5bc0
        cmp     esi, eax
        jae     L5b90
        movzx   edi, BYTE PTR [rdx]
        cmp     BYTE PTR [rbx+rcx*1], dil
        jb      L5b90
L5bb6:
        mov     eax, 0xffffffff
        pop     rbx
        pop     rbp
        ret
        // xchg    ax, ax
        .byte   0x66,0x90
L5bc0:
        cmp     ebp, 0x5
        je      L5bd0
L5bc5:
        xor     eax, eax
        pop     rbx
        pop     rbp
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L5bd0:
        cmp     r9d, 0x37
        je      L5bc5
        cmp     BYTE PTR [r11+r10*1+0xcb0], 0x0
        jne     L5bb6
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L5be8:
        add     r10, 0x1
        cmp     r10d, 0x37
        je      L5bc5
        cmp     BYTE PTR [r11+r10*1+0xcb0], 0x0
        je      L5be8
        jmp     L5bb6
        // nop
        .byte   0x90

// mld_rej_eta_c65.constprop.0 (0x5c00)

L5c00:
        cmp     esi, 0xff
        ja      L5c90
        push    rbx
        mov     r10d, 0x1
        mov     r8, rdi
        mov     r9d, ecx
        mov     r11d, 0x4
        sub     r10d, edx
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L5c28:
        movzx   eax, BYTE PTR [rdx]
        mov     ecx, eax
        shr     al, 0x4
        and     ecx, 0xf
        cmp     cl, 0x8
        ja      L5c49
        movzx   ecx, cl
        mov     ebx, r11d
        mov     edi, esi
        add     esi, 0x1
        sub     ebx, ecx
        mov     DWORD PTR [r8+rdi*4], ebx
L5c49:
        cmp     esi, 0xff
        setbe   cl
        cmp     al, 0x8
        ja      L5c76
        test    cl, cl
        je      L5c76
        lea     edi, [rsi+0x1]
        movzx   eax, al
        mov     ecx, r11d
        mov     esi, esi
        sub     ecx, eax
        cmp     edi, 0xff
        mov     DWORD PTR [r8+rsi*4], ecx
        setbe   cl
        mov     esi, edi
L5c76:
        lea     eax, [r10+rdx*1]
        cmp     eax, r9d
        setb    al
        add     rdx, 0x1
        test    al, cl
        jne     L5c28
        mov     eax, esi
        pop     rbx
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L5c90:
        mov     eax, esi
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_poly_decompose (0x5ca0)

L5ca0:
        xor     ecx, ecx
        mov     r8d, 0x3ff000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L5cb0:
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
        jne     L5cb0
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_poly_use_hint (0x5d10)

L5d10:
        mov     r8, rsi
        mov     r9d, 0x3ff000
        xor     esi, esi
        jmp     L5d36
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L5d20:
        add     edx, 0x1
        and     edx, 0xf
L5d26:
        mov     DWORD PTR [rdi+rsi*1], edx
        add     rsi, 0x4
        cmp     rsi, 0x400
        je      L5d9d
L5d36:
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
        je      L5d26
        lea     r10d, [rcx-0x7fe001]
        xor     r10d, ecx
        and     eax, r10d
        xor     eax, ecx
        jg      L5d20
        sub     edx, 0x1
        and     edx, 0xf
        mov     DWORD PTR [rdi+rsi*1], edx
        add     rsi, 0x4
        cmp     rsi, 0x400
        jne     L5d36
L5d9d:
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_poly_uniform_eta_4x (0x5da0)

L5da0:
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
        call    L16d0
        mov     r8, r12
        mov     rcx, r13
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r15
        mov     r9d, 0x42
        mov     rbx, r15
        call    L14a0
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
        call    L1630
        mov     rdi, QWORD PTR [rsp+0x40]
        xor     esi, esi
        mov     rdx, r14
        mov     ecx, 0x110
        call    L5c00
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     rdx, rbx
        xor     esi, esi
        mov     ecx, 0x110
        mov     r13d, eax
        call    L5c00
        mov     rdi, QWORD PTR [rsp+0x30]
        xor     esi, esi
        mov     rdx, r15
        mov     ecx, 0x110
        mov     r12d, eax
        call    L5c00
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     rdi, QWORD PTR [rsp+0x28]
        xor     esi, esi
        mov     ecx, 0x110
        mov     ebx, eax
        call    L5c00
        cmp     r12d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r13d, 0xff
        jmp     L6051
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L5fb8:
        mov     r9, QWORD PTR [rsp+0x20]
        mov     rcx, QWORD PTR [rsp+0x58]
        mov     rdx, r15
        mov     rdi, r14
        mov     rsi, QWORD PTR [rsp+0x50]
        mov     r8d, 0x1
        mov     DWORD PTR [rsp+0x4c], r10d
        call    L1630
        mov     rdi, QWORD PTR [rsp+0x40]
        mov     esi, r13d
        mov     rdx, r14
        mov     ecx, 0x88
        call    L5c00
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     esi, r12d
        mov     ecx, 0x88
        mov     r13d, eax
        call    L5c00
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     esi, ebx
        mov     rdx, r15
        mov     ecx, 0x88
        mov     r12d, eax
        call    L5c00
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     esi, DWORD PTR [rsp+0x4c]
        mov     ecx, 0x88
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     ebx, eax
        call    L5c00
        cmp     r13d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r12d, 0xff
L6051:
        setbe   dl
        or      eax, edx
        cmp     ebx, 0xff
        setbe   dl
        or      al, dl
        jne     L5fb8
        cmp     r10d, 0xff
        jbe     L5fb8
        mov     rdi, QWORD PTR [rsp+0x20]
        call    L16e0
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

// mldsa65_poly_challenge (0x60b0)

L60b0:
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
        call    L1230
        mov     rsi, rbx
        mov     edx, 0x30
        mov     rdi, r12
        call    L1270
        lea     rbx, [rsp+0x20]
        mov     rdi, r12
        call    L1300
        mov     esi, 0x88
        mov     rdi, rbx
        mov     rdx, r12
        call    L1350
        mov     rax, rbx
        lea     rdi, [rsp+0x28]
        xor     ecx, ecx
        xor     esi, esi
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L6120:
        movzx   edx, BYTE PTR [rax]
        add     rax, 0x1
        shl     rdx, cl
        add     ecx, 0x8
        or      rsi, rdx
        cmp     rax, rdi
        jne     L6120
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
        jmp     L618f
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L6180:
        mov     eax, ecx
L6182:
        movzx   edx, BYTE PTR [rsp+rax*1+0x20]
        lea     ecx, [rax+0x1]
        cmp     r15d, edx
        jae     L61bb
L618f:
        cmp     ecx, 0x88
        jne     L6180
        mov     rdx, r12
        mov     esi, 0x88
        mov     rdi, rbx
        call    L1350
        movzx   edx, BYTE PTR [rsp+0x20]
        mov     eax, 0x1
        cmp     r15d, edx
        jb      L6182
        mov     ecx, 0x1
L61bb:
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
        jne     L618f
        mov     rdi, r12
        call    L13f0
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

// mldsa65_polyeta_pack (0x6230)

L6230:
        xor     eax, eax
        mov     ecx, 0x4
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L6240:
        mov     edx, ecx
        sub     dl, BYTE PTR [rsi+rax*8+0x4]
        mov     r8d, ecx
        sub     r8b, BYTE PTR [rsi+rax*8]
        shl     edx, 0x4
        or      edx, r8d
        mov     BYTE PTR [rdi+rax*1], dl
        add     rax, 0x1
        cmp     rax, 0x80
        jne     L6240
        mov     QWORD PTR [rsp-0x8], 0x0
        lea     rax, [rsp-0x8]
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_polyeta_unpack (0x6280)

L6280:
        lea     rdx, [rdi+0x4]
        lea     r9, [rsi+0x80]
        mov     edi, 0x4
L6290:
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
        jne     L6290
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa65_polyz_pack (0x62d0)

L62d0:
        push    rbx
        mov     rax, rdi
        mov     r8d, 0x80000
        mov     rdi, rsi
        lea     r9, [rax+0x280]
        mov     rsi, rax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L62f0:
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
        jne     L62f0
        pxor    xmm0, xmm0
        lea     rax, [rsp-0x10]
        movaps  XMMWORD PTR [rsp-0x10], xmm0
        pop     rbx
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_polyz_unpack (0x6360)

L6360:
        mov     rax, rsi
        mov     rdx, rdi
        lea     r9, [rsi+0x280]
        mov     r8d, 0x80000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L6378:
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
        jne     L6378
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_poly_uniform_gamma1 (0x63e0)

L63e0:
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
        call    L1230
        mov     rsi, r14
        mov     edx, 0x42
        mov     rdi, r12
        call    L1270
        mov     rdi, r12
        call    L1300
        mov     rdx, r12
        mov     rdi, rbx
        mov     esi, 0x2a8
        call    L1350
        mov     rsi, rbx
        mov     rdi, r13
        call    L6360
        mov     rdi, r12
        call    L13f0
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

// mldsa65_polyvecl_ntt (0x64b0)

L64b0:
        push    rbp
        lea     rbp, [rdi+0x1400]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L64c0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L25f0
        cmp     rbx, rbp
        jne     L64c0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyvecl_chknorm (0x64e0)

L64e0:
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
L6500:
        mov     rdi, rbx
        mov     esi, r12d
        add     rbx, 0x400
        call    L2e00
        or      ebp, eax
        cmp     rbx, r13
        jne     L6500
        add     rsp, 0x8
        mov     eax, ebp
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_polyveck_reduce (0x6530)

L6530:
        push    rbp
        lea     rbp, [rdi+0x1800]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L6540:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L24d0
        cmp     rbx, rbp
        jne     L6540
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyveck_caddq (0x6560)

L6560:
        push    rbp
        lea     rbp, [rdi+0x1800]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L6570:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L2520
        cmp     rbx, rbp
        jne     L6570
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyveck_invntt_tomont (0x6590)

L6590:
        push    rbp
        lea     rbp, [rdi+0x1800]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L65a0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L2700
        cmp     rbx, rbp
        jne     L65a0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyveck_unpack_eta_chknorm (0x65c0)

L65c0:
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
L65e0:
        mov     rsi, rbx
        mov     rdi, rbp
        sub     rbx, 0xffffffffffffff80
        call    L6280
        mov     esi, r13d
        mov     rdi, rbp
        call    L2e00
        or      r12d, eax
        cmp     rbx, r14
        jne     L65e0
        pop     rbx
        mov     eax, r12d
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_polyveck_decompose_pack_w1 (0x6610)

L6610:
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
L6630:
        mov     rsi, rbx
        mov     rdi, r12
        add     rbx, 0x400
        call    L5ca0
        mov     rdi, rbp
        mov     rsi, r12
        sub     rbp, 0xffffffffffffff80
        call    L2ea0
        cmp     rbx, r13
        jne     L6630
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

// mldsa65_polyvecl_unpack_eta (0x6670)

L6670:
        push    r12
        lea     r12, [rdi+0x1400]
        push    rbp
        mov     rbp, rsi
        push    rbx
        mov     rbx, rdi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L6688:
        mov     rsi, rbp
        mov     rdi, rbx
        add     rbx, 0x400
        sub     rbp, 0xffffffffffffff80
        call    L6280
        cmp     rbx, r12
        jne     L6688
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_polyvecl_unpack_z (0x66b0)

L66b0:
        push    r12
        lea     r12, [rsi+0xc80]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L66c8:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x280
        add     rbp, 0x400
        call    L6360
        cmp     rbx, r12
        jne     L66c8
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa65_polyvec_matrix_expand_lazy (0x66f0)

L66f0:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi+0x400], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x410], xmm1
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy (0x6710)

L6710:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15d, 0x1
        push    r14
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12, rsi
        push    rbx
        mov     rbx, rdx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x60
        movdqu  xmm1, XMMWORD PTR [rsi+0x400]
        movdqu  xmm2, XMMWORD PTR [rsi+0x410]
        lea     r14, [rsp+0x20]
        mov     BYTE PTR [rsp+0x1f], cl
        mov     rsi, r14
        mov     BYTE PTR [rsp+0x41], cl
        movaps  XMMWORD PTR [rsp+0x20], xmm1
        movaps  XMMWORD PTR [rsp+0x30], xmm2
        mov     BYTE PTR [rsp+0x40], 0x0
        call    L28f0
        mov     rsi, rbx
        mov     rdi, r13
        add     rbx, 0x400
        call    L2850
L677a:
        movzx   eax, BYTE PTR [rsp+0x1f]
        mov     rsi, r14
        mov     rdi, r12
        mov     BYTE PTR [rsp+0x40], r15b
        add     r15d, 0x1
        mov     BYTE PTR [rsp+0x41], al
        call    L28f0
        mov     rsi, rbx
        mov     rdi, r12
        add     rbx, 0x400
        call    L2850
        mov     rsi, r12
        mov     rdi, r13
        call    L2560
        cmp     r15d, 0x5
        jne     L677a
        mov     rdi, r13
        call    L24d0
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy (0x67f0)

L67f0:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, rsi
        push    r12
        xor     r12d, r12d
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x60
        movdqu  xmm1, XMMWORD PTR [rsi+0x400]
        movdqu  xmm2, XMMWORD PTR [rsi+0x410]
        lea     rax, [rsp+0x20]
        mov     QWORD PTR [rsp+0x10], rdi
        mov     QWORD PTR [rsp+0x8], rdx
        mov     QWORD PTR [rsp+0x18], rax
        movaps  XMMWORD PTR [rsp+0x20], xmm1
        movaps  XMMWORD PTR [rsp+0x30], xmm2
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L6840:
        mov     rax, QWORD PTR [rsp+0x8]
        mov     rdi, r14
        xor     r15d, r15d
        movzx   edx, WORD PTR [rax+0x8]
        mov     rsi, QWORD PTR [rax]
        add     edx, r12d
        movzx   edx, dx
        call    L63e0
        mov     rdi, r14
        call    L25f0
        mov     rbx, QWORD PTR [rsp+0x10]
        jmp     L68ae
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L6870:
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, r13
        mov     BYTE PTR [rsp+0x40], r12b
        mov     BYTE PTR [rsp+0x41], r15b
        call    L28f0
        mov     rsi, r14
        mov     rdi, r13
        call    L2850
        mov     rsi, r13
        mov     rdi, rbx
        call    L2560
L689d:
        add     r15d, 0x1
        add     rbx, 0x400
        cmp     r15d, 0x6
        je      L68e0
L68ae:
        test    r12d, r12d
        jne     L6870
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, rbx
        mov     BYTE PTR [rsp+0x40], 0x0
        mov     BYTE PTR [rsp+0x41], r15b
        call    L28f0
        mov     rsi, r14
        mov     rdi, rbx
        call    L2850
        jmp     L689d
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L68e0:
        add     r12d, 0x1
        cmp     r12d, 0x5
        jne     L6840
        pxor    xmm0, xmm0
        mov     rax, QWORD PTR [rsp+0x18]
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        mov     rbx, QWORD PTR [rsp+0x10]
        mov     rdi, rbx
        call    L6530
        mov     rdi, rbx
        call    L6590
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop
        .byte   0x90

// mld_compute_pack_t0_t165 (0x6930)

L6930:
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
        sub     rsp, 0xc40
        lea     rax, [rsp+0x820]
        mov     QWORD PTR [rsp+0x8], rdx
        lea     rbx, [rsp+0x20]
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x10], rax
        lea     r12, [rsp+0x420]
        call    L66f0
        xor     eax, eax
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L6980:
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     rsi, QWORD PTR [rsp+0x10]
        mov     ecx, eax
        mov     rdi, rbx
        mov     DWORD PTR [rsp+0x1c], eax
        call    L6710
        mov     rdi, rbx
        call    L2700
        mov     rsi, r15
        mov     rdi, r12
        sub     r15, 0xffffffffffffff80
        call    L6280
        mov     rsi, r12
        mov     rdi, rbx
        call    L2560
        mov     rdi, rbx
        call    L24d0
        mov     rdi, rbx
        call    L2520
        mov     rdx, rbx
        mov     rsi, rbx
        mov     rdi, r12
        call    L28a0
        mov     rdi, r14
        mov     rsi, r12
        add     r14, 0x140
        call    L29c0
        mov     rdi, r13
        mov     rsi, rbx
        add     r13, 0x1a0
        call    L2ab0
        mov     eax, DWORD PTR [rsp+0x1c]
        add     eax, 0x1
        cmp     eax, 0x6
        jne     L6980
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x10]
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x10]
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

// mld_H65 (0x6a50)

L6a50:
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
        call    L1230
        mov     rdx, r14
        mov     rsi, r13
        mov     rdi, rbx
        call    L1270
        test    r15, r15
        jne     L6ae0
        cmp     QWORD PTR [rsp+0x128], 0x0
        jne     L6afb
L6aa0:
        mov     rdi, rbx
        call    L1300
        mov     rdx, rbx
        mov     rsi, r12
        mov     rdi, rbp
        call    L1350
        mov     rdi, rbx
        call    L13f0
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
L6ae0:
        mov     rsi, QWORD PTR [rsp+0x8]
        mov     rdx, r15
        mov     rdi, rbx
        call    L1270
        cmp     QWORD PTR [rsp+0x128], 0x0
        je      L6aa0
L6afb:
        mov     rdx, QWORD PTR [rsp+0x128]
        mov     rsi, QWORD PTR [rsp+0x120]
        mov     rdi, rbx
        call    L1270
        jmp     L6aa0
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_keypair_internal (0x6b20)

L6b20:
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
        movzx   eax, WORD PTR [rip+Lc602]
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
        call    L1430
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
        call    L5da0
        add     rsp, 0x20
        lea     rdi, [rbx+0x400]
        mov     rsi, r12
        call    L6230
        mov     rsi, r13
        lea     rdi, [rbx+0x480]
        call    L6230
        mov     rsi, r15
        lea     rdi, [rbx+0x500]
        call    L6230
        mov     rsi, QWORD PTR [rbp-0x1540]
        lea     rdi, [rbx+0x580]
        call    L6230
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
        call    L5da0
        mov     rsi, QWORD PTR [rbp-0x1558]
        add     rsp, 0x20
        lea     rdi, [rbx+0x280]
        call    L6230
        mov     rdi, QWORD PTR [rbp-0x1548]
        mov     rsi, r12
        call    L6230
        mov     rsi, r13
        lea     rdi, [rbx+0x380]
        call    L6230
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
        call    L5da0
        add     rsp, 0x20
        lea     rdi, [rbx+0x80]
        mov     rsi, r12
        call    L6230
        mov     rsi, r13
        lea     rdi, [rbx+0x100]
        call    L6230
        mov     rsi, r15
        lea     rdi, [rbx+0x180]
        lea     r15, [rbp-0x14f0]
        call    L6230
        mov     rsi, QWORD PTR [rbp-0x1540]
        lea     rdi, [rbx+0x200]
        call    L6230
        mov     rdi, r12
        call    L64b0
        movdqa  xmm3, XMMWORD PTR [rbp-0x14b0]
        lea     rdi, [r14+0x20]
        movdqa  xmm4, XMMWORD PTR [rbp-0x14a0]
        mov     r8, QWORD PTR [rbp-0x1538]
        mov     rcx, QWORD PTR [rbp-0x1548]
        lea     rsi, [rbx+0x600]
        mov     rdx, r12
        movups  XMMWORD PTR [r14], xmm3
        movups  XMMWORD PTR [r14+0x10], xmm4
        call    L6930
        mov     r13d, eax
        test    eax, eax
        jne     L6da3
        mov     ecx, 0x7a0
        mov     rdx, r14
        mov     esi, 0x40
        mov     rdi, r15
        call    L1430
        mov     rsi, QWORD PTR [rbp-0x1538]
        mov     rdx, r15
        mov     rdi, rbx
        lea     rcx, [rbp-0x1450]
        call    L5940
L6da3:
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
        jne     L6e28
L6e09:
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
L6e28:
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
        jmp     L6e09
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa65_keypair (0x6e90)

L6e90:
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
        jne     L6ee8
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    L6b20
L6ec9:
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
L6ee8:
        mov     eax, 0xfffffffd
        jmp     L6ec9
        // nop
        .byte   0x90

// mldsa65_signature_internal (0x6ef0)

L6ef0:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rsi
        push    r14
        lea     rax, [rbp-0x2d10]
        lea     r14, [rbp-0x2bf0]
        push    r13
        push    r12
        lea     r12, [rbp-0x2c30]
        push    r10
        mov     rsi, r12
        push    rbx
        mov     rbx, r9
        lea     r9, [rbp-0x2cd0]
        sub     rsp, 0x2d68
        mov     QWORD PTR [rbp-0x2d28], rdi
        lea     rdi, [rbp-0x2c50]
        mov     r13d, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x2d20], rcx
        lea     rcx, [rbp-0x2cf0]
        mov     QWORD PTR [rbp-0x2d18], rdx
        mov     rdx, r14
        mov     QWORD PTR [rbp-0x2d30], r8
        mov     r8, rax
        mov     QWORD PTR [rbp-0x2d88], r9
        mov     QWORD PTR [rbp-0x2d78], rax
        mov     QWORD PTR [rbp-0x2d80], rcx
        mov     QWORD PTR [rbp-0x2d70], rdi
        push    QWORD PTR [r10]
        call    L5990
        pop     r8
        pop     r9
        test    r13d, r13d
        jne     L7478
        lea     rax, [rbp-0x2bd0]
        mov     r9, QWORD PTR [rbp-0x2d30]
        mov     esi, 0x40
        mov     rdx, r12
        mov     QWORD PTR [rbp-0x2d60], rax
        mov     r8, QWORD PTR [rbp-0x2d20]
        mov     rdi, rax
        mov     ecx, 0x40
        push    QWORD PTR [rbp-0x2d18]
        push    r15
        call    L6a50
        pop     rsi
        pop     rdi
L6fd8:
        mov     rdx, r14
        mov     r8, rbx
        mov     ecx, 0x20
        mov     esi, 0x40
        lea     rax, [rbp-0x2b90]
        mov     r9d, 0x20
        lea     r15, [rbp-0x2450]
        mov     QWORD PTR [rbp-0x2d68], rax
        mov     rdi, rax
        lea     rbx, [rbp-0x2850]
        lea     r12, [rbp-0x2050]
        push    0x40
        lea     r14, [rbp-0x2c90]
        push    QWORD PTR [rbp-0x2d60]
        call    L6a50
        lea     rax, [rbp-0x1c50]
        mov     rsi, QWORD PTR [rbp-0x2d70]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x2d58], rax
        call    L66f0
        pop     rax
        lea     rax, [rbp-0x2cb0]
        pop     rdx
        mov     QWORD PTR [rbp-0x2d40], rax
        lea     rax, [rbp-0x1830]
        xor     ecx, ecx
        mov     QWORD PTR [rbp-0x2d20], rax
        lea     rax, [rbp-0x2b50]
        mov     WORD PTR [rbp-0x2d30], cx
        mov     QWORD PTR [rbp-0x2d38], rax
        mov     QWORD PTR [rbp-0x2d18], r15
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L7088:
        mov     rax, QWORD PTR [rbp-0x2d68]
        mov     r15, QWORD PTR [rbp-0x2d20]
        mov     rcx, rbx
        mov     rdx, QWORD PTR [rbp-0x2d40]
        mov     rsi, QWORD PTR [rbp-0x2d58]
        mov     QWORD PTR [rbp-0x2cb0], rax
        movzx   eax, WORD PTR [rbp-0x2d30]
        mov     rdi, r15
        mov     WORD PTR [rbp-0x2ca8], ax
        call    L67f0
        mov     rdi, r15
        call    L6560
        mov     rsi, r15
        mov     r15, QWORD PTR [rbp-0x2d38]
        mov     rdx, rbx
        mov     rdi, r15
        call    L6610
        mov     rdi, r12
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x2d60]
        mov     rdi, r12
        mov     edx, 0x40
        call    L1270
        mov     rsi, r15
        mov     edx, 0x300
        mov     rdi, r12
        call    L1270
        mov     rdi, r12
        call    L1300
        mov     rdx, r12
        mov     esi, 0x30
        mov     rdi, r14
        call    L1350
        mov     rdi, r12
        call    L13f0
        mov     rdi, r12
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     r15, QWORD PTR [rbp-0x2d18]
        mov     rsi, r14
        mov     rdi, r15
        call    L60b0
        mov     rdi, r15
        xor     r15d, r15d
        call    L25f0
L7157:
        mov     rsi, r15
        mov     rdi, r12
        shl     rsi, 0x7
        add     rsi, QWORD PTR [rbp-0x2d10]
        call    L6280
        mov     rdi, r12
        call    L25f0
        mov     rsi, QWORD PTR [rbp-0x2d18]
        mov     rdi, r12
        call    L2850
        mov     rdi, r12
        call    L2700
        movzx   edx, WORD PTR [rbp-0x2ca8]
        mov     rsi, QWORD PTR [rbp-0x2cb0]
        mov     rdi, rbx
        add     edx, r15d
        movzx   edx, dx
        call    L63e0
        mov     rsi, rbx
        mov     rdi, r12
        call    L2560
        mov     rdi, r12
        call    L24d0
        mov     esi, 0x7ff3c
        mov     rdi, r12
        call    L2e00
        test    eax, eax
        jne     L746e
        mov     rdi, QWORD PTR [rbp-0x2d28]
        mov     edx, r15d
        mov     rsi, r12
        add     r15, 0x1
        call    L5b00
        cmp     r15, 0x5
        jne     L7157
        mov     QWORD PTR [rbp-0x2d48], r14
        xor     r15d, r15d
        xor     r13d, r13d
        mov     QWORD PTR [rbp-0x2d50], r12
        mov     r12, QWORD PTR [rbp-0x2d18]
L720b:
        mov     rsi, QWORD PTR [rbp-0x2cd0]
        mov     rdi, rbx
        add     rsi, r13
        call    L6280
        mov     rdi, rbx
        call    L25f0
        mov     rsi, r12
        mov     rdi, rbx
        call    L2850
        mov     rdi, rbx
        call    L2700
        mov     rax, QWORD PTR [rbp-0x2d20]
        mov     rsi, rbx
        lea     r14, [rax+r13*8]
        mov     rdi, r14
        call    L2590
        mov     rdi, r14
        call    L24d0
        mov     esi, 0x3fe3c
        mov     rdi, r14
        call    L2e00
        test    eax, eax
        jne     L7460
        mov     rsi, QWORD PTR [rbp-0x2cf0]
        mov     rdi, rbx
        add     rsi, r15
        call    L2c40
        mov     rdi, rbx
        call    L25f0
        mov     rsi, r12
        mov     rdi, rbx
        call    L2850
        mov     rdi, rbx
        call    L2700
        mov     rdi, rbx
        call    L24d0
        mov     esi, 0x3ff00
        mov     rdi, rbx
        call    L2e00
        test    eax, eax
        jne     L7460
        mov     rsi, rbx
        mov     rdi, r14
        sub     r13, 0xffffffffffffff80
        add     r15, 0x1a0
        call    L2560
        cmp     r13, 0x300
        jne     L720b
        mov     r15, QWORD PTR [rbp-0x2d28]
        mov     r14, QWORD PTR [rbp-0x2d48]
        mov     r12, QWORD PTR [rbp-0x2d50]
        mov     rsi, r14
        mov     rdi, r15
        call    L5a00
        mov     rdx, QWORD PTR [rbp-0x2d38]
        mov     rcx, rbx
        mov     rdi, r15
        mov     rsi, QWORD PTR [rbp-0x2d20]
        call    L5a20
        mov     edx, eax
L7313:
        mov     rdi, r12
        xor     eax, eax
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2d18]
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2d18]
        mov     rdi, QWORD PTR [rbp-0x2d20]
        mov     ecx, 0x300
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2d20]
        mov     rdi, QWORD PTR [rbp-0x2d38]
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2d38]
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rax, QWORD PTR [rbp-0x2d40]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rax], xmm0
        movaps  XMMWORD PTR [r14], xmm0
        movaps  XMMWORD PTR [r14+0x10], xmm0
        movaps  XMMWORD PTR [r14+0x20], xmm0
        test    edx, edx
        je      L73e5
        cmp     edx, 0xffffffff
        jne     L73b0
        add     WORD PTR [rbp-0x2d30], 0x5
        movzx   eax, WORD PTR [rbp-0x2d30]
        cmp     ax, 0xfffa
        jne     L7088
        mov     edx, 0xfffffffc
L73b0:
        mov     rbx, QWORD PTR [rbp-0x2d28]
        xor     eax, eax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0xce5], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0xced
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
L73e5:
        mov     QWORD PTR [rbp-0x2cd0], 0x0
        mov     rax, QWORD PTR [rbp-0x2d88]
        mov     QWORD PTR [rbp-0x2cf0], 0x0
        mov     rax, QWORD PTR [rbp-0x2d80]
        mov     QWORD PTR [rbp-0x2d10], 0x0
        mov     rax, QWORD PTR [rbp-0x2d78]
        mov     rdi, QWORD PTR [rbp-0x2d58]
        xor     eax, eax
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2d58]
        mov     rdi, QWORD PTR [rbp-0x2d70]
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2d70]
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
L7460:
        mov     r14, QWORD PTR [rbp-0x2d48]
        mov     r12, QWORD PTR [rbp-0x2d50]
L746e:
        mov     edx, 0xffffffff
        jmp     L7313
L7478:
        movdqu  xmm1, XMMWORD PTR [r15]
        movdqu  xmm2, XMMWORD PTR [r15+0x10]
        lea     rax, [rbp-0x2bd0]
        movdqu  xmm3, XMMWORD PTR [r15+0x20]
        movdqu  xmm4, XMMWORD PTR [r15+0x30]
        mov     QWORD PTR [rbp-0x2d60], rax
        movaps  XMMWORD PTR [rbp-0x2bd0], xmm1
        movaps  XMMWORD PTR [rbp-0x2bc0], xmm2
        movaps  XMMWORD PTR [rbp-0x2bb0], xmm3
        movaps  XMMWORD PTR [rbp-0x2ba0], xmm4
        jmp     L6fd8
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_signature_extmu (0x74c0)

L74c0:
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
        jne     L7540
        push    0x1
        xor     ecx, ecx
        mov     edx, 0x40
        mov     r9, rbx
        push    r14
        xor     r8d, r8d
        mov     rsi, r13
        mov     rdi, r12
        call    L6ef0
        pop     rdx
        pop     rcx
L751a:
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
L7540:
        mov     eax, 0xfffffffd
        jmp     L751a
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_verify_internal (0x7550)

L7550:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rdx
        push    r14
        lea     rax, [rbp-0x1430]
        mov     r14, rcx
        push    r13
        mov     r13, rax
        push    r12
        mov     r12, rsi
        lea     rsi, [rdi+0x30]
        push    r10
        push    rbx
        sub     rsp, 0x2900
        movdqu  xmm3, XMMWORD PTR [rdi]
        movdqu  xmm4, XMMWORD PTR [rdi+0x10]
        mov     QWORD PTR [rbp-0x28f8], rdi
        movdqu  xmm5, XMMWORD PTR [rdi+0x20]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x2908], r8
        mov     QWORD PTR [rbp-0x2910], r9
        mov     ebx, DWORD PTR [r10]
        mov     QWORD PTR [rbp-0x2900], rax
        movaps  XMMWORD PTR [rbp-0x28f0], xmm3
        movaps  XMMWORD PTR [rbp-0x28e0], xmm4
        movaps  XMMWORD PTR [rbp-0x28d0], xmm5
        call    L66b0
        mov     esi, 0x7ff3c
        mov     rdi, r13
        call    L64e0
        mov     r11, QWORD PTR [rbp-0x28f8]
        test    eax, eax
        jne     L7a79
        mov     r13d, eax
        test    ebx, ebx
        je      L7980
        movdqu  xmm6, XMMWORD PTR [r12]
        movdqu  xmm7, XMMWORD PTR [r12+0x10]
        lea     rax, [rbp-0x1850]
        lea     rbx, [rbp-0x1c50]
        mov     QWORD PTR [rbp-0x28f8], rax
        lea     rax, [rbp-0x2870]
        movaps  XMMWORD PTR [rbp-0x2870], xmm6
        movdqu  xmm6, XMMWORD PTR [r12+0x20]
        movaps  XMMWORD PTR [rbp-0x2860], xmm7
        movdqu  xmm7, XMMWORD PTR [r12+0x30]
        mov     QWORD PTR [rbp-0x2928], rax
        movaps  XMMWORD PTR [rbp-0x2850], xmm6
        movaps  XMMWORD PTR [rbp-0x2840], xmm7
L7655:
        mov     rdi, QWORD PTR [rbp-0x2900]
        mov     QWORD PTR [rbp-0x2918], r11
        lea     r12, [rbp-0x2050]
        call    L64b0
        mov     rsi, QWORD PTR [rbp-0x2910]
        mov     rdi, QWORD PTR [rbp-0x28f8]
        call    L66f0
        lea     rax, [rbp-0x2450]
        lea     r8, [rbp-0x28f0]
        mov     r14, rax
        mov     rdi, rax
        mov     rsi, r8
        mov     QWORD PTR [rbp-0x2908], rax
        mov     QWORD PTR [rbp-0x2930], r8
        call    L60b0
        mov     rdi, r14
        call    L25f0
        lea     rax, [rbp-0x2750]
        mov     QWORD PTR [rbp-0x2920], rax
        mov     r15, rax
L76c5:
        mov     rdx, QWORD PTR [rbp-0x2900]
        mov     rsi, QWORD PTR [rbp-0x28f8]
        mov     ecx, r13d
        mov     rdi, r12
        call    L6710
        mov     rsi, QWORD PTR [rbp-0x2910]
        mov     edx, r13d
        mov     rdi, rbx
        call    L5930
        mov     rdi, rbx
        call    L25c0
        mov     rdi, rbx
        call    L25f0
        mov     rsi, QWORD PTR [rbp-0x2908]
        mov     rdi, rbx
        call    L2850
        mov     rsi, rbx
        mov     rdi, r12
        call    L2590
        mov     rdi, r12
        call    L24d0
        mov     rdi, r12
        call    L2700
        mov     rdi, r12
        call    L2520
        mov     rsi, QWORD PTR [rbp-0x2918]
        mov     edx, r13d
        mov     rdi, rbx
        call    L5b10
        mov     r14d, eax
        test    eax, eax
        jne     L7a60
        mov     rsi, rbx
        mov     rdi, r12
        add     r13d, 0x1
        call    L5d10
        mov     rdi, r15
        mov     rsi, r12
        sub     r15, 0xffffffffffffff80
        call    L2ea0
        cmp     r13d, 0x6
        jne     L76c5
        mov     r8, QWORD PTR [rbp-0x2930]
        lea     r13, [rbp-0x2820]
        lea     r15, [rbp-0x28b0]
        mov     rdi, r13
        mov     QWORD PTR [rbp-0x2910], r8
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x2928]
        mov     rdi, r13
        mov     edx, 0x40
        call    L1270
        mov     rsi, QWORD PTR [rbp-0x2920]
        mov     edx, 0x300
        mov     rdi, r13
        call    L1270
        mov     rdi, r13
        call    L1300
        mov     rdx, r13
        mov     esi, 0x30
        mov     rdi, r15
        call    L1350
        mov     rdi, r13
        call    L13f0
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm1, xmm1
        mov     r8, QWORD PTR [rbp-0x2910]
        movdqa  xmm0, xmm1
L77ff:
        movdqa  xmm2, XMMWORD PTR [r8+rax*1]
        pxor    xmm2, XMMWORD PTR [r15+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x30
        jne     L77ff
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
        jne     L7a6e
L78a1:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x28f8]
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x28f8]
        mov     rdi, QWORD PTR [rbp-0x2908]
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2908]
        mov     rdi, QWORD PTR [rbp-0x2900]
        mov     ecx, 0x280
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2900]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x28b0], xmm0
        movaps  XMMWORD PTR [rbp-0x28a0], xmm0
        movaps  XMMWORD PTR [rbp-0x2890], xmm0
        movaps  XMMWORD PTR [rbp-0x28f0], xmm0
        movaps  XMMWORD PTR [rbp-0x28e0], xmm0
        movaps  XMMWORD PTR [rbp-0x28d0], xmm0
        mov     rdx, QWORD PTR [rbp-0x2928]
        movaps  XMMWORD PTR [rbp-0x2870], xmm0
        movaps  XMMWORD PTR [rbp-0x2860], xmm0
        movaps  XMMWORD PTR [rbp-0x2850], xmm0
        movaps  XMMWORD PTR [rbp-0x2840], xmm0
        mov     rdi, QWORD PTR [rbp-0x2920]
        mov     ecx, 0x60
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x2920]
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
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L7980:
        lea     rax, [rbp-0x1850]
        mov     QWORD PTR [rbp-0x2918], r11
        mov     rdi, rax
        mov     rbx, rax
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x2910]
        mov     edx, 0x7a0
        mov     rdi, rbx
        call    L1270
        mov     rdi, rbx
        mov     QWORD PTR [rbp-0x28f8], rbx
        lea     rbx, [rbp-0x1c50]
        call    L1300
        mov     rdx, QWORD PTR [rbp-0x28f8]
        mov     esi, 0x40
        mov     rdi, rbx
        call    L1350
        mov     rdi, QWORD PTR [rbp-0x28f8]
        call    L13f0
        mov     rdi, QWORD PTR [rbp-0x28f8]
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x28f8]
        mov     ecx, 0x40
        mov     r8, r14
        mov     rdx, rbx
        mov     esi, 0x40
        lea     rax, [rbp-0x2870]
        mov     r9, QWORD PTR [rbp-0x2908]
        mov     QWORD PTR [rbp-0x2928], rax
        mov     rdi, rax
        push    r15
        push    r12
        call    L6a50
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x1c50], xmm0
        movaps  XMMWORD PTR [rbp-0x1c40], xmm0
        movaps  XMMWORD PTR [rbp-0x1c30], xmm0
        movaps  XMMWORD PTR [rbp-0x1c20], xmm0
        pop     rax
        mov     r11, QWORD PTR [rbp-0x2918]
        pop     rdx
        jmp     L7655
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L7a60:
        mov     r8, QWORD PTR [rbp-0x2930]
        lea     r15, [rbp-0x28b0]
L7a6e:
        mov     r14d, 0xfffffffa
        jmp     L78a1
L7a79:
        lea     rax, [rbp-0x1850]
        lea     rbx, [rbp-0x1c50]
        mov     QWORD PTR [rbp-0x28f8], rax
        lea     rax, [rbp-0x2870]
        lea     r8, [rbp-0x28f0]
        mov     QWORD PTR [rbp-0x2928], rax
        lea     rax, [rbp-0x2450]
        lea     r12, [rbp-0x2050]
        mov     QWORD PTR [rbp-0x2908], rax
        lea     rax, [rbp-0x2750]
        lea     r15, [rbp-0x28b0]
        mov     QWORD PTR [rbp-0x2920], rax
        jmp     L7a6e
        // nop
        .byte   0x90

// mldsa65_verify_extmu (0x7ad0)

L7ad0:
        sub     rsp, 0x10
        mov     r9, rdx
        xor     r8d, r8d
        xor     ecx, ecx
        push    0x1
        mov     edx, 0x40
        call    L7550
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa65_prepare_domain_separation_prefix (0x7af0)

L7af0:
        xor     eax, eax
        cmp     r8, 0xff
        ja      L7b60
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbp
        mov     rbp, r8
        sub     rsp, 0x18
        test    r9d, r9d
        jne     L7b38
        mov     BYTE PTR [rdi], 0x0
        mov     BYTE PTR [r12+0x1], r8b
        test    r8, r8
        jne     L7c18
L7b22:
        lea     rax, [rbp+0x2]
L7b26:
        add     rsp, 0x18
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L7b38:
        cmp     r9d, 0xc
        ja      L7bce
        mov     r13, rdx
        mov     eax, r9d
        lea     rdx, [rip+Lc620]
        mov     r14, rsi
        movsxd  rax, DWORD PTR [rdx+rax*4]
        add     rax, rdx
        jmp     rax
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L7b60:
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
        cmp     r13, 0x20
        jne     L7bce
L7b6e:
        mov     BYTE PTR [r12], 0x1
        mov     BYTE PTR [r12+0x1], bpl
        test    rbp, rbp
        jne     L7c30
L7b81:
        lea     rcx, [rip+Lc660]
        xor     eax, eax
        mov     rdx, rcx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L7b90:
        cmp     r9d, DWORD PTR [rdx]
        je      L7bf8
        add     eax, 0x1
        add     rdx, 0x10
        cmp     eax, 0xc
        jne     L7b90
L7ba1:
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
        je      L7b6e
L7bce:
        xor     eax, eax
        jmp     L7b26
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x40
        je      L7b6e
        xor     eax, eax
        jmp     L7b26
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x30
        je      L7b6e
        xor     eax, eax
        jmp     L7b26
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L7bf8:
        shl     rax, 0x4
        lea     rdx, [r12+rbp*1+0x2]
        lea     rax, [rcx+rax*1+0x4]
        mov     rcx, QWORD PTR [rax]
        mov     QWORD PTR [rdx], rcx
        mov     eax, DWORD PTR [rax+0x7]
        mov     DWORD PTR [rdx+0x7], eax
        jmp     L7ba1
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L7c18:
        lea     rdi, [rdi+0x2]
        mov     rdx, r8
        mov     rsi, rcx
        call    L1010
        jmp     L7b22
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L7c30:
        lea     rdi, [r12+0x2]
        mov     rdx, rbp
        mov     rsi, rcx
        mov     DWORD PTR [rsp+0xc], r9d
        call    L1010
        mov     r9d, DWORD PTR [rsp+0xc]
        jmp     L7b81
        // nop
        .byte   0x90

// mldsa65_signature (0x7c50)

L7c50:
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
        call    L7af0
        test    rax, rax
        mov     QWORD PTR [rbp-0x1c0], rax
        jne     L7d20
        mov     edx, 0xfffffff7
        lea     r13, [rbp-0x1b0]
L7cb1:
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
L7cdf:
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
L7d20:
        lea     r13, [rbp-0x1b0]
        mov     esi, 0x20
        mov     rdi, r13
        call    L1020
        mov     edx, 0xfffffffd
        test    eax, eax
        jne     L7cb1
        push    0x0
        mov     r8, QWORD PTR [rbp-0x1c0]
        mov     rcx, r12
        mov     rdx, r14
        push    r15
        mov     rsi, QWORD PTR [rbp-0x1b8]
        mov     r9, r13
        mov     rdi, rbx
        call    L6ef0
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      L7cdf
        jmp     L7cb1
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa65_verify (0x7d80)

L7d80:
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
        call    L7af0
        test    rax, rax
        je      L7e18
        sub     rsp, 0x8
        mov     rcx, rbx
        mov     rdx, r14
        mov     r8, rax
        push    0x0
        mov     r9, r15
        mov     rsi, r13
        mov     rdi, r12
        call    L7550
        mov     edx, eax
        pop     rax
        pop     rcx
L7deb:
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
L7e18:
        mov     edx, 0xfffffff7
        jmp     L7deb
        // nop
        .byte   0x90

// mldsa65_signature_pre_hash_internal (0x7e20)

L7e20:
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
        jne     L7eb8
L7e5a:
        mov     edx, 0xfffffff7
L7e5f:
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
L7e8d:
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
L7eb8:
        mov     rdi, r12
        call    L7af0
        test    rax, rax
        je      L7e5a
        push    0x0
        xor     ecx, ecx
        mov     rdx, rax
        mov     r9, r13
        push    r14
        xor     r8d, r8d
        mov     rsi, r12
        mov     rdi, rbx
        call    L6ef0
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      L7e8d
        jmp     L7e5f
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa65_signature_pre_hash_shake256 (0x7ef0)

L7ef0:
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
        call    L1430
        push    0xc
        mov     rdi, QWORD PTR [rbp-0x78]
        mov     r9, r15
        push    r12
        mov     r8, r14
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        call    L7e20
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

// mldsa65_verify_pre_hash_internal (0x7f80)

L7f80:
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
        je      L8010
        lea     rbx, [rbp-0x190]
        mov     r12, rdi
        mov     rdi, rbx
        call    L7af0
        mov     rdx, rax
        test    rax, rax
        je      L8017
        sub     rsp, 0x8
        xor     ecx, ecx
        mov     r9, r13
        xor     r8d, r8d
        push    0x0
        mov     rsi, rbx
        mov     rdi, r12
        call    L7550
        mov     edx, eax
        pop     rax
        pop     rcx
L7fe1:
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
L8010:
        lea     rbx, [rbp-0x190]
L8017:
        mov     edx, 0xfffffff7
        jmp     L7fe1
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa65_verify_pre_hash_shake256 (0x8020)

L8020:
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
        call    L1430
        sub     rsp, 0x8
        mov     r9, r15
        mov     r8, r14
        push    0xc
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        mov     rdi, r12
        call    L7f80
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

// mldsa65_pk_from_sk (0x80b0)

L80b0:
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
        call    L6670
        mov     esi, 0x5
        mov     rdi, r14
        call    L64e0
        lea     rcx, [rbx+0x300]
        mov     rdx, r15
        mov     esi, 0x5
        mov     rdi, rcx
        mov     QWORD PTR [rsp+0x38], rcx
        mov     r13d, eax
        call    L65c0
        mov     rdi, r14
        mov     DWORD PTR [rsp+0x2c], eax
        call    L64b0
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
        call    L6930
        mov     r9, QWORD PTR [rsp+0x38]
        mov     r8, QWORD PTR [rsp+0x30]
        test    eax, eax
        mov     r11d, eax
        je      L82b0
        lea     rbx, [rsp+0xc0]
        lea     rdx, [rsp+0x80]
L81e6:
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
L8217:
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
L82b0:
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L82c0:
        movdqu  xmm1, XMMWORD PTR [rbx+rax*1+0x600]
        pxor    xmm1, XMMWORD PTR [r9+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0x9c0
        jne     L82c0
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
        call    L1430
        pxor    xmm1, xmm1
        mov     r9, QWORD PTR [rsp+0x18]
        xor     eax, eax
        mov     r8, QWORD PTR [rsp+0x20]
        mov     r11d, DWORD PTR [rsp+0x30]
        movdqa  xmm0, xmm1
        lea     rdx, [rsp+0x80]
L83b2:
        movdqa  xmm2, XMMWORD PTR [rbx+rax*1]
        pxor    xmm2, XMMWORD PTR [rdx+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x40
        jne     L83b2
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
        je      L8217
        mov     r11d, 0xfffffff9
        jmp     L81e6

// mldsa87_unpack_pk_t1 (0x8470)

L8470:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x6
        lea     rsi, [rax+rsi*1+0x20]
        jmp     L2a20

// mldsa87_pack_sk_rho_key_tr (0x8480)

L8480:
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

// mldsa87_unpack_sk (0x84d0)

L84d0:
        mov     rax, QWORD PTR [rsp+0x8]
        movdqu  xmm0, XMMWORD PTR [rax]
        movups  XMMWORD PTR [rdi], xmm0
        movdqu  xmm1, XMMWORD PTR [rax+0x10]
        movups  XMMWORD PTR [rdi+0x10], xmm1
        movdqu  xmm2, XMMWORD PTR [rax+0x20]
        movups  XMMWORD PTR [rdx], xmm2
        movdqu  xmm3, XMMWORD PTR [rax+0x30]
        movups  XMMWORD PTR [rdx+0x10], xmm3
        movdqu  xmm4, XMMWORD PTR [rax+0x40]
        lea     rdx, [rax+0x80]
        movups  XMMWORD PTR [rsi], xmm4
        movdqu  xmm5, XMMWORD PTR [rax+0x50]
        movups  XMMWORD PTR [rsi+0x10], xmm5
        movdqu  xmm6, XMMWORD PTR [rax+0x60]
        movups  XMMWORD PTR [rsi+0x20], xmm6
        movdqu  xmm7, XMMWORD PTR [rax+0x70]
        movups  XMMWORD PTR [rsi+0x30], xmm7
        mov     QWORD PTR [r8], rdx
        lea     rdx, [rax+0x320]
        add     rax, 0x620
        mov     QWORD PTR [r9], rdx
        mov     QWORD PTR [rcx], rax
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_pack_sig_c (0x8540)

L8540:
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

// mldsa87_pack_sig_h (0x8570)

L8570:
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
L85d2:
        mov     rsi, r12
        mov     rdi, r13
        call    L2f40
        xor     eax, eax
        jmp     L85fd
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L85e8:
        mov     ecx, ebx
        add     ebx, 0x1
        mov     BYTE PTR [r15+rcx*1], al
L85f1:
        add     rax, 0x1
        cmp     rax, 0x100
        je      L8639
L85fd:
        mov     ecx, DWORD PTR [r14+rax*4]
        mov     edi, DWORD PTR [r13+rax*4+0x0]
        lea     esi, [rcx+0x3ff00]
        cmp     esi, 0x7fe00
        ja      L8620
        cmp     ecx, 0xfffc0100
        jne     L85f1
        test    edi, edi
        je      L85f1
L8620:
        cmp     ebx, 0x4b
        jne     L85e8
        mov     eax, 0xffffffff
L862a:
        add     rsp, 0x18
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
L8639:
        mov     rax, QWORD PTR [rsp+0x8]
        sub     r12, 0xffffffffffffff80
        mov     BYTE PTR [rbp+0x0], bl
        add     rbp, 0x1
        add     r14, 0x400
        cmp     r12, rax
        jne     L85d2
        xor     eax, eax
        jmp     L862a
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_pack_sig_z (0x8660)

L8660:
        lea     eax, [rdx+rdx*4]
        shl     eax, 0x7
        lea     rdi, [rax+rdi*1+0x40]
        jmp     L8f40

// mldsa87_sig_unpack_hints (0x8670)

L8670:
        push    rbp
        mov     r11, rsi
        mov     r8, rdi
        mov     ebp, edx
        push    rbx
        lea     rbx, [rsi+0x11c0]
        xor     esi, esi
        test    edx, edx
        je      L8693
        lea     eax, [rdx+0x4a]
        movzx   esi, BYTE PTR [r11+rax*1+0x11c0]
L8693:
        lea     eax, [rbp+0x4b]
        movzx   r9d, BYTE PTR [r11+rax*1+0x11c0]
        mov     r10, r9
        cmp     r9d, esi
        jb      L8716
        cmp     r9d, 0x4b
        ja      L8716
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
        jae     L8720
        lea     edx, [rsi+0x11c0]
        mov     eax, esi
        add     rdx, r11
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L86f0:
        movzx   ecx, BYTE PTR [rdx]
        add     rdx, 0x1
        mov     DWORD PTR [r8+rcx*4], 0x1
        mov     ecx, eax
        add     eax, 0x1
        cmp     eax, r9d
        jae     L8720
        cmp     esi, eax
        jae     L86f0
        movzx   edi, BYTE PTR [rdx]
        cmp     BYTE PTR [rbx+rcx*1], dil
        jb      L86f0
L8716:
        mov     eax, 0xffffffff
        pop     rbx
        pop     rbp
        ret
        // xchg    ax, ax
        .byte   0x66,0x90
L8720:
        cmp     ebp, 0x7
        je      L8730
L8725:
        xor     eax, eax
        pop     rbx
        pop     rbp
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
L8730:
        cmp     r9d, 0x4b
        je      L8725
        cmp     BYTE PTR [r11+r10*1+0x11c0], 0x0
        jne     L8716
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L8748:
        add     r10, 0x1
        cmp     r10d, 0x4b
        je      L8725
        cmp     BYTE PTR [r11+r10*1+0x11c0], 0x0
        je      L8748
        jmp     L8716
        // nop
        .byte   0x90

// mld_rej_eta_c87.constprop.0 (0x8760)

L8760:
        mov     r8, rdi
        cmp     esi, 0xff
        ja      L8806
        mov     r9d, 0x1
        mov     r10d, 0x2
        sub     r9d, edx
        // xchg    ax, ax
        .byte   0x66,0x90
L8780:
        movzx   eax, BYTE PTR [rdx]
        mov     ecx, eax
        shr     al, 0x4
        and     ecx, 0xf
        movzx   eax, al
        cmp     cl, 0xf
        je      L87b5
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
L87b5:
        cmp     esi, 0xff
        setbe   cl
        cmp     eax, 0xe
        ja      L87ee
        test    cl, cl
        je      L87ee
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
L87ee:
        lea     eax, [r9+rdx*1]
        cmp     eax, 0x87
        setbe   al
        add     rdx, 0x1
        test    al, cl
        jne     L8780
L8806:
        mov     eax, esi
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00

// mldsa87_poly_decompose (0x8810)

L8810:
        xor     ecx, ecx
        mov     r8d, 0x3ff000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L8820:
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
        jne     L8820
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_poly_use_hint (0x8880)

L8880:
        mov     r8, rsi
        mov     r9d, 0x3ff000
        xor     esi, esi
        jmp     L88a6
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L8890:
        add     edx, 0x1
        and     edx, 0xf
L8896:
        mov     DWORD PTR [rdi+rsi*1], edx
        add     rsi, 0x4
        cmp     rsi, 0x400
        je      L890d
L88a6:
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
        je      L8896
        lea     r10d, [rcx-0x7fe001]
        xor     r10d, ecx
        and     eax, r10d
        xor     eax, ecx
        jg      L8890
        sub     edx, 0x1
        and     edx, 0xf
        mov     DWORD PTR [rdi+rsi*1], edx
        add     rsi, 0x4
        cmp     rsi, 0x400
        jne     L88a6
L890d:
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_poly_uniform_eta_4x (0x8910)

L8910:
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
        call    L16d0
        mov     r8, r12
        mov     rcx, r13
        mov     rdx, rbx
        mov     rsi, r14
        mov     rdi, r15
        mov     r9d, 0x42
        mov     rbx, r15
        call    L14a0
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
        call    L1630
        mov     rdi, QWORD PTR [rsp+0x40]
        xor     esi, esi
        mov     rdx, r14
        call    L8760
        mov     rdi, QWORD PTR [rsp+0x38]
        xor     esi, esi
        mov     rdx, r15
        mov     r13d, eax
        call    L8760
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     rdx, rbx
        xor     esi, esi
        mov     r12d, eax
        call    L8760
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     rdi, QWORD PTR [rsp+0x28]
        xor     esi, esi
        mov     ebx, eax
        call    L8760
        cmp     r12d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r13d, 0xff
        jmp     L8b95
L8b10:
        mov     r9, QWORD PTR [rsp+0x20]
        mov     rcx, QWORD PTR [rsp+0x58]
        mov     rsi, r15
        mov     rdi, r14
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     r8d, 0x1
        mov     DWORD PTR [rsp+0x4c], r10d
        call    L1630
        mov     rdi, QWORD PTR [rsp+0x40]
        mov     esi, r13d
        mov     rdx, r14
        call    L8760
        mov     rdi, QWORD PTR [rsp+0x38]
        mov     esi, r12d
        mov     rdx, r15
        mov     r13d, eax
        call    L8760
        mov     rdx, QWORD PTR [rsp+0x50]
        mov     rdi, QWORD PTR [rsp+0x30]
        mov     esi, ebx
        mov     r12d, eax
        call    L8760
        mov     rdx, QWORD PTR [rsp+0x58]
        mov     esi, DWORD PTR [rsp+0x4c]
        mov     rdi, QWORD PTR [rsp+0x28]
        mov     ebx, eax
        call    L8760
        cmp     r13d, 0xff
        mov     r10d, eax
        setbe   al
        cmp     r12d, 0xff
L8b95:
        setbe   dl
        or      eax, edx
        cmp     ebx, 0xff
        setbe   dl
        or      al, dl
        jne     L8b10
        cmp     r10d, 0xff
        jbe     L8b10
        mov     rdi, QWORD PTR [rsp+0x20]
        call    L16e0
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

// mldsa87_poly_challenge (0x8bf0)

L8bf0:
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
        call    L1230
        mov     rsi, rbx
        mov     edx, 0x40
        mov     rdi, r12
        call    L1270
        lea     rbx, [rsp+0x20]
        mov     rdi, r12
        call    L1300
        mov     esi, 0x88
        mov     rdi, rbx
        mov     rdx, r12
        call    L1350
        mov     rax, rbx
        lea     rdi, [rsp+0x28]
        xor     ecx, ecx
        xor     esi, esi
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L8c60:
        movzx   edx, BYTE PTR [rax]
        add     rax, 0x1
        shl     rdx, cl
        add     ecx, 0x8
        or      rsi, rdx
        cmp     rax, rdi
        jne     L8c60
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
        jmp     L8ccf
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L8cc0:
        mov     eax, ecx
L8cc2:
        movzx   edx, BYTE PTR [rsp+rax*1+0x20]
        lea     ecx, [rax+0x1]
        cmp     r15d, edx
        jae     L8cfb
L8ccf:
        cmp     ecx, 0x88
        jne     L8cc0
        mov     rdx, r12
        mov     esi, 0x88
        mov     rdi, rbx
        call    L1350
        movzx   edx, BYTE PTR [rsp+0x20]
        mov     eax, 0x1
        cmp     r15d, edx
        jb      L8cc2
        mov     ecx, 0x1
L8cfb:
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
        jne     L8ccf
        mov     rdi, r12
        call    L13f0
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

// mldsa87_polyeta_pack (0x8d70)

L8d70:
        push    r12
        mov     rax, rsi
        mov     r8, rdi
        lea     r9, [rsi+0x400]
        push    rbp
        mov     edx, 0x2
        push    rbx
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L8d90:
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
        jne     L8d90
        mov     QWORD PTR [rsp-0x8], 0x0
        lea     rax, [rsp-0x8]
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_polyeta_unpack (0x8e30)

L8e30:
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
L8e50:
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
        jne     L8e50
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyz_pack (0x8f40)

L8f40:
        push    rbx
        mov     rax, rdi
        mov     r8d, 0x80000
        mov     rdi, rsi
        lea     r9, [rax+0x280]
        mov     rsi, rax
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L8f60:
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
        jne     L8f60
        pxor    xmm0, xmm0
        lea     rax, [rsp-0x10]
        movaps  XMMWORD PTR [rsp-0x10], xmm0
        pop     rbx
        ret
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_polyz_unpack (0x8fd0)

L8fd0:
        mov     rax, rsi
        mov     rdx, rdi
        lea     r9, [rsi+0x280]
        mov     r8d, 0x80000
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
L8fe8:
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
        jne     L8fe8
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_poly_uniform_gamma1 (0x9050)

L9050:
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
        call    L1230
        mov     rsi, r14
        mov     edx, 0x42
        mov     rdi, r12
        call    L1270
        mov     rdi, r12
        call    L1300
        mov     rdx, r12
        mov     rdi, rbx
        mov     esi, 0x2a8
        call    L1350
        mov     rsi, rbx
        mov     rdi, r13
        call    L8fd0
        mov     rdi, r12
        call    L13f0
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

// mldsa87_polyvecl_ntt (0x9120)

L9120:
        push    rbp
        lea     rbp, [rdi+0x1c00]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L9130:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L25f0
        cmp     rbx, rbp
        jne     L9130
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyvecl_chknorm (0x9150)

L9150:
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
L9170:
        mov     rdi, rbx
        mov     esi, r12d
        add     rbx, 0x400
        call    L2e00
        or      ebp, eax
        cmp     rbx, r13
        jne     L9170
        add     rsp, 0x8
        mov     eax, ebp
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        ret
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyveck_reduce (0x91a0)

L91a0:
        push    rbp
        lea     rbp, [rdi+0x2000]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L91b0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L24d0
        cmp     rbx, rbp
        jne     L91b0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyveck_caddq (0x91d0)

L91d0:
        push    rbp
        lea     rbp, [rdi+0x2000]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L91e0:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L2520
        cmp     rbx, rbp
        jne     L91e0
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyveck_invntt_tomont (0x9200)

L9200:
        push    rbp
        lea     rbp, [rdi+0x2000]
        push    rbx
        mov     rbx, rdi
        sub     rsp, 0x8
L9210:
        mov     rdi, rbx
        add     rbx, 0x400
        call    L2700
        cmp     rbx, rbp
        jne     L9210
        add     rsp, 0x8
        pop     rbx
        pop     rbp
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyveck_unpack_eta_chknorm (0x9230)

L9230:
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
L9250:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        call    L8e30
        mov     esi, r13d
        mov     rdi, rbp
        call    L2e00
        or      r12d, eax
        cmp     rbx, r14
        jne     L9250
        pop     rbx
        mov     eax, r12d
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_polyveck_decompose_pack_w1 (0x9280)

L9280:
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
L92a0:
        mov     rsi, rbx
        mov     rdi, r12
        add     rbx, 0x400
        call    L8810
        mov     rdi, rbp
        mov     rsi, r12
        sub     rbp, 0xffffffffffffff80
        call    L2ea0
        cmp     rbx, r13
        jne     L92a0
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

// mldsa87_polyvecl_unpack_eta (0x92e0)

L92e0:
        push    r12
        lea     r12, [rsi+0x2a0]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L92f8:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x60
        add     rbp, 0x400
        call    L8e30
        cmp     rbx, r12
        jne     L92f8
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyvecl_unpack_z (0x9320)

L9320:
        push    r12
        lea     r12, [rsi+0x1180]
        push    rbp
        mov     rbp, rdi
        push    rbx
        mov     rbx, rsi
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
L9338:
        mov     rsi, rbx
        mov     rdi, rbp
        add     rbx, 0x280
        add     rbp, 0x400
        call    L8fd0
        cmp     rbx, r12
        jne     L9338
        pop     rbx
        pop     rbp
        pop     r12
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00

// mldsa87_polyvec_matrix_expand_lazy (0x9360)

L9360:
        movdqu  xmm0, XMMWORD PTR [rsi]
        movups  XMMWORD PTR [rdi+0x400], xmm0
        movdqu  xmm1, XMMWORD PTR [rsi+0x10]
        movups  XMMWORD PTR [rdi+0x410], xmm1
        ret
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy (0x9380)

L9380:
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15d, ecx
        push    r14
        mov     r14d, 0x1
        push    r13
        mov     r13, rdi
        push    r12
        mov     r12, rsi
        push    rbx
        mov     rbx, rdx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x60
        movdqu  xmm1, XMMWORD PTR [r12+0x400]
        movdqu  xmm2, XMMWORD PTR [r12+0x410]
        lea     rsi, [rsp+0x20]
        mov     BYTE PTR [rsp+0x41], cl
        mov     QWORD PTR [rsp+0x18], rsi
        movaps  XMMWORD PTR [rsp+0x20], xmm1
        movaps  XMMWORD PTR [rsp+0x30], xmm2
        mov     BYTE PTR [rsp+0x40], 0x0
        call    L28f0
        mov     rsi, rbx
        mov     rdi, r13
        add     rbx, 0x400
        call    L2850
        // nop
        .byte   0x90
L93f0:
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, r12
        mov     BYTE PTR [rsp+0x40], r14b
        add     r14d, 0x1
        mov     BYTE PTR [rsp+0x41], r15b
        call    L28f0
        mov     rsi, rbx
        mov     rdi, r12
        add     rbx, 0x400
        call    L2850
        mov     rsi, r12
        mov     rdi, r13
        call    L2560
        cmp     r14d, 0x7
        jne     L93f0
        mov     rdi, r13
        call    L24d0
        pxor    xmm0, xmm0
        mov     rax, QWORD PTR [rsp+0x18]
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
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
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy (0x9470)

L9470:
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        mov     r14, rcx
        push    r13
        mov     r13, rsi
        push    r12
        xor     r12d, r12d
        push    rbx
        and     rsp, 0xffffffffffffffe0
        sub     rsp, 0x60
        movdqu  xmm1, XMMWORD PTR [rsi+0x400]
        movdqu  xmm2, XMMWORD PTR [rsi+0x410]
        lea     rax, [rsp+0x20]
        mov     QWORD PTR [rsp+0x10], rdi
        mov     QWORD PTR [rsp+0x8], rdx
        mov     QWORD PTR [rsp+0x18], rax
        movaps  XMMWORD PTR [rsp+0x20], xmm1
        movaps  XMMWORD PTR [rsp+0x30], xmm2
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L94c0:
        mov     rax, QWORD PTR [rsp+0x8]
        mov     rdi, r14
        xor     r15d, r15d
        movzx   edx, WORD PTR [rax+0x8]
        mov     rsi, QWORD PTR [rax]
        add     edx, r12d
        movzx   edx, dx
        call    L9050
        mov     rdi, r14
        call    L25f0
        mov     rbx, QWORD PTR [rsp+0x10]
        jmp     L952e
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L94f0:
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, r13
        mov     BYTE PTR [rsp+0x40], r12b
        mov     BYTE PTR [rsp+0x41], r15b
        call    L28f0
        mov     rsi, r14
        mov     rdi, r13
        call    L2850
        mov     rsi, r13
        mov     rdi, rbx
        call    L2560
L951d:
        add     r15d, 0x1
        add     rbx, 0x400
        cmp     r15d, 0x8
        je      L9560
L952e:
        test    r12d, r12d
        jne     L94f0
        mov     rsi, QWORD PTR [rsp+0x18]
        mov     rdi, rbx
        mov     BYTE PTR [rsp+0x40], 0x0
        mov     BYTE PTR [rsp+0x41], r15b
        call    L28f0
        mov     rsi, r14
        mov     rdi, rbx
        call    L2850
        jmp     L951d
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L9560:
        add     r12d, 0x1
        cmp     r12d, 0x7
        jne     L94c0
        pxor    xmm0, xmm0
        mov     rax, QWORD PTR [rsp+0x18]
        movaps  XMMWORD PTR [rsp+0x20], xmm0
        movaps  XMMWORD PTR [rsp+0x30], xmm0
        movaps  XMMWORD PTR [rsp+0x40], xmm0
        movaps  XMMWORD PTR [rsp+0x50], xmm0
        mov     rbx, QWORD PTR [rsp+0x10]
        mov     rdi, rbx
        call    L91a0
        mov     rdi, rbx
        call    L9200
        lea     rsp, [rbp-0x28]
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret
        // nop
        .byte   0x90

// mld_compute_pack_t0_t187 (0x95b0)

L95b0:
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
        sub     rsp, 0xc40
        lea     rax, [rsp+0x820]
        mov     QWORD PTR [rsp+0x8], rdx
        lea     rbx, [rsp+0x20]
        mov     rdi, rax
        mov     QWORD PTR [rsp+0x10], rax
        lea     r12, [rsp+0x420]
        call    L9360
        xor     eax, eax
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
L9600:
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     rsi, QWORD PTR [rsp+0x10]
        mov     ecx, eax
        mov     rdi, rbx
        mov     DWORD PTR [rsp+0x1c], eax
        call    L9380
        mov     rdi, rbx
        call    L2700
        mov     rsi, r15
        mov     rdi, r12
        add     r15, 0x60
        call    L8e30
        mov     rsi, r12
        mov     rdi, rbx
        call    L2560
        mov     rdi, rbx
        call    L24d0
        mov     rdi, rbx
        call    L2520
        mov     rdx, rbx
        mov     rsi, rbx
        mov     rdi, r12
        call    L28a0
        mov     rdi, r14
        mov     rsi, r12
        add     r14, 0x140
        call    L29c0
        mov     rdi, r13
        mov     rsi, rbx
        add     r13, 0x1a0
        call    L2ab0
        mov     eax, DWORD PTR [rsp+0x1c]
        add     eax, 0x1
        cmp     eax, 0x8
        jne     L9600
        xor     eax, eax
        mov     rdi, r12
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x10]
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rsp+0x10]
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

// mld_H87.constprop.0 (0x96d0)

L96d0:
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
        call    L1230
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     rsi, r12
        mov     rdi, rbx
        call    L1270
        test    r15, r15
        jne     L9768
        cmp     QWORD PTR [rsp+0x120], 0x0
        jne     L9781
L9722:
        mov     rdi, rbx
        call    L1300
        mov     rdx, rbx
        mov     esi, 0x40
        mov     rdi, rbp
        call    L1350
        mov     rdi, rbx
        call    L13f0
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
L9768:
        mov     rdx, r15
        mov     rsi, r14
        mov     rdi, rbx
        call    L1270
        cmp     QWORD PTR [rsp+0x120], 0x0
        je      L9722
L9781:
        mov     rdx, QWORD PTR [rsp+0x120]
        mov     rsi, r13
        mov     rdi, rbx
        call    L1270
        jmp     L9722
        // cs      nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_keypair_internal (0x97a0)

L97a0:
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
        movzx   eax, WORD PTR [rip+Lc604]
        mov     rdx, rsi
        mov     rdi, r15
        mov     QWORD PTR [rbp-0x1d58], rsi
        mov     esi, 0x80
        movaps  XMMWORD PTR [rbp-0x1d30], xmm1
        movaps  XMMWORD PTR [rbp-0x1d20], xmm2
        mov     WORD PTR [rbp-0x1d10], ax
        mov     QWORD PTR [rbp-0x1d40], r15
        lea     r15, [rbp-0x1830]
        call    L1430
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
        call    L8910
        add     rsp, 0x20
        lea     rdi, [rbx+0x4a0]
        mov     rsi, r12
        call    L8d70
        mov     rsi, r15
        lea     rdi, [rbx+0x500]
        call    L8d70
        mov     rsi, r14
        lea     rdi, [rbx+0x560]
        call    L8d70
        mov     rsi, r13
        lea     rdi, [rbx+0x5c0]
        call    L8d70
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
        call    L8910
        mov     rdi, QWORD PTR [rbp-0x1d48]
        add     rsp, 0x20
        mov     rsi, r12
        call    L8d70
        mov     rsi, r15
        lea     rdi, [rbx+0x380]
        call    L8d70
        mov     rsi, r14
        lea     rdi, [rbx+0x3e0]
        call    L8d70
        mov     rsi, r13
        lea     rdi, [rbx+0x440]
        call    L8d70
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
        call    L8910
        mov     rsi, QWORD PTR [rbp-0x1d50]
        add     rsp, 0x20
        lea     rdi, [rbx+0x200]
        call    L8d70
        mov     rsi, QWORD PTR [rbp-0x1d60]
        lea     rdi, [rbx+0x260]
        call    L8d70
        mov     rsi, QWORD PTR [rbp-0x1d68]
        lea     rdi, [rbx+0x2c0]
        call    L8d70
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
        call    L8910
        add     rsp, 0x20
        lea     rdi, [rbx+0x80]
        mov     rsi, r12
        call    L8d70
        mov     rsi, r15
        lea     rdi, [rbx+0xe0]
        call    L8d70
        mov     rsi, r14
        lea     rdi, [rbx+0x140]
        lea     r14, [rbp-0x1cf0]
        call    L8d70
        mov     rsi, r13
        lea     rdi, [rbx+0x1a0]
        call    L8d70
        mov     rdi, r12
        call    L9120
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
        call    L95b0
        mov     r10, QWORD PTR [rbp-0x1d38]
        test    eax, eax
        mov     r13d, eax
        jne     L9ab7
        mov     rdx, r10
        mov     ecx, 0xa20
        mov     esi, 0x40
        mov     rdi, r14
        call    L1430
        mov     rdx, r14
        mov     rsi, r15
        mov     rdi, rbx
        lea     rcx, [rbp-0x1c50]
        call    L8480
        mov     r10, QWORD PTR [rbp-0x1d38]
L9ab7:
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
        jne     L9b38
L9b1d:
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
L9b38:
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
        jmp     L9b1d
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_keypair (0x9ba0)

L9ba0:
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
        jne     L9bf8
        mov     rdx, rbx
        mov     rsi, r13
        mov     rdi, r12
        call    L97a0
L9bd9:
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
L9bf8:
        mov     eax, 0xfffffffd
        jmp     L9bd9
        // nop
        .byte   0x90

// mldsa87_signature_internal (0x9c00)

L9c00:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        push    r14
        lea     rax, [rbp-0x3610]
        lea     r14, [rbp-0x34f0]
        push    r13
        mov     r13, rsi
        lea     rsi, [rbp-0x35f0]
        lea     r15, [rbp-0x3530]
        push    r12
        push    r10
        push    rbx
        mov     rbx, r9
        lea     r9, [rbp-0x35d0]
        sub     rsp, 0x3668
        mov     QWORD PTR [rbp-0x3618], rdi
        lea     rdi, [rbp-0x3550]
        mov     r12d, DWORD PTR [r10+0x8]
        mov     QWORD PTR [rbp-0x3620], rdx
        mov     rdx, r14
        mov     QWORD PTR [rbp-0x3628], rcx
        mov     rcx, rsi
        mov     QWORD PTR [rbp-0x3630], r8
        mov     r8, rax
        mov     QWORD PTR [rbp-0x3680], r9
        mov     QWORD PTR [rbp-0x3678], rsi
        mov     rsi, r15
        mov     QWORD PTR [rbp-0x3670], rax
        mov     QWORD PTR [rbp-0x3668], rdi
        push    QWORD PTR [r10]
        call    L84d0
        pop     r8
        pop     r9
        test    r12d, r12d
        jne     La181
        sub     rsp, 0x8
        mov     rsi, r15
        mov     r9, r13
        mov     edx, 0x40
        lea     rax, [rbp-0x34d0]
        mov     r8, QWORD PTR [rbp-0x3630]
        mov     rcx, QWORD PTR [rbp-0x3628]
        mov     QWORD PTR [rbp-0x3658], rax
        mov     rdi, rax
        push    QWORD PTR [rbp-0x3620]
        call    L96d0
        pop     rsi
        pop     rdi
L9ceb:
        sub     rsp, 0x8
        mov     rcx, rbx
        mov     edx, 0x20
        mov     rsi, r14
        lea     rax, [rbp-0x3490]
        mov     r9, QWORD PTR [rbp-0x3658]
        mov     r8d, 0x20
        lea     rbx, [rbp-0x3450]
        mov     QWORD PTR [rbp-0x3660], rax
        mov     rdi, rax
        lea     r12, [rbp-0x2850]
        lea     r15, [rbp-0x2c50]
        push    0x40
        call    L96d0
        lea     rax, [rbp-0x2450]
        mov     rsi, QWORD PTR [rbp-0x3668]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x3650], rax
        call    L9360
        pop     rax
        lea     rax, [rbp-0x35b0]
        pop     rdx
        mov     QWORD PTR [rbp-0x3640], rax
        lea     rax, [rbp-0x2030]
        xor     ecx, ecx
        mov     QWORD PTR [rbp-0x3620], rax
        lea     rax, [rbp-0x3050]
        mov     QWORD PTR [rbp-0x3630], rax
        lea     rax, [rbp-0x3590]
        mov     WORD PTR [rbp-0x3628], cx
        mov     QWORD PTR [rbp-0x3638], rax
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L9d98:
        mov     rax, QWORD PTR [rbp-0x3660]
        mov     r14, QWORD PTR [rbp-0x3620]
        mov     rcx, rbx
        mov     rdx, QWORD PTR [rbp-0x3640]
        mov     rsi, QWORD PTR [rbp-0x3650]
        mov     QWORD PTR [rbp-0x35b0], rax
        movzx   eax, WORD PTR [rbp-0x3628]
        mov     rdi, r14
        mov     WORD PTR [rbp-0x35a8], ax
        call    L9470
        mov     rdi, r14
        call    L91d0
        mov     rsi, r14
        mov     r14, QWORD PTR [rbp-0x3630]
        mov     rdx, rbx
        mov     rdi, r14
        call    L9280
        mov     rdi, r12
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x3658]
        mov     rdi, r12
        mov     edx, 0x40
        call    L1270
        mov     rsi, r14
        mov     edx, 0x400
        mov     rdi, r12
        call    L1270
        mov     rdi, r12
        call    L1300
        mov     r14, QWORD PTR [rbp-0x3638]
        mov     rdx, r12
        mov     esi, 0x40
        mov     rdi, r14
        call    L1350
        mov     rdi, r12
        call    L13f0
        mov     rdi, r12
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rsi, r14
        mov     rdi, r15
        xor     r14d, r14d
        call    L8bf0
        mov     rdi, r15
        call    L25f0
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
L9e70:
        lea     rsi, [r14+r14*2]
        mov     rdi, r12
        shl     rsi, 0x5
        add     rsi, QWORD PTR [rbp-0x3610]
        call    L8e30
        mov     rdi, r12
        call    L25f0
        mov     rsi, r15
        mov     rdi, r12
        call    L2850
        mov     rdi, r12
        call    L2700
        movzx   edx, WORD PTR [rbp-0x35a8]
        mov     rsi, QWORD PTR [rbp-0x35b0]
        mov     rdi, rbx
        add     edx, r14d
        movzx   edx, dx
        call    L9050
        mov     rsi, rbx
        mov     rdi, r12
        call    L2560
        mov     rdi, r12
        call    L24d0
        mov     esi, 0x7ff88
        mov     rdi, r12
        call    L2e00
        test    eax, eax
        jne     La177
        mov     rdi, QWORD PTR [rbp-0x3618]
        mov     edx, r14d
        mov     rsi, r12
        add     r14, 0x1
        call    L8660
        cmp     r14, 0x7
        jne     L9e70
        xor     eax, eax
        mov     r13, QWORD PTR [rbp-0x3620]
        mov     QWORD PTR [rbp-0x3648], r12
        xor     r14d, r14d
        mov     r12, rax
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
L9f20:
        mov     rsi, QWORD PTR [rbp-0x35d0]
        mov     rdi, rbx
        add     rsi, r14
        call    L8e30
        mov     rdi, rbx
        call    L25f0
        mov     rsi, r15
        mov     rdi, rbx
        call    L2850
        mov     rdi, rbx
        call    L2700
        mov     rsi, rbx
        mov     rdi, r13
        call    L2590
        mov     rdi, r13
        call    L24d0
        mov     esi, 0x3fe88
        mov     rdi, r13
        call    L2e00
        test    eax, eax
        jne     La170
        mov     rsi, QWORD PTR [rbp-0x35f0]
        mov     rdi, rbx
        add     rsi, r12
        call    L2c40
        mov     rdi, rbx
        call    L25f0
        mov     rsi, r15
        mov     rdi, rbx
        call    L2850
        mov     rdi, rbx
        call    L2700
        mov     rdi, rbx
        call    L24d0
        mov     esi, 0x3ff00
        mov     rdi, rbx
        call    L2e00
        test    eax, eax
        jne     La170
        mov     rdi, r13
        mov     rsi, rbx
        add     r14, 0x60
        add     r13, 0x400
        call    L2560
        add     r12, 0x1a0
        cmp     r14, 0x300
        jne     L9f20
        mov     r14, QWORD PTR [rbp-0x3618]
        mov     rsi, QWORD PTR [rbp-0x3638]
        mov     r12, QWORD PTR [rbp-0x3648]
        mov     rdi, r14
        call    L8540
        mov     rdx, QWORD PTR [rbp-0x3630]
        mov     rcx, rbx
        mov     rdi, r14
        mov     rsi, QWORD PTR [rbp-0x3620]
        call    L8570
        mov     edx, eax
La021:
        mov     rdi, r12
        xor     eax, eax
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r15
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3620]
        mov     ecx, 0x400
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3620]
        mov     rdi, QWORD PTR [rbp-0x3630]
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3630]
        mov     ecx, 0x80
        mov     rdi, rbx
        rep stos QWORD PTR es:[rdi], rax
        mov     rax, QWORD PTR [rbp-0x3640]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rax], xmm0
        mov     rax, QWORD PTR [rbp-0x3638]
        movaps  XMMWORD PTR [rax], xmm0
        movaps  XMMWORD PTR [rax+0x10], xmm0
        movaps  XMMWORD PTR [rax+0x20], xmm0
        movaps  XMMWORD PTR [rax+0x30], xmm0
        test    edx, edx
        je      La0f0
        cmp     edx, 0xffffffff
        jne     La0bb
        add     WORD PTR [rbp-0x3628], 0x7
        movzx   eax, WORD PTR [rbp-0x3628]
        cmp     ax, 0xfff7
        jne     L9d98
        mov     edx, 0xfffffffc
La0bb:
        mov     rbx, QWORD PTR [rbp-0x3618]
        xor     eax, eax
        lea     rdi, [rbx+0x8]
        mov     rcx, rbx
        mov     QWORD PTR [rbx], 0x0
        mov     QWORD PTR [rbx+0x120b], 0x0
        and     rdi, 0xfffffffffffffff8
        sub     rcx, rdi
        add     ecx, 0x1213
        shr     ecx, 0x3
        rep stos QWORD PTR es:[rdi], rax
La0f0:
        mov     QWORD PTR [rbp-0x35d0], 0x0
        mov     rax, QWORD PTR [rbp-0x3680]
        mov     QWORD PTR [rbp-0x35f0], 0x0
        mov     rax, QWORD PTR [rbp-0x3678]
        mov     QWORD PTR [rbp-0x3610], 0x0
        mov     rax, QWORD PTR [rbp-0x3670]
        mov     rdi, QWORD PTR [rbp-0x3650]
        xor     eax, eax
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3650]
        mov     rdi, QWORD PTR [rbp-0x3668]
        mov     ecx, 0x20
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3668]
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
La170:
        mov     r12, QWORD PTR [rbp-0x3648]
La177:
        mov     edx, 0xffffffff
        jmp     La021
La181:
        movdqu  xmm1, XMMWORD PTR [r13+0x0]
        movdqu  xmm2, XMMWORD PTR [r13+0x10]
        lea     rax, [rbp-0x34d0]
        movdqu  xmm3, XMMWORD PTR [r13+0x20]
        movdqu  xmm4, XMMWORD PTR [r13+0x30]
        mov     QWORD PTR [rbp-0x3658], rax
        movaps  XMMWORD PTR [rbp-0x34d0], xmm1
        movaps  XMMWORD PTR [rbp-0x34c0], xmm2
        movaps  XMMWORD PTR [rbp-0x34b0], xmm3
        movaps  XMMWORD PTR [rbp-0x34a0], xmm4
        jmp     L9ceb
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_signature_extmu (0xa1d0)

La1d0:
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
        jne     La250
        push    0x1
        xor     ecx, ecx
        mov     edx, 0x40
        mov     r9, rbx
        push    r14
        xor     r8d, r8d
        mov     rsi, r13
        mov     rdi, r12
        call    L9c00
        pop     rdx
        pop     rcx
La22a:
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
La250:
        mov     eax, 0xfffffffd
        jmp     La22a
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_verify_internal (0xa260)

La260:
        lea     r10, [rsp+0x8]
        and     rsp, 0xffffffffffffffe0
        push    QWORD PTR [r10-0x8]
        push    rbp
        mov     rbp, rsp
        push    r15
        mov     r15, rsi
        lea     rsi, [rdi+0x40]
        push    r14
        lea     rax, [rbp-0x1c30]
        mov     r14, r8
        push    r13
        mov     r13, rax
        push    r12
        mov     r12, rdx
        push    r10
        push    rbx
        sub     rsp, 0x3200
        movdqu  xmm3, XMMWORD PTR [rdi]
        mov     ebx, DWORD PTR [r10]
        mov     QWORD PTR [rbp-0x31f8], rdi
        movdqu  xmm4, XMMWORD PTR [rdi+0x10]
        movdqu  xmm5, XMMWORD PTR [rdi+0x20]
        mov     QWORD PTR [rbp-0x3208], rcx
        movdqu  xmm6, XMMWORD PTR [rdi+0x30]
        mov     rdi, rax
        mov     QWORD PTR [rbp-0x3210], r9
        mov     QWORD PTR [rbp-0x3200], rax
        movaps  XMMWORD PTR [rbp-0x31b0], xmm3
        movaps  XMMWORD PTR [rbp-0x31a0], xmm4
        movaps  XMMWORD PTR [rbp-0x3190], xmm5
        movaps  XMMWORD PTR [rbp-0x3180], xmm6
        call    L9320
        mov     esi, 0x7ff88
        mov     rdi, r13
        call    L9150
        mov     r11, QWORD PTR [rbp-0x31f8]
        test    eax, eax
        jne     La7a1
        mov     r13d, eax
        test    ebx, ebx
        je      La6a8
        movdqu  xmm7, XMMWORD PTR [r15]
        lea     rax, [rbp-0x2050]
        movdqu  xmm3, XMMWORD PTR [r15+0x20]
        lea     rbx, [rbp-0x2450]
        mov     QWORD PTR [rbp-0x31f8], rax
        lea     rax, [rbp-0x31f0]
        movdqu  xmm4, XMMWORD PTR [r15+0x30]
        movaps  XMMWORD PTR [rbp-0x31f0], xmm7
        movdqu  xmm7, XMMWORD PTR [r15+0x10]
        mov     QWORD PTR [rbp-0x3228], rax
        movaps  XMMWORD PTR [rbp-0x31e0], xmm7
        movaps  XMMWORD PTR [rbp-0x31d0], xmm3
        movaps  XMMWORD PTR [rbp-0x31c0], xmm4
La36d:
        mov     rdi, QWORD PTR [rbp-0x3200]
        mov     QWORD PTR [rbp-0x3218], r11
        lea     r12, [rbp-0x2850]
        call    L9120
        mov     rsi, QWORD PTR [rbp-0x3210]
        mov     rdi, QWORD PTR [rbp-0x31f8]
        call    L9360
        lea     rax, [rbp-0x2c50]
        lea     r9, [rbp-0x31b0]
        mov     r15, rax
        mov     rdi, rax
        mov     rsi, r9
        mov     QWORD PTR [rbp-0x3208], rax
        mov     QWORD PTR [rbp-0x3230], r9
        call    L8bf0
        mov     rdi, r15
        call    L25f0
        lea     rax, [rbp-0x3050]
        mov     QWORD PTR [rbp-0x3220], rax
        mov     r14, rax
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
La3e0:
        mov     rdx, QWORD PTR [rbp-0x3200]
        mov     rsi, QWORD PTR [rbp-0x31f8]
        mov     ecx, r13d
        mov     rdi, r12
        call    L9380
        mov     rsi, QWORD PTR [rbp-0x3210]
        mov     edx, r13d
        mov     rdi, rbx
        call    L8470
        mov     rdi, rbx
        call    L25c0
        mov     rdi, rbx
        call    L25f0
        mov     rsi, QWORD PTR [rbp-0x3208]
        mov     rdi, rbx
        call    L2850
        mov     rsi, rbx
        mov     rdi, r12
        call    L2590
        mov     rdi, r12
        call    L24d0
        mov     rdi, r12
        call    L2700
        mov     rdi, r12
        call    L2520
        mov     rsi, QWORD PTR [rbp-0x3218]
        mov     edx, r13d
        mov     rdi, rbx
        call    L8670
        mov     r15d, eax
        test    eax, eax
        jne     La788
        mov     rsi, rbx
        mov     rdi, r12
        add     r13d, 0x1
        call    L8880
        mov     rdi, r14
        mov     rsi, r12
        sub     r14, 0xffffffffffffff80
        call    L2ea0
        cmp     r13d, 0x8
        jne     La3e0
        mov     r9, QWORD PTR [rbp-0x3230]
        lea     r13, [rbp-0x3120]
        lea     r14, [rbp-0x3170]
        mov     rdi, r13
        mov     QWORD PTR [rbp-0x3210], r9
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x3228]
        mov     rdi, r13
        mov     edx, 0x40
        call    L1270
        mov     rsi, QWORD PTR [rbp-0x3220]
        mov     edx, 0x400
        mov     rdi, r13
        call    L1270
        mov     rdi, r13
        call    L1300
        mov     rdx, r13
        mov     esi, 0x40
        mov     rdi, r14
        call    L1350
        mov     rdi, r13
        call    L13f0
        xor     eax, eax
        mov     rdi, r13
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        pxor    xmm1, xmm1
        mov     r9, QWORD PTR [rbp-0x3210]
        movdqa  xmm0, xmm1
La51a:
        movdqa  xmm2, XMMWORD PTR [r9+rax*1]
        pxor    xmm2, XMMWORD PTR [r14+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x40
        jne     La51a
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
        jne     La796
La5bc:
        xor     eax, eax
        mov     rdi, rbx
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     ecx, 0x80
        mov     rdi, r12
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x31f8]
        mov     ecx, 0x84
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x31f8]
        mov     rdi, QWORD PTR [rbp-0x3208]
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3208]
        mov     rdi, QWORD PTR [rbp-0x3200]
        mov     ecx, 0x380
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3200]
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x3170], xmm0
        movaps  XMMWORD PTR [rbp-0x3160], xmm0
        movaps  XMMWORD PTR [rbp-0x3150], xmm0
        movaps  XMMWORD PTR [rbp-0x3140], xmm0
        movaps  XMMWORD PTR [rbp-0x31b0], xmm0
        movaps  XMMWORD PTR [rbp-0x31a0], xmm0
        movaps  XMMWORD PTR [rbp-0x3190], xmm0
        movaps  XMMWORD PTR [rbp-0x3180], xmm0
        mov     rcx, QWORD PTR [rbp-0x3228]
        movaps  XMMWORD PTR [rbp-0x31f0], xmm0
        movaps  XMMWORD PTR [rbp-0x31e0], xmm0
        movaps  XMMWORD PTR [rbp-0x31d0], xmm0
        movaps  XMMWORD PTR [rbp-0x31c0], xmm0
        mov     rdi, QWORD PTR [rbp-0x3220]
        mov     ecx, 0x80
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x3220]
        lea     rsp, [rbp-0x30]
        mov     eax, r15d
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
La6a8:
        lea     rax, [rbp-0x2050]
        mov     QWORD PTR [rbp-0x3218], r11
        mov     rdi, rax
        mov     rbx, rax
        call    L1230
        mov     rsi, QWORD PTR [rbp-0x3210]
        mov     edx, 0xa20
        mov     rdi, rbx
        call    L1270
        mov     rdi, rbx
        mov     QWORD PTR [rbp-0x31f8], rbx
        lea     rbx, [rbp-0x2450]
        call    L1300
        mov     rdx, QWORD PTR [rbp-0x31f8]
        mov     esi, 0x40
        mov     rdi, rbx
        call    L1350
        mov     rdi, QWORD PTR [rbp-0x31f8]
        call    L13f0
        mov     rdi, QWORD PTR [rbp-0x31f8]
        xor     eax, eax
        mov     ecx, 0x1a
        rep stos QWORD PTR es:[rdi], rax
        mov     rdi, QWORD PTR [rbp-0x31f8]
        lea     rax, [rbp-0x31f0]
        mov     r9, r15
        mov     r8, r14
        mov     rsi, rbx
        sub     rsp, 0x8
        mov     QWORD PTR [rbp-0x3228], rax
        mov     edx, 0x40
        mov     rdi, rax
        push    r12
        mov     rcx, QWORD PTR [rbp-0x3208]
        call    L96d0
        pxor    xmm0, xmm0
        movaps  XMMWORD PTR [rbp-0x2450], xmm0
        movaps  XMMWORD PTR [rbp-0x2440], xmm0
        movaps  XMMWORD PTR [rbp-0x2430], xmm0
        movaps  XMMWORD PTR [rbp-0x2420], xmm0
        pop     rax
        mov     r11, QWORD PTR [rbp-0x3218]
        pop     rdx
        jmp     La36d
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
La788:
        mov     r9, QWORD PTR [rbp-0x3230]
        lea     r14, [rbp-0x3170]
La796:
        mov     r15d, 0xfffffffa
        jmp     La5bc
La7a1:
        lea     rax, [rbp-0x2050]
        lea     rbx, [rbp-0x2450]
        mov     QWORD PTR [rbp-0x31f8], rax
        lea     rax, [rbp-0x31f0]
        lea     r9, [rbp-0x31b0]
        mov     QWORD PTR [rbp-0x3228], rax
        lea     rax, [rbp-0x2c50]
        lea     r12, [rbp-0x2850]
        mov     QWORD PTR [rbp-0x3208], rax
        lea     rax, [rbp-0x3050]
        lea     r14, [rbp-0x3170]
        mov     QWORD PTR [rbp-0x3220], rax
        jmp     La796
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_verify_extmu (0xa800)

La800:
        sub     rsp, 0x10
        mov     r9, rdx
        xor     r8d, r8d
        xor     ecx, ecx
        push    0x1
        mov     edx, 0x40
        call    La260
        add     rsp, 0x18
        ret
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00

// mldsa87_prepare_domain_separation_prefix (0xa820)

La820:
        xor     eax, eax
        cmp     r8, 0xff
        ja      La890
        push    r14
        push    r13
        push    r12
        mov     r12, rdi
        push    rbp
        mov     rbp, r8
        sub     rsp, 0x18
        test    r9d, r9d
        jne     La868
        mov     BYTE PTR [rdi], 0x0
        mov     BYTE PTR [r12+0x1], r8b
        test    r8, r8
        jne     La948
La852:
        lea     rax, [rbp+0x2]
La856:
        add     rsp, 0x18
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        ret
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
La868:
        cmp     r9d, 0xc
        ja      La8fe
        mov     r13, rdx
        mov     eax, r9d
        lea     rdx, [rip+Lc720]
        mov     r14, rsi
        movsxd  rax, DWORD PTR [rdx+rax*4]
        add     rax, rdx
        jmp     rax
        // nop     DWORD PTR [rax+rax*1+0x0]
        .byte   0x0f,0x1f,0x44,0x00,0x00
La890:
        ret
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
        cmp     r13, 0x20
        jne     La8fe
La89e:
        mov     BYTE PTR [r12], 0x1
        mov     BYTE PTR [r12+0x1], bpl
        test    rbp, rbp
        jne     La960
La8b1:
        lea     rcx, [rip+Lc760]
        xor     eax, eax
        mov     rdx, rcx
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
La8c0:
        cmp     r9d, DWORD PTR [rdx]
        je      La928
        add     eax, 0x1
        add     rdx, 0x10
        cmp     eax, 0xc
        jne     La8c0
La8d1:
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
        je      La89e
La8fe:
        xor     eax, eax
        jmp     La856
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x40
        je      La89e
        xor     eax, eax
        jmp     La856
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
        cmp     r13, 0x30
        je      La89e
        xor     eax, eax
        jmp     La856
        // nop     DWORD PTR [rax]
        .byte   0x0f,0x1f,0x00
La928:
        shl     rax, 0x4
        lea     rdx, [r12+rbp*1+0x2]
        lea     rax, [rcx+rax*1+0x4]
        mov     rcx, QWORD PTR [rax]
        mov     QWORD PTR [rdx], rcx
        mov     eax, DWORD PTR [rax+0x7]
        mov     DWORD PTR [rdx+0x7], eax
        jmp     La8d1
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
La948:
        lea     rdi, [rdi+0x2]
        mov     rdx, r8
        mov     rsi, rcx
        call    L1010
        jmp     La852
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00
La960:
        lea     rdi, [r12+0x2]
        mov     rdx, rbp
        mov     rsi, rcx
        mov     DWORD PTR [rsp+0xc], r9d
        call    L1010
        mov     r9d, DWORD PTR [rsp+0xc]
        jmp     La8b1
        // nop
        .byte   0x90

// mldsa87_signature (0xa980)

La980:
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
        call    La820
        test    rax, rax
        mov     QWORD PTR [rbp-0x1c0], rax
        jne     Laa50
        mov     edx, 0xfffffff7
        lea     r13, [rbp-0x1b0]
La9e1:
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
Laa0f:
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
Laa50:
        lea     r13, [rbp-0x1b0]
        mov     esi, 0x20
        mov     rdi, r13
        call    L1020
        mov     edx, 0xfffffffd
        test    eax, eax
        jne     La9e1
        push    0x0
        mov     r8, QWORD PTR [rbp-0x1c0]
        mov     rcx, r12
        mov     rdx, r14
        push    r15
        mov     rsi, QWORD PTR [rbp-0x1b8]
        mov     r9, r13
        mov     rdi, rbx
        call    L9c00
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      Laa0f
        jmp     La9e1
        // data16  cs nop WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x66,0x2e,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00

// mldsa87_verify (0xaab0)

Laab0:
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
        call    La820
        test    rax, rax
        je      Lab48
        sub     rsp, 0x8
        mov     rcx, rbx
        mov     rdx, r14
        mov     r8, rax
        push    0x0
        mov     r9, r15
        mov     rsi, r13
        mov     rdi, r12
        call    La260
        mov     edx, eax
        pop     rax
        pop     rcx
Lab1b:
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
Lab48:
        mov     edx, 0xfffffff7
        jmp     Lab1b
        // nop
        .byte   0x90

// mldsa87_signature_pre_hash_internal (0xab50)

Lab50:
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
        jne     Labe8
Lab8a:
        mov     edx, 0xfffffff7
Lab8f:
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
Labbd:
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
Labe8:
        mov     rdi, r12
        call    La820
        test    rax, rax
        je      Lab8a
        push    0x0
        xor     ecx, ecx
        mov     rdx, rax
        mov     r9, r13
        push    r14
        xor     r8d, r8d
        mov     rsi, r12
        mov     rdi, rbx
        call    L9c00
        mov     edx, eax
        pop     rax
        pop     rcx
        test    edx, edx
        je      Labbd
        jmp     Lab8f
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x40,0x00

// mldsa87_signature_pre_hash_shake256 (0xac20)

Lac20:
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
        call    L1430
        push    0xc
        mov     rdi, QWORD PTR [rbp-0x78]
        mov     r9, r15
        push    r12
        mov     r8, r14
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        call    Lab50
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

// mldsa87_verify_pre_hash_internal (0xacb0)

Lacb0:
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
        je      Lad40
        lea     rbx, [rbp-0x190]
        mov     r12, rdi
        mov     rdi, rbx
        call    La820
        mov     rdx, rax
        test    rax, rax
        je      Lad47
        sub     rsp, 0x8
        xor     ecx, ecx
        mov     r9, r13
        xor     r8d, r8d
        push    0x0
        mov     rsi, rbx
        mov     rdi, r12
        call    La260
        mov     edx, eax
        pop     rax
        pop     rcx
Lad11:
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
Lad40:
        lea     rbx, [rbp-0x190]
Lad47:
        mov     edx, 0xfffffff7
        jmp     Lad11
        // xchg    ax, ax
        .byte   0x66,0x90

// mldsa87_verify_pre_hash_shake256 (0xad50)

Lad50:
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
        call    L1430
        sub     rsp, 0x8
        mov     r9, r15
        mov     r8, r14
        push    0xc
        mov     rcx, r13
        mov     edx, 0x40
        mov     rsi, rbx
        mov     rdi, r12
        call    Lacb0
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

// mldsa87_pk_from_sk (0xade0)

Lade0:
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
        call    L92e0
        mov     esi, 0x3
        mov     rdi, r14
        call    L9150
        lea     rcx, [rbx+0x320]
        mov     rdx, r15
        mov     esi, 0x3
        mov     rdi, rcx
        mov     QWORD PTR [rsp+0x38], rcx
        mov     r13d, eax
        call    L9230
        mov     rdi, r14
        mov     DWORD PTR [rsp+0x2c], eax
        call    L9120
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
        call    L95b0
        mov     r9, QWORD PTR [rsp+0x38]
        mov     r8, QWORD PTR [rsp+0x30]
        test    eax, eax
        mov     r11d, eax
        je      Lafe0
        lea     rbx, [rsp+0xc0]
        lea     rdx, [rsp+0x80]
Laf16:
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
Laf47:
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
Lafe0:
        pxor    xmm2, xmm2
        xor     eax, eax
        movdqa  xmm0, xmm2
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Laff0:
        movdqu  xmm1, XMMWORD PTR [rbx+rax*1+0x620]
        pxor    xmm1, XMMWORD PTR [r9+rax*1]
        add     rax, 0x10
        por     xmm0, xmm1
        pxor    xmm2, xmm1
        cmp     rax, 0xd00
        jne     Laff0
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
        call    L1430
        pxor    xmm1, xmm1
        mov     r8, QWORD PTR [rsp+0x18]
        xor     eax, eax
        mov     r9, QWORD PTR [rsp+0x20]
        mov     r11d, DWORD PTR [rsp+0x30]
        movdqa  xmm0, xmm1
        lea     rdx, [rsp+0x80]
Lb0e2:
        movdqa  xmm2, XMMWORD PTR [rbx+rax*1]
        pxor    xmm2, XMMWORD PTR [rdx+rax*1]
        add     rax, 0x10
        por     xmm0, xmm2
        pxor    xmm1, xmm2
        cmp     rax, 0x40
        jne     Lb0e2
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
        je      Laf47
        mov     r11d, 0xfffffff9
        jmp     Laf16

// Padding (0xb1a0 to 0xc000)

        .zero   3680

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
        .quad   0xffff8b88ffff8b8e
        .quad   0xffff8ba8ffff8b28
        .quad   0xffff8b88ffff8b98
        .quad   0xffff8b88ffff8b28
        .quad   0xffff8ba8ffff8b28
        .quad   0xffff8b28ffff8b98
        .quad   0x00000000ffff8b98
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
        .byte   0x06
        .byte   0x05
Lc604:
        .byte   0x08
        .byte   0x07
        .zero   26
Lc620:
        .quad   0xffffb5a8ffffb5ae
        .quad   0xffffb5c8ffffb548
        .quad   0xffffb5a8ffffb5b8
        .quad   0xffffb5a8ffffb548
        .quad   0xffffb5c8ffffb548
        .quad   0xffffb548ffffb5b8
        .quad   0x00000000ffffb5b8
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
        .quad   0xffffe1d8ffffe1de
        .quad   0xffffe1f8ffffe178
        .quad   0xffffe1d8ffffe1e8
        .quad   0xffffe1d8ffffe178
        .quad   0xffffe1f8ffffe178
        .quad   0xffffe178ffffe1e8
        .quad   0x00000000ffffe1e8
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
