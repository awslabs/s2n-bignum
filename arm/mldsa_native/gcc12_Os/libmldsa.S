// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mldsa-native's libmldsa.so (gcc 12, -Os)
//
// This is a transcription of the binary
// binaries/multilevel/gcc12/Os/libmldsa.so from the binary branch of
// mldsa-native (see README.md), as loaded at an address that is a multiple
// of 4096: the start of its first segment, from address 0 up to the end of
// the read-only data. The ELF header and dynamic linking information at the
// start are given as data, as are the padding and the read-only data at the
// end, while the procedure linkage table and the code are given as
// instructions. The ADRP instructions, which compute addresses of pages
// relative to that of the instruction, are given as words. The labels are
// named after the addresses in the binary.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_native_libmldsa_gcc12_Os)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_native_libmldsa_gcc12_Os)
        .text
        .balign 4

S2N_BN_SYMBOL(mldsa_native_libmldsa_gcc12_Os):

// ELF header and dynamic linking information (0x0 to 0xe30)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x000000000002d2e0
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000000000c438
        .quad   0x000000000000c438
        .quad   0x0000000000010000
        .quad   0x0000000600000001
        .quad   0x000000000000fe38
        .quad   0x000000000001fe38
        .quad   0x000000000001fe38
        .quad   0x00000000000001c8
        .quad   0x00000000000001c8
        .quad   0x0000000000010000
        .quad   0x0000000600000002
        .quad   0x000000000000fe38
        .quad   0x000000000001fe38
        .quad   0x000000000001fe38
        .quad   0x0000000000000180
        .quad   0x0000000000000180
        .quad   0x0000000000000008
        .quad   0x000000066474e551
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000010
        .quad   0x000000046474e552
        .quad   0x000000000000fe38
        .quad   0x000000000001fe38
        .quad   0x000000000001fe38
        .quad   0x00000000000001c8
        .quad   0x00000000000001c8
        .quad   0x0000000000000001
        .quad   0x0000003100000025
        .quad   0x0000000000000014
        .quad   0x0000002c00000026
        .quad   0x0000000000000000
        .quad   0x0000000000000020
        .quad   0x0000000d00000024
        .quad   0x0000001a0000001b
        .quad   0x000000270000000c
        .quad   0x0000000000000018
        .quad   0x0000001f0000002b
        .quad   0x0000000000000010
        .quad   0x0000001700000000
        .quad   0x0000002800000007
        .quad   0x0000001e0000000a
        .quad   0x000000190000001d
        .quad   0x0000000000000000
        .quad   0x0000000f0000002a
        .quad   0x0000002300000006
        .quad   0x0000001500000012
        .quad   0x0000000000000030
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001c00000029
        .quad   0x0000000000000000
        .quad   0x0000002100000000
        .quad   0x0000000900000000
        .quad   0x0000002f00000025
        .quad   0x0000000000000000
        .quad   0x0000002200000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000e00000000
        .quad   0x0000000200000013
        .quad   0x0000000000000004
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000011
        .quad   0x0000000300000000
        .quad   0x000000000000002d
        .quad   0x000000050000000b
        .quad   0x0000002e00000000
        .quad   0x0000000000000016
        .quad   0x0000000000000008
        .quad   0x0000000700000025
        .quad   0x0000000800000004
        .quad   0x0a6340a0460288d5
        .quad   0x10a640204e3c180a
        .quad   0x087445801d011110
        .quad   0x00a4c96828348108
        .quad   0x0000000800000007
        .quad   0x0000000c0000000b
        .quad   0x000000000000000d
        .quad   0x000000110000000e
        .quad   0x0000001300000012
        .quad   0x0000001400000000
        .quad   0x0000000000000016
        .quad   0x0000001800000017
        .quad   0x0000001b00000019
        .quad   0x0000001e00000000
        .quad   0x0000002100000020
        .quad   0x0000002500000023
        .quad   0x0000002800000026
        .quad   0x0000002a00000029
        .quad   0x0000002b00000000
        .quad   0x0000000000000000
        .quad   0x000000000000002c
        .quad   0x0000002d00000000
        .quad   0x28bfc2110000002e
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
        .quad   0x0008000300000000
        .quad   0x0000000000000e90
        .quad   0x0000000000000000
        .quad   0x0000001000000008
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000002b
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000005b
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000001a
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00080012000001ae
        .quad   0x000000000000626c
        .quad   0x0000000000000290
        .quad   0x00080012000001f2
        .quad   0x00000000000069dc
        .quad   0x00000000000000b4
        .quad   0x00080012000000f0
        .quad   0x00000000000047bc
        .quad   0x0000000000000100
        .quad   0x0008001200000082
        .quad   0x00000000000042b8
        .quad   0x00000000000000b4
        .quad   0x00080012000003f1
        .quad   0x00000000000098c8
        .quad   0x00000000000000c8
        .quad   0x0008001200000067
        .quad   0x0000000000003e80
        .quad   0x0000000000000438
        .quad   0x000800120000037a
        .quad   0x00000000000092b0
        .quad   0x000000000000030c
        .quad   0x0008001200000439
        .quad   0x0000000000009a50
        .quad   0x00000000000000a8
        .quad   0x0008001200000347
        .quad   0x0000000000008dc8
        .quad   0x0000000000000434
        .quad   0x000800120000020a
        .quad   0x0000000000006a90
        .quad   0x0000000000000324
        .quad   0x00080012000002a5
        .quad   0x0000000000007188
        .quad   0x00000000000000c0
        .quad   0x000800120000031e
        .quad   0x0000000000008a30
        .quad   0x0000000000000304
        .quad   0x00080012000002ea
        .quad   0x00000000000072f0
        .quad   0x00000000000000b0
        .quad   0x0008001200000272
        .quad   0x0000000000007004
        .quad   0x00000000000000bc
        .quad   0x000800120000004b
        .quad   0x0000000000003dec
        .quad   0x0000000000000094
        .quad   0x0008001200000111
        .quad   0x0000000000004978
        .quad   0x00000000000000c8
        .quad   0x0008001200000415
        .quad   0x0000000000009990
        .quad   0x00000000000000c0
        .quad   0x0008001200000392
        .quad   0x00000000000095bc
        .quad   0x0000000000000018
        .quad   0x00080012000000b2
        .quad   0x000000000000466c
        .quad   0x0000000000000018
        .quad   0x0008001200000102
        .quad   0x00000000000048bc
        .quad   0x00000000000000bc
        .quad   0x00080012000001d7
        .quad   0x0000000000006590
        .quad   0x000000000000044c
        .quad   0x0008001200000159
        .quad   0x0000000000004b00
        .quad   0x00000000000000a8
        .quad   0x00080012000003e2
        .quad   0x000000000000980c
        .quad   0x00000000000000bc
        .quad   0x00080012000003d0
        .quad   0x000000000000970c
        .quad   0x0000000000000100
        .quad   0x000800120000047b
        .quad   0x0000000000009ba8
        .quad   0x000000000000020c
        .quad   0x000800120000019b
        .quad   0x0000000000004c58
        .quad   0x0000000000000208
        .quad   0x00080012000000c7
        .quad   0x0000000000004684
        .quad   0x0000000000000138
        .quad   0x0008001200000260
        .quad   0x0000000000006f04
        .quad   0x0000000000000100
        .quad   0x0008001200000237
        .quad   0x0000000000006dcc
        .quad   0x0000000000000138
        .quad   0x0008001200000032
        .quad   0x0000000000003bb8
        .quad   0x0000000000000234
        .quad   0x00080012000003a7
        .quad   0x00000000000095d4
        .quad   0x0000000000000138
        .quad   0x0008001200000135
        .quad   0x0000000000004a40
        .quad   0x00000000000000c0
        .quad   0x0008001200000337
        .quad   0x0000000000008d34
        .quad   0x0000000000000094
        .quad   0x000800120000045a
        .quad   0x0000000000009af8
        .quad   0x00000000000000b0
        .quad   0x0008001200000222
        .quad   0x0000000000006db4
        .quad   0x0000000000000018
        .quad   0x00080012000002c9
        .quad   0x0000000000007248
        .quad   0x00000000000000a8
        .quad   0x00080012000001c7
        .quad   0x00000000000064fc
        .quad   0x0000000000000094
        .quad   0x0008001200000281
        .quad   0x00000000000070c0
        .quad   0x00000000000000c8
        .quad   0x000800120000030b
        .quad   0x00000000000073a0
        .quad   0x0000000000000210
        .quad   0x0008001200000362
        .quad   0x00000000000091fc
        .quad   0x00000000000000b4
        .quad   0x000800120000009a
        .quad   0x000000000000436c
        .quad   0x0000000000000300
        .quad   0x000800120000017a
        .quad   0x0000000000004ba8
        .quad   0x00000000000000b0
        .quad   0x007465736d656d00
        .quad   0x5f6b636174735f5f
        .quad   0x726175675f6b6863
        .quad   0x636174735f5f0064
        .quad   0x61665f6b68635f6b
        .quad   0x70636d656d006c69
        .quad   0x346173646c6d0079
        .quad   0x69617079656b5f34
        .quad   0x6e7265746e695f72
        .quad   0x6173646c6d006c61
        .quad   0x617079656b5f3434
        .quad   0x6f646e6172007269
        .quad   0x6d0073657479626d
        .quad   0x735f34346173646c
        .quad   0x65727574616e6769
        .quad   0x616e7265746e695f
        .quad   0x346173646c6d006c
        .quad   0x74616e6769735f34
        .quad   0x6d7478655f657275
        .quad   0x346173646c6d0075
        .quad   0x7966697265765f34
        .quad   0x616e7265746e695f
        .quad   0x346173646c6d006c
        .quad   0x7966697265765f34
        .quad   0x6d00756d7478655f
        .quad   0x705f34346173646c
        .quad   0x645f657261706572
        .quad   0x65735f6e69616d6f
        .quad   0x6e6f697461726170
        .quad   0x007869666572705f
        .quad   0x5f34346173646c6d
        .quad   0x727574616e676973
        .quad   0x346173646c6d0065
        .quad   0x7966697265765f34
        .quad   0x34346173646c6d00
        .quad   0x7574616e6769735f
        .quad   0x685f6572705f6572
        .quad   0x65746e695f687361
        .quad   0x646c6d006c616e72
        .quad   0x6769735f34346173
        .quad   0x705f65727574616e
        .quad   0x5f687361685f6572
        .quad   0x363532656b616873
        .quad   0x34346173646c6d00
        .quad   0x5f7966697265765f
        .quad   0x687361685f657270
        .quad   0x616e7265746e695f
        .quad   0x346173646c6d006c
        .quad   0x7966697265765f34
        .quad   0x7361685f6572705f
        .quad   0x32656b6168735f68
        .quad   0x6173646c6d003635
        .quad   0x72665f6b705f3434
        .quad   0x6c6d006b735f6d6f
        .quad   0x656b5f3536617364
        .quad   0x6e695f7269617079
        .quad   0x6d006c616e726574
        .quad   0x6b5f35366173646c
        .quad   0x6d00726961707965
        .quad   0x735f35366173646c
        .quad   0x65727574616e6769
        .quad   0x616e7265746e695f
        .quad   0x366173646c6d006c
        .quad   0x74616e6769735f35
        .quad   0x6d7478655f657275
        .quad   0x366173646c6d0075
        .quad   0x7966697265765f35
        .quad   0x616e7265746e695f
        .quad   0x366173646c6d006c
        .quad   0x7966697265765f35
        .quad   0x6d00756d7478655f
        .quad   0x705f35366173646c
        .quad   0x645f657261706572
        .quad   0x65735f6e69616d6f
        .quad   0x6e6f697461726170
        .quad   0x007869666572705f
        .quad   0x5f35366173646c6d
        .quad   0x727574616e676973
        .quad   0x366173646c6d0065
        .quad   0x7966697265765f35
        .quad   0x35366173646c6d00
        .quad   0x7574616e6769735f
        .quad   0x685f6572705f6572
        .quad   0x65746e695f687361
        .quad   0x646c6d006c616e72
        .quad   0x6769735f35366173
        .quad   0x705f65727574616e
        .quad   0x5f687361685f6572
        .quad   0x363532656b616873
        .quad   0x35366173646c6d00
        .quad   0x5f7966697265765f
        .quad   0x687361685f657270
        .quad   0x616e7265746e695f
        .quad   0x366173646c6d006c
        .quad   0x7966697265765f35
        .quad   0x7361685f6572705f
        .quad   0x32656b6168735f68
        .quad   0x6173646c6d003635
        .quad   0x72665f6b705f3536
        .quad   0x6c6d006b735f6d6f
        .quad   0x656b5f3738617364
        .quad   0x6e695f7269617079
        .quad   0x6d006c616e726574
        .quad   0x6b5f37386173646c
        .quad   0x6d00726961707965
        .quad   0x735f37386173646c
        .quad   0x65727574616e6769
        .quad   0x616e7265746e695f
        .quad   0x386173646c6d006c
        .quad   0x74616e6769735f37
        .quad   0x6d7478655f657275
        .quad   0x386173646c6d0075
        .quad   0x7966697265765f37
        .quad   0x616e7265746e695f
        .quad   0x386173646c6d006c
        .quad   0x7966697265765f37
        .quad   0x6d00756d7478655f
        .quad   0x705f37386173646c
        .quad   0x645f657261706572
        .quad   0x65735f6e69616d6f
        .quad   0x6e6f697461726170
        .quad   0x007869666572705f
        .quad   0x5f37386173646c6d
        .quad   0x727574616e676973
        .quad   0x386173646c6d0065
        .quad   0x7966697265765f37
        .quad   0x37386173646c6d00
        .quad   0x7574616e6769735f
        .quad   0x685f6572705f6572
        .quad   0x65746e695f687361
        .quad   0x646c6d006c616e72
        .quad   0x6769735f37386173
        .quad   0x705f65727574616e
        .quad   0x5f687361685f6572
        .quad   0x363532656b616873
        .quad   0x37386173646c6d00
        .quad   0x5f7966697265765f
        .quad   0x687361685f657270
        .quad   0x616e7265746e695f
        .quad   0x386173646c6d006c
        .quad   0x7966697265765f37
        .quad   0x7361685f6572705f
        .quad   0x32656b6168735f68
        .quad   0x6173646c6d003635
        .quad   0x72665f6b705f3738
        .quad   0x696c006b735f6d6f
        .quad   0x732e6173646c6d62
        .quad   0x6c61636f6c2f006f
        .quad   0x65622f656d6f682f
        .quad   0x722f6e6168706b63
        .quad   0x646c6d2f736f7065
        .quad   0x766974616e2d6173
        .quad   0x7972616e69622d65
        .quad   0x646c69756265722d
        .quad   0x2f554e507468542e
        .quad   0x6f2f656372756f73
        .quad   0x6f2f737475707475
        .quad   0x000062696c2f7475
        .quad   0x000000000001fff8
        .quad   0x0000000200000401
        .quad   0x0000000000000000
        .quad   0x000000000001ffd0
        .quad   0x0000000300000402
        .quad   0x0000000000000000
        .quad   0x000000000001ffd8
        .quad   0x0000000400000402
        .quad   0x0000000000000000
        .quad   0x000000000001ffe0
        .quad   0x0000000500000402
        .quad   0x0000000000000000
        .quad   0x000000000001ffe8
        .quad   0x0000000600000402
        .quad   0x0000000000000000
        .quad   0x0000000000000000

// The procedure linkage table and the code (0xe30 to 0x9db4)
// .plt
        stp     x16, x30, [sp, #-16]!
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4040]
        add     x16, x16, #0xfc8
        br      x17
        nop
        nop
        nop
L0e50:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4048]
        add     x16, x16, #0xfd0
        br      x17
L0e60:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4056]
        add     x16, x16, #0xfd8
        br      x17
L0e70:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4064]
        add     x16, x16, #0xfe0
        br      x17
L0e80:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4072]
        add     x16, x16, #0xfe8
        br      x17

// keccak_absorb (0x88 bytes)
L0e90:
        stp     x19, x20, [sp, #-64]!
        mov     w19, w1
        mov     x20, x4
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        mov     x21, x3
        stp     x23, x24, [sp, #32]
        mov     w23, w2
        str     x30, [sp, #48]
L0eb4:
        sub     w24, w23, w19
        sub     w3, w23, w19
        cmp     x24, x20
        b.ls    L0ef0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x21
        mov     x0, x22
        bl      L1594
        ldp     x21, x22, [sp, #16]
        add     w0, w19, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L0ef0:
        mov     w2, w19
        mov     x1, x21
        mov     x0, x22
        bl      L1594
        mov     x0, x22
        sub     x20, x20, x24
        add     x21, x21, x24
        mov     w19, #0x0
        bl      L16c0
        b       L0eb4

// keccak_squeeze (0x8c bytes)
L0f18:
        stp     x19, x20, [sp, #-64]!
        mov     x20, x1
        mov     w19, w3
        stp     x21, x22, [sp, #16]
        mov     w22, w4
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x2
        stp     x25, x30, [sp, #48]
        mov     x25, #0x0
L0f40:
        cbnz    x20, L0f5c
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L0f5c:
        cmp     w19, w22
        b.ne    L0f70
        mov     w19, #0x0
        mov     x0, x23
        bl      L16c0
L0f70:
        sub     w0, w22, w19
        sub     w21, w22, w19
        cmp     x0, x20
        mov     w2, w19
        csel    w21, w20, w21, hi
        add     x1, x24, x25
        mov     w3, w21
        mov     x0, x23
        sub     x20, x20, w21, uxtw
        add     w19, w19, w21
        add     x25, x25, w21, uxtw
        bl      L1570
        b       L0f40

// mldsa_shake128_init (0x20 bytes)
L0fa4:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        mov     x2, #0xc8
        mov     w1, #0x0
        bl      L0e80
        str     wzr, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_absorb (0x28 bytes)
L0fc4:
        stp     x19, x30, [sp, #-16]!
        mov     x3, x1
        mov     x19, x0
        ldr     w1, [x0, #200]
        mov     x4, x2
        mov     w2, #0xa8
        bl      L0e90
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_finalize (0x80 bytes)
L0fec:
        .inst   0xf00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        stp     x19, x30, [sp, #-32]!
        mov     w3, #0x1
        ldr     x2, [x1]
        str     x2, [sp, #24]
        mov     x2, #0x0
        mov     w1, #0x1f
        ldr     w2, [x0, #200]
        mov     x19, x0
        strb    w1, [sp, #23]
        mov     w1, #0xffffff80
        strb    w1, [sp, #22]
        add     x1, sp, #0x17
        bl      L1594
        add     x1, sp, #0x16
        mov     x0, x19
        mov     w2, #0xa7
        mov     w3, #0x1
        bl      L1594
        mov     w0, #0xa8
        str     w0, [x19, #200]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1064
        bl      L0e70
L1064:
        ldp     x19, x30, [sp], #32
        ret

// mldsa_shake128_squeeze (0x20 bytes)
L106c:
        ldr     w3, [x2, #200]
        mov     w4, #0xa8
        stp     x19, x30, [sp, #-16]!
        mov     x19, x2
        bl      L0f18
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_release (0x1c bytes)

// mldsa_shake128_release.localalias (0x1c bytes)
L108c:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0xd0
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_init (0x20 bytes)
L10a8:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        mov     x2, #0xc8
        mov     w1, #0x0
        bl      L0e80
        str     wzr, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_absorb (0x28 bytes)
L10c8:
        stp     x19, x30, [sp, #-16]!
        mov     x3, x1
        mov     x19, x0
        ldr     w1, [x0, #200]
        mov     x4, x2
        mov     w2, #0x88
        bl      L0e90
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_finalize (0x80 bytes)
L10f0:
        .inst   0xd00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        stp     x19, x30, [sp, #-32]!
        mov     w3, #0x1
        ldr     x2, [x1]
        str     x2, [sp, #24]
        mov     x2, #0x0
        mov     w1, #0x1f
        ldr     w2, [x0, #200]
        mov     x19, x0
        strb    w1, [sp, #23]
        mov     w1, #0xffffff80
        strb    w1, [sp, #22]
        add     x1, sp, #0x17
        bl      L1594
        add     x1, sp, #0x16
        mov     x0, x19
        mov     w2, #0x87
        mov     w3, #0x1
        bl      L1594
        mov     w0, #0x88
        str     w0, [x19, #200]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1168
        bl      L0e70
L1168:
        ldp     x19, x30, [sp], #32
        ret

// mldsa_shake256_squeeze (0x20 bytes)
L1170:
        ldr     w3, [x2, #200]
        mov     w4, #0x88
        stp     x19, x30, [sp, #-16]!
        mov     x19, x2
        bl      L0f18
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_release (0x4 bytes)
L1190:
        b       L108c

// mldsa_shake256 (0x9c bytes)
L1194:
        stp     x19, x20, [sp, #-272]!
        mov     x20, x0
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        mov     x21, x1
        stp     x23, x30, [sp, #32]
        add     x19, sp, #0x38
        mov     x23, x3
        ldr     x1, [x0]
        str     x1, [sp, #264]
        mov     x1, #0x0
        mov     x22, x2
        mov     x0, x19
        bl      L10a8
        mov     x2, x23
        mov     x1, x22
        mov     x0, x19
        bl      L10c8
        mov     x0, x19
        bl      L10f0
        mov     x2, x19
        mov     x1, x21
        mov     x0, x20
        bl      L1170
        mov     x0, x19
        bl      L1190
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #264]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1220
        bl      L0e70
L1220:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #272
        ret

// mld_keccak_absorb_once_x4.constprop.0 (0x150 bytes)
L1230:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        mov     x19, x6
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        mov     x22, #0x0
        stp     x23, x24, [sp, #32]
        mov     w23, w1
        mov     x21, x23
        stp     x25, x26, [sp, #48]
        mov     x24, x2
        mov     x25, x3
        stp     x27, x30, [sp, #64]
        mov     x26, x4
        mov     x27, x5
        ldr     x1, [x0]
        str     x1, [sp, #88]
        mov     x1, #0x0
        mov     w0, #0x1f
        strb    w0, [sp, #87]
L1284:
        add     x4, x27, x22
        add     x3, x26, x22
        add     x2, x25, x22
        add     x1, x24, x22
        add     x22, x22, x23
        cmp     x19, x23
        b.cs    L1314
        mov     w23, w19
        sub     w21, w21, #0x1
        add     x22, sp, #0x57
        cbz     x19, L1334
        mov     w6, w19
        mov     x0, x20
        mov     w5, #0x0
        bl      L1640
        cmp     x19, w21, uxtw
        b.ne    L1334
        ldrb    w0, [sp, #87]
        mov     w5, w19
        mov     w6, #0x1
        orr     w0, w0, #0xffffff80
        strb    w0, [sp, #87]
L12dc:
        mov     x2, x22
        mov     x1, x22
        mov     x0, x20
        mov     x4, x22
        mov     x3, x22
        bl      L1640
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1368
        bl      L0e70
L1314:
        mov     w6, w21
        mov     w5, #0x0
        mov     x0, x20
        bl      L1640
        mov     x0, x20
        sub     x19, x19, x23
        bl      L1cb4
        b       L1284
L1334:
        mov     w5, w23
        mov     x0, x20
        mov     w6, #0x1
        mov     x4, x22
        mov     x3, x22
        mov     x2, x22
        mov     x1, x22
        bl      L1640
        mov     w0, #0xffffff80
        mov     w5, w21
        mov     w6, #0x1
        strb    w0, [sp, #87]
        b       L12dc
L1368:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #96
        ret

// mldsa_shake128x4_absorb_once (0x64 bytes)
L1380:
        stp     x19, x20, [sp, #-64]!
        mov     x19, x0
        mov     x20, x1
        mov     w1, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        mov     x21, x2
        mov     x2, #0x320
        stp     x23, x24, [sp, #32]
        mov     x23, x4
        mov     x24, x5
        str     x30, [sp, #48]
        bl      L0e80
        ldr     x30, [sp, #48]
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        ldp     x23, x24, [sp, #32]
        mov     x3, x21
        ldp     x21, x22, [sp, #16]
        mov     x2, x20
        mov     x0, x19
        mov     w1, #0xa8
        ldp     x19, x20, [sp], #64
        b       L1230

// mldsa_shake128x4_squeezeblocks (0x80 bytes)
L13e4:
        stp     x19, x20, [sp, #-64]!
        mov     x19, x4
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x1
        mov     x22, x2
        stp     x23, x24, [sp, #32]
        mov     x24, x5
        mov     x23, x3
        str     x30, [sp, #48]
L140c:
        cbnz    x19, L1424
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L1424:
        mov     x0, x24
        bl      L1cb4
        mov     x4, x23
        mov     x3, x22
        mov     x2, x21
        mov     x1, x20
        mov     x0, x24
        mov     w6, #0xa8
        mov     w5, #0x0
        sub     x19, x19, #0x1
        add     x20, x20, #0xa8
        add     x21, x21, #0xa8
        add     x22, x22, #0xa8
        add     x23, x23, #0xa8
        bl      L15c0
        b       L140c

// mldsa_shake128x4_init (0x4 bytes)
L1464:
        ret

// mldsa_shake128x4_release (0x1c bytes)

// mldsa_shake128x4_release.localalias (0x1c bytes)
L1468:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0x320
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256x4_absorb_once (0x64 bytes)
L1484:
        stp     x19, x20, [sp, #-64]!
        mov     x19, x0
        mov     x20, x1
        mov     w1, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        mov     x21, x2
        mov     x2, #0x320
        stp     x23, x24, [sp, #32]
        mov     x23, x4
        mov     x24, x5
        str     x30, [sp, #48]
        bl      L0e80
        ldr     x30, [sp, #48]
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        ldp     x23, x24, [sp, #32]
        mov     x3, x21
        ldp     x21, x22, [sp, #16]
        mov     x2, x20
        mov     x0, x19
        mov     w1, #0x88
        ldp     x19, x20, [sp], #64
        b       L1230

// mldsa_shake256x4_squeezeblocks (0x80 bytes)
L14e8:
        stp     x19, x20, [sp, #-64]!
        mov     x19, x4
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x1
        mov     x22, x2
        stp     x23, x24, [sp, #32]
        mov     x24, x5
        mov     x23, x3
        str     x30, [sp, #48]
L1510:
        cbnz    x19, L1528
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L1528:
        mov     x0, x24
        bl      L1cb4
        mov     x4, x23
        mov     x3, x22
        mov     x2, x21
        mov     x1, x20
        mov     x0, x24
        mov     w6, #0x88
        mov     w5, #0x0
        sub     x19, x19, #0x1
        add     x20, x20, #0x88
        add     x21, x21, #0x88
        add     x22, x22, #0x88
        add     x23, x23, #0x88
        bl      L15c0
        b       L1510

// mldsa_shake256x4_init (0x4 bytes)
L1568:
        ret

// mldsa_shake256x4_release (0x4 bytes)
L156c:
        b       L1468

// mldsa_keccakf1600_extract_bytes (0x24 bytes)
L1570:
        add     x2, x0, w2, uxtw
        mov     x4, #0x0
L1578:
        cmp     w3, w4
        b.hi    L1584
        ret
L1584:
        ldrb    w0, [x2, x4]
        strb    w0, [x1, x4]
        add     x4, x4, #0x1
        b       L1578

// mldsa_keccakf1600_xor_bytes (0x2c bytes)
L1594:
        add     x2, x0, w2, uxtw
        mov     x0, #0x0
L159c:
        cmp     w3, w0
        b.hi    L15a8
        ret
L15a8:
        ldrb    w5, [x1, x0]
        add     x0, x0, #0x1
        ldrb    w4, [x2]
        eor     w4, w4, w5
        strb    w4, [x2], #1
        b       L159c

// mldsa_keccakf1600x4_extract_bytes (0x80 bytes)
L15c0:
        stp     x19, x20, [sp, #-64]!
        mov     w19, w5
        mov     w20, w6
        stp     x21, x22, [sp, #16]
        mov     x22, x4
        mov     x21, x0
        stp     x23, x24, [sp, #32]
        mov     x24, x2
        mov     x23, x3
        mov     w2, w5
        mov     w3, w6
        str     x30, [sp, #48]
        bl      L1570
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L1570
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L1570
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L1570

// mldsa_keccakf1600x4_xor_bytes (0x80 bytes)
L1640:
        stp     x19, x20, [sp, #-64]!
        mov     w19, w5
        mov     w20, w6
        stp     x21, x22, [sp, #16]
        mov     x22, x4
        mov     x21, x0
        stp     x23, x24, [sp, #32]
        mov     x24, x2
        mov     x23, x3
        mov     w2, w5
        mov     w3, w6
        str     x30, [sp, #48]
        bl      L1594
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L1594
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L1594
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L1594

// mldsa_keccakf1600_permute (0x5f4 bytes)
L16c0:
        stp     x19, x20, [sp, #-224]!
        .inst   0x90000042  // adrp x2, 0x9000
        ldp     x17, x1, [x0]
        str     x30, [sp, #80]
        str     x1, [sp, #104]
        ldp     x1, x30, [x0, #16]
        str     x1, [sp, #112]
        ldr     x1, [x0, #32]
        str     x1, [sp, #120]
        ldr     x1, [x0, #40]
        str     x1, [sp, #128]
        ldr     x1, [x0, #64]
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        add     x24, x2, #0xdb8
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        str     x1, [sp, #136]
        ldr     x1, [x0, #120]
        ldp     x16, x15, [x0, #48]
        ldp     x14, x4, [x0, #72]
        ldp     x21, x9, [x0, #88]
        ldp     x3, x10, [x0, #104]
        str     x1, [sp, #144]
        ldp     x18, x8, [x0, #128]
        str     wzr, [sp, #156]
        ldp     x13, x7, [x0, #144]
        ldp     x6, x22, [x0, #160]
        ldp     x12, x5, [x0, #176]
        ldr     x1, [x0, #192]
L1738:
        eor     x11, x21, x18
        ldr     x2, [sp, #144]
        eor     x20, x10, x7
        add     x24, x24, #0x10
        eor     x19, x4, x2
        ldr     x2, [sp, #128]
        eor     x2, x17, x2
        eor     x19, x19, x2
        ldr     x2, [sp, #104]
        eor     x19, x19, x6
        eor     x2, x2, x16
        eor     x11, x11, x2
        ldr     x2, [sp, #112]
        eor     x11, x11, x22
        eor     x26, x2, x15
        eor     x2, x9, x8
        eor     x26, x26, x2
        ldr     x2, [sp, #136]
        eor     x26, x26, x12
        eor     x25, x30, x2
        eor     x2, x3, x13
        eor     x25, x25, x2
        ldr     x2, [sp, #120]
        eor     x25, x25, x5
        eor     x2, x2, x14
        eor     x2, x2, x20
        eor     x20, x19, x26, ror #63
        eor     x2, x2, x1
        eor     x19, x25, x19, ror #63
        eor     x23, x2, x11, ror #63
        eor     x16, x20, x16
        eor     x11, x11, x25, ror #63
        eor     x2, x26, x2, ror #63
        ldur    x25, [x24, #-16]
        eor     x9, x11, x9
        eor     x17, x23, x17
        mvn     x26, x16, ror #20
        eor     x13, x2, x13
        eor     x25, x17, x25
        and     x26, x26, x9, ror #21
        eor     x14, x19, x14
        eor     x26, x26, x25
        mvn     x25, x9, ror #21
        eor     x1, x19, x1
        ror     x28, x13, #43
        and     x13, x25, x13, ror #43
        ror     x14, x14, #44
        eor     x13, x13, x16, ror #20
        eor     x4, x23, x4
        str     x13, [sp, #160]
        mvn     x13, x28
        eor     x30, x2, x30
        ror     x27, x1, #50
        and     x1, x13, x1, ror #50
        mvn     x13, x14
        eor     x18, x20, x18
        eor     x1, x1, x9, ror #21
        eor     x12, x11, x12
        ror     x9, x4, #61
        and     x4, x13, x4, ror #61
        eor     x15, x11, x15
        eor     x4, x4, x30, ror #36
        stp     x1, x4, [sp, #168]
        bic     x1, x17, x27
        mvn     x4, x18, ror #19
        eor     x28, x1, x28
        and     x4, x4, x12, ror #3
        ror     x1, x30, #36
        eor     x4, x4, x9
        bic     x1, x14, x1
        str     x4, [sp, #184]
        mvn     x4, x12, ror #3
        eor     x12, x1, x12, ror #3
        and     x30, x4, x30, ror #36
        ldr     x1, [sp, #104]
        eor     x4, x30, x18, ror #19
        eor     x3, x2, x3
        mvn     x17, x17
        and     x16, x17, x16, ror #20
        ror     x15, x15, #58
        str     x4, [sp, #192]
        eor     x4, x20, x1
        eor     x7, x19, x7
        eor     x6, x23, x6
        eor     x27, x16, x27
        mvn     x17, x15
        mvn     x13, x9
        ror     x16, x3, #39
        and     x13, x13, x18, ror #19
        and     x3, x17, x3, ror #39
        mvn     x17, x16
        ror     x1, x4, #63
        eor     x13, x13, x14
        ror     x9, x6, #46
        bic     x1, x15, x1
        ror     x14, x7, #56
        and     x7, x17, x7, ror #56
        eor     x1, x1, x9
        eor     x7, x7, x15
        str     x7, [sp, #200]
        mvn     x7, x14
        str     x1, [sp, #208]
        ldr     x1, [sp, #120]
        and     x6, x7, x6, ror #46
        mvn     x7, x9
        eor     x3, x3, x4, ror #63
        and     x4, x7, x4, ror #63
        eor     x21, x20, x21
        eor     x4, x4, x14
        eor     x14, x19, x1
        ldr     x1, [sp, #128]
        eor     x6, x6, x16
        eor     x8, x11, x8
        ror     x15, x21, #54
        eor     x1, x23, x1
        eor     x5, x2, x5
        ror     x9, x8, #49
        mvn     x16, x1, ror #28
        ror     x7, x14, #37
        and     x21, x16, x21, ror #54
        mvn     x7, x7
        eor     x16, x21, x14, ror #37
        str     x16, [sp, #216]
        mvn     x16, x15
        eor     x10, x19, x10
        and     x8, x16, x8, ror #49
        mvn     x16, x9
        eor     x8, x8, x1, ror #28
        and     x16, x16, x5, ror #8
        and     x1, x7, x1, ror #28
        eor     x18, x16, x15
        mvn     x15, x5, ror #8
        eor     x5, x1, x5, ror #8
        ldr     x1, [sp, #112]
        eor     x20, x20, x22
        and     x14, x15, x14, ror #37
        mvn     x15, x10, ror #25
        eor     x11, x11, x1
        eor     x14, x14, x9
        ldr     x1, [sp, #136]
        eor     x2, x2, x1
        ldr     x1, [sp, #144]
        mvn     x9, x2, ror #9
        and     x9, x9, x10, ror #25
        eor     x7, x23, x1
        ror     x1, x20, #62
        eor     x9, x9, x11, ror #2
        and     x15, x15, x7, ror #23
        eor     x25, x15, x2, ror #9
        mvn     x15, x7, ror #23
        and     x20, x15, x20, ror #62
        mvn     x15, x1
        and     x15, x15, x11, ror #2
        mvn     x11, x11, ror #2
        and     x2, x11, x2, ror #9
        eor     x7, x15, x7, ror #23
        eor     x2, x2, x1
        eor     x10, x20, x10, ror #25
        ldp     x1, x15, [sp, #176]
        eor     x17, x5, x2
        ldur    x23, [x24, #-8]
        eor     x19, x26, x1
        ldr     x1, [sp, #216]
        eor     x1, x3, x1
        eor     x19, x19, x1
        ldr     x1, [sp, #160]
        eor     x19, x19, x9
        eor     x11, x1, x13
        ldr     x1, [sp, #200]
        eor     x1, x1, x8
        eor     x11, x11, x1
        ldr     x1, [sp, #168]
        eor     x11, x11, x25
        eor     x16, x1, x15
        eor     x1, x6, x18
        eor     x16, x16, x1
        ldr     x1, [sp, #192]
        eor     x16, x16, x10
        eor     x15, x28, x1
        eor     x1, x4, x14
        eor     x15, x15, x1
        eor     x22, x19, x16, ror #63
        ldr     x1, [sp, #208]
        eor     x15, x15, x7
        eor     x13, x13, x22
        eor     x19, x15, x19, ror #63
        eor     x1, x12, x1
        eor     x2, x2, x19
        eor     x1, x1, x17
        mvn     x17, x13, ror #20
        eor     x1, x1, x27
        eor     x12, x12, x19
        eor     x20, x1, x11, ror #63
        eor     x11, x11, x15, ror #63
        eor     x6, x6, x11
        eor     x1, x16, x1, ror #63
        eor     x15, x26, x20
        eor     x14, x14, x1
        eor     x23, x15, x23
        and     x17, x17, x6, ror #21
        eor     x17, x17, x23
        mvn     x23, x6, ror #21
        ror     x21, x14, #43
        and     x14, x23, x14, ror #43
        ror     x16, x2, #50
        eor     x14, x14, x13, ror #20
        str     x14, [sp, #104]
        mvn     x14, x21
        bic     x30, x15, x16
        and     x2, x14, x2, ror #50
        mvn     x15, x15
        and     x13, x15, x13, ror #20
        eor     x2, x2, x6, ror #21
        eor     x3, x3, x20
        ror     x12, x12, #44
        str     x2, [sp, #112]
        eor     x2, x13, x16
        mvn     x13, x12
        str     x2, [sp, #120]
        eor     x2, x28, x1
        eor     x10, x10, x11
        eor     x8, x8, x22
        ror     x6, x3, #61
        and     x3, x13, x3, ror #61
        ror     x14, x2, #36
        eor     x3, x3, x2, ror #36
        str     x3, [sp, #128]
        mvn     x3, x10, ror #3
        eor     x4, x4, x1
        and     x2, x3, x2, ror #36
        mvn     x16, x6
        eor     x2, x2, x8, ror #19
        str     x2, [sp, #136]
        ldr     x2, [sp, #160]
        and     x16, x16, x8, ror #19
        eor     x5, x5, x19
        bic     x14, x12, x14
        eor     x3, x2, x22
        eor     x16, x16, x12
        ldr     x2, [sp, #184]
        ror     x12, x4, #39
        eor     x9, x9, x20
        mvn     x15, x8, ror #19
        eor     x2, x2, x11
        ror     x8, x5, #56
        and     x15, x15, x10, ror #3
        eor     x14, x14, x10, ror #3
        ror     x2, x2, #58
        mvn     x13, x2
        ror     x10, x3, #63
        and     x4, x13, x4, ror #39
        mvn     x13, x12
        and     x5, x13, x5, ror #56
        bic     x10, x2, x10
        eor     x30, x30, x21
        eor     x15, x15, x6
        eor     x21, x5, x2
        ror     x6, x9, #46
        ldr     x2, [sp, #176]
        mvn     x5, x8
        and     x9, x5, x9, ror #46
        eor     x10, x10, x6
        mvn     x5, x6
        eor     x2, x2, x20
        ldr     x6, [sp, #200]
        eor     x4, x4, x3, ror #63
        and     x3, x5, x3, ror #63
        eor     x13, x27, x19
        eor     x3, x3, x8
        eor     x8, x6, x22
        mvn     x23, x2, ror #28
        eor     x18, x18, x11
        eor     x9, x9, x12
        ror     x12, x8, #54
        and     x8, x23, x8, ror #54
        eor     x7, x7, x1
        eor     x8, x8, x13, ror #37
        ror     x6, x18, #49
        str     x8, [sp, #144]
        ror     x5, x13, #37
        mvn     x8, x12
        mvn     x5, x5
        and     x18, x8, x18, ror #49
        mvn     x8, x6
        and     x8, x8, x7, ror #8
        eor     x18, x18, x2, ror #28
        and     x2, x5, x2, ror #28
        eor     x8, x8, x12
        mvn     x12, x7, ror #8
        eor     x7, x2, x7, ror #8
        ldr     x2, [sp, #168]
        eor     x5, x25, x22
        and     x13, x12, x13, ror #37
        eor     x11, x2, x11
        eor     x13, x13, x6
        ldr     x2, [sp, #192]
        eor     x1, x2, x1
        ldr     x2, [sp, #208]
        mvn     x6, x1, ror #9
        eor     x19, x2, x19
        ldr     x2, [sp, #216]
        and     x6, x6, x19, ror #25
        mvn     x22, x19, ror #25
        eor     x6, x6, x11, ror #2
        eor     x20, x2, x20
        ror     x2, x5, #62
        mvn     x12, x20, ror #23
        and     x22, x22, x20, ror #23
        and     x5, x12, x5, ror #62
        eor     x22, x22, x1, ror #9
        eor     x12, x5, x19, ror #25
        mvn     x5, x2
        and     x5, x5, x11, ror #2
        mvn     x11, x11, ror #2
        and     x1, x11, x1, ror #9
        eor     x5, x5, x20, ror #23
        eor     x1, x1, x2
        ldr     w2, [sp, #156]
        add     w2, w2, #0x2
        str     w2, [sp, #156]
        cmp     w2, #0x18
        b.ne    L1738
        ldr     x2, [sp, #104]
        stp     x17, x2, [x0]
        ldr     x2, [sp, #112]
        str     x2, [x0, #16]
        ldr     x2, [sp, #120]
        str     x2, [x0, #32]
        ldr     x2, [sp, #128]
        str     x2, [x0, #40]
        ldr     x2, [sp, #136]
        str     x2, [x0, #64]
        ldr     x2, [sp, #144]
        str     x30, [x0, #24]
        stp     x16, x15, [x0, #48]
        stp     x14, x4, [x0, #72]
        stp     x21, x9, [x0, #88]
        stp     x3, x10, [x0, #104]
        str     x2, [x0, #120]
        stp     x18, x8, [x0, #128]
        stp     x13, x7, [x0, #144]
        stp     x6, x22, [x0, #160]
        stp     x12, x5, [x0, #176]
        str     x1, [x0, #192]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #224
        ret

// mldsa_keccakf1600x4_permute (0x28 bytes)
L1cb4:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L16c0
        add     x0, x19, #0xc8
        bl      L16c0
        add     x0, x19, #0x190
        bl      L16c0
        add     x0, x19, #0x258
        ldp     x19, x30, [sp], #16
        b       L16c0

// mldsa44_unpack_pk_t1 (0x14 bytes)
L1cdc:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25f0

// mldsa44_pack_sk_rho_key_tr (0x28 bytes)
L1cf0:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x3]
        stp     q0, q1, [x0, #32]
        add     x0, x0, #0x40
        ldp     q0, q1, [x2]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x2, #32]
        stp     q0, q1, [x0, #32]
        ret

// mldsa44_unpack_sk (0xa4 bytes)
L1d18:
        ldp     q0, q1, [x6]
        stp     x19, x20, [sp, #-48]!
        mov     x19, x6
        stp     x21, x22, [sp, #16]
        mov     x20, x3
        mov     x21, x5
        str     x30, [sp, #32]
        mov     x22, x4
        stp     q0, q1, [x0]
        add     x0, x6, #0x40
        ldp     q0, q1, [x6, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x0]
        stp     q0, q1, [x1]
        ldp     q0, q1, [x0, #32]
        mov     x0, x4
        stp     q0, q1, [x1, #32]
        add     x1, x6, #0x80
        bl      L36f0
        mov     x0, x22
        mov     x22, x20
        bl      L3520
        add     x1, x19, #0x200
        mov     x0, x21
        bl      L3768
        mov     x0, x21
        add     x21, x19, #0x380
        add     x19, x19, #0xa00
        bl      L3614
L1d8c:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L2774
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L1d8c
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L3614

// mldsa44_pack_sig_c (0xc bytes)
L1dbc:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ret

// mldsa44_pack_sig_h (0xec bytes)
L1dc8:
        stp     x19, x20, [sp, #-96]!
        mov     x19, #0x0
        mov     w20, #0x0
        stp     x25, x26, [sp, #48]
        add     x25, x0, #0x920
        mov     x26, #0xc0
        stp     x27, x28, [sp, #64]
        mov     w27, #0x7400
        mov     w28, #0xe800
        movk    w27, #0x1, lsl #16
        movk    w28, #0x2, lsl #16
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     x22, x3
        mov     x0, x25
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x24, x2
        mov     w1, #0x0
        mov     x2, #0x54
        str     x30, [sp, #80]
        bl      L0e80
L1e20:
        madd    x1, x19, x26, x24
        mov     x0, x22
        bl      L2994
        mov     w2, #0x8c00
        add     x1, x23, x19, lsl #10
        mov     x4, #0x0
        movk    w2, #0xfffe, lsl #16
L1e3c:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w3, [x22, x4, lsl #2]
        add     w5, w0, w27
        cmp     w5, w28
        b.hi    L1e5c
        cmp     w3, #0x0
        ccmp    w0, w2, #0x0, ne
        b.ne    L1e6c
L1e5c:
        cmp     w20, #0x50
        b.eq    L1eac
        strb    w4, [x25, w20, uxtw]
        add     w20, w20, #0x1
L1e6c:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L1e3c
        add     x0, x21, #0x970
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x4
        b.ne    L1e20
        mov     w0, #0x0
L1e90:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L1eac:
        mov     w0, #0xffffffff
        b       L1e90

// mldsa44_pack_sig_z (0x14 bytes)
L1eb4:
        mov     w3, #0x240
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x0, x0, x2
        b       L3190

// mldsa44_sig_unpack_hints (0xdc bytes)
L1ec8:
        stp     x19, x20, [sp, #-48]!
        mov     x3, x0
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, #0x920
        cbz     w2, L1f18
        add     w0, w2, #0x4f
        ldrb    w22, [x23, x0]
L1ef0:
        add     w0, w21, #0x50
        ldrb    w19, [x23, x0]
        cmp     w19, #0x50
        ccmp    w22, w19, #0x2, ls
        b.ls    L1f20
L1f04:
        mov     w0, #0xffffffff
L1f08:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L1f18:
        mov     w22, #0x0
        b       L1ef0
L1f20:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        add     x2, x20, w22, uxtb
        mov     x3, x0
        mov     w1, w22
        mov     w4, #0x1
L1f40:
        cmp     w1, w19
        b.cc    L1f64
        cmp     w21, #0x3
        b.ne    L1f5c
        add     x20, x20, #0x91f
L1f54:
        cmp     w19, #0x50
        b.ne    L1f94
L1f5c:
        mov     w0, #0x0
        b       L1f08
L1f64:
        cmp     w1, w22
        b.ls    L1f80
        sub     w0, w1, #0x1
        ldrb    w5, [x2, #2336]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L1f04
L1f80:
        ldrb    w0, [x2, #2336]
        add     w1, w1, #0x1
        add     x2, x2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L1f40
L1f94:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L1f54
        b       L1f04

// mld_rej_uniform_c.constprop.0 (0x5c bytes)
L1fa4:
        mov     x5, x0
        mov     w0, w1
        mov     w1, #0x3
        sub     w1, w1, w2
L1fb4:
        cmp     w0, #0xff
        b.hi    L1fc8
L1fbc:
        add     w4, w1, w2
        cmp     w3, w4
        b.cs    L1fcc
L1fc8:
        ret
L1fcc:
        ldrb    w6, [x2, #2]
        add     x2, x2, #0x3
        ldurb   w4, [x2, #-2]
        ldurb   w7, [x2, #-3]
        lsl     w6, w6, #16
        orr     w4, w6, w4, lsl #8
        orr     w4, w4, w7
        and     w4, w4, #0x7fffff
        cmp     w4, #0x7fe, lsl #12
        b.hi    L1fbc
        str     w4, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
        b       L1fb4

// mldsa_poly_reduce (0x2c bytes)
L2000:
        mov     x1, #0x0
        mov     w4, #0xff801fff
L2008:
        ldr     w3, [x0, x1, lsl #2]
        add     w2, w3, #0x400, lsl #12
        asr     w2, w2, #23
        madd    w2, w2, w4, w3
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L2008
        ret

// mldsa_poly_caddq (0x3c bytes)
L202c:
        mov     w5, #0xe001
        mov     x3, #0x0
        movk    w5, #0x7f, lsl #16
L2038:
        ldr     w4, [x0, x3, lsl #2]
        sxtw    x1, w4
        asr     x1, x1, #31
        add     w2, w4, w5
        eor     w2, w2, w4
        and     w1, w2, w1
        eor     w1, w1, w4
        str     w1, [x0, x3, lsl #2]
        add     x3, x3, #0x1
        cmp     x3, #0x100
        b.ne    L2038
        ret

// mldsa_poly_add (0x24 bytes)
L2068:
        mov     x2, #0x0
L206c:
        ldr     w3, [x0, x2]
        ldr     w4, [x1, x2]
        add     w3, w3, w4
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L206c
        ret

// mldsa_poly_sub (0x24 bytes)
L208c:
        mov     x2, #0x0
L2090:
        ldr     w3, [x0, x2]
        ldr     w4, [x1, x2]
        sub     w3, w3, w4
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L2090
        ret

// mldsa_poly_shiftl (0x20 bytes)
L20b0:
        mov     x1, #0x0
L20b4:
        ldr     w2, [x0, x1, lsl #2]
        lsl     w2, w2, #13
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L20b4
        ret

// mldsa_poly_ntt (0xa8 bytes)
L20d0:
        mov     w1, #0x1
        .inst   0xf0000028  // adrp x8, 0x9000
        mov     w13, #0x2001
        mov     w11, w1
        add     x8, x8, #0xe78
        mov     w12, #0x100
        movk    w13, #0x380, lsl #16
        mov     w14, #0xff801fff
L20f0:
        sub     w6, w1, #0x1
        lsr     w2, w12, w1
        lsl     w10, w2, #1
        mov     w5, #0x0
        lsl     w6, w11, w6
L2104:
        mov     w3, w6
        add     w6, w6, #0x1
        ldr     w15, [x8, w3, uxtw #2]
        cmp     w5, w2
        b.cs    L2158
        mov     w3, w5
        add     x9, x0, w2, uxtw #2
L2120:
        ldr     w7, [x9]
        smull   x7, w15, w7
        mul     w4, w7, w13
        smaddl  x4, w4, w14, x7
        ldr     w7, [x0, x3, lsl #2]
        asr     x4, x4, #32
        sub     w7, w7, w4
        str     w7, [x9], #4
        ldr     w7, [x0, x3, lsl #2]
        add     w4, w7, w4
        str     w4, [x0, x3, lsl #2]
        add     x3, x3, #0x1
        cmp     w2, w3
        b.hi    L2120
L2158:
        add     w5, w5, w10
        add     w2, w2, w10
        cmp     w5, #0xff
        b.ls    L2104
        add     w1, w1, #0x1
        cmp     w1, #0x9
        b.ne    L20f0
        ret

// mldsa_poly_invntt_tomont (0xe0 bytes)
L2178:
        .inst   0xf0000029  // adrp x9, 0x9000
        mov     w14, #0x2001
        add     x9, x9, #0xe78
        mov     w3, #0x8
        mov     w12, #0x100
        mov     w13, #0x1
        movk    w14, #0x380, lsl #16
        mov     w15, #0xff801fff
L2198:
        lsr     w2, w12, w3
        mov     w4, #0x0
        lsl     w5, w13, w3
        lsl     w11, w2, #1
        sub     w5, w5, #0x1
L21ac:
        mov     w1, w5
        sub     w5, w5, #0x1
        ldr     w10, [x9, w1, uxtw #2]
        neg     w10, w10
        cmp     w4, w2
        b.cs    L2204
        mov     w6, w4
        add     x8, x0, w2, uxtw #2
L21cc:
        ldr     w1, [x0, x6, lsl #2]
        ldr     w7, [x8]
        add     w7, w7, w1
        str     w7, [x0, x6, lsl #2]
        add     x6, x6, #0x1
        ldr     w7, [x8]
        sub     w1, w1, w7
        smull   x1, w1, w10
        mul     w7, w1, w14
        smaddl  x1, w7, w15, x1
        asr     x1, x1, #32
        str     w1, [x8], #4
        cmp     w2, w6
        b.hi    L21cc
L2204:
        add     w4, w4, w11
        add     w2, w2, w11
        cmp     w4, #0xff
        b.ls    L21ac
        subs    w3, w3, #0x1
        b.ne    L2198
        mov     w5, #0x2001
        mov     x1, #0x0
        mov     w6, #0xa3fa
        movk    w5, #0x380, lsl #16
        mov     w4, #0xff801fff
L2230:
        ldr     w3, [x0, x1, lsl #2]
        smull   x3, w3, w6
        mul     w2, w3, w5
        smaddl  x2, w2, w4, x3
        asr     x2, x2, #32
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L2230
        ret

// mldsa_poly_pointwise_montgomery (0x3c bytes)
L2258:
        mov     w6, #0x2001
        mov     x2, #0x0
        movk    w6, #0x380, lsl #16
        mov     w5, #0xff801fff
L2268:
        ldr     w3, [x1, x2]
        ldr     w4, [x0, x2]
        smull   x4, w4, w3
        mul     w3, w4, w6
        smaddl  x3, w3, w5, x4
        asr     x3, x3, #32
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L2268
        ret

// mldsa_poly_power2round (0x30 bytes)
L2294:
        mov     x3, #0x0
L2298:
        ldr     w4, [x2, x3]
        add     w5, w4, #0xfff
        asr     w6, w5, #13
        and     w5, w5, #0xffffe000
        str     w6, [x0, x3]
        sub     w4, w4, w5
        str     w4, [x1, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L2298
        ret

// mldsa_poly_uniform (0xf4 bytes)
L22c4:
        sub     sp, sp, #0x470
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x21, sp, #0x398
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        mov     x20, x1
        str     x30, [sp, #32]
        add     x19, sp, #0x4f
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #1128]
        mov     x1, #0x0
        mov     x0, x21
        bl      L0fa4
        mov     x1, x20
        mov     x2, #0x22
        mov     x0, x21
        bl      L0fc4
        mov     x0, x21
        bl      L0fec
        mov     x2, x21
        mov     x1, #0x348
        mov     x0, x19
        bl      L106c
        mov     x2, x19
        mov     w3, #0x348
        mov     w1, #0x0
L2338:
        mov     x0, x22
        bl      L1fa4
        mov     w20, w0
        cmp     w0, #0xff
        b.ls    L2384
        mov     x0, x21
        bl      L108c
        mov     x0, x19
        mov     x2, #0x348
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1128]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L23a4
        bl      L0e70
L2384:
        mov     x2, x21
        mov     x1, #0xa8
        mov     x0, x19
        bl      L106c
        mov     x2, x19
        mov     w1, w20
        mov     w3, #0xa8
        b       L2338
L23a4:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x470
        ret

// mldsa_poly_uniform_4x (0x1dc bytes)
L23b8:
        mov     x12, #0x1140
        sub     sp, sp, x12
        stp     x0, x1, [sp, #104]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x9f
        stp     x21, x22, [sp, #16]
        mov     x20, x4
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x23, sp, #0xe18
        mov     x24, x2
        stp     x25, x26, [sp, #48]
        mov     x25, x3
        add     x26, x19, #0xa20
        stp     x27, x28, [sp, #64]
        add     x27, x19, #0x6c0
        add     x28, x19, #0x360
        str     x30, [sp, #80]
        ldr     x1, [x0]
        str     x1, [sp, #4408]
        mov     x1, #0x0
        mov     x0, x23
        bl      L1464
        add     x4, x20, #0xc0
        add     x3, x20, #0x80
        add     x2, x20, #0x40
        mov     x1, x20
        mov     x0, x23
        mov     x5, #0x22
        bl      L1380
        mov     x5, x23
        mov     x4, #0x5
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L13e4
        ldr     x0, [sp, #104]
        mov     w3, #0x348
        mov     x2, x19
        mov     w1, #0x0
        bl      L1fa4
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     x2, x28
        mov     w1, #0x0
        bl      L1fa4
        mov     w22, w0
        mov     x2, x27
        mov     w1, #0x0
        mov     x0, x24
        bl      L1fa4
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L249c:
        mov     x0, x25
        bl      L1fa4
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L2500
        cmp     w22, #0xff
        b.ls    L2500
        cmp     w20, #0xff
        b.ls    L2500
        cmp     w0, #0xff
        b.ls    L2500
        mov     x0, x23
        bl      L1468
        mov     x0, x19
        mov     x2, #0xd80
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2570
        bl      L0e70
L2500:
        mov     x5, x23
        mov     x4, #0x1
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L13e4
        ldr     x0, [sp, #104]
        mov     w1, w21
        mov     w3, #0xa8
        mov     x2, x19
        bl      L1fa4
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     w1, w22
        mov     x2, x28
        bl      L1fa4
        mov     w22, w0
        mov     w1, w20
        mov     x2, x27
        mov     x0, x24
        bl      L1fa4
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     x2, x26
        mov     w1, w6
        b       L249c
L2570:
        ldp     x19, x20, [sp]
        mov     x12, #0x1140
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa_polyt1_pack (0x5c bytes)
L2594:
        add     x4, x1, #0x400
L2598:
        ldr     w2, [x1]
        add     x0, x0, #0x5
        sturb   w2, [x0, #-5]
        ldp     w2, w3, [x1]
        lsl     w3, w3, #2
        orr     w2, w3, w2, asr #8
        sturb   w2, [x0, #-4]
        ldp     w2, w3, [x1, #4]
        lsl     w3, w3, #4
        orr     w2, w3, w2, asr #6
        sturb   w2, [x0, #-3]
        ldp     w2, w3, [x1, #8]
        add     x1, x1, #0x10
        lsl     w3, w3, #6
        orr     w2, w3, w2, asr #4
        sturb   w2, [x0, #-2]
        ldur    w2, [x1, #-4]
        asr     w2, w2, #2
        sturb   w2, [x0, #-1]
        cmp     x1, x4
        b.ne    L2598
        ret

// mldsa_polyt1_unpack (0x70 bytes)
L25f0:
        add     x4, x1, #0x140
L25f4:
        ldrb    w3, [x1]
        add     x1, x1, #0x5
        ldurb   w2, [x1, #-4]
        add     x0, x0, #0x10
        orr     w2, w3, w2, lsl #8
        and     w2, w2, #0x3ff
        stur    w2, [x0, #-16]
        ldurb   w3, [x1, #-3]
        ldurb   w2, [x1, #-4]
        lsl     w3, w3, #6
        orr     w2, w3, w2, lsr #2
        and     w2, w2, #0x3ff
        stur    w2, [x0, #-12]
        ldurb   w3, [x1, #-2]
        ldurb   w2, [x1, #-3]
        lsl     w3, w3, #4
        orr     w2, w3, w2, lsr #4
        and     w2, w2, #0x3ff
        stur    w2, [x0, #-8]
        ldurb   w3, [x1, #-1]
        ldurb   w2, [x1, #-2]
        lsl     w3, w3, #2
        orr     w2, w3, w2, lsr #6
        stur    w2, [x0, #-4]
        cmp     x4, x1
        b.ne    L25f4
        ret

// mldsa_polyt0_pack (0x114 bytes)
L2660:
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-64]!
        add     x11, x0, #0x1a0
        ldr     x3, [x2]
        str     x3, [sp, #56]
        mov     x3, #0x0
        mov     w2, #0x1000
L2680:
        ldp     w10, w6, [x1]
        add     x0, x0, #0xd
        ldp     w9, w5, [x1, #8]
        sub     w6, w2, w6
        sub     w10, w2, w10
        ubfiz   w12, w6, #5, #3
        sub     w9, w2, w9
        ldp     w4, w8, [x1, #16]
        sub     w5, w2, w5
        ldp     w3, w7, [x1, #24]
        sturb   w10, [x0, #-13]
        orr     w10, w12, w10, lsr #8
        sturb   w10, [x0, #-12]
        lsr     w10, w6, #3
        sturb   w10, [x0, #-11]
        ubfiz   w10, w9, #2, #6
        sub     w4, w2, w4
        orr     w6, w10, w6, lsr #11
        sturb   w6, [x0, #-10]
        ubfiz   w6, w5, #7, #1
        sub     w8, w2, w8
        orr     w9, w6, w9, lsr #6
        lsr     w6, w5, #1
        sturb   w6, [x0, #-8]
        ubfiz   w6, w4, #4, #4
        orr     w5, w6, w5, lsr #9
        sturb   w5, [x0, #-7]
        lsr     w5, w4, #4
        sub     w3, w2, w3
        sturb   w5, [x0, #-6]
        ubfiz   w5, w8, #1, #7
        orr     w4, w5, w4, lsr #12
        sub     w7, w2, w7
        sturb   w4, [x0, #-5]
        ubfiz   w4, w3, #6, #2
        orr     w8, w4, w8, lsr #7
        lsr     w4, w3, #2
        sturb   w4, [x0, #-3]
        ubfiz   w4, w7, #3, #5
        orr     w3, w4, w3, lsr #10
        lsr     w7, w7, #5
        sturb   w9, [x0, #-9]
        add     x1, x1, #0x20
        sturb   w8, [x0, #-4]
        sturb   w3, [x0, #-2]
        sturb   w7, [x0, #-1]
        cmp     x11, x0
        b.ne    L2680
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        stp     xzr, xzr, [sp, #40]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #56]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L276c
        bl      L0e70
L276c:
        ldr     x30, [sp], #64
        ret

// mldsa_polyt0_unpack (0x154 bytes)
L2774:
        add     x12, x0, #0x400
        mov     w2, #0x1000
L277c:
        ldrb    w3, [x1]
        add     x1, x1, #0xd
        str     w3, [x0]
        ldurb   w9, [x1, #-12]
        orr     w9, w3, w9, lsl #8
        and     w9, w9, #0x1fff
        str     w9, [x0]
        sub     w9, w2, w9
        ldurb   w4, [x1, #-12]
        lsr     w4, w4, #5
        str     w4, [x0, #4]
        ldurb   w3, [x1, #-11]
        orr     w3, w4, w3, lsl #3
        str     w3, [x0, #4]
        ldurb   w8, [x1, #-10]
        orr     w8, w3, w8, lsl #11
        and     w8, w8, #0x1fff
        str     w8, [x0, #4]
        sub     w8, w2, w8
        ldurb   w3, [x1, #-10]
        lsr     w3, w3, #2
        str     w3, [x0, #8]
        ldurb   w7, [x1, #-9]
        orr     w7, w3, w7, lsl #6
        and     w7, w7, #0x1fff
        str     w7, [x0, #8]
        sub     w7, w2, w7
        ldurb   w4, [x1, #-9]
        lsr     w4, w4, #7
        str     w4, [x0, #12]
        ldurb   w3, [x1, #-8]
        orr     w3, w4, w3, lsl #1
        str     w3, [x0, #12]
        ldurb   w6, [x1, #-7]
        orr     w6, w3, w6, lsl #9
        and     w6, w6, #0x1fff
        str     w6, [x0, #12]
        sub     w6, w2, w6
        ldurb   w4, [x1, #-7]
        lsr     w4, w4, #4
        str     w4, [x0, #16]
        ldurb   w3, [x1, #-6]
        orr     w3, w4, w3, lsl #4
        str     w3, [x0, #16]
        ldurb   w5, [x1, #-5]
        orr     w5, w3, w5, lsl #12
        and     w5, w5, #0x1fff
        str     w5, [x0, #16]
        sub     w5, w2, w5
        ldurb   w3, [x1, #-5]
        lsr     w3, w3, #1
        str     w3, [x0, #20]
        ldurb   w4, [x1, #-4]
        orr     w4, w3, w4, lsl #7
        and     w4, w4, #0x1fff
        str     w4, [x0, #20]
        sub     w4, w2, w4
        ldurb   w3, [x1, #-4]
        lsr     w3, w3, #6
        str     w3, [x0, #24]
        ldurb   w10, [x1, #-3]
        orr     w10, w3, w10, lsl #2
        str     w10, [x0, #24]
        ldurb   w3, [x1, #-2]
        orr     w3, w10, w3, lsl #10
        and     w3, w3, #0x1fff
        str     w3, [x0, #24]
        sub     w3, w2, w3
        ldurb   w11, [x1, #-2]
        lsr     w11, w11, #3
        str     w11, [x0, #28]
        ldurb   w10, [x1, #-1]
        stp     w9, w8, [x0]
        stp     w7, w6, [x0, #8]
        orr     w10, w11, w10, lsl #5
        stp     w5, w4, [x0, #16]
        add     x0, x0, #0x20
        stur    w3, [x0, #-8]
        sub     w3, w2, w10
        stur    w3, [x0, #-4]
        cmp     x0, x12
        b.ne    L277c
        ret

// mldsa_poly_chknorm (0x4c bytes)
L28c8:
        sub     w1, w1, #0x1
        mov     x6, x0
        mov     x4, #0x0
        mov     w0, #0x0
L28d8:
        ldr     w5, [x6, x4, lsl #2]
        sxtw    x3, w5
        asr     x3, x3, #31
        neg     w2, w5
        eor     w2, w2, w5
        and     w2, w2, w3
        eor     w2, w2, w5
        sub     w2, w1, w2
        sxtw    x2, w2
        asr     x2, x2, #31
        add     x4, x4, #0x1
        orr     w0, w0, w2
        cmp     x4, #0x100
        b.ne    L28d8
        ret

// mldsa_polyw1_pack_88 (0x5c bytes)
L2914:
        add     x4, x1, #0x400
L2918:
        ldrb    w3, [x1]
        add     x1, x1, #0x10
        strb    w3, [x0]
        add     x0, x0, #0x3
        ldur    w2, [x1, #-12]
        orr     w2, w3, w2, lsl #6
        sturb   w2, [x0, #-3]
        ldur    w2, [x1, #-12]
        ubfx    x2, x2, #2, #8
        sturb   w2, [x0, #-2]
        ldur    w3, [x1, #-8]
        orr     w2, w2, w3, lsl #4
        sturb   w2, [x0, #-2]
        ldur    w2, [x1, #-8]
        ubfx    x2, x2, #4, #8
        sturb   w2, [x0, #-1]
        ldur    w3, [x1, #-4]
        orr     w2, w2, w3, lsl #2
        sturb   w2, [x0, #-1]
        cmp     x1, x4
        b.ne    L2918
        ret

// mldsa_polyw1_pack_32 (0x24 bytes)
L2970:
        mov     x2, #0x0
L2974:
        ldr     w3, [x1, #4]
        ldr     w4, [x1], #8
        orr     w3, w4, w3, lsl #4
        strb    w3, [x0, x2]
        add     x2, x2, #0x1
        cmp     x2, #0x80
        b.ne    L2974
        ret

// mldsa_polyw1_unpack_88 (0x60 bytes)
L2994:
        add     x4, x1, #0xc0
L2998:
        ldrb    w2, [x1]
        add     x1, x1, #0x3
        add     x0, x0, #0x10
        and     w2, w2, #0x3f
        stur    w2, [x0, #-16]
        ldurb   w3, [x1, #-2]
        ldurb   w2, [x1, #-3]
        lsl     w3, w3, #2
        orr     w2, w3, w2, lsr #6
        and     w2, w2, #0x3f
        stur    w2, [x0, #-12]
        ldurb   w3, [x1, #-1]
        ldurb   w2, [x1, #-2]
        lsl     w3, w3, #4
        orr     w2, w3, w2, lsr #4
        and     w2, w2, #0x3f
        stur    w2, [x0, #-8]
        ldurb   w2, [x1, #-1]
        lsr     w2, w2, #2
        stur    w2, [x0, #-4]
        cmp     x1, x4
        b.ne    L2998
        ret

// mldsa_polyw1_unpack_32 (0x30 bytes)
L29f4:
        mov     x2, #0x0
L29f8:
        ldrb    w3, [x1, x2]
        add     x0, x0, #0x8
        and     w3, w3, #0xf
        stur    w3, [x0, #-8]
        ldrb    w3, [x1, x2]
        add     x2, x2, #0x1
        lsr     w3, w3, #4
        stur    w3, [x0, #-4]
        cmp     x2, #0x80
        b.ne    L29f8
        ret

// mld_decompose44 (0x68 bytes)
L2a24:
        add     w3, w2, #0x7f
        mov     w4, #0x2c0b
        mov     w5, #0x2b
        asr     w3, w3, #7
        mul     w3, w3, w4
        add     w3, w3, #0x800, lsl #12
        asr     w4, w3, #24
        sub     w3, w5, w3, asr #24
        sxtw    x3, w3
        asr     x3, x3, #31
        bic     w3, w4, w3
        str     w3, [x1]
        mov     w1, #0x1800
        movk    w1, #0xfffd, lsl #16
        madd    w2, w3, w1, w2
        mov     w1, #0x3ff000
        sub     w1, w1, w2
        sxtw    x1, w1
        asr     x1, x1, #31
        mov     w3, #0xff801fff
        add     w3, w2, w3
        eor     w3, w3, w2
        and     w1, w3, w1
        eor     w1, w1, w2
        str     w1, [x0]
        ret

// mld_zeroize (0x1c bytes)
L2a8c:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c44.constprop.0 (0x88 bytes)
L2aa8:
        mov     x6, x0
        mov     w0, w1
        mov     x5, #0x0
        mov     w9, #0x87
        mov     w7, #0xcd
        mov     w8, #0x2
L2ac0:
        cmp     w0, #0xff
        ccmp    w5, w9, #0x2, ls
        b.ls    L2ad0
        ret
L2ad0:
        ldrb    w1, [x2, x5]
        and     w3, w1, #0xf
        lsr     w1, w1, #4
        cmp     w3, #0xf
        b.eq    L2b00
        mul     w4, w3, w7
        lsr     w4, w4, #10
        add     w4, w4, w4, lsl #2
        sub     w3, w3, w4
        sub     w3, w8, w3
        str     w3, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L2b00:
        cmp     w0, #0xff
        ccmp    w1, #0xe, #0x2, ls
        b.hi    L2b28
        mul     w3, w1, w7
        lsr     w3, w3, #10
        add     w3, w3, w3, lsl #2
        sub     w1, w1, w3
        sub     w1, w8, w1
        str     w1, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L2b28:
        add     x5, x5, #0x1
        b       L2ac0

// mldsa44_poly_decompose (0x34 bytes)
L2b30:
        mov     x8, x0
        mov     x7, x1
        mov     x6, #0x0
        str     x30, [sp, #-16]!
L2b40:
        ldr     w2, [x7, x6]
        add     x1, x8, x6
        add     x0, x7, x6
        add     x6, x6, #0x4
        bl      L2a24
        cmp     x6, #0x400
        b.ne    L2b40
        ldr     x30, [sp], #16
        ret

// mldsa44_poly_use_hint (0xa4 bytes)
L2b64:
        mov     x7, x0
        str     x30, [sp, #-32]!
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x8, x1
        add     x9, sp, #0x14
        mov     x6, #0x0
        ldr     x1, [x0]
        str     x1, [sp, #24]
        mov     x1, #0x0
        add     x0, sp, #0x10
        mov     w10, #0x2b
L2b94:
        ldr     w2, [x7, x6]
        mov     x1, x9
        ldr     w11, [x8, x6]
        bl      L2a24
        ldr     w2, [sp, #20]
        cbz     w11, L2bc0
        ldr     w1, [sp, #16]
        cmp     w1, #0x0
        b.le    L2bf0
        cmp     w2, #0x2b
        csinc   w2, wzr, w2, eq
L2bc0:
        str     w2, [x7, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L2b94
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2c00
        bl      L0e70
L2bf0:
        sub     w1, w2, #0x1
        cmp     w2, #0x0
        csel    w2, w1, w10, ne
        b       L2bc0
L2c00:
        ldr     x30, [sp], #32
        ret

// mldsa44_poly_uniform_eta_4x (0x22c bytes)
L2c08:
        sub     sp, sp, #0x7c0
        stp     x19, x20, [sp]
        add     x19, sp, #0x9f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x20, x19, #0x2e0
        add     x21, x19, #0x340
        stp     x23, x24, [sp, #32]
        add     x24, x19, #0x280
        add     x22, x19, #0x3a0
        stp     x25, x26, [sp, #48]
        add     x23, sp, #0x498
        mov     x25, x3
        stp     x27, x28, [sp, #64]
        add     x26, x19, #0x1e0
        add     x27, x19, #0x140
        str     x30, [sp, #80]
        add     x28, x19, #0xa0
        stp     x0, x1, [sp, #96]
        ldp     q0, q1, [x4, #32]
        str     x2, [sp, #112]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q2, q3, [x4]
        ldr     x1, [x0]
        str     x1, [sp, #1976]
        mov     x1, #0x0
        stp     q0, q1, [x20, #32]
        stp     q0, q1, [x24, #32]
        stp     q2, q3, [x20]
        stp     q2, q3, [x21]
        stp     q2, q3, [x24]
        stp     q0, q1, [x21, #32]
        stp     q2, q3, [x22]
        ldrb    w0, [sp, #1984]
        stp     q0, q1, [x22, #32]
        strb    w5, [x24, #64]
        strb    wzr, [x24, #65]
        strb    w6, [x24, #160]
        strb    wzr, [x24, #161]
        strb    w7, [x24, #256]
        strb    wzr, [x24, #257]
        strb    w0, [x24, #352]
        mov     x0, x23
        strb    wzr, [x24, #353]
        bl      L1568
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1484
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14e8
        ldr     x0, [sp, #96]
        mov     x2, x19
        mov     w1, #0x0
        bl      L2aa8
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L2aa8
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L2aa8
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L2d3c:
        mov     x0, x25
        bl      L2aa8
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L2da8
        cmp     w22, #0xff
        b.ls    L2da8
        cmp     w20, #0xff
        b.ls    L2da8
        cmp     w0, #0xff
        b.ls    L2da8
        mov     x0, x23
        bl      L156c
        mov     x0, x19
        mov     x1, #0x280
        bl      L2a8c
        mov     x0, x24
        mov     x1, #0x180
        bl      L2a8c
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1976]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2e14
        bl      L0e70
L2da8:
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14e8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     x2, x19
        bl      L2aa8
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L2aa8
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L2aa8
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L2d3c
L2e14:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7c0
        ret

// mldsa44_poly_challenge (0x160 bytes)
L2e34:
        stp     x19, x20, [sp, #-464]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x21, sp, #0xf8
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        add     x20, sp, #0x6f
        str     x30, [sp, #48]
        and     x20, x20, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #456]
        mov     x1, #0x0
        mov     x0, x21
        bl      L10a8
        mov     x1, x19
        mov     x2, #0x20
        mov     x0, x21
        bl      L10c8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10f0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1170
        mov     x0, #0x0
L2ea4:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L2ea4
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xd9
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e80
L2edc:
        cmp     w19, #0x88
        b.ne    L2f78
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1170
        mov     w0, #0x0
L2ef8:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L2edc
        ubfiz   x0, x0, #2, #8
        ldr     w1, [x22, x0]
        str     w1, [x22, x23, lsl #2]
        add     x23, x23, #0x1
        ldr     x1, [sp, #72]
        ubfiz   x2, x1, #1, #1
        lsr     x1, x1, #1
        sub     w2, w24, w2
        str     w2, [x22, x0]
        str     x1, [sp, #72]
        cmp     x23, #0x100
        b.ne    L2edc
        mov     x0, x21
        bl      L1190
        mov     x0, x20
        mov     x1, #0x88
        bl      L2a8c
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L2a8c
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2f80
        bl      L0e70
L2f78:
        mov     w0, w19
        b       L2ef8
L2f80:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa44_polyeta_pack (0x13c bytes)
L2f94:
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x30, [sp, #-32]!
        mov     x8, x0
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x14, x1, #0x400
        mov     w6, #0x2
L2fb8:
        ldp     w5, w2, [x1, #8]
        add     x8, x8, #0x3
        ldp     w30, w17, [x1, #16]
        sub     w2, w6, w2
        ldp     w7, w3, [x1]
        sub     w30, w6, w30
        ldp     w4, w18, [x1, #24]
        sub     w5, w6, w5
        sub     w17, w6, w17
        sub     w3, w6, w3
        sub     w4, w6, w4
        sub     w18, w6, w18
        sub     w7, w6, w7
        and     w16, w2, #0xff
        and     w12, w30, #0xff
        ubfiz   w2, w2, #1, #8
        ubfiz   w30, w30, #4, #8
        ubfiz   w19, w5, #6, #8
        orr     w2, w2, w30
        and     w15, w3, #0xff
        ubfiz   w30, w17, #7, #8
        and     w13, w5, #0xff
        and     w10, w4, #0xff
        and     w9, w18, #0xff
        ubfiz   w3, w3, #3, #8
        ubfx    x5, x5, #2, #6
        ubfiz   w4, w4, #2, #8
        ubfiz   w18, w18, #5, #8
        sxtb    w7, w7
        and     w11, w17, #0xff
        orr     w3, w3, w19
        orr     w5, w5, w30
        orr     w4, w4, w18
        ubfx    x17, x17, #1, #7
        orr     w3, w7, w3
        orr     w2, w2, w5
        orr     w4, w4, w17
        and     w3, w3, #0xff
        and     w2, w2, #0xff
        and     w4, w4, #0xff
        add     x1, x1, #0x20
        sturb   w3, [x8, #-3]
        sturb   w2, [x8, #-2]
        sturb   w4, [x8, #-1]
        cmp     x14, x1
        b.ne    L2fb8
        strb    w3, [x0, #93]
        mov     x1, #0x8
        strb    w2, [x0, #94]
        strb    w4, [x0, #95]
        add     x0, sp, #0x10
        strb    w7, [sp, #16]
        strb    w15, [sp, #17]
        strb    w13, [sp, #18]
        strb    w16, [sp, #19]
        strb    w12, [sp, #20]
        strb    w11, [sp, #21]
        strb    w10, [sp, #22]
        strb    w9, [sp, #23]
        bl      L2a8c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L30c8
        bl      L0e70
L30c8:
        ldp     x19, x30, [sp], #32
        ret

// mldsa44_polyeta_unpack (0xc0 bytes)
L30d0:
        add     x11, x0, #0x400
        mov     w2, #0x2
L30d8:
        ldrb    w9, [x1]
        add     x1, x1, #0x3
        and     w9, w9, #0x7
        str     w9, [x0]
        sub     w9, w2, w9
        ldurb   w8, [x1, #-3]
        ubfx    x8, x8, #3, #3
        str     w8, [x0, #4]
        sub     w8, w2, w8
        ldurb   w3, [x1, #-2]
        ldurb   w4, [x1, #-3]
        lsl     w3, w3, #2
        orr     w4, w3, w4, lsr #6
        and     w4, w4, #0x7
        str     w4, [x0, #8]
        sub     w4, w2, w4
        ldurb   w7, [x1, #-2]
        ubfx    x7, x7, #1, #3
        str     w7, [x0, #12]
        sub     w7, w2, w7
        ldurb   w6, [x1, #-2]
        ubfx    x6, x6, #4, #3
        str     w6, [x0, #16]
        sub     w6, w2, w6
        ldurb   w5, [x1, #-1]
        ldurb   w3, [x1, #-2]
        lsl     w5, w5, #1
        orr     w3, w5, w3, lsr #7
        and     w3, w3, #0x7
        str     w3, [x0, #20]
        sub     w3, w2, w3
        ldurb   w5, [x1, #-1]
        ubfx    x5, x5, #2, #3
        str     w5, [x0, #24]
        sub     w5, w2, w5
        ldurb   w10, [x1, #-1]
        stp     w9, w8, [x0]
        stp     w4, w7, [x0, #8]
        stp     w6, w3, [x0, #16]
        sub     w3, w2, w10, lsr #5
        add     x0, x0, #0x20
        stur    w5, [x0, #-8]
        stur    w3, [x0, #-4]
        cmp     x0, x11
        b.ne    L30d8
        ret

// mldsa44_polyz_pack (0x108 bytes)
L3190:
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x15, x0, #0x240
        mov     w10, #0x20000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        mov     x2, x0
L31b4:
        ldp     w3, w9, [x1]
        add     x2, x2, #0x9
        ldp     w8, w7, [x1, #8]
        sub     w3, w10, w3
        sub     w9, w10, w9
        sturb   w3, [x2, #-9]
        sub     w8, w10, w8
        sub     w7, w10, w7
        lsr     w4, w3, #8
        ubfiz   w6, w9, #2, #6
        ubfiz   w5, w8, #4, #4
        sturb   w4, [x2, #-8]
        ubfiz   w4, w7, #6, #2
        orr     w6, w6, w3, lsr #16
        orr     w5, w5, w9, lsr #14
        orr     w4, w4, w8, lsr #12
        and     w6, w6, #0xff
        ubfx    x14, x9, #6, #8
        and     w5, w5, #0xff
        ubfx    x13, x8, #4, #8
        and     w4, w4, #0xff
        ubfx    x12, x7, #2, #8
        ubfx    x11, x7, #10, #8
        sturb   w6, [x2, #-7]
        sturb   w14, [x2, #-6]
        add     x1, x1, #0x10
        sturb   w5, [x2, #-5]
        sturb   w13, [x2, #-4]
        sturb   w4, [x2, #-3]
        sturb   w12, [x2, #-2]
        sturb   w11, [x2, #-1]
        cmp     x15, x2
        b.ne    L31b4
        add     x1, x0, #0x200
        stp     w3, w9, [sp, #24]
        stp     w8, w7, [sp, #32]
        sturh   w3, [x1, #55]
        mov     x1, #0x10
        strb    w6, [x0, #569]
        strb    w14, [x0, #570]
        strb    w5, [x0, #571]
        strb    w13, [x0, #572]
        strb    w4, [x0, #573]
        strb    w12, [x0, #574]
        strb    w11, [x0, #575]
        add     x0, sp, #0x18
        bl      L2a8c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3290
        bl      L0e70
L3290:
        ldr     x30, [sp], #48
        ret

// mldsa44_polyz_unpack (0xcc bytes)
L3298:
        add     x8, x0, #0x400
        mov     w6, #0x20000
L32a0:
        ldrb    w3, [x1]
        add     x1, x1, #0x9
        str     w3, [x0]
        ldurb   w2, [x1, #-8]
        orr     w2, w3, w2, lsl #8
        str     w2, [x0]
        ldurb   w4, [x1, #-7]
        orr     w4, w2, w4, lsl #16
        and     w4, w4, #0x3ffff
        str     w4, [x0]
        sub     w4, w6, w4
        ldurb   w3, [x1, #-7]
        lsr     w3, w3, #2
        str     w3, [x0, #4]
        ldurb   w2, [x1, #-6]
        orr     w2, w3, w2, lsl #6
        str     w2, [x0, #4]
        ldurb   w3, [x1, #-5]
        orr     w3, w2, w3, lsl #14
        and     w3, w3, #0x3ffff
        str     w3, [x0, #4]
        sub     w3, w6, w3
        ldurb   w2, [x1, #-5]
        lsr     w2, w2, #4
        str     w2, [x0, #8]
        ldurb   w5, [x1, #-4]
        orr     w5, w2, w5, lsl #4
        str     w5, [x0, #8]
        ldurb   w2, [x1, #-3]
        orr     w2, w5, w2, lsl #12
        and     w2, w2, #0x3ffff
        str     w2, [x0, #8]
        sub     w2, w6, w2
        ldurb   w5, [x1, #-3]
        lsr     w5, w5, #6
        str     w5, [x0, #12]
        ldurb   w7, [x1, #-2]
        orr     w7, w5, w7, lsl #2
        str     w7, [x0, #12]
        ldurb   w5, [x1, #-1]
        stp     w4, w3, [x0]
        add     x0, x0, #0x10
        stur    w2, [x0, #-8]
        orr     w5, w7, w5, lsl #10
        sub     w2, w6, w5
        stur    w2, [x0, #-4]
        cmp     x0, x8
        b.ne    L32a0
        ret

// mldsa44_poly_uniform_gamma1_4x (0x17c bytes)
L3364:
        mov     x12, #0x1020
        sub     sp, sp, x12
        stp     x19, x20, [sp]
        add     x19, sp, #0x7f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x20, x19, #0xb00
        add     x21, x19, #0xb60
        stp     x23, x24, [sp, #32]
        mov     x24, x1
        mov     x23, x2
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        add     x26, x19, #0xbc0
        stp     x27, x28, [sp, #64]
        add     x27, x19, #0xc20
        add     x28, sp, #0xcf8
        str     x30, [sp, #80]
        mov     x22, x3
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q0, q1, [x4, #32]
        ldr     x1, [x0]
        str     x1, [sp, #4120]
        mov     x1, #0x0
        ldp     q2, q3, [x4]
        stp     q0, q1, [x21, #32]
        stp     q0, q1, [x26, #32]
        stp     q0, q1, [x20, #32]
        stp     q2, q3, [x21]
        stp     q2, q3, [x26]
        stp     q2, q3, [x27]
        stp     q2, q3, [x20]
        stp     q0, q1, [x27, #32]
        ldrh    w0, [sp, #4128]
        strh    w5, [x19, #2880]
        strh    w6, [x19, #2976]
        strh    w7, [x19, #3072]
        strh    w0, [x19, #3168]
        mov     x0, x28
        bl      L1568
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1484
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14e8
        mov     x1, x19
        mov     x0, x25
        bl      L3298
        mov     x1, x27
        mov     x0, x24
        bl      L3298
        mov     x1, x26
        mov     x0, x23
        bl      L3298
        mov     x1, x21
        mov     x0, x22
        bl      L3298
        mov     x0, x28
        bl      L156c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L2a8c
        mov     x0, x20
        mov     x1, #0x180
        bl      L2a8c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L34bc
        bl      L0e70
L34bc:
        ldp     x19, x20, [sp]
        mov     x12, #0x1020
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa44_polyvecl_uniform_gamma1 (0x40 bytes)
L34e0:
        sub     sp, sp, #0x20
        sxth    w3, w2
        add     w7, w3, #0x2
        add     w6, w3, #0x1
        add     w3, w3, #0x3
        mov     w5, w2
        strh    w3, [sp]
        mov     x4, x1
        add     x3, x0, #0xc00
        add     x2, x0, #0x800
        add     x1, x0, #0x400
        str     x30, [sp, #16]
        bl      L3364
        ldr     x30, [sp, #16]
        add     sp, sp, #0x20
        ret

// mldsa44_polyvecl_ntt (0x28 bytes)

// mldsa44_polyvecl_ntt.localalias (0x28 bytes)
L3520:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L20d0
        add     x0, x19, #0x400
        bl      L20d0
        add     x0, x19, #0x800
        bl      L20d0
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L20d0

// mldsa44_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L3548:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L3558:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L3564:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x4
        b.ne    L3564
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L3558
        ret

// mldsa44_polyvecl_chknorm (0x4c bytes)
L35a0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     w20, #0x0
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x0, #0x1, lsl #12
        str     x30, [sp, #32]
L35bc:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L28c8
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L35bc
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyveck_caddq (0x28 bytes)
L35ec:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L202c
        add     x0, x19, #0x400
        bl      L202c
        add     x0, x19, #0x800
        bl      L202c
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L202c

// mldsa44_polyveck_ntt (0x4 bytes)
L3614:
        b       L3520

// mldsa44_polyveck_invntt_tomont (0x28 bytes)
L3618:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L2178
        add     x0, x19, #0x400
        bl      L2178
        add     x0, x19, #0x800
        bl      L2178
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L2178

// mldsa44_polyveck_unpack_eta_chknorm (0x5c bytes)
L3640:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x180
L3660:
        mov     x1, x19
        mov     x0, x20
        bl      L30d0
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L28c8
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L3660
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyveck_decompose_pack_w1 (0x54 bytes)
L369c:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, #0x1, lsl #12
        str     x30, [sp, #32]
L36b8:
        mov     x1, x19
        mov     x0, x21
        bl      L2b30
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2914
        add     x20, x20, #0xc0
        cmp     x19, x22
        b.ne    L36b8
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyvecl_unpack_eta (0x3c bytes)

// mldsa44_polyvecl_unpack_eta.localalias (0x3c bytes)
L36f0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x1, lsl #12
L3704:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L30d0
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L3704
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa44_polyvecl_unpack_z (0x3c bytes)
L372c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x1, lsl #12
L3740:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L3298
        add     x20, x20, #0x240
        cmp     x19, x21
        b.ne    L3740
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa44_polyveck_unpack_eta (0x4 bytes)
L3768:
        b       L36f0

// mldsa44_polyvec_matrix_expand_eager (0x120 bytes)
L376c:
        stp     x19, x20, [sp, #-352]!
        mov     x20, x0
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x19, sp, #0x5f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        stp     x25, x30, [sp, #48]
        ldr     x2, [x0]
        str     x2, [sp, #344]
        mov     x2, #0x0
        mov     x0, x19
L37a0:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L37a0
        mov     w5, #0x0
        mov     w22, #0x1000
        mov     x23, #0xc00
        mov     x24, #0x800
        mov     x25, #0x400
L37cc:
        mov     x1, x19
        mov     w0, w5
        add     w21, w5, #0x4
L37d8:
        and     w2, w0, #0x3
        strb    w2, [x1, #32]
        lsr     w2, w0, #2
        add     w0, w0, #0x1
        strb    w2, [x1, #33]
        add     x1, x1, #0x40
        cmp     w21, w0
        b.ne    L37d8
        add     w3, w5, #0x3
        add     w2, w5, #0x2
        add     w1, w5, #0x1
        lsr     w5, w5, #2
        lsr     w3, w3, #2
        lsr     w2, w2, #2
        lsr     w1, w1, #2
        mov     x4, x19
        add     x0, x20, x5, lsl #12
        umaddl  x3, w3, w22, x23
        umaddl  x2, w2, w22, x24
        umaddl  x1, w1, w22, x25
        add     x3, x20, x3
        add     x2, x20, x2
        add     x1, x20, x1
        bl      L23b8
        cmp     w21, #0x10
        b.eq    L3848
        mov     w5, w21
        b       L37cc
L3848:
        mov     x0, x19
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e80
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #344]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3878
        bl      L0e70
L3878:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #352
        ret

// mldsa44_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L388c:
        ubfiz   x3, x3, #12, #32
        add     x1, x1, x3
        b       L3548

// mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L3898:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x3
        mov     x19, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x1
        mov     x1, x2
        mov     x2, #0x1000
        mov     x21, x0
        mov     x0, x3
        str     x30, [sp, #32]
        bl      L0e50
        mov     x0, x20
        bl      L3520
L38cc:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L388c
        cmp     x19, #0x4
        b.ne    L38cc
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L3618

// mld_ct_memcmp (0x54 bytes)
L3900:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L390c:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L3934
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L3934:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L390c

// mld_zeroize (0x1c bytes)
L3954:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t144 (0x158 bytes)
L3970:
        mov     x12, #0x4890
        sub     sp, sp, x12
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x3
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        mov     x3, #0x4400
        stp     x21, x22, [sp, #16]
        add     x20, sp, #0x8f
        and     x20, x20, #0xffffffffffffffe0
        stp     x25, x26, [sp, #48]
        mov     x22, x1
        add     x19, x20, x3
        stp     x27, x28, [sp, #64]
        mov     x1, x4
        add     x21, x20, #0x4, lsl #12
        str     x30, [sp, #80]
        mov     x25, #0x0
        str     x2, [sp, #104]
        mov     x28, #0x60
        mov     x27, #0x140
        mov     x26, #0x1a0
        ldr     x2, [x0]
        str     x2, [sp, #18568]
        mov     x2, #0x0
        mov     x0, x20
        bl      L376c
L39e4:
        ldr     x2, [sp, #104]
        mov     w3, w25
        mov     x1, x20
        mov     x0, x19
        bl      L388c
        mov     x0, x19
        bl      L2178
        madd    x1, x25, x28, x24
        mov     x0, x21
        bl      L30d0
        mov     x1, x21
        mov     x0, x19
        bl      L2068
        mov     x0, x19
        bl      L2000
        mov     x0, x19
        bl      L202c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x21
        bl      L2294
        madd    x0, x25, x27, x23
        mov     x1, x21
        bl      L2594
        madd    x0, x25, x26, x22
        mov     x1, x19
        add     x25, x25, #0x1
        bl      L2660
        cmp     x25, #0x4
        b.ne    L39e4
        mov     x0, x21
        mov     x1, #0x400
        bl      L3954
        mov     x0, x19
        mov     x1, #0x400
        bl      L3954
        mov     x0, x20
        mov     x1, #0x4000
        bl      L3954
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #18568]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3aa0
        bl      L0e70
L3aa0:
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x4890
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mld_H44 (0xf0 bytes)
L3ac8:
        stp     x19, x20, [sp, #-304]!
        mov     x20, x7
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x19, sp, #0x58
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        stp     x25, x26, [sp, #48]
        mov     x21, x5
        mov     x26, x2
        stp     x27, x30, [sp, #64]
        mov     x25, x4
        mov     x27, x3
        ldr     x1, [x0]
        str     x1, [sp, #296]
        mov     x1, #0x0
        mov     x24, x6
        mov     x0, x19
        bl      L10a8
        mov     x2, x27
        mov     x1, x26
        mov     x0, x19
        bl      L10c8
        cbz     x21, L3b40
        mov     x2, x21
        mov     x1, x25
        mov     x0, x19
        bl      L10c8
L3b40:
        cbz     x20, L3b54
        mov     x2, x20
        mov     x1, x24
        mov     x0, x19
        bl      L10c8
L3b54:
        mov     x0, x19
        bl      L10f0
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L1170
        mov     x0, x19
        bl      L1190
        mov     x0, x19
        mov     x1, #0xd0
        bl      L3954
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3ba0
        bl      L0e70
L3ba0:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa44_keypair_internal (0x234 bytes)
L3bb8:
        mov     x12, #0x1180
        sub     sp, sp, x12
        mov     x3, #0x22
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x8f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        mov     x20, x1
        mov     x22, x0
        stp     x23, x24, [sp, #48]
        mov     x1, #0x10c0
        add     x24, x19, x1
        stp     x25, x26, [sp, #64]
        add     x21, x19, #0x1, lsl #12
        add     x23, x19, #0xc00
        stp     x27, x28, [sp, #80]
        add     x25, x19, #0x800
        add     x28, x21, #0x20
        str     x30, [sp, #96]
        add     x26, x19, #0x400
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x27, x20, #0x200
        ldp     q0, q1, [x2]
        ldr     x1, [x0]
        str     x1, [sp, #4472]
        mov     x1, #0x0
        mov     w0, #0x404
        mov     x2, x24
        mov     x1, #0x80
        stp     q0, q1, [x24]
        strh    w0, [x19, #4320]
        mov     x0, x21
        bl      L1194
        mov     x3, x23
        mov     x2, x25
        mov     x4, x28
        mov     w0, #0x7
        strb    w0, [sp]
        mov     w7, #0x6
        mov     w6, #0x5
        mov     w5, #0x4
        mov     x1, x26
        mov     x0, x19
        bl      L2c08
        mov     x1, x19
        mov     x0, x27
        bl      L2f94
        mov     x1, x26
        add     x0, x20, #0x260
        bl      L2f94
        mov     x1, x25
        add     x0, x20, #0x2c0
        bl      L2f94
        mov     x1, x23
        add     x0, x20, #0x320
        bl      L2f94
        mov     x3, x23
        mov     x2, x25
        mov     x4, x28
        mov     w0, #0x3
        strb    w0, [sp]
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x1, x26
        mov     x0, x19
        bl      L2c08
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L2f94
        mov     x1, x26
        add     x0, x20, #0xe0
        bl      L2f94
        mov     x1, x25
        add     x0, x20, #0x140
        bl      L2f94
        mov     x1, x23
        add     x0, x20, #0x1a0
        bl      L2f94
        mov     x0, x19
        bl      L3520
        ldp     q0, q1, [x21]
        mov     x2, x19
        mov     x4, x21
        mov     x3, x27
        add     x1, x20, #0x380
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L3970
        mov     x2, #0x1080
        mov     w23, w0
        add     x25, x19, x2
        cbnz    w0, L3d58
        mov     x2, x22
        mov     x0, x25
        mov     x3, #0x520
        mov     x1, #0x40
        bl      L1194
        add     x3, x21, #0x60
        mov     x2, x25
        mov     x1, x21
        mov     x0, x20
        bl      L1cf0
L3d58:
        mov     x0, x19
        mov     x1, #0x1000
        bl      L3954
        mov     x0, x25
        mov     x1, #0x40
        bl      L3954
        mov     x0, x24
        mov     x1, #0x22
        bl      L3954
        mov     x0, x21
        mov     x1, #0x80
        bl      L3954
        cbz     w23, L3da4
        mov     x0, x22
        mov     x1, #0x520
        bl      L3954
        mov     x0, x20
        mov     x1, #0xa00
        bl      L3954
L3da4:
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3dc4
        bl      L0e70
L3dc4:
        ldp     x19, x20, [sp, #16]
        mov     w0, w23
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x1180
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret

// mldsa44_keypair (0x94 bytes)
L3dec:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #88]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e60
        cbnz    w0, L3e68
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L3bb8
        mov     w20, w0
L3e3c:
        mov     x0, x19
        mov     x1, #0x20
        bl      L3954
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3e70
        bl      L0e70
L3e68:
        mov     w20, #0xfffffffd
        b       L3e3c
L3e70:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa44_signature_internal (0x438 bytes)
L3e80:
        mov     x12, #0xace0
        sub     sp, sp, x12
        mov     x8, #0xab00
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x4
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0xbf
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x21, x19, x8
        stp     x25, x26, [sp, #48]
        mov     x26, x1
        mov     x25, x2
        stp     x27, x28, [sp, #64]
        mov     w27, w7
        mov     x7, #0x8040
        str     x30, [sp, #80]
        add     x1, sp, x7
        add     x28, x21, #0x20
        mov     x22, x3
        ldr     x2, [x0]
        str     x2, [x1, #11416]
        mov     x2, #0x0
        add     x0, x19, #0x7, lsl #12
        str     x0, [sp, #128]
        add     x0, x19, #0x9, lsl #12
        str     x0, [sp, #136]
        add     x0, x19, #0x8, lsl #12
        mov     x3, x0
        mov     x20, x5
        add     x4, x19, #0x9, lsl #12
        add     x5, x19, #0x7, lsl #12
        add     x2, x21, #0x60
        mov     x1, x28
        str     x0, [sp, #144]
        mov     x0, x21
        bl      L1d18
        add     x0, x21, #0x80
        cbnz    w27, L4188
        mov     x3, #0x40
        mov     x7, x25
        mov     x6, x26
        mov     x5, x24
        mov     x4, x22
        mov     x2, x28
        mov     x1, x3
        bl      L3ac8
L3f48:
        mov     x5, #0x20
        mov     x4, x20
        mov     x3, x5
        add     x6, x21, #0x80
        add     x2, x21, #0x60
        mov     x7, #0x40
        add     x0, x21, #0xc0
        mov     x1, x7
        bl      L3ac8
        mov     x0, x19
        mov     x1, x21
        bl      L376c
        str     wzr, [sp, #124]
        mov     x4, #0xa800
        add     x0, x19, x4
        mov     x5, #0xac00
        str     x0, [sp, #104]
        add     x0, x19, x5
        str     x0, [sp, #112]
L3f94:
        ldrh    w2, [sp, #124]
        add     x27, x19, #0x6, lsl #12
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0x5, lsl #12
        add     x24, x19, #0x4, lsl #12
        mov     w26, #0xffb2
        add     x22, x19, #0xa, lsl #12
        bl      L34e0
        mov     x28, #0x0
        mov     x3, x20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x24
        bl      L3898
        movk    w26, #0x1, lsl #16
        mov     x0, x24
        bl      L35ec
        ldr     x0, [sp, #104]
        mov     x3, #0xa400
        mov     x2, x20
        add     x25, x19, x3
        mov     x1, x24
        bl      L369c
        ldp     x4, x0, [sp, #104]
        add     x2, x21, #0x80
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x300
        mov     x3, #0x40
        mov     x1, #0x20
        bl      L3ac8
        ldr     x1, [sp, #112]
        mov     x0, x25
        bl      L2e34
        mov     x0, x25
        bl      L20d0
L4028:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e50
        mov     x1, x25
        mov     x0, x22
        bl      L2258
        mov     x0, x22
        bl      L2178
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x27, x3
        bl      L0e50
        mov     x1, x20
        mov     x0, x22
        bl      L2068
        mov     x0, x22
        bl      L2000
        mov     w1, w26
        mov     x0, x22
        bl      L28c8
        cbnz    w0, L419c
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L1eb4
        cmp     x28, #0x4
        b.ne    L4028
        mov     x26, #0x0
L40b0:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x24, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e50
        mov     x1, x25
        mov     x0, x20
        bl      L2258
        mov     x0, x20
        bl      L2178
        mov     x1, x20
        mov     x0, x28
        bl      L208c
        mov     x0, x28
        bl      L2000
        mov     w1, #0x73b2
        mov     x0, x28
        movk    w1, #0x1, lsl #16
        bl      L28c8
        cbnz    w0, L419c
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e50
        mov     x1, x25
        mov     x0, x20
        bl      L2258
        mov     x0, x20
        bl      L2178
        mov     x0, x20
        bl      L2000
        mov     w1, #0x7400
        mov     x0, x20
        movk    w1, #0x1, lsl #16
        bl      L28c8
        cbnz    w0, L419c
        mov     x1, x20
        mov     x0, x28
        add     x26, x26, #0x400
        bl      L2068
        cmp     x26, #0x1, lsl #12
        b.ne    L40b0
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L1dbc
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x24
        mov     x0, x23
        bl      L1dc8
        mov     w26, w0
        b       L41a0
L4188:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L3f48
L419c:
        mov     w26, #0xffffffff
L41a0:
        mov     x0, x22
        mov     x1, #0x400
        bl      L3954
        mov     x0, x25
        mov     x1, #0x400
        bl      L3954
        mov     x0, x24
        mov     x1, #0x1000
        bl      L3954
        ldr     x0, [sp, #104]
        mov     x1, #0x300
        bl      L3954
        mov     x0, x20
        mov     x1, #0x1000
        bl      L3954
        mov     x0, x27
        mov     x1, #0x1000
        bl      L3954
        ldr     x0, [sp, #112]
        mov     x1, #0x20
        bl      L3954
        cbz     w26, L422c
        cmn     w26, #0x1
        b.ne    L4220
        ldr     w0, [sp, #124]
        add     w0, w0, #0x4
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfff8
        cmp     w1, w0, uxth
        b.ne    L3f94
        mov     w26, #0xfffffffc
L4220:
        mov     x0, x23
        mov     x1, #0x974
        bl      L3954
L422c:
        ldr     x0, [sp, #128]
        mov     x1, #0x1000
        bl      L3954
        ldr     x0, [sp, #144]
        mov     x1, #0x1000
        bl      L3954
        ldr     x0, [sp, #136]
        mov     x1, #0x1000
        bl      L3954
        mov     x0, x19
        mov     x1, #0x4000
        bl      L3954
        mov     x0, x21
        mov     x1, #0x100
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x1, #0x8040
        add     x2, sp, x1
        ldr     x3, [x2, #11416]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L4290
        bl      L0e70
L4290:
        ldp     x19, x20, [sp]
        mov     w0, w26
        ldp     x21, x22, [sp, #16]
        mov     x12, #0xace0
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa44_signature_extmu (0xb4 bytes)
L42b8:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        mov     x22, x2
        ldr     x1, [x0]
        str     x1, [sp, #104]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e60
        cbnz    w0, L4350
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L3e80
        mov     w20, w0
L4324:
        mov     x0, x19
        mov     x1, #0x20
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4358
        bl      L0e70
L4350:
        mov     w20, #0xfffffffd
        b       L4324
L4358:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa44_verify_internal (0x300 bytes)
L436c:
        mov     x12, #0x6030
        sub     sp, sp, x12
        mov     x11, #0x5c00
        mov     x12, #0x5800
        mov     x13, #0x5400
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        stp     x19, x20, [sp]
        add     x19, sp, #0xaf
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x23, x19, x11
        add     x21, x19, x13
        stp     x25, x26, [sp, #48]
        add     x25, x19, #0x6, lsl #12
        add     x26, x19, #0x4, lsl #12
        stp     x27, x28, [sp, #64]
        mov     x28, x1
        add     x27, x19, x12
        str     x30, [sp, #80]
        add     x22, x19, #0x5, lsl #12
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x5, [sp, #96]
        ldp     q0, q1, [x24]
        stp     x2, x3, [sp, #112]
        str     x4, [sp, #128]
        str     w6, [sp, #140]
        ldr     x1, [x0]
        str     x1, [sp, #24616]
        mov     x1, #0x0
        mov     x0, x26
        add     x1, x24, #0x20
        stp     q0, q1, [x25, #-160]
        bl      L372c
        mov     w1, #0xffb2
        mov     x0, x26
        movk    w1, #0x1, lsl #16
        bl      L35a0
        mov     x14, #0x5f60
        mov     w20, w0
        add     x0, x19, x14
        str     x0, [sp, #104]
        cbnz    w20, L4594
        ldr     w6, [sp, #140]
        cbnz    w6, L462c
        ldr     x2, [sp, #96]
        mov     x0, x23
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x520
        mov     x1, #0x40
        bl      L3ac8
        ldp     x7, x4, [sp, #112]
        mov     x10, #0x5f00
        ldr     x5, [sp, #128]
        mov     x6, x28
        mov     x2, x23
        mov     x3, #0x40
        add     x0, x19, x10
        mov     x1, x3
        bl      L3ac8
        mov     x0, x23
        mov     x1, #0x40
        bl      L3954
L4478:
        mov     x0, x26
        bl      L3520
        ldr     x1, [sp, #96]
        mov     x0, x19
        mov     x28, x23
        bl      L376c
        mov     x9, #0x5f60
        add     x1, x19, x9
        mov     x0, x27
        bl      L2e34
        mov     x0, x27
        bl      L20d0
L44a8:
        mov     w3, w20
        mov     x2, x26
        mov     x1, x19
        mov     x0, x21
        bl      L388c
        ldr     x1, [sp, #96]
        mov     w2, w20
        mov     x0, x22
        bl      L1cdc
        mov     x0, x22
        bl      L20b0
        mov     x0, x22
        bl      L20d0
        mov     x1, x27
        mov     x0, x22
        bl      L2258
        mov     x1, x22
        mov     x0, x21
        bl      L208c
        mov     x0, x21
        bl      L2000
        mov     x0, x21
        bl      L2178
        mov     x0, x21
        bl      L202c
        mov     w2, w20
        mov     x1, x24
        mov     x0, x22
        bl      L1ec8
        mov     w25, w0
        cbnz    w0, L4594
        mov     x1, x22
        mov     x0, x21
        bl      L2b64
        add     w20, w20, #0x1
        mov     x0, x28
        mov     x1, x21
        bl      L2914
        add     x28, x28, #0xc0
        cmp     w20, #0x4
        b.ne    L44a8
        mov     x8, #0x5f00
        mov     x3, #0x5f40
        add     x20, x19, x3
        add     x2, x19, x8
        mov     x0, x20
        mov     x1, #0x20
        mov     x4, x23
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x300
        mov     x3, #0x40
        bl      L3ac8
        ldr     x0, [sp, #104]
        mov     x1, x20
        mov     x2, #0x20
        bl      L3900
        tst     w0, #0xff
        b.eq    L4598
L4594:
        mov     w25, #0xfffffffa
L4598:
        mov     x0, x22
        mov     x1, #0x400
        bl      L3954
        mov     x0, x21
        mov     x1, #0x400
        bl      L3954
        mov     x0, x19
        mov     x1, #0x4000
        bl      L3954
        mov     x0, x27
        mov     x1, #0x400
        bl      L3954
        mov     x0, x26
        mov     x1, #0x1000
        bl      L3954
        mov     x1, #0x20
        mov     x0, #0x5f40
        add     x0, x19, x0
        bl      L3954
        ldr     x0, [sp, #104]
        mov     x1, #0x20
        bl      L3954
        mov     x2, #0x5f00
        mov     x1, #0x40
        add     x0, x19, x2
        bl      L3954
        mov     x0, x23
        mov     x1, #0x300
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24616]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4644
        bl      L0e70
L462c:
        ldp     q0, q1, [x28]
        sub     x0, x25, #0x100
        stp     q0, q1, [x0]
        ldp     q0, q1, [x28, #32]
        stp     q0, q1, [x0, #32]
        b       L4478
L4644:
        ldp     x19, x20, [sp]
        mov     w0, w25
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x6030
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa44_verify_extmu (0x18 bytes)
L466c:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L436c

// mldsa44_prepare_domain_separation_prefix (0x138 bytes)
L4684:
        cmp     x4, #0xff
        b.hi    L47ac
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L4770
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L47b4
        .inst   0xd0000020  // adrp x0, 0xa000
        add     x0, x0, #0x278
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 46d8 <mldsa44_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L46dc:
        b.ne    L47b4
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L46fc
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e50
L46fc:
        .inst   0xd0000020  // adrp x0, 0xa000
        add     x0, x0, #0x284
        mov     x1, #0x0
L4708:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L479c
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L4738:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e50
        add     x0, x20, x19
        b       L478c
        cmp     x20, #0x20
        b       L46dc
        cmp     x20, #0x30
        b       L46dc
        cmp     x20, #0x40
        b       L46dc
L4770:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L4788
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e50
L4788:
        add     x0, x19, #0x2
L478c:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L479c:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L4708
        b       L4738
L47ac:
        mov     x0, #0x0
        ret
L47b4:
        mov     x0, #0x0
        b       L478c

// mldsa44_signature (0x100 bytes)
L47bc:
        stp     x19, x20, [sp, #-480]!
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        add     x20, sp, #0x5f
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        and     x20, x20, #0xffffffffffffffe0
        stp     x25, x30, [sp, #48]
        mov     x23, x1
        mov     x24, x2
        ldr     x1, [x0]
        str     x1, [sp, #472]
        mov     x1, #0x0
        mov     x25, x5
        mov     x0, x20
        mov     w5, #0x0
        mov     x2, #0x0
        add     x22, x20, #0x160
        bl      L4684
        cbz     x0, L4894
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e60
        cbnz    w0, L489c
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L3e80
        mov     w19, w0
        cbz     w0, L485c
L4850:
        mov     x0, x21
        mov     x1, #0x974
        bl      L3954
L485c:
        mov     x0, x22
        mov     x1, #0x20
        bl      L3954
        mov     x0, x20
        mov     x1, #0x14c
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L48a4
        bl      L0e70
L4894:
        mov     w19, #0xfffffff7
        b       L4850
L489c:
        mov     w19, #0xfffffffd
        b       L4850
L48a4:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa44_verify (0xbc bytes)
L48bc:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x5
        .inst   0xf00000c5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        mov     x21, x0
        and     x19, x19, #0xffffffffffffffe0
        ldr     x0, [x5]
        str     x0, [sp, #408]
        mov     x0, #0x0
        mov     x22, x1
        mov     x23, x2
        mov     x0, x19
        mov     w5, #0x0
        mov     x2, #0x0
        mov     x1, #0x0
        bl      L4684
        cbz     x0, L495c
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L436c
        mov     w20, w0
L4930:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4964
        bl      L0e70
L495c:
        mov     w20, #0xfffffff7
        b       L4930
L4964:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa44_signature_pre_hash_internal (0xc8 bytes)
L4978:
        stp     x19, x20, [sp, #-416]!
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     x22, x6
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #32]
        add     x20, sp, #0x4f
        ldr     x6, [x0]
        str     x6, [sp, #408]
        mov     x6, #0x0
        and     x20, x20, #0xffffffffffffffe0
        cbnz    w7, L49c0
L49ac:
        mov     w19, #0xfffffff7
L49b0:
        mov     x0, x21
        mov     x1, #0x974
        bl      L3954
        b       L4a00
L49c0:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L4684
        mov     x2, x0
        cbz     x0, L49ac
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L3e80
        mov     w19, w0
        cbnz    w0, L49b0
L4a00:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4a2c
        bl      L0e70
L4a2c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa44_signature_pre_hash_shake256 (0xc0 bytes)
L4a40:
        stp     x19, x20, [sp, #-160]!
        mov     x20, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x3
        str     x30, [sp, #48]
        mov     x22, x4
        mov     x23, x5
        mov     x24, x6
        ldr     x3, [x0]
        str     x3, [sp, #152]
        mov     x3, #0x0
        mov     x0, x19
        mov     x3, x2
        mov     x2, x1
        mov     x1, #0x40
        bl      L1194
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L4978
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4ae8
        bl      L0e70
L4ae8:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa44_verify_pre_hash_internal (0xa8 bytes)
L4b00:
        stp     x19, x20, [sp, #-400]!
        mov     x20, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        ldr     x6, [x0]
        str     x6, [sp, #392]
        mov     x6, #0x0
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        cbnz    w5, L4b64
L4b34:
        mov     w20, #0xfffffff7
L4b38:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4b98
        bl      L0e70
L4b64:
        mov     x0, x19
        bl      L4684
        mov     x2, x0
        cbz     x0, L4b34
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L436c
        mov     w20, w0
        b       L4b38
L4b98:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa44_verify_pre_hash_shake256 (0xb0 bytes)
L4ba8:
        stp     x19, x20, [sp, #-144]!
        mov     x20, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x3
        ldr     x3, [x0]
        str     x3, [sp, #136]
        mov     x3, #0x0
        mov     x22, x4
        mov     x3, x2
        mov     x23, x5
        mov     x2, x1
        mov     x0, x19
        mov     x1, #0x40
        bl      L1194
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L4b00
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4c44
        bl      L0e70
L4c44:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa44_pk_from_sk (0x208 bytes)
L4c58:
        mov     x12, #0x1bd0
        sub     sp, sp, x12
        mov     x4, #0x1c00
        mov     x3, #0x1ac0
        mov     x2, #0x1b20
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x25, x26, [sp, #48]
        mov     x25, x1
        stp     x19, x20, [sp]
        add     x19, sp, #0x8f
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x23, x1, #0x200
        mov     x1, #0x1680
        stp     x27, x28, [sp, #64]
        add     x28, x19, x1
        add     x27, x19, x3
        str     x30, [sp, #80]
        add     x26, x19, x2
        add     x24, x19, #0x1, lsl #12
        ldp     q0, q1, [x25]
        ldr     x1, [x0]
        str     x1, [sp, #7112]
        mov     x1, #0x0
        add     x0, x19, x4
        add     x1, x25, #0x40
        sub     x22, x0, #0xe0
        stp     q0, q1, [x22]
        ldp     q0, q1, [x25, #32]
        stp     q0, q1, [x0, #-256]
        sub     x0, x0, #0x140
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x1, #32]
        add     x1, x25, #0x80
        stp     q0, q1, [x0, #32]
        mov     x0, x19
        bl      L36f0
        mov     w1, #0x3
        mov     x0, x19
        bl      L35a0
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x3
        mov     x0, x23
        bl      L3640
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L3520
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L3970
        mov     x5, #0x1a80
        mov     w22, w0
        add     x23, x19, x5
        cbnz    w0, L4db4
        add     x1, x25, #0x380
        mov     x0, x24
        mov     x2, #0x680
        bl      L3900
        and     w4, w0, #0xff
        mov     x3, #0x520
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1194
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L3900
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L4dc0
        mov     w22, #0xfffffff9
L4db4:
        mov     x0, x21
        mov     x1, #0x520
        bl      L3954
L4dc0:
        mov     x0, x24
        mov     x1, #0x680
        bl      L3954
        mov     x0, x28
        mov     x1, #0x400
        bl      L3954
        mov     x0, x19
        mov     x1, #0x1000
        bl      L3954
        mov     x1, #0x20
        mov     x0, #0x1b00
        add     x0, x19, x0
        bl      L3954
        mov     x0, x23
        mov     x1, #0x40
        bl      L3954
        mov     x0, x27
        mov     x1, #0x40
        bl      L3954
        mov     x0, x26
        mov     x1, #0x20
        bl      L3954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7112]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4e38
        bl      L0e70
L4e38:
        ldp     x19, x20, [sp]
        mov     w0, w22
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1bd0
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa65_unpack_pk_t1 (0x14 bytes)
L4e60:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25f0

// mldsa65_pack_sk_rho_key_tr (0x28 bytes)
L4e74:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x3]
        stp     q0, q1, [x0, #32]
        add     x0, x0, #0x40
        ldp     q0, q1, [x2]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x2, #32]
        stp     q0, q1, [x0, #32]
        ret

// mldsa65_unpack_sk (0xa4 bytes)
L4e9c:
        ldp     q0, q1, [x6]
        stp     x19, x20, [sp, #-48]!
        mov     x19, x6
        stp     x21, x22, [sp, #16]
        mov     x20, x3
        mov     x21, x5
        str     x30, [sp, #32]
        mov     x22, x4
        stp     q0, q1, [x0]
        add     x0, x6, #0x40
        ldp     q0, q1, [x6, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x0]
        stp     q0, q1, [x1]
        ldp     q0, q1, [x0, #32]
        mov     x0, x4
        stp     q0, q1, [x1, #32]
        add     x1, x6, #0x80
        bl      L5d1c
        mov     x0, x22
        mov     x22, x20
        bl      L5af0
        add     x1, x19, #0x300
        mov     x0, x21
        bl      L5d9c
        mov     x0, x21
        add     x21, x19, #0x600
        add     x19, x19, #0xfc0
        bl      L5c00
L4f10:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L2774
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L4f10
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L5c00

// mldsa65_pack_sig_c (0x14 bytes)
L4f40:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldr     q0, [x1, #32]
        str     q0, [x0, #32]
        ret

// mldsa65_pack_sig_h (0xe0 bytes)
L4f54:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-96]!
        mov     x19, #0x0
        stp     x21, x22, [sp, #16]
        add     x21, x0, #0xcb0
        mov     x22, x0
        stp     x23, x24, [sp, #32]
        mov     x24, x1
        mov     x23, x3
        stp     x25, x26, [sp, #48]
        mov     x25, x2
        mov     w20, #0x0
        stp     x27, x28, [sp, #64]
        mov     w28, #0x100
        mov     w26, #0x3ff00
        str     x30, [sp, #80]
        mov     w27, #0x7fe00
        movk    w28, #0xfffc, lsl #16
        str     q0, [x21, #32]
        stp     q0, q0, [x21]
        stur    q0, [x21, #45]
L4fa8:
        add     x1, x25, x19, lsl #7
        mov     x0, x23
        bl      L29f4
        add     x1, x24, x19, lsl #10
        mov     x4, #0x0
L4fbc:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w2, [x23, x4, lsl #2]
        add     w3, w0, w26
        cmp     w3, w27
        b.hi    L4fdc
        cmp     w2, #0x0
        ccmp    w0, w28, #0x0, ne
        b.ne    L4fec
L4fdc:
        cmp     w20, #0x37
        b.eq    L502c
        strb    w4, [x21, w20, uxtw]
        add     w20, w20, #0x1
L4fec:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L4fbc
        add     x0, x22, #0xce7
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x6
        b.ne    L4fa8
        mov     w0, #0x0
L5010:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L502c:
        mov     w0, #0xffffffff
        b       L5010

// mldsa65_pack_sig_z (0x14 bytes)
L5034:
        mov     w3, #0x280
        mul     w2, w2, w3
        add     x2, x2, #0x30
        add     x0, x0, x2
        b       L5714

// mldsa65_sig_unpack_hints (0xdc bytes)
L5048:
        stp     x19, x20, [sp, #-48]!
        mov     x3, x0
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, #0xcb0
        cbz     w2, L5098
        add     w0, w2, #0x36
        ldrb    w22, [x23, x0]
L5070:
        add     w0, w21, #0x37
        ldrb    w19, [x23, x0]
        cmp     w19, #0x37
        ccmp    w22, w19, #0x2, ls
        b.ls    L50a0
L5084:
        mov     w0, #0xffffffff
L5088:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L5098:
        mov     w22, #0x0
        b       L5070
L50a0:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        add     x2, x20, w22, uxtb
        mov     x3, x0
        mov     w1, w22
        mov     w4, #0x1
L50c0:
        cmp     w1, w19
        b.cc    L50e4
        cmp     w21, #0x5
        b.ne    L50dc
        add     x20, x20, #0xcaf
L50d4:
        cmp     w19, #0x37
        b.ne    L5114
L50dc:
        mov     w0, #0x0
        b       L5088
L50e4:
        cmp     w1, w22
        b.ls    L5100
        sub     w0, w1, #0x1
        ldrb    w5, [x2, #3248]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L5084
L5100:
        ldrb    w0, [x2, #3248]
        add     w1, w1, #0x1
        add     x2, x2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L50c0
L5114:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L50d4
        b       L5084

// mld_decompose65 (0x4c bytes)
L5124:
        add     w3, w2, #0x7f
        asr     w3, w3, #7
        add     w3, w3, w3, lsl #10
        add     w3, w3, #0x200, lsl #12
        ubfx    x3, x3, #22, #4
        str     w3, [x1]
        mov     w1, #0x3ff000
        sub     w3, w3, w3, lsl #10
        add     w2, w2, w3, lsl #9
        sub     w1, w1, w2
        sxtw    x1, w1
        asr     x1, x1, #31
        mov     w3, #0xff801fff
        add     w3, w2, w3
        eor     w3, w3, w2
        and     w1, w3, w1
        eor     w1, w1, w2
        str     w1, [x0]
        ret

// mld_zeroize (0x1c bytes)
L5170:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c65.constprop.0 (0x60 bytes)
L518c:
        mov     x5, x0
        mov     w0, w1
        mov     x4, #0x0
        mov     w7, #0x4
L519c:
        cmp     w0, #0xff
        ccmp    w3, w4, #0x0, ls
        b.hi    L51ac
        ret
L51ac:
        ldrb    w1, [x2, x4]
        and     w6, w1, #0xf
        lsr     w1, w1, #4
        cmp     w6, #0x8
        b.hi    L51cc
        sub     w6, w7, w6
        str     w6, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
L51cc:
        cmp     w0, #0xff
        ccmp    w1, #0x8, #0x2, ls
        b.hi    L51e4
        sub     w1, w7, w1
        str     w1, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
L51e4:
        add     x4, x4, #0x1
        b       L519c

// mldsa65_poly_decompose (0x34 bytes)
L51ec:
        mov     x6, x0
        mov     x5, x1
        mov     x4, #0x0
        str     x30, [sp, #-16]!
L51fc:
        ldr     w2, [x5, x4]
        add     x1, x6, x4
        add     x0, x5, x4
        add     x4, x4, #0x4
        bl      L5124
        cmp     x4, #0x400
        b.ne    L51fc
        ldr     x30, [sp], #16
        ret

// mldsa65_poly_use_hint (0x98 bytes)
L5220:
        mov     x5, x0
        str     x30, [sp, #-32]!
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x6, x1
        add     x7, sp, #0x14
        mov     x4, #0x0
        ldr     x1, [x0]
        str     x1, [sp, #24]
        mov     x1, #0x0
        add     x0, sp, #0x10
L524c:
        ldr     w2, [x5, x4]
        mov     x1, x7
        ldr     w8, [x6, x4]
        bl      L5124
        ldr     w2, [sp, #20]
        cbz     w8, L5280
        ldr     w1, [sp, #16]
        add     w3, w2, #0x1
        sub     w2, w2, #0x1
        and     w3, w3, #0xf
        and     w2, w2, #0xf
        cmp     w1, #0x0
        csel    w2, w2, w3, le
L5280:
        str     w2, [x5, x4]
        add     x4, x4, #0x4
        cmp     x4, #0x400
        b.ne    L524c
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L52b0
        bl      L0e70
L52b0:
        ldr     x30, [sp], #32
        ret

// mldsa65_poly_uniform_eta_4x (0x234 bytes)
L52b8:
        sub     sp, sp, #0x9c0
        stp     x19, x20, [sp]
        add     x19, sp, #0x9f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x20, x19, #0x4e0
        add     x21, x19, #0x540
        stp     x23, x24, [sp, #32]
        add     x24, x19, #0x480
        add     x22, x19, #0x5a0
        stp     x25, x26, [sp, #48]
        add     x23, sp, #0x698
        mov     x25, x3
        stp     x27, x28, [sp, #64]
        add     x26, x19, #0x360
        add     x27, x19, #0x240
        str     x30, [sp, #80]
        add     x28, x19, #0x120
        stp     x0, x1, [sp, #96]
        ldp     q0, q1, [x4, #32]
        str     x2, [sp, #112]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q2, q3, [x4]
        ldr     x1, [x0]
        str     x1, [sp, #2488]
        mov     x1, #0x0
        stp     q0, q1, [x20, #32]
        stp     q0, q1, [x24, #32]
        stp     q2, q3, [x20]
        stp     q2, q3, [x21]
        stp     q2, q3, [x24]
        stp     q0, q1, [x21, #32]
        stp     q2, q3, [x22]
        ldrb    w0, [sp, #2496]
        stp     q0, q1, [x22, #32]
        strb    w5, [x24, #64]
        strb    wzr, [x24, #65]
        strb    w6, [x24, #160]
        strb    wzr, [x24, #161]
        strb    w7, [x24, #256]
        strb    wzr, [x24, #257]
        strb    w0, [x24, #352]
        mov     x0, x23
        strb    wzr, [x24, #353]
        bl      L1568
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1484
        mov     x5, x23
        mov     x4, #0x2
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14e8
        ldr     x0, [sp, #96]
        mov     w3, #0x110
        mov     x2, x19
        mov     w1, #0x0
        bl      L518c
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L518c
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L518c
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L53f0:
        mov     x0, x25
        bl      L518c
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L545c
        cmp     w22, #0xff
        b.ls    L545c
        cmp     w20, #0xff
        b.ls    L545c
        cmp     w0, #0xff
        b.ls    L545c
        mov     x0, x23
        bl      L156c
        mov     x0, x19
        mov     x1, #0x480
        bl      L5170
        mov     x0, x24
        mov     x1, #0x180
        bl      L5170
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L54cc
        bl      L0e70
L545c:
        mov     x5, x23
        mov     x4, #0x1
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14e8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     w3, #0x88
        mov     x2, x19
        bl      L518c
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L518c
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L518c
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L53f0
L54cc:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x9c0
        ret

// mldsa65_poly_challenge (0x160 bytes)
L54ec:
        stp     x19, x20, [sp, #-464]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x21, sp, #0xf8
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        add     x20, sp, #0x6f
        str     x30, [sp, #48]
        and     x20, x20, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #456]
        mov     x1, #0x0
        mov     x0, x21
        bl      L10a8
        mov     x1, x19
        mov     x2, #0x30
        mov     x0, x21
        bl      L10c8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10f0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1170
        mov     x0, #0x0
L555c:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L555c
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xcf
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e80
L5594:
        cmp     w19, #0x88
        b.ne    L5630
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1170
        mov     w0, #0x0
L55b0:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L5594
        ubfiz   x0, x0, #2, #8
        ldr     w1, [x22, x0]
        str     w1, [x22, x23, lsl #2]
        add     x23, x23, #0x1
        ldr     x1, [sp, #72]
        ubfiz   x2, x1, #1, #1
        lsr     x1, x1, #1
        sub     w2, w24, w2
        str     w2, [x22, x0]
        str     x1, [sp, #72]
        cmp     x23, #0x100
        b.ne    L5594
        mov     x0, x21
        bl      L1190
        mov     x0, x20
        mov     x1, #0x88
        bl      L5170
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L5170
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5638
        bl      L0e70
L5630:
        mov     w0, w19
        b       L55b0
L5638:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa65_polyeta_pack (0x8c bytes)
L564c:
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     x4, #0x0
        mov     w5, #0x4
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
L566c:
        ldp     w3, w2, [x1]
        add     x1, x1, #0x8
        sub     w2, w5, w2
        sub     w3, w5, w3
        and     w3, w3, #0xff
        and     w6, w2, #0xff
        ubfiz   w2, w2, #4, #8
        orr     w2, w3, w2
        strb    w2, [x0, x4]
        add     x4, x4, #0x1
        cmp     x4, #0x80
        b.ne    L566c
        add     x0, sp, #0x10
        mov     x1, #0x8
        strb    w3, [sp, #16]
        strb    w6, [sp, #17]
        bl      L5170
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L56d0
        bl      L0e70
L56d0:
        ldr     x30, [sp], #32
        ret

// mldsa65_polyeta_unpack (0x3c bytes)
L56d8:
        mov     x3, #0x0
        mov     w5, #0x4
L56e0:
        ldrb    w2, [x1, x3]
        add     x0, x0, #0x8
        and     w2, w2, #0xf
        stur    w2, [x0, #-8]
        sub     w2, w5, w2
        ldrb    w4, [x1, x3]
        add     x3, x3, #0x1
        stur    w2, [x0, #-8]
        sub     w2, w5, w4, lsr #4
        stur    w2, [x0, #-4]
        cmp     x3, #0x80
        b.ne    L56e0
        ret

// mldsa65_polyz_pack (0xb8 bytes)
L5714:
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x9, x0, #0x280
        mov     w8, #0x80000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        mov     x2, x0
L5738:
        ldp     w3, w5, [x1]
        add     x2, x2, #0x5
        add     x1, x1, #0x8
        sub     w3, w8, w3
        sub     w5, w8, w5
        sturb   w3, [x2, #-5]
        lsr     w4, w3, #8
        sturb   w4, [x2, #-4]
        ubfiz   w4, w5, #4, #4
        ubfx    x7, x5, #4, #8
        orr     w4, w4, w3, lsr #16
        ubfx    x6, x5, #12, #8
        and     w4, w4, #0xff
        sturb   w4, [x2, #-3]
        sturb   w7, [x2, #-2]
        sturb   w6, [x2, #-1]
        cmp     x9, x2
        b.ne    L5738
        add     x1, x0, #0x200
        stp     w3, w5, [sp, #24]
        sturh   w3, [x1, #123]
        mov     x1, #0x10
        strb    w4, [x0, #637]
        strb    w7, [x0, #638]
        strb    w6, [x0, #639]
        add     x0, sp, #0x18
        bl      L5170
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L57c4
        bl      L0e70
L57c4:
        ldr     x30, [sp], #48
        ret

// mldsa65_polyz_unpack (0x70 bytes)
L57cc:
        add     x6, x0, #0x400
        mov     w5, #0x80000
L57d4:
        ldrb    w2, [x1]
        add     x0, x0, #0x8
        stur    w2, [x0, #-8]
        add     x1, x1, #0x5
        ldurb   w3, [x1, #-4]
        orr     w3, w2, w3, lsl #8
        stur    w3, [x0, #-8]
        ldurb   w2, [x1, #-3]
        orr     w2, w3, w2, lsl #16
        and     w2, w2, #0xfffff
        stur    w2, [x0, #-8]
        sub     w2, w5, w2
        ldurb   w3, [x1, #-3]
        lsr     w3, w3, #4
        stur    w3, [x0, #-4]
        ldurb   w4, [x1, #-2]
        orr     w4, w3, w4, lsl #4
        stur    w4, [x0, #-4]
        ldurb   w3, [x1, #-1]
        stur    w2, [x0, #-8]
        orr     w3, w4, w3, lsl #12
        sub     w2, w5, w3
        stur    w2, [x0, #-4]
        cmp     x0, x6
        b.ne    L57d4
        ret

// mldsa65_poly_uniform_gamma1 (0xdc bytes)
L583c:
        sub     sp, sp, #0x430
        stp     x19, x20, [sp]
        add     x19, sp, #0x4f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x20, x19, #0x2c0
        mov     x22, x0
        str     x30, [sp, #32]
        add     x21, sp, #0x358
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q0, q1, [x1]
        ldr     x3, [x0]
        str     x3, [sp, #1064]
        mov     x3, #0x0
        mov     x0, x21
        stp     q0, q1, [x20]
        ldp     q0, q1, [x1, #32]
        stp     q0, q1, [x20, #32]
        strh    w2, [x19, #768]
        bl      L10a8
        mov     x1, x20
        mov     x2, #0x42
        mov     x0, x21
        bl      L10c8
        mov     x0, x21
        bl      L10f0
        mov     x2, x21
        mov     x0, x19
        mov     x1, #0x2a8
        bl      L1170
        mov     x1, x19
        mov     x0, x22
        bl      L57cc
        mov     x0, x21
        bl      L1190
        mov     x0, x19
        mov     x1, #0x2a8
        bl      L5170
        mov     x0, x20
        mov     x1, #0x42
        bl      L5170
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1064]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5904
        bl      L0e70
L5904:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x430
        ret

// mldsa65_poly_uniform_gamma1_4x (0x17c bytes)
L5918:
        mov     x12, #0x1020
        sub     sp, sp, x12
        stp     x19, x20, [sp]
        add     x19, sp, #0x7f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x20, x19, #0xb00
        add     x21, x19, #0xb60
        stp     x23, x24, [sp, #32]
        mov     x24, x1
        mov     x23, x2
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        add     x26, x19, #0xbc0
        stp     x27, x28, [sp, #64]
        add     x27, x19, #0xc20
        add     x28, sp, #0xcf8
        str     x30, [sp, #80]
        mov     x22, x3
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q0, q1, [x4, #32]
        ldr     x1, [x0]
        str     x1, [sp, #4120]
        mov     x1, #0x0
        ldp     q2, q3, [x4]
        stp     q0, q1, [x21, #32]
        stp     q0, q1, [x26, #32]
        stp     q0, q1, [x20, #32]
        stp     q2, q3, [x21]
        stp     q2, q3, [x26]
        stp     q2, q3, [x27]
        stp     q2, q3, [x20]
        stp     q0, q1, [x27, #32]
        ldrh    w0, [sp, #4128]
        strh    w5, [x19, #2880]
        strh    w6, [x19, #2976]
        strh    w7, [x19, #3072]
        strh    w0, [x19, #3168]
        mov     x0, x28
        bl      L1568
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1484
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14e8
        mov     x1, x19
        mov     x0, x25
        bl      L57cc
        mov     x1, x27
        mov     x0, x24
        bl      L57cc
        mov     x1, x26
        mov     x0, x23
        bl      L57cc
        mov     x1, x21
        mov     x0, x22
        bl      L57cc
        mov     x0, x28
        bl      L156c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L5170
        mov     x0, x20
        mov     x1, #0x180
        bl      L5170
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5a70
        bl      L0e70
L5a70:
        ldp     x19, x20, [sp]
        mov     x12, #0x1020
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa65_polyvecl_uniform_gamma1 (0x5c bytes)
L5a94:
        sub     sp, sp, #0x30
        mov     w5, w2
        add     x3, x0, #0xc00
        stp     x19, x20, [sp, #16]
        sxth    w20, w2
        mov     x19, x0
        stp     x21, x30, [sp, #32]
        mov     x21, x1
        add     w1, w20, #0x3
        strh    w1, [sp]
        add     w7, w20, #0x2
        add     w6, w20, #0x1
        mov     x4, x21
        add     x2, x0, #0x800
        add     x1, x0, #0x400
        bl      L5918
        add     w2, w20, #0x4
        mov     x1, x21
        ldp     x21, x30, [sp, #32]
        add     x0, x19, #0x1, lsl #12
        ldp     x19, x20, [sp, #16]
        add     sp, sp, #0x30
        b       L583c

// mldsa65_polyvecl_ntt (0x34 bytes)
L5af0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1400
        add     x20, x19, x0
        str     x30, [sp, #16]
L5b04:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20d0
        cmp     x19, x20
        b.ne    L5b04
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L5b24:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L5b34:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L5b40:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x5
        b.ne    L5b40
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L5b34
        ret

// mldsa65_polyvecl_chknorm (0x50 bytes)
L5b7c:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1400
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
L5b9c:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L28c8
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L5b9c
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyveck_caddq (0x34 bytes)
L5bcc:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L5be0:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L202c
        cmp     x19, x20
        b.ne    L5be0
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_ntt (0x34 bytes)
L5c00:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L5c14:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20d0
        cmp     x19, x20
        b.ne    L5c14
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_invntt_tomont (0x34 bytes)
L5c34:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L5c48:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2178
        cmp     x19, x20
        b.ne    L5c48
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_unpack_eta_chknorm (0x5c bytes)
L5c68:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L5c88:
        mov     x1, x19
        mov     x0, x20
        bl      L56d8
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x80
        bl      L28c8
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L5c88
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyveck_decompose_pack_w1 (0x58 bytes)
L5cc4:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        mov     x0, #0x1800
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, x0
        str     x30, [sp, #32]
L5ce4:
        mov     x1, x19
        mov     x0, x21
        bl      L51ec
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2970
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L5ce4
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyvecl_unpack_eta (0x40 bytes)
L5d1c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1400
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5d34:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L56d8
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L5d34
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvecl_unpack_z (0x40 bytes)
L5d5c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1400
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5d74:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L57cc
        add     x20, x20, #0x280
        cmp     x19, x21
        b.ne    L5d74
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_unpack_eta (0x40 bytes)
L5d9c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1800
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5db4:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L56d8
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L5db4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvec_matrix_expand_eager (0x15c bytes)
L5ddc:
        stp     x19, x20, [sp, #-336]!
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x19, sp, #0x4f
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        ldr     x2, [x0]
        str     x2, [sp, #328]
        mov     x2, #0x0
        mov     x0, x19
L5e0c:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L5e0c
        mov     w20, #0x0
        mov     w21, #0x5
L5e2c:
        mov     x1, x19
        mov     w0, #0x0
L5e34:
        add     w2, w20, w0
        add     w0, w0, #0x1
        add     x1, x1, #0x40
        udiv    w3, w2, w21
        add     w4, w3, w3, lsl #2
        sturb   w3, [x1, #-31]
        sub     w2, w2, w4
        sturb   w2, [x1, #-32]
        cmp     w0, #0x4
        b.ne    L5e34
        add     w2, w20, #0x3
        add     w1, w20, #0x2
        add     w0, w20, #0x1
        udiv    w3, w2, w21
        add     w4, w3, w3, lsl #2
        sub     w2, w2, w4
        umaddl  x3, w3, w21, x2
        udiv    w2, w1, w21
        add     x3, x22, x3, lsl #10
        add     w4, w2, w2, lsl #2
        sub     w1, w1, w4
        umaddl  x2, w2, w21, x1
        udiv    w1, w0, w21
        add     x2, x22, x2, lsl #10
        add     w4, w1, w1, lsl #2
        sub     w0, w0, w4
        umaddl  x1, w1, w21, x0
        udiv    w0, w20, w21
        add     x1, x22, x1, lsl #10
        add     w4, w0, w0, lsl #2
        sub     w4, w20, w4
        add     w20, w20, #0x4
        umaddl  x0, w0, w21, x4
        mov     x4, x19
        add     x0, x22, x0, lsl #10
        bl      L23b8
        cmp     w20, #0x1c
        b.ne    L5e2c
        mov     w0, #0x503
        mov     x1, x19
        strh    w0, [x19, #32]
        add     x0, x22, #0x7, lsl #12
        bl      L22c4
        mov     w0, #0x504
        mov     x1, x19
        strh    w0, [x19, #32]
        mov     x0, #0x7400
        add     x0, x22, x0
        bl      L22c4
        mov     x0, x19
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e80
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5f28
        bl      L0e70
L5f28:
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret

// mldsa65_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L5f38:
        mov     w4, #0x1400
        umaddl  x1, w3, w4, x1
        b       L5b24

// mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L5f44:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x3
        mov     x19, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x1
        mov     x1, x2
        mov     x2, #0x1400
        mov     x21, x0
        mov     x0, x3
        str     x30, [sp, #32]
        bl      L0e50
        mov     x0, x20
        bl      L5af0
L5f78:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L5f38
        cmp     x19, #0x6
        b.ne    L5f78
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L5c34

// mld_ct_memcmp (0x54 bytes)
L5fac:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L5fb8:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L5fe0
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L5fe0:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L5fb8

// mld_zeroize (0x1c bytes)
L6000:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t165 (0x160 bytes)
L601c:
        mov     x12, #0x8080
        sub     sp, sp, x12
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x1
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x7f
        stp     x21, x22, [sp, #16]
        and     x20, x20, #0xffffffffffffffe0
        mov     x1, x4
        stp     x25, x26, [sp, #48]
        mov     x26, x2
        mov     x25, x3
        stp     x27, x28, [sp, #64]
        mov     x3, #0x7c00
        add     x2, sp, #0x8, lsl #12
        str     x30, [sp, #80]
        add     x19, x20, x3
        mov     x4, #0x7800
        mov     x21, #0x0
        ldr     x3, [x0]
        str     x3, [x2, #120]
        mov     x3, #0x0
        add     x22, x20, x4
        mov     x0, x20
        mov     x28, #0x140
        mov     x27, #0x1a0
        bl      L5ddc
L6094:
        mov     w3, w21
        mov     x2, x26
        mov     x1, x20
        mov     x0, x19
        bl      L5f38
        mov     x0, x19
        bl      L2178
        add     x1, x25, x21, lsl #7
        mov     x0, x22
        bl      L56d8
        mov     x1, x22
        mov     x0, x19
        bl      L2068
        mov     x0, x19
        bl      L2000
        mov     x0, x19
        bl      L202c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x22
        bl      L2294
        madd    x0, x21, x28, x24
        mov     x1, x22
        bl      L2594
        madd    x0, x21, x27, x23
        mov     x1, x19
        add     x21, x21, #0x1
        bl      L2660
        cmp     x21, #0x6
        b.ne    L6094
        mov     x0, x22
        mov     x1, #0x400
        bl      L6000
        mov     x0, x19
        mov     x1, #0x400
        bl      L6000
        mov     x0, x20
        mov     x1, #0x7800
        bl      L6000
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x8, lsl #12
        ldr     x3, [x2, #120]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L6154
        bl      L0e70
L6154:
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x8080
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mld_H65 (0xf0 bytes)
L617c:
        stp     x19, x20, [sp, #-304]!
        mov     x20, x7
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x19, sp, #0x58
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        stp     x25, x26, [sp, #48]
        mov     x21, x5
        mov     x26, x2
        stp     x27, x30, [sp, #64]
        mov     x25, x4
        mov     x27, x3
        ldr     x1, [x0]
        str     x1, [sp, #296]
        mov     x1, #0x0
        mov     x24, x6
        mov     x0, x19
        bl      L10a8
        mov     x2, x27
        mov     x1, x26
        mov     x0, x19
        bl      L10c8
        cbz     x21, L61f4
        mov     x2, x21
        mov     x1, x25
        mov     x0, x19
        bl      L10c8
L61f4:
        cbz     x20, L6208
        mov     x2, x20
        mov     x1, x24
        mov     x0, x19
        bl      L10c8
L6208:
        mov     x0, x19
        bl      L10f0
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L1170
        mov     x0, x19
        bl      L1190
        mov     x0, x19
        mov     x1, #0xd0
        bl      L6000
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6254
        bl      L0e70
L6254:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa65_keypair_internal (0x290 bytes)
L626c:
        mov     x12, #0x1590
        sub     sp, sp, x12
        mov     x3, #0x1400
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x9f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        mov     x20, x1
        mov     x22, x0
        stp     x23, x24, [sp, #48]
        mov     x1, #0x14c0
        add     x21, x19, x3
        stp     x25, x26, [sp, #64]
        add     x25, x19, x1
        add     x24, x19, #0x800
        stp     x27, x28, [sp, #80]
        add     x26, x19, #0xc00
        add     x27, x21, #0x20
        str     x30, [sp, #96]
        mov     x3, #0x22
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x23, x19, #0x400
        ldp     q0, q1, [x2]
        ldr     x1, [x0]
        str     x1, [sp, #5512]
        mov     x1, #0x0
        mov     w0, #0x506
        mov     x2, x25
        mov     x1, #0x80
        add     x28, x20, #0x300
        stp     q0, q1, [x25]
        strh    w0, [x19, #5344]
        mov     x0, x21
        bl      L1194
        mov     x2, x24
        mov     x4, x27
        mov     x3, x26
        mov     w0, #0xa
        strb    w0, [sp]
        mov     w7, #0x9
        mov     w6, #0x8
        mov     w5, #0x7
        mov     x1, x23
        mov     x0, x19
        bl      L52b8
        mov     x1, x19
        add     x0, x20, #0x400
        bl      L564c
        mov     x1, x23
        add     x0, x20, #0x480
        bl      L564c
        mov     x1, x24
        add     x0, x20, #0x500
        bl      L564c
        mov     x1, x26
        add     x0, x20, #0x580
        bl      L564c
        mov     w1, #0xffffffff
        strb    w1, [sp]
        mov     x3, x24
        mov     x2, x23
        mov     x4, x27
        mov     w7, #0x6
        mov     w6, #0x5
        mov     w5, #0x4
        add     x0, x19, #0x1, lsl #12
        mov     x1, x19
        str     x0, [sp, #120]
        bl      L52b8
        ldr     x0, [sp, #120]
        mov     x1, x0
        add     x0, x20, #0x280
        bl      L564c
        mov     x1, x19
        mov     x0, x28
        bl      L564c
        mov     x1, x23
        add     x0, x20, #0x380
        bl      L564c
        mov     x2, x24
        mov     x4, x27
        mov     x3, x26
        mov     w0, #0x3
        strb    w0, [sp]
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x1, x23
        mov     x0, x19
        bl      L52b8
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L564c
        mov     x1, x23
        add     x0, x20, #0x100
        bl      L564c
        mov     x1, x24
        add     x0, x20, #0x180
        bl      L564c
        mov     x1, x26
        add     x0, x20, #0x200
        bl      L564c
        mov     x0, x19
        bl      L5af0
        ldp     q0, q1, [x21]
        mov     x4, x21
        mov     x3, x28
        mov     x2, x19
        add     x1, x20, #0x600
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L601c
        mov     x4, #0x1480
        mov     w23, w0
        add     x24, x19, x4
        cbnz    w0, L6468
        mov     x2, x22
        mov     x0, x24
        mov     x3, #0x7a0
        mov     x1, #0x40
        bl      L1194
        add     x3, x21, #0x60
        mov     x2, x24
        mov     x1, x21
        mov     x0, x20
        bl      L4e74
L6468:
        mov     x0, x19
        mov     x1, #0x1400
        bl      L6000
        mov     x0, x24
        mov     x1, #0x40
        bl      L6000
        mov     x0, x25
        mov     x1, #0x22
        bl      L6000
        mov     x0, x21
        mov     x1, #0x80
        bl      L6000
        cbz     w23, L64b4
        mov     x0, x22
        mov     x1, #0x7a0
        bl      L6000
        mov     x0, x20
        mov     x1, #0xfc0
        bl      L6000
L64b4:
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5512]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L64d4
        bl      L0e70
L64d4:
        ldp     x19, x20, [sp, #16]
        mov     w0, w23
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x1590
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret

// mldsa65_keypair (0x94 bytes)
L64fc:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #88]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e60
        cbnz    w0, L6578
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L626c
        mov     w20, w0
L654c:
        mov     x0, x19
        mov     x1, #0x20
        bl      L6000
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6580
        bl      L0e70
L6578:
        mov     w20, #0xfffffffd
        b       L654c
L6580:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa65_signature_internal (0x44c bytes)
L6590:
        sub     sp, sp, #0x8f0
        mov     x8, #0xa800
        sub     sp, sp, #0x10, lsl #12
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x4
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0xbf
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x21, x19, #0x10, lsl #12
        stp     x25, x26, [sp, #48]
        mov     x26, x1
        add     x1, sp, #0x10, lsl #12
        stp     x27, x28, [sp, #64]
        add     x1, x1, #0x40
        mov     x25, x2
        str     x30, [sp, #80]
        add     x21, x21, #0x700
        mov     w27, w7
        mov     x7, #0xe800
        ldr     x2, [x0]
        str     x2, [x1, #2216]
        mov     x2, #0x0
        add     x0, x19, #0x9, lsl #12
        str     x0, [sp, #128]
        add     x0, x19, x7
        add     x28, x21, #0x20
        str     x0, [sp, #136]
        add     x0, x19, x8
        mov     x22, x3
        mov     x20, x5
        mov     x3, x0
        add     x5, x19, #0x9, lsl #12
        add     x2, x21, #0x60
        mov     x1, x28
        mov     x4, #0xe800
        add     x4, x19, x4
        str     x0, [sp, #144]
        mov     x0, x21
        bl      L4e9c
        add     x0, x21, #0x80
        cbnz    w27, L68ac
        mov     x3, #0x40
        mov     x7, x25
        mov     x6, x26
        mov     x5, x24
        mov     x4, x22
        mov     x2, x28
        mov     x1, x3
        bl      L617c
L6664:
        mov     x5, #0x20
        add     x6, x21, #0x80
        mov     x4, x20
        mov     x3, x5
        add     x2, x21, #0x60
        mov     x7, #0x40
        add     x0, x21, #0xc0
        mov     x1, x7
        bl      L617c
        mov     x0, x19
        mov     x1, x21
        bl      L5ddc
        str     wzr, [sp, #124]
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0x400
        str     x0, [sp, #104]
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0x800
        str     x0, [sp, #112]
L66b0:
        ldrh    w2, [sp, #124]
        mov     x0, #0xd400
        add     x27, x19, x0
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0xc, lsl #12
        add     x25, x19, #0x10, lsl #12
        mov     w26, #0xff3c
        bl      L5a94
        mov     x28, #0x0
        mov     x1, #0x7800
        mov     x3, x20
        add     x24, x19, x1
        mov     x2, x27
        mov     x1, x19
        mov     x0, x24
        bl      L5f44
        movk    w26, #0x7, lsl #16
        mov     x0, x24
        bl      L5bcc
        ldr     x0, [sp, #104]
        mov     x3, #0xfc00
        mov     x2, x20
        mov     x1, x24
        add     x22, x19, x3
        bl      L5cc4
        ldp     x4, x0, [sp, #104]
        add     x2, x21, #0x80
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x300
        mov     x3, #0x40
        mov     x1, #0x30
        bl      L617c
        ldr     x1, [sp, #112]
        mov     x0, x25
        bl      L54ec
        mov     x0, x25
        bl      L20d0
L674c:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e50
        mov     x1, x25
        mov     x0, x22
        bl      L2258
        mov     x0, x22
        bl      L2178
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x3, x27
        bl      L0e50
        mov     x1, x20
        mov     x0, x22
        bl      L2068
        mov     x0, x22
        bl      L2000
        mov     w1, w26
        mov     x0, x22
        bl      L28c8
        cbnz    w0, L68c0
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L5034
        cmp     x28, #0x5
        b.ne    L674c
        mov     x26, #0x0
L67d4:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x24, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e50
        mov     x1, x25
        mov     x0, x20
        bl      L2258
        mov     x0, x20
        bl      L2178
        mov     x1, x20
        mov     x0, x28
        bl      L208c
        mov     x0, x28
        bl      L2000
        mov     w1, #0xfe3c
        mov     x0, x28
        movk    w1, #0x3, lsl #16
        bl      L28c8
        cbnz    w0, L68c0
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x26, x0
        mov     x0, x20
        bl      L0e50
        mov     x1, x25
        mov     x0, x20
        bl      L2258
        mov     x0, x20
        bl      L2178
        mov     x0, x20
        bl      L2000
        mov     x0, x20
        mov     w1, #0x3ff00
        bl      L28c8
        cbnz    w0, L68c0
        mov     x0, x28
        mov     x1, x20
        add     x26, x26, #0x400
        bl      L2068
        mov     x0, #0x1800
        cmp     x26, x0
        b.ne    L67d4
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L4f40
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x24
        mov     x0, x23
        bl      L4f54
        mov     w26, w0
        b       L68c4
L68ac:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L6664
L68c0:
        mov     w26, #0xffffffff
L68c4:
        mov     x0, x22
        mov     x1, #0x400
        bl      L6000
        mov     x0, x25
        mov     x1, #0x400
        bl      L6000
        mov     x0, x24
        mov     x1, #0x1800
        bl      L6000
        ldr     x0, [sp, #104]
        mov     x1, #0x300
        bl      L6000
        mov     x0, x20
        mov     x1, #0x1400
        bl      L6000
        mov     x0, x27
        mov     x1, #0x1400
        bl      L6000
        ldr     x0, [sp, #112]
        mov     x1, #0x30
        bl      L6000
        cbz     w26, L6950
        cmn     w26, #0x1
        b.ne    L6944
        ldr     w0, [sp, #124]
        add     w0, w0, #0x5
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfffa
        cmp     w1, w0, uxth
        b.ne    L66b0
        mov     w26, #0xfffffffc
L6944:
        mov     x0, x23
        mov     x1, #0xced
        bl      L6000
L6950:
        ldr     x0, [sp, #128]
        mov     x1, #0x1800
        bl      L6000
        ldr     x0, [sp, #144]
        mov     x1, #0x1800
        bl      L6000
        ldr     x0, [sp, #136]
        mov     x1, #0x1400
        bl      L6000
        mov     x0, x19
        mov     x1, #0x7800
        bl      L6000
        mov     x0, x21
        mov     x1, #0x100
        bl      L6000
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x10, lsl #12
        add     x2, x2, #0x40
        ldr     x3, [x2, #2216]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L69b4
        bl      L0e70
L69b4:
        ldp     x19, x20, [sp]
        mov     w0, w26
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x8f0
        add     sp, sp, #0x10, lsl #12
        ret

// mldsa65_signature_extmu (0xb4 bytes)
L69dc:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        mov     x22, x2
        ldr     x1, [x0]
        str     x1, [sp, #104]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e60
        cbnz    w0, L6a74
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L6590
        mov     w20, w0
L6a48:
        mov     x0, x19
        mov     x1, #0x20
        bl      L6000
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6a7c
        bl      L0e70
L6a74:
        mov     w20, #0xfffffffd
        b       L6a48
L6a7c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa65_verify_internal (0x324 bytes)
L6a90:
        mov     x12, #0x9c60
        sub     sp, sp, x12
        mov     x11, #0x8030
        mov     x12, #0x9c00
        mov     x13, #0x7800
        mov     x14, #0x9800
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x15, #0x9400
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0xaf
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x16, #0x8c00
        stp     x25, x26, [sp, #48]
        add     x25, x19, x12
        add     x26, x19, x13
        stp     x27, x28, [sp, #64]
        mov     x28, x1
        add     x1, sp, x11
        str     x30, [sp, #80]
        add     x24, x19, x14
        str     x5, [sp, #96]
        add     x27, x19, x15
        stp     x2, x3, [sp, #112]
        add     x22, x19, x16
        add     x21, x19, #0x9, lsl #12
        str     x4, [sp, #128]
        str     w6, [sp, #140]
        ldp     q0, q1, [x23]
        ldr     x2, [x0]
        str     x2, [x1, #7208]
        mov     x2, #0x0
        sub     x0, x25, #0x80
        add     x1, x23, #0x30
        stp     q0, q1, [x0]
        ldr     q0, [x23, #32]
        str     q0, [x0, #32]
        mov     x0, x26
        bl      L5d5c
        mov     w1, #0xff3c
        mov     x0, x26
        movk    w1, #0x7, lsl #16
        bl      L5b7c
        mov     x17, #0x9b80
        mov     w20, w0
        add     x0, x19, x17
        str     x0, [sp, #104]
        cbnz    w20, L6cd4
        ldr     w6, [sp, #140]
        cbnz    w6, L6d74
        ldr     x2, [sp, #96]
        mov     x0, x24
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x7a0
        mov     x1, #0x40
        bl      L617c
        ldp     x7, x4, [sp, #112]
        mov     x10, #0x9b00
        ldr     x5, [sp, #128]
        mov     x6, x28
        mov     x2, x24
        mov     x3, #0x40
        add     x0, x19, x10
        mov     x1, x3
        bl      L617c
        mov     x0, x24
        mov     x1, #0x40
        bl      L6000
L6bb8:
        mov     x0, x26
        bl      L5af0
        ldr     x1, [sp, #96]
        mov     x0, x19
        mov     x28, x24
        bl      L5ddc
        mov     x9, #0x9b80
        add     x1, x19, x9
        mov     x0, x27
        bl      L54ec
        mov     x0, x27
        bl      L20d0
L6be8:
        mov     w3, w20
        mov     x2, x26
        mov     x1, x19
        mov     x0, x21
        bl      L5f38
        ldr     x1, [sp, #96]
        mov     w2, w20
        mov     x0, x22
        bl      L4e60
        mov     x0, x22
        bl      L20b0
        mov     x0, x22
        bl      L20d0
        mov     x1, x27
        mov     x0, x22
        bl      L2258
        mov     x1, x22
        mov     x0, x21
        bl      L208c
        mov     x0, x21
        bl      L2000
        mov     x0, x21
        bl      L2178
        mov     x0, x21
        bl      L202c
        mov     w2, w20
        mov     x1, x23
        mov     x0, x22
        bl      L5048
        mov     w25, w0
        cbnz    w0, L6cd4
        mov     x1, x22
        mov     x0, x21
        bl      L5220
        add     w20, w20, #0x1
        mov     x0, x28
        mov     x1, x21
        bl      L2970
        add     x28, x28, #0x80
        cmp     w20, #0x6
        b.ne    L6be8
        mov     x8, #0x9b00
        mov     x4, #0x9b40
        add     x20, x19, x4
        add     x2, x19, x8
        mov     x0, x20
        mov     x1, #0x30
        mov     x4, x24
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x300
        mov     x3, #0x40
        bl      L617c
        ldr     x0, [sp, #104]
        mov     x1, x20
        mov     x2, #0x30
        bl      L5fac
        tst     w0, #0xff
        b.eq    L6cd8
L6cd4:
        mov     w25, #0xfffffffa
L6cd8:
        mov     x0, x22
        mov     x1, #0x400
        bl      L6000
        mov     x0, x21
        mov     x1, #0x400
        bl      L6000
        mov     x0, x19
        mov     x1, #0x7800
        bl      L6000
        mov     x0, x27
        mov     x1, #0x400
        bl      L6000
        mov     x0, x26
        mov     x1, #0x1400
        bl      L6000
        mov     x1, #0x30
        mov     x0, #0x9b40
        add     x0, x19, x0
        bl      L6000
        ldr     x0, [sp, #104]
        mov     x1, #0x30
        bl      L6000
        mov     x2, #0x9b00
        mov     x1, #0x40
        add     x0, x19, x2
        bl      L6000
        mov     x0, x24
        mov     x1, #0x300
        bl      L6000
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x3, #0x8030
        add     x2, sp, x3
        ldr     x3, [x2, #7208]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L6d8c
        bl      L0e70
L6d74:
        ldp     q0, q1, [x28]
        sub     x0, x25, #0x100
        stp     q0, q1, [x0]
        ldp     q0, q1, [x28, #32]
        stp     q0, q1, [x0, #32]
        b       L6bb8
L6d8c:
        ldp     x19, x20, [sp]
        mov     w0, w25
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x9c60
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa65_verify_extmu (0x18 bytes)
L6db4:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L6a90

// mldsa65_prepare_domain_separation_prefix (0x138 bytes)
L6dcc:
        cmp     x4, #0xff
        b.hi    L6ef4
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L6eb8
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L6efc
        .inst   0x90000020  // adrp x0, 0xa000
        add     x0, x0, #0x344
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 6e20 <mldsa65_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L6e24:
        b.ne    L6efc
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L6e44
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e50
L6e44:
        .inst   0x90000020  // adrp x0, 0xa000
        add     x0, x0, #0x350
        mov     x1, #0x0
L6e50:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L6ee4
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L6e80:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e50
        add     x0, x20, x19
        b       L6ed4
        cmp     x20, #0x20
        b       L6e24
        cmp     x20, #0x30
        b       L6e24
        cmp     x20, #0x40
        b       L6e24
L6eb8:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L6ed0
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e50
L6ed0:
        add     x0, x19, #0x2
L6ed4:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L6ee4:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L6e50
        b       L6e80
L6ef4:
        mov     x0, #0x0
        ret
L6efc:
        mov     x0, #0x0
        b       L6ed4

// mldsa65_signature (0x100 bytes)
L6f04:
        stp     x19, x20, [sp, #-480]!
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        add     x20, sp, #0x5f
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        and     x20, x20, #0xffffffffffffffe0
        stp     x25, x30, [sp, #48]
        mov     x23, x1
        mov     x24, x2
        ldr     x1, [x0]
        str     x1, [sp, #472]
        mov     x1, #0x0
        mov     x25, x5
        mov     x0, x20
        mov     w5, #0x0
        mov     x2, #0x0
        add     x22, x20, #0x160
        bl      L6dcc
        cbz     x0, L6fdc
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e60
        cbnz    w0, L6fe4
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L6590
        mov     w19, w0
        cbz     w0, L6fa4
L6f98:
        mov     x0, x21
        mov     x1, #0xced
        bl      L6000
L6fa4:
        mov     x0, x22
        mov     x1, #0x20
        bl      L6000
        mov     x0, x20
        mov     x1, #0x14c
        bl      L6000
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6fec
        bl      L0e70
L6fdc:
        mov     w19, #0xfffffff7
        b       L6f98
L6fe4:
        mov     w19, #0xfffffffd
        b       L6f98
L6fec:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa65_verify (0xbc bytes)
L7004:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x5
        .inst   0x900000c5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        mov     x21, x0
        and     x19, x19, #0xffffffffffffffe0
        ldr     x0, [x5]
        str     x0, [sp, #408]
        mov     x0, #0x0
        mov     x22, x1
        mov     x23, x2
        mov     x0, x19
        mov     w5, #0x0
        mov     x2, #0x0
        mov     x1, #0x0
        bl      L6dcc
        cbz     x0, L70a4
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L6a90
        mov     w20, w0
L7078:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L6000
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L70ac
        bl      L0e70
L70a4:
        mov     w20, #0xfffffff7
        b       L7078
L70ac:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa65_signature_pre_hash_internal (0xc8 bytes)
L70c0:
        stp     x19, x20, [sp, #-416]!
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     x22, x6
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #32]
        add     x20, sp, #0x4f
        ldr     x6, [x0]
        str     x6, [sp, #408]
        mov     x6, #0x0
        and     x20, x20, #0xffffffffffffffe0
        cbnz    w7, L7108
L70f4:
        mov     w19, #0xfffffff7
L70f8:
        mov     x0, x21
        mov     x1, #0xced
        bl      L6000
        b       L7148
L7108:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L6dcc
        mov     x2, x0
        cbz     x0, L70f4
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L6590
        mov     w19, w0
        cbnz    w0, L70f8
L7148:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L6000
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7174
        bl      L0e70
L7174:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa65_signature_pre_hash_shake256 (0xc0 bytes)
L7188:
        stp     x19, x20, [sp, #-160]!
        mov     x20, x0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x3
        str     x30, [sp, #48]
        mov     x22, x4
        mov     x23, x5
        mov     x24, x6
        ldr     x3, [x0]
        str     x3, [sp, #152]
        mov     x3, #0x0
        mov     x0, x19
        mov     x3, x2
        mov     x2, x1
        mov     x1, #0x40
        bl      L1194
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L70c0
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L6000
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7230
        bl      L0e70
L7230:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa65_verify_pre_hash_internal (0xa8 bytes)
L7248:
        stp     x19, x20, [sp, #-400]!
        mov     x20, x0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        ldr     x6, [x0]
        str     x6, [sp, #392]
        mov     x6, #0x0
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        cbnz    w5, L72ac
L727c:
        mov     w20, #0xfffffff7
L7280:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L6000
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L72e0
        bl      L0e70
L72ac:
        mov     x0, x19
        bl      L6dcc
        mov     x2, x0
        cbz     x0, L727c
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L6a90
        mov     w20, w0
        b       L7280
L72e0:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa65_verify_pre_hash_shake256 (0xb0 bytes)
L72f0:
        stp     x19, x20, [sp, #-144]!
        mov     x20, x0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x3
        ldr     x3, [x0]
        str     x3, [sp, #136]
        mov     x3, #0x0
        mov     x22, x4
        mov     x3, x2
        mov     x23, x5
        mov     x2, x1
        mov     x0, x19
        mov     x1, #0x40
        bl      L1194
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L7248
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L6000
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L738c
        bl      L0e70
L738c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa65_pk_from_sk (0x210 bytes)
L73a0:
        mov     x12, #0x2310
        sub     sp, sp, x12
        mov     x5, #0x2400
        mov     x3, #0x1400
        mov     x4, #0x2200
        mov     x2, #0x2260
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x25, x26, [sp, #48]
        mov     x25, x1
        stp     x19, x20, [sp]
        add     x19, sp, #0x8f
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x23, x1, #0x300
        mov     x1, #0x1dc0
        stp     x27, x28, [sp, #64]
        add     x28, x19, x1
        add     x24, x19, x3
        str     x30, [sp, #80]
        add     x27, x19, x4
        add     x26, x19, x2
        ldp     q0, q1, [x25]
        ldr     x1, [x0]
        str     x1, [sp, #8968]
        mov     x1, #0x0
        add     x0, x19, x5
        sub     x22, x0, #0x1a0
        sub     x1, x0, #0x1c0
        sub     x0, x0, #0x200
        stp     q0, q1, [x22]
        ldp     q0, q1, [x25, #32]
        stp     q0, q1, [x1]
        add     x1, x25, #0x40
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x1, #32]
        add     x1, x25, #0x80
        stp     q0, q1, [x0, #32]
        mov     x0, x19
        bl      L5d1c
        mov     w1, #0x5
        mov     x0, x19
        bl      L5b7c
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x5
        mov     x0, x23
        bl      L5c68
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L5af0
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L601c
        mov     x6, #0x21c0
        mov     w22, w0
        add     x23, x19, x6
        cbnz    w0, L7504
        add     x1, x25, #0x600
        mov     x0, x24
        mov     x2, #0x9c0
        bl      L5fac
        and     w4, w0, #0xff
        mov     x3, #0x7a0
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1194
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L5fac
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L7510
        mov     w22, #0xfffffff9
L7504:
        mov     x0, x21
        mov     x1, #0x7a0
        bl      L6000
L7510:
        mov     x0, x24
        mov     x1, #0x9c0
        bl      L6000
        mov     x0, x28
        mov     x1, #0x400
        bl      L6000
        mov     x0, x19
        mov     x1, #0x1400
        bl      L6000
        mov     x1, #0x20
        mov     x0, #0x2240
        add     x0, x19, x0
        bl      L6000
        mov     x0, x23
        mov     x1, #0x40
        bl      L6000
        mov     x0, x27
        mov     x1, #0x40
        bl      L6000
        mov     x0, x26
        mov     x1, #0x20
        bl      L6000
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8968]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7588
        bl      L0e70
L7588:
        ldp     x19, x20, [sp]
        mov     w0, w22
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x2310
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa87_unpack_pk_t1 (0x14 bytes)
L75b0:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25f0

// mldsa87_pack_sk_rho_key_tr (0x28 bytes)
L75c4:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x3]
        stp     q0, q1, [x0, #32]
        add     x0, x0, #0x40
        ldp     q0, q1, [x2]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x2, #32]
        stp     q0, q1, [x0, #32]
        ret

// mldsa87_unpack_sk (0xa8 bytes)
L75ec:
        ldp     q0, q1, [x6]
        stp     x19, x20, [sp, #-48]!
        mov     x19, x6
        stp     x21, x22, [sp, #16]
        mov     x20, x3
        mov     x21, x5
        str     x30, [sp, #32]
        mov     x22, x4
        stp     q0, q1, [x0]
        add     x0, x6, #0x40
        ldp     q0, q1, [x6, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x0]
        stp     q0, q1, [x1]
        ldp     q0, q1, [x0, #32]
        mov     x0, x4
        stp     q0, q1, [x1, #32]
        add     x1, x6, #0x80
        bl      L8520
        mov     x0, x22
        mov     x22, x20
        bl      L8304
        add     x1, x19, #0x320
        mov     x0, x21
        bl      L85a0
        mov     x0, x21
        add     x21, x19, #0x620
        bl      L8410
        mov     x0, #0x1320
        add     x19, x19, x0
L7664:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L2774
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L7664
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L8410

// mldsa87_pack_sig_c (0x14 bytes)
L7694:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x1, #32]
        stp     q0, q1, [x0, #32]
        ret

// mldsa87_pack_sig_h (0xe8 bytes)
L76a8:
        stp     x19, x20, [sp, #-96]!
        mov     x19, #0x0
        mov     w20, #0x0
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x1, #0x11c0
        stp     x25, x26, [sp, #48]
        add     x25, x0, x1
        mov     x24, x2
        stp     x27, x28, [sp, #64]
        mov     w28, #0x100
        mov     x2, #0x53
        mov     w1, #0x0
        mov     w26, #0x3ff00
        mov     w27, #0x7fe00
        movk    w28, #0xfffc, lsl #16
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     x22, x3
        mov     x0, x25
        str     x30, [sp, #80]
        bl      L0e80
L7700:
        add     x1, x24, x19, lsl #7
        mov     x0, x22
        bl      L29f4
        add     x1, x23, x19, lsl #10
        mov     x4, #0x0
L7714:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w2, [x22, x4, lsl #2]
        add     w3, w0, w26
        cmp     w3, w27
        b.hi    L7734
        cmp     w2, #0x0
        ccmp    w0, w28, #0x0, ne
        b.ne    L7744
L7734:
        cmp     w20, #0x4b
        b.eq    L7788
        strb    w4, [x25, w20, uxtw]
        add     w20, w20, #0x1
L7744:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L7714
        mov     x0, #0x120b
        add     x0, x21, x0
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x8
        b.ne    L7700
        mov     w0, #0x0
L776c:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L7788:
        mov     w0, #0xffffffff
        b       L776c

// mldsa87_pack_sig_z (0x14 bytes)
L7790:
        mov     w3, #0x280
        mul     w2, w2, w3
        add     x2, x2, #0x40
        add     x0, x0, x2
        b       L7fd0

// mldsa87_sig_unpack_hints (0xe8 bytes)
L77a4:
        stp     x19, x20, [sp, #-48]!
        mov     x4, #0x11c0
        mov     x3, x0
        stp     x21, x22, [sp, #16]
        mov     x20, x1
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, x4
        cbz     w2, L77f8
        add     w0, w2, #0x4a
        ldrb    w22, [x23, x0]
L77d0:
        add     w0, w21, #0x4b
        ldrb    w19, [x23, x0]
        cmp     w19, #0x4b
        ccmp    w22, w19, #0x2, ls
        b.ls    L7800
L77e4:
        mov     w0, #0xffffffff
L77e8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L77f8:
        mov     w22, #0x0
        b       L77d0
L7800:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     w1, #0x11c0
        add     w1, w22, w1
        mov     x3, x0
        add     x1, x20, x1
        mov     w2, w22
        mov     w4, #0x1
L7828:
        cmp     w2, w19
        b.cc    L7850
        cmp     w21, #0x7
        b.ne    L7848
        mov     x0, #0x11bf
        add     x20, x20, x0
L7840:
        cmp     w19, #0x4b
        b.ne    L787c
L7848:
        mov     w0, #0x0
        b       L77e8
L7850:
        cmp     w2, w22
        b.ls    L786c
        sub     w0, w2, #0x1
        ldrb    w5, [x1]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L77e4
L786c:
        ldrb    w0, [x1], #1
        add     w2, w2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L7828
L787c:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L7840
        b       L77e4

// mld_decompose87 (0x4c bytes)
L788c:
        add     w3, w2, #0x7f
        asr     w3, w3, #7
        add     w3, w3, w3, lsl #10
        add     w3, w3, #0x200, lsl #12
        ubfx    x3, x3, #22, #4
        str     w3, [x1]
        mov     w1, #0x3ff000
        sub     w3, w3, w3, lsl #10
        add     w2, w2, w3, lsl #9
        sub     w1, w1, w2
        sxtw    x1, w1
        asr     x1, x1, #31
        mov     w3, #0xff801fff
        add     w3, w2, w3
        eor     w3, w3, w2
        and     w1, w3, w1
        eor     w1, w1, w2
        str     w1, [x0]
        ret

// mld_zeroize (0x1c bytes)
L78d8:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c87.constprop.0 (0x88 bytes)
L78f4:
        mov     x6, x0
        mov     w0, w1
        mov     x5, #0x0
        mov     w9, #0x87
        mov     w7, #0xcd
        mov     w8, #0x2
L790c:
        cmp     w0, #0xff
        ccmp    w5, w9, #0x2, ls
        b.ls    L791c
        ret
L791c:
        ldrb    w1, [x2, x5]
        and     w3, w1, #0xf
        lsr     w1, w1, #4
        cmp     w3, #0xf
        b.eq    L794c
        mul     w4, w3, w7
        lsr     w4, w4, #10
        add     w4, w4, w4, lsl #2
        sub     w3, w3, w4
        sub     w3, w8, w3
        str     w3, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L794c:
        cmp     w0, #0xff
        ccmp    w1, #0xe, #0x2, ls
        b.hi    L7974
        mul     w3, w1, w7
        lsr     w3, w3, #10
        add     w3, w3, w3, lsl #2
        sub     w1, w1, w3
        sub     w1, w8, w1
        str     w1, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L7974:
        add     x5, x5, #0x1
        b       L790c

// mldsa87_poly_decompose (0x34 bytes)
L797c:
        mov     x6, x0
        mov     x5, x1
        mov     x4, #0x0
        str     x30, [sp, #-16]!
L798c:
        ldr     w2, [x5, x4]
        add     x1, x6, x4
        add     x0, x5, x4
        add     x4, x4, #0x4
        bl      L788c
        cmp     x4, #0x400
        b.ne    L798c
        ldr     x30, [sp], #16
        ret

// mldsa87_poly_use_hint (0x98 bytes)
L79b0:
        mov     x5, x0
        str     x30, [sp, #-32]!
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x6, x1
        add     x7, sp, #0x14
        mov     x4, #0x0
        ldr     x1, [x0]
        str     x1, [sp, #24]
        mov     x1, #0x0
        add     x0, sp, #0x10
L79dc:
        ldr     w2, [x5, x4]
        mov     x1, x7
        ldr     w8, [x6, x4]
        bl      L788c
        ldr     w2, [sp, #20]
        cbz     w8, L7a10
        ldr     w1, [sp, #16]
        add     w3, w2, #0x1
        sub     w2, w2, #0x1
        and     w3, w3, #0xf
        and     w2, w2, #0xf
        cmp     w1, #0x0
        csel    w2, w2, w3, le
L7a10:
        str     w2, [x5, x4]
        add     x4, x4, #0x4
        cmp     x4, #0x400
        b.ne    L79dc
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7a40
        bl      L0e70
L7a40:
        ldr     x30, [sp], #32
        ret

// mldsa87_poly_uniform_eta_4x (0x22c bytes)
L7a48:
        sub     sp, sp, #0x7c0
        stp     x19, x20, [sp]
        add     x19, sp, #0x9f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x20, x19, #0x2e0
        add     x21, x19, #0x340
        stp     x23, x24, [sp, #32]
        add     x24, x19, #0x280
        add     x22, x19, #0x3a0
        stp     x25, x26, [sp, #48]
        add     x23, sp, #0x498
        mov     x25, x3
        stp     x27, x28, [sp, #64]
        add     x26, x19, #0x1e0
        add     x27, x19, #0x140
        str     x30, [sp, #80]
        add     x28, x19, #0xa0
        stp     x0, x1, [sp, #96]
        ldp     q0, q1, [x4, #32]
        str     x2, [sp, #112]
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q2, q3, [x4]
        ldr     x1, [x0]
        str     x1, [sp, #1976]
        mov     x1, #0x0
        stp     q0, q1, [x20, #32]
        stp     q0, q1, [x24, #32]
        stp     q2, q3, [x20]
        stp     q2, q3, [x21]
        stp     q2, q3, [x24]
        stp     q0, q1, [x21, #32]
        stp     q2, q3, [x22]
        ldrb    w0, [sp, #1984]
        stp     q0, q1, [x22, #32]
        strb    w5, [x24, #64]
        strb    wzr, [x24, #65]
        strb    w6, [x24, #160]
        strb    wzr, [x24, #161]
        strb    w7, [x24, #256]
        strb    wzr, [x24, #257]
        strb    w0, [x24, #352]
        mov     x0, x23
        strb    wzr, [x24, #353]
        bl      L1568
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1484
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14e8
        ldr     x0, [sp, #96]
        mov     x2, x19
        mov     w1, #0x0
        bl      L78f4
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L78f4
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L78f4
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L7b7c:
        mov     x0, x25
        bl      L78f4
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L7be8
        cmp     w22, #0xff
        b.ls    L7be8
        cmp     w20, #0xff
        b.ls    L7be8
        cmp     w0, #0xff
        b.ls    L7be8
        mov     x0, x23
        bl      L156c
        mov     x0, x19
        mov     x1, #0x280
        bl      L78d8
        mov     x0, x24
        mov     x1, #0x180
        bl      L78d8
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1976]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7c54
        bl      L0e70
L7be8:
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14e8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     x2, x19
        bl      L78f4
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L78f4
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L78f4
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L7b7c
L7c54:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7c0
        ret

// mldsa87_poly_challenge (0x160 bytes)
L7c74:
        stp     x19, x20, [sp, #-464]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x21, sp, #0xf8
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        add     x20, sp, #0x6f
        str     x30, [sp, #48]
        and     x20, x20, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #456]
        mov     x1, #0x0
        mov     x0, x21
        bl      L10a8
        mov     x1, x19
        mov     x2, #0x40
        mov     x0, x21
        bl      L10c8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10f0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1170
        mov     x0, #0x0
L7ce4:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L7ce4
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xc4
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e80
L7d1c:
        cmp     w19, #0x88
        b.ne    L7db8
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1170
        mov     w0, #0x0
L7d38:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L7d1c
        ubfiz   x0, x0, #2, #8
        ldr     w1, [x22, x0]
        str     w1, [x22, x23, lsl #2]
        add     x23, x23, #0x1
        ldr     x1, [sp, #72]
        ubfiz   x2, x1, #1, #1
        lsr     x1, x1, #1
        sub     w2, w24, w2
        str     w2, [x22, x0]
        str     x1, [sp, #72]
        cmp     x23, #0x100
        b.ne    L7d1c
        mov     x0, x21
        bl      L1190
        mov     x0, x20
        mov     x1, #0x88
        bl      L78d8
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L78d8
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7dc0
        bl      L0e70
L7db8:
        mov     w0, w19
        b       L7d38
L7dc0:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa87_polyeta_pack (0x13c bytes)
L7dd4:
        .inst   0x900000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x30, [sp, #-32]!
        mov     x8, x0
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x14, x1, #0x400
        mov     w6, #0x2
L7df8:
        ldp     w5, w2, [x1, #8]
        add     x8, x8, #0x3
        ldp     w30, w17, [x1, #16]
        sub     w2, w6, w2
        ldp     w7, w3, [x1]
        sub     w30, w6, w30
        ldp     w4, w18, [x1, #24]
        sub     w5, w6, w5
        sub     w17, w6, w17
        sub     w3, w6, w3
        sub     w4, w6, w4
        sub     w18, w6, w18
        sub     w7, w6, w7
        and     w16, w2, #0xff
        and     w12, w30, #0xff
        ubfiz   w2, w2, #1, #8
        ubfiz   w30, w30, #4, #8
        ubfiz   w19, w5, #6, #8
        orr     w2, w2, w30
        and     w15, w3, #0xff
        ubfiz   w30, w17, #7, #8
        and     w13, w5, #0xff
        and     w10, w4, #0xff
        and     w9, w18, #0xff
        ubfiz   w3, w3, #3, #8
        ubfx    x5, x5, #2, #6
        ubfiz   w4, w4, #2, #8
        ubfiz   w18, w18, #5, #8
        sxtb    w7, w7
        and     w11, w17, #0xff
        orr     w3, w3, w19
        orr     w5, w5, w30
        orr     w4, w4, w18
        ubfx    x17, x17, #1, #7
        orr     w3, w7, w3
        orr     w2, w2, w5
        orr     w4, w4, w17
        and     w3, w3, #0xff
        and     w2, w2, #0xff
        and     w4, w4, #0xff
        add     x1, x1, #0x20
        sturb   w3, [x8, #-3]
        sturb   w2, [x8, #-2]
        sturb   w4, [x8, #-1]
        cmp     x14, x1
        b.ne    L7df8
        strb    w3, [x0, #93]
        mov     x1, #0x8
        strb    w2, [x0, #94]
        strb    w4, [x0, #95]
        add     x0, sp, #0x10
        strb    w7, [sp, #16]
        strb    w15, [sp, #17]
        strb    w13, [sp, #18]
        strb    w16, [sp, #19]
        strb    w12, [sp, #20]
        strb    w11, [sp, #21]
        strb    w10, [sp, #22]
        strb    w9, [sp, #23]
        bl      L78d8
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7f08
        bl      L0e70
L7f08:
        ldp     x19, x30, [sp], #32
        ret

// mldsa87_polyeta_unpack (0xc0 bytes)
L7f10:
        add     x11, x0, #0x400
        mov     w2, #0x2
L7f18:
        ldrb    w9, [x1]
        add     x1, x1, #0x3
        and     w9, w9, #0x7
        str     w9, [x0]
        sub     w9, w2, w9
        ldurb   w8, [x1, #-3]
        ubfx    x8, x8, #3, #3
        str     w8, [x0, #4]
        sub     w8, w2, w8
        ldurb   w3, [x1, #-2]
        ldurb   w4, [x1, #-3]
        lsl     w3, w3, #2
        orr     w4, w3, w4, lsr #6
        and     w4, w4, #0x7
        str     w4, [x0, #8]
        sub     w4, w2, w4
        ldurb   w7, [x1, #-2]
        ubfx    x7, x7, #1, #3
        str     w7, [x0, #12]
        sub     w7, w2, w7
        ldurb   w6, [x1, #-2]
        ubfx    x6, x6, #4, #3
        str     w6, [x0, #16]
        sub     w6, w2, w6
        ldurb   w5, [x1, #-1]
        ldurb   w3, [x1, #-2]
        lsl     w5, w5, #1
        orr     w3, w5, w3, lsr #7
        and     w3, w3, #0x7
        str     w3, [x0, #20]
        sub     w3, w2, w3
        ldurb   w5, [x1, #-1]
        ubfx    x5, x5, #2, #3
        str     w5, [x0, #24]
        sub     w5, w2, w5
        ldurb   w10, [x1, #-1]
        stp     w9, w8, [x0]
        stp     w4, w7, [x0, #8]
        stp     w6, w3, [x0, #16]
        sub     w3, w2, w10, lsr #5
        add     x0, x0, #0x20
        stur    w5, [x0, #-8]
        stur    w3, [x0, #-4]
        cmp     x0, x11
        b.ne    L7f18
        ret

// mldsa87_polyz_pack (0xb8 bytes)
L7fd0:
        .inst   0x900000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x9, x0, #0x280
        mov     w8, #0x80000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        mov     x2, x0
L7ff4:
        ldp     w3, w5, [x1]
        add     x2, x2, #0x5
        add     x1, x1, #0x8
        sub     w3, w8, w3
        sub     w5, w8, w5
        sturb   w3, [x2, #-5]
        lsr     w4, w3, #8
        sturb   w4, [x2, #-4]
        ubfiz   w4, w5, #4, #4
        ubfx    x7, x5, #4, #8
        orr     w4, w4, w3, lsr #16
        ubfx    x6, x5, #12, #8
        and     w4, w4, #0xff
        sturb   w4, [x2, #-3]
        sturb   w7, [x2, #-2]
        sturb   w6, [x2, #-1]
        cmp     x9, x2
        b.ne    L7ff4
        add     x1, x0, #0x200
        stp     w3, w5, [sp, #24]
        sturh   w3, [x1, #123]
        mov     x1, #0x10
        strb    w4, [x0, #637]
        strb    w7, [x0, #638]
        strb    w6, [x0, #639]
        add     x0, sp, #0x18
        bl      L78d8
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8080
        bl      L0e70
L8080:
        ldr     x30, [sp], #48
        ret

// mldsa87_polyz_unpack (0x70 bytes)
L8088:
        add     x6, x0, #0x400
        mov     w5, #0x80000
L8090:
        ldrb    w2, [x1]
        add     x0, x0, #0x8
        stur    w2, [x0, #-8]
        add     x1, x1, #0x5
        ldurb   w3, [x1, #-4]
        orr     w3, w2, w3, lsl #8
        stur    w3, [x0, #-8]
        ldurb   w2, [x1, #-3]
        orr     w2, w3, w2, lsl #16
        and     w2, w2, #0xfffff
        stur    w2, [x0, #-8]
        sub     w2, w5, w2
        ldurb   w3, [x1, #-3]
        lsr     w3, w3, #4
        stur    w3, [x0, #-4]
        ldurb   w4, [x1, #-2]
        orr     w4, w3, w4, lsl #4
        stur    w4, [x0, #-4]
        ldurb   w3, [x1, #-1]
        stur    w2, [x0, #-8]
        orr     w3, w4, w3, lsl #12
        sub     w2, w5, w3
        stur    w2, [x0, #-4]
        cmp     x0, x6
        b.ne    L8090
        ret

// mldsa87_poly_uniform_gamma1_4x (0x17c bytes)
L80f8:
        mov     x12, #0x1020
        sub     sp, sp, x12
        stp     x19, x20, [sp]
        add     x19, sp, #0x7f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x20, x19, #0xb00
        add     x21, x19, #0xb60
        stp     x23, x24, [sp, #32]
        mov     x24, x1
        mov     x23, x2
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        add     x26, x19, #0xbc0
        stp     x27, x28, [sp, #64]
        add     x27, x19, #0xc20
        add     x28, sp, #0xcf8
        str     x30, [sp, #80]
        mov     x22, x3
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q0, q1, [x4, #32]
        ldr     x1, [x0]
        str     x1, [sp, #4120]
        mov     x1, #0x0
        ldp     q2, q3, [x4]
        stp     q0, q1, [x21, #32]
        stp     q0, q1, [x26, #32]
        stp     q0, q1, [x20, #32]
        stp     q2, q3, [x21]
        stp     q2, q3, [x26]
        stp     q2, q3, [x27]
        stp     q2, q3, [x20]
        stp     q0, q1, [x27, #32]
        ldrh    w0, [sp, #4128]
        strh    w5, [x19, #2880]
        strh    w6, [x19, #2976]
        strh    w7, [x19, #3072]
        strh    w0, [x19, #3168]
        mov     x0, x28
        bl      L1568
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1484
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14e8
        mov     x1, x19
        mov     x0, x25
        bl      L8088
        mov     x1, x27
        mov     x0, x24
        bl      L8088
        mov     x1, x26
        mov     x0, x23
        bl      L8088
        mov     x1, x21
        mov     x0, x22
        bl      L8088
        mov     x0, x28
        bl      L156c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L78d8
        mov     x0, x20
        mov     x1, #0x180
        bl      L78d8
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8250
        bl      L0e70
L8250:
        ldp     x19, x20, [sp]
        mov     x12, #0x1020
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mldsa87_polyvecl_uniform_gamma1 (0x90 bytes)
L8274:
        sub     sp, sp, #0x40
        mov     w5, w2
        stp     x21, x22, [sp, #32]
        mov     x21, x1
        mov     w1, #0xff
        strh    w1, [sp]
        add     x22, x0, #0xc00
        stp     x19, x20, [sp, #16]
        sxth    w20, w2
        mov     x19, x0
        add     w7, w20, #0x2
        add     w6, w20, #0x1
        mov     x4, x21
        mov     x3, x22
        add     x2, x0, #0x800
        add     x1, x0, #0x400
        str     x30, [sp, #48]
        bl      L80f8
        add     w7, w20, #0x5
        add     w6, w20, #0x4
        add     w5, w20, #0x3
        add     w20, w20, #0x6
        strh    w20, [sp]
        mov     x0, #0x1800
        mov     x1, #0x1400
        add     x3, x19, x0
        add     x2, x19, x1
        mov     x4, x21
        add     x1, x19, #0x1, lsl #12
        mov     x0, x22
        bl      L80f8
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, #0x40
        ret

// mldsa87_polyvecl_ntt (0x34 bytes)
L8304:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1c00
        add     x20, x19, x0
        str     x30, [sp, #16]
L8318:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20d0
        cmp     x19, x20
        b.ne    L8318
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L8338:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L8348:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L8354:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x7
        b.ne    L8354
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L8348
        ret

// mldsa87_polyvecl_chknorm (0x50 bytes)
L8390:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1c00
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
L83b0:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L28c8
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L83b0
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyveck_caddq (0x30 bytes)
L83e0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L83f0:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L202c
        cmp     x19, x20
        b.ne    L83f0
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_ntt (0x30 bytes)
L8410:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L8420:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20d0
        cmp     x19, x20
        b.ne    L8420
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_invntt_tomont (0x30 bytes)
L8440:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L8450:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2178
        cmp     x19, x20
        b.ne    L8450
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta_chknorm (0x5c bytes)
L8470:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L8490:
        mov     x1, x19
        mov     x0, x20
        bl      L7f10
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L28c8
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L8490
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyveck_decompose_pack_w1 (0x54 bytes)
L84cc:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, #0x2, lsl #12
        str     x30, [sp, #32]
L84e8:
        mov     x1, x19
        mov     x0, x21
        bl      L797c
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2970
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L84e8
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyvecl_unpack_eta (0x40 bytes)
L8520:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1c00
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L8538:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L7f10
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L8538
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvecl_unpack_z (0x40 bytes)
L8560:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1c00
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L8578:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L8088
        add     x20, x20, #0x280
        cmp     x19, x21
        b.ne    L8578
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta (0x3c bytes)
L85a0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x2, lsl #12
L85b4:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L7f10
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L85b4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvec_matrix_expand_eager (0x11c bytes)
L85dc:
        stp     x19, x20, [sp, #-336]!
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x21, sp, #0x4f
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #32]
        and     x21, x21, #0xffffffffffffffe0
        ldr     x2, [x0]
        str     x2, [sp, #328]
        mov     x2, #0x0
        mov     x0, x21
L860c:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L860c
        mov     w20, #0x0
        mov     w19, #0x7
L862c:
        mov     x1, x21
        mov     w0, #0x0
L8634:
        add     w2, w20, w0
        add     w0, w0, #0x1
        add     x1, x1, #0x40
        udiv    w3, w2, w19
        msub    w2, w3, w19, w2
        sturb   w3, [x1, #-31]
        sturb   w2, [x1, #-32]
        cmp     w0, #0x4
        b.ne    L8634
        add     w2, w20, #0x3
        add     w1, w20, #0x2
        add     w0, w20, #0x1
        udiv    w3, w2, w19
        msub    w2, w3, w19, w2
        umaddl  x3, w3, w19, x2
        udiv    w2, w1, w19
        add     x3, x22, x3, lsl #10
        msub    w1, w2, w19, w1
        umaddl  x2, w2, w19, x1
        udiv    w1, w0, w19
        add     x2, x22, x2, lsl #10
        msub    w0, w1, w19, w0
        umaddl  x1, w1, w19, x0
        udiv    w0, w20, w19
        add     x1, x22, x1, lsl #10
        msub    w4, w0, w19, w20
        add     w20, w20, #0x4
        umaddl  x0, w0, w19, x4
        mov     x4, x21
        add     x0, x22, x0, lsl #10
        bl      L23b8
        cmp     w20, #0x38
        b.ne    L862c
        mov     x0, x21
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e80
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L86e8
        bl      L0e70
L86e8:
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret

// mldsa87_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L86f8:
        mov     w4, #0x1c00
        umaddl  x1, w3, w4, x1
        b       L8338

// mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L8704:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x3
        mov     x19, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x1
        mov     x1, x2
        mov     x2, #0x1c00
        mov     x21, x0
        mov     x0, x3
        str     x30, [sp, #32]
        bl      L0e50
        mov     x0, x20
        bl      L8304
L8738:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L86f8
        cmp     x19, #0x8
        b.ne    L8738
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L8440

// mld_ct_memcmp (0x54 bytes)
L876c:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L8778:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L87a0
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L87a0:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L8778

// mld_zeroize (0x1c bytes)
L87c0:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t187 (0x168 bytes)
L87dc:
        mov     x12, #0xe890
        sub     sp, sp, x12
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x3
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x8f
        stp     x21, x22, [sp, #16]
        and     x20, x20, #0xffffffffffffffe0
        mov     x3, #0xe400
        stp     x25, x26, [sp, #48]
        mov     x22, x1
        mov     x1, x4
        stp     x27, x28, [sp, #64]
        mov     x4, #0xc010
        add     x19, x20, x3
        str     x30, [sp, #80]
        add     x21, x20, #0xe, lsl #12
        str     x2, [sp, #104]
        add     x2, sp, x4
        mov     x25, #0x0
        mov     x28, #0x60
        ldr     x3, [x0]
        str     x3, [x2, #10360]
        mov     x3, #0x0
        mov     x27, #0x140
        mov     x0, x20
        mov     x26, #0x1a0
        bl      L85dc
L8858:
        ldr     x2, [sp, #104]
        mov     w3, w25
        mov     x1, x20
        mov     x0, x19
        bl      L86f8
        mov     x0, x19
        bl      L2178
        madd    x1, x25, x28, x24
        mov     x0, x21
        bl      L7f10
        mov     x1, x21
        mov     x0, x19
        bl      L2068
        mov     x0, x19
        bl      L2000
        mov     x0, x19
        bl      L202c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x21
        bl      L2294
        madd    x0, x25, x27, x23
        mov     x1, x21
        bl      L2594
        madd    x0, x25, x26, x22
        mov     x1, x19
        add     x25, x25, #0x1
        bl      L2660
        cmp     x25, #0x8
        b.ne    L8858
        mov     x0, x21
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x19
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x20
        mov     x1, #0xe000
        bl      L87c0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x1, #0xc010
        add     x2, sp, x1
        ldr     x3, [x2, #10360]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L891c
        bl      L0e70
L891c:
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0xe890
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// mld_H87.constprop.0 (0xec bytes)
L8944:
        stp     x19, x20, [sp, #-304]!
        mov     x20, x6
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x19, sp, #0x58
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        mov     x21, x4
        stp     x25, x26, [sp, #48]
        mov     x25, x1
        mov     x26, x2
        str     x30, [sp, #64]
        mov     x24, x3
        mov     x23, x5
        ldr     x1, [x0]
        str     x1, [sp, #296]
        mov     x1, #0x0
        mov     x0, x19
        bl      L10a8
        mov     x2, x26
        mov     x1, x25
        mov     x0, x19
        bl      L10c8
        cbz     x21, L89b8
        mov     x2, x21
        mov     x1, x24
        mov     x0, x19
        bl      L10c8
L89b8:
        cbz     x20, L89cc
        mov     x2, x20
        mov     x1, x23
        mov     x0, x19
        bl      L10c8
L89cc:
        mov     x0, x19
        bl      L10f0
        mov     x2, x19
        mov     x1, #0x40
        mov     x0, x22
        bl      L1170
        mov     x0, x19
        bl      L1190
        mov     x0, x19
        mov     x1, #0xd0
        bl      L87c0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8a18
        bl      L0e70
L8a18:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa87_keypair_internal (0x304 bytes)
L8a30:
        mov     x12, #0x1da0
        sub     sp, sp, x12
        mov     x3, #0x1c00
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0xaf
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        mov     x20, x1
        mov     x22, x0
        stp     x23, x24, [sp, #48]
        mov     x1, #0x1cc0
        add     x21, x19, x3
        stp     x25, x26, [sp, #64]
        add     x26, x19, x1
        add     x23, x19, #0xc00
        stp     x27, x28, [sp, #80]
        add     x24, x19, #0x800
        add     x27, x21, #0x20
        str     x30, [sp, #96]
        mov     x3, #0x22
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x25, x19, #0x400
        ldp     q0, q1, [x2]
        ldr     x1, [x0]
        str     x1, [sp, #7576]
        mov     x1, #0x0
        mov     w0, #0x708
        mov     x2, x26
        mov     x1, #0x80
        add     x28, x20, #0x320
        stp     q0, q1, [x26]
        strh    w0, [x19, #7392]
        mov     x0, x21
        bl      L1194
        mov     x3, x23
        mov     x2, x24
        mov     x4, x27
        mov     w0, #0xe
        strb    w0, [sp]
        mov     w7, #0xd
        mov     w6, #0xc
        mov     w5, #0xb
        mov     x1, x25
        mov     x0, x19
        bl      L7a48
        mov     x1, x19
        add     x0, x20, #0x4a0
        bl      L7dd4
        mov     x1, x25
        add     x0, x20, #0x500
        bl      L7dd4
        mov     x1, x24
        add     x0, x20, #0x560
        bl      L7dd4
        mov     x1, x23
        add     x0, x20, #0x5c0
        bl      L7dd4
        mov     x3, x23
        mov     x2, x24
        mov     x4, x27
        mov     w0, #0xa
        strb    w0, [sp]
        mov     w7, #0x9
        mov     w6, #0x8
        mov     w5, #0x7
        mov     x1, x25
        mov     x0, x19
        bl      L7a48
        mov     x1, x19
        mov     x0, x28
        bl      L7dd4
        mov     x1, x25
        add     x0, x20, #0x380
        bl      L7dd4
        mov     x1, x24
        add     x0, x20, #0x3e0
        bl      L7dd4
        mov     x1, x23
        add     x0, x20, #0x440
        bl      L7dd4
        mov     x5, #0x1400
        add     x8, x19, x5
        mov     w1, #0xffffffff
        strb    w1, [sp]
        mov     x4, #0x1800
        mov     x3, x19
        add     x2, x19, x4
        mov     w7, #0x6
        mov     x4, x27
        mov     w6, #0x5
        mov     w5, #0x4
        mov     x1, x8
        add     x0, x19, #0x1, lsl #12
        stp     x0, x8, [sp, #120]
        str     x2, [sp, #136]
        bl      L7a48
        ldr     x0, [sp, #120]
        mov     x1, x0
        add     x0, x20, #0x200
        bl      L7dd4
        ldr     x8, [sp, #128]
        add     x0, x20, #0x260
        mov     x1, x8
        bl      L7dd4
        ldr     x2, [sp, #136]
        add     x0, x20, #0x2c0
        mov     x1, x2
        bl      L7dd4
        mov     x3, x23
        mov     x2, x24
        mov     x4, x27
        mov     w0, #0x3
        strb    w0, [sp]
        mov     w6, #0x1
        mov     w7, #0x2
        mov     w5, #0x0
        mov     x1, x25
        mov     x0, x19
        bl      L7a48
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L7dd4
        mov     x1, x25
        add     x0, x20, #0xe0
        bl      L7dd4
        mov     x1, x24
        add     x0, x20, #0x140
        bl      L7dd4
        mov     x1, x23
        add     x0, x20, #0x1a0
        bl      L7dd4
        mov     x0, x19
        bl      L8304
        ldp     q0, q1, [x21]
        mov     x4, x21
        mov     x3, x28
        mov     x2, x19
        add     x1, x20, #0x620
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L87dc
        mov     x6, #0x1c80
        mov     w23, w0
        add     x24, x19, x6
        cbnz    w0, L8ca0
        mov     x2, x22
        mov     x0, x24
        mov     x3, #0xa20
        mov     x1, #0x40
        bl      L1194
        add     x3, x21, #0x60
        mov     x2, x24
        mov     x1, x21
        mov     x0, x20
        bl      L75c4
L8ca0:
        mov     x0, x19
        mov     x1, #0x1c00
        bl      L87c0
        mov     x0, x24
        mov     x1, #0x40
        bl      L87c0
        mov     x0, x26
        mov     x1, #0x22
        bl      L87c0
        mov     x0, x21
        mov     x1, #0x80
        bl      L87c0
        cbz     w23, L8cec
        mov     x0, x22
        mov     x1, #0xa20
        bl      L87c0
        mov     x0, x20
        mov     x1, #0x1320
        bl      L87c0
L8cec:
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7576]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8d0c
        bl      L0e70
L8d0c:
        ldp     x19, x20, [sp, #16]
        mov     w0, w23
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x1da0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret

// mldsa87_keypair (0x94 bytes)
L8d34:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #88]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e60
        cbnz    w0, L8db0
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L8a30
        mov     w20, w0
L8d84:
        mov     x0, x19
        mov     x1, #0x20
        bl      L87c0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8db8
        bl      L0e70
L8db0:
        mov     w20, #0xfffffffd
        b       L8d84
L8db8:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa87_signature_internal (0x434 bytes)
L8dc8:
        sub     sp, sp, #0x200
        sub     sp, sp, #0x1a, lsl #12
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x4
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0xbf
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x21, x19, #0x1a, lsl #12
        stp     x25, x26, [sp, #48]
        mov     x26, x1
        add     x1, sp, #0x18, lsl #12
        stp     x27, x28, [sp, #64]
        add     x1, x1, #0x40
        mov     x25, x2
        str     x30, [sp, #80]
        add     x28, x21, #0x20
        add     x4, x19, #0x17, lsl #12
        mov     x22, x3
        ldr     x2, [x0]
        str     x2, [x1, #8632]
        mov     x2, #0x0
        add     x0, x19, #0x10, lsl #12
        str     x0, [sp, #128]
        add     x0, x19, #0x17, lsl #12
        add     x0, x0, #0x800
        str     x0, [sp, #136]
        add     x0, x19, #0x12, lsl #12
        mov     x20, x5
        mov     x3, x0
        mov     w27, w7
        add     x5, x19, #0x10, lsl #12
        add     x4, x4, #0x800
        add     x2, x21, #0x60
        mov     x1, x28
        str     x0, [sp, #144]
        mov     x0, x21
        bl      L75ec
        add     x0, x21, #0x80
        cbnz    w27, L90cc
        mov     x6, x25
        mov     x5, x26
        mov     x4, x24
        mov     x3, x22
        mov     x1, x28
        mov     x2, #0x40
        bl      L8944
L8e90:
        mov     x4, #0x20
        add     x5, x21, #0x80
        mov     x3, x20
        mov     x2, x4
        mov     x6, #0x40
        add     x1, x21, #0x60
        add     x0, x21, #0xc0
        bl      L8944
        mov     x0, x19
        mov     x1, x21
        bl      L85dc
        add     x27, x19, #0x15, lsl #12
        add     x0, x19, #0x19, lsl #12
        add     x24, x19, #0x19, lsl #12
        add     x0, x0, #0xc00
        add     x27, x27, #0xc00
        add     x24, x24, #0x800
        str     x0, [sp, #104]
        add     x0, x19, #0x1a, lsl #12
        str     wzr, [sp, #124]
        add     x0, x0, #0x100
        str     x0, [sp, #112]
L8ee8:
        ldrh    w2, [sp, #124]
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0x14, lsl #12
        add     x25, x19, #0xe, lsl #12
        add     x22, x19, #0x19, lsl #12
        mov     w26, #0xff88
        add     x22, x22, #0x400
        bl      L8274
        mov     x28, #0x0
        mov     x3, x20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x25
        bl      L8704
        movk    w26, #0x7, lsl #16
        mov     x0, x25
        bl      L83e0
        ldr     x0, [sp, #104]
        mov     x2, x20
        mov     x1, x25
        bl      L84cc
        ldp     x3, x0, [sp, #104]
        add     x1, x21, #0x80
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x400
        mov     x2, #0x40
        bl      L8944
        ldr     x1, [sp, #112]
        mov     x0, x24
        bl      L7c74
        mov     x0, x24
        bl      L20d0
L8f70:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e50
        mov     x1, x24
        mov     x0, x22
        bl      L2258
        mov     x0, x22
        bl      L2178
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x3, x27
        bl      L0e50
        mov     x1, x20
        mov     x0, x22
        bl      L2068
        mov     x0, x22
        bl      L2000
        mov     w1, w26
        mov     x0, x22
        bl      L28c8
        cbnz    w0, L90e0
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L7790
        cmp     x28, #0x7
        b.ne    L8f70
        mov     x26, #0x0
L8ff8:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x25, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e50
        mov     x1, x24
        mov     x0, x20
        bl      L2258
        mov     x0, x20
        bl      L2178
        mov     x1, x20
        mov     x0, x28
        bl      L208c
        mov     x0, x28
        bl      L2000
        mov     w1, #0xfe88
        mov     x0, x28
        movk    w1, #0x3, lsl #16
        bl      L28c8
        cbnz    w0, L90e0
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e50
        mov     x1, x24
        mov     x0, x20
        bl      L2258
        mov     x0, x20
        bl      L2178
        mov     x0, x20
        bl      L2000
        mov     x0, x20
        mov     w1, #0x3ff00
        bl      L28c8
        cbnz    w0, L90e0
        mov     x1, x20
        mov     x0, x28
        add     x26, x26, #0x400
        bl      L2068
        cmp     x26, #0x2, lsl #12
        b.ne    L8ff8
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L7694
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x25
        mov     x0, x23
        bl      L76a8
        mov     w26, w0
        b       L90e4
L90cc:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L8e90
L90e0:
        mov     w26, #0xffffffff
L90e4:
        mov     x0, x22
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x24
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x25
        mov     x1, #0x2000
        bl      L87c0
        ldr     x0, [sp, #104]
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x20
        mov     x1, #0x1c00
        bl      L87c0
        mov     x0, x27
        mov     x1, #0x1c00
        bl      L87c0
        ldr     x0, [sp, #112]
        mov     x1, #0x40
        bl      L87c0
        cbz     w26, L9170
        cmn     w26, #0x1
        b.ne    L9164
        ldr     w0, [sp, #124]
        add     w0, w0, #0x7
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfff7
        cmp     w1, w0, uxth
        b.ne    L8ee8
        mov     w26, #0xfffffffc
L9164:
        mov     x0, x23
        mov     x1, #0x1213
        bl      L87c0
L9170:
        ldr     x0, [sp, #128]
        mov     x1, #0x2000
        bl      L87c0
        ldr     x0, [sp, #144]
        mov     x1, #0x2000
        bl      L87c0
        ldr     x0, [sp, #136]
        mov     x1, #0x1c00
        bl      L87c0
        mov     x0, x19
        mov     x1, #0xe000
        bl      L87c0
        mov     x0, x21
        mov     x1, #0x100
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x18, lsl #12
        add     x2, x2, #0x40
        ldr     x3, [x2, #8632]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L91d4
        bl      L0e70
L91d4:
        ldp     x19, x20, [sp]
        mov     w0, w26
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x200
        add     sp, sp, #0x1a, lsl #12
        ret

// mldsa87_signature_extmu (0xb4 bytes)
L91fc:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        mov     x22, x2
        ldr     x1, [x0]
        str     x1, [sp, #104]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e60
        cbnz    w0, L9294
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L8dc8
        mov     w20, w0
L9268:
        mov     x0, x19
        mov     x1, #0x20
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L929c
        bl      L0e70
L9294:
        mov     w20, #0xfffffffd
        b       L9268
L929c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa87_verify_internal (0x30c bytes)
L92b0:
        sub     sp, sp, #0xd70
        mov     x7, #0xfc00
        sub     sp, sp, #0x10, lsl #12
        stp     x19, x20, [sp]
        add     x19, sp, #0xaf
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        add     x24, x19, #0x10, lsl #12
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x22, x19, x7
        stp     x25, x26, [sp, #48]
        mov     x25, x1
        add     x26, x19, #0x10, lsl #12
        stp     x27, x28, [sp, #64]
        add     x1, sp, #0x10, lsl #12
        add     x1, x1, #0x30
        str     x30, [sp, #80]
        add     x26, x26, #0xc00
        stp     x2, x5, [sp, #96]
        add     x27, x19, #0xe, lsl #12
        add     x28, x19, #0x10, lsl #12
        stp     x3, x4, [sp, #120]
        add     x24, x24, #0x800
        add     x28, x28, #0x400
        str     w6, [sp, #140]
        add     x21, x19, #0x10, lsl #12
        ldp     q0, q1, [x23]
        ldr     x2, [x0]
        str     x2, [x1, #3384]
        mov     x2, #0x0
        add     x0, x26, #0x40
        add     x1, x23, #0x40
        stp     q0, q1, [x0]
        ldp     q0, q1, [x23, #32]
        stp     q0, q1, [x0, #32]
        mov     x0, x27
        bl      L8560
        mov     w1, #0xff88
        mov     x0, x27
        movk    w1, #0x7, lsl #16
        bl      L8390
        mov     w20, w0
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0xc40
        str     x0, [sp, #112]
        cbnz    w20, L94e0
        ldr     w6, [sp, #140]
        cbnz    w6, L957c
        ldr     x1, [sp, #104]
        mov     x0, x24
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0xa20
        bl      L8944
        ldp     x3, x4, [sp, #120]
        mov     x5, x25
        ldr     x6, [sp, #96]
        add     x0, x19, #0x10, lsl #12
        mov     x2, #0x40
        mov     x1, x24
        add     x0, x0, #0xc80
        bl      L8944
        mov     x0, x24
        mov     x1, #0x40
        bl      L87c0
L93c8:
        mov     x0, x27
        bl      L8304
        ldr     x1, [sp, #104]
        mov     x0, x19
        bl      L85dc
        add     x1, x19, #0x10, lsl #12
        mov     x0, x28
        add     x1, x1, #0xc40
        bl      L7c74
        mov     x0, x28
        bl      L20d0
        str     x24, [sp, #96]
L93f8:
        mov     w3, w20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x21
        bl      L86f8
        ldr     x1, [sp, #104]
        mov     w2, w20
        mov     x0, x22
        bl      L75b0
        mov     x0, x22
        bl      L20b0
        mov     x0, x22
        bl      L20d0
        mov     x1, x28
        mov     x0, x22
        bl      L2258
        mov     x1, x22
        mov     x0, x21
        bl      L208c
        mov     x0, x21
        bl      L2000
        mov     x0, x21
        bl      L2178
        mov     x0, x21
        bl      L202c
        mov     w2, w20
        mov     x1, x23
        mov     x0, x22
        bl      L77a4
        mov     w25, w0
        cbnz    w0, L94e0
        mov     x1, x22
        mov     x0, x21
        bl      L79b0
        add     w20, w20, #0x1
        ldr     x0, [sp, #96]
        mov     x1, x21
        bl      L2970
        ldr     x0, [sp, #96]
        add     x0, x0, #0x80
        str     x0, [sp, #96]
        cmp     w20, #0x8
        b.ne    L93f8
        add     x1, x19, #0x10, lsl #12
        mov     x0, x26
        add     x1, x1, #0xc80
        mov     x2, #0x40
        mov     x3, x24
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x400
        bl      L8944
        ldr     x0, [sp, #112]
        mov     x1, x26
        mov     x2, #0x40
        bl      L876c
        tst     w0, #0xff
        b.eq    L94e4
L94e0:
        mov     w25, #0xfffffffa
L94e4:
        mov     x0, x22
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x21
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x19
        mov     x1, #0xe000
        bl      L87c0
        mov     x0, x28
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x27
        mov     x1, #0x1c00
        bl      L87c0
        mov     x0, x26
        mov     x1, #0x40
        bl      L87c0
        ldr     x0, [sp, #112]
        mov     x1, #0x40
        bl      L87c0
        add     x0, x19, #0x10, lsl #12
        mov     x1, #0x40
        add     x0, x0, #0xc80
        bl      L87c0
        mov     x0, x24
        mov     x1, #0x400
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x10, lsl #12
        add     x2, x2, #0x30
        ldr     x3, [x2, #3384]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L9594
        bl      L0e70
L957c:
        ldp     q0, q1, [x25]
        add     x0, x26, #0x80
        stp     q0, q1, [x0]
        ldp     q0, q1, [x25, #32]
        stp     q0, q1, [x0, #32]
        b       L93c8
L9594:
        ldp     x19, x20, [sp]
        mov     w0, w25
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0xd70
        add     sp, sp, #0x10, lsl #12
        ret

// mldsa87_verify_extmu (0x18 bytes)
L95bc:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L92b0

// mldsa87_prepare_domain_separation_prefix (0x138 bytes)
L95d4:
        cmp     x4, #0xff
        b.hi    L96fc
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L96c0
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L9704
        .inst   0xb0000000  // adrp x0, 0xa000
        add     x0, x0, #0x410
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 9628 <mldsa87_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L962c:
        b.ne    L9704
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L964c
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e50
L964c:
        .inst   0xb0000000  // adrp x0, 0xa000
        add     x0, x0, #0x41c
        mov     x1, #0x0
L9658:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L96ec
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L9688:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e50
        add     x0, x20, x19
        b       L96dc
        cmp     x20, #0x20
        b       L962c
        cmp     x20, #0x30
        b       L962c
        cmp     x20, #0x40
        b       L962c
L96c0:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L96d8
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e50
L96d8:
        add     x0, x19, #0x2
L96dc:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L96ec:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L9658
        b       L9688
L96fc:
        mov     x0, #0x0
        ret
L9704:
        mov     x0, #0x0
        b       L96dc

// mldsa87_signature (0x100 bytes)
L970c:
        stp     x19, x20, [sp, #-480]!
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        add     x20, sp, #0x5f
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x23, x24, [sp, #32]
        and     x20, x20, #0xffffffffffffffe0
        stp     x25, x30, [sp, #48]
        mov     x23, x1
        mov     x24, x2
        ldr     x1, [x0]
        str     x1, [sp, #472]
        mov     x1, #0x0
        mov     x25, x5
        mov     x0, x20
        mov     w5, #0x0
        mov     x2, #0x0
        add     x22, x20, #0x160
        bl      L95d4
        cbz     x0, L97e4
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e60
        cbnz    w0, L97ec
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L8dc8
        mov     w19, w0
        cbz     w0, L97ac
L97a0:
        mov     x0, x21
        mov     x1, #0x1213
        bl      L87c0
L97ac:
        mov     x0, x22
        mov     x1, #0x20
        bl      L87c0
        mov     x0, x20
        mov     x1, #0x14c
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L97f4
        bl      L0e70
L97e4:
        mov     w19, #0xfffffff7
        b       L97a0
L97ec:
        mov     w19, #0xfffffffd
        b       L97a0
L97f4:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa87_verify (0xbc bytes)
L980c:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x5
        .inst   0xd00000a5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        mov     x21, x0
        and     x19, x19, #0xffffffffffffffe0
        ldr     x0, [x5]
        str     x0, [sp, #408]
        mov     x0, #0x0
        mov     x22, x1
        mov     x23, x2
        mov     x0, x19
        mov     w5, #0x0
        mov     x2, #0x0
        mov     x1, #0x0
        bl      L95d4
        cbz     x0, L98ac
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L92b0
        mov     w20, w0
L9880:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L98b4
        bl      L0e70
L98ac:
        mov     w20, #0xfffffff7
        b       L9880
L98b4:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa87_signature_pre_hash_internal (0xc8 bytes)
L98c8:
        stp     x19, x20, [sp, #-416]!
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     x22, x6
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #32]
        add     x20, sp, #0x4f
        ldr     x6, [x0]
        str     x6, [sp, #408]
        mov     x6, #0x0
        and     x20, x20, #0xffffffffffffffe0
        cbnz    w7, L9910
L98fc:
        mov     w19, #0xfffffff7
L9900:
        mov     x0, x21
        mov     x1, #0x1213
        bl      L87c0
        b       L9950
L9910:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L95d4
        mov     x2, x0
        cbz     x0, L98fc
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L8dc8
        mov     w19, w0
        cbnz    w0, L9900
L9950:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L997c
        bl      L0e70
L997c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa87_signature_pre_hash_shake256 (0xc0 bytes)
L9990:
        stp     x19, x20, [sp, #-160]!
        mov     x20, x0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x3
        str     x30, [sp, #48]
        mov     x22, x4
        mov     x23, x5
        mov     x24, x6
        ldr     x3, [x0]
        str     x3, [sp, #152]
        mov     x3, #0x0
        mov     x0, x19
        mov     x3, x2
        mov     x2, x1
        mov     x1, #0x40
        bl      L1194
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L98c8
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9a38
        bl      L0e70
L9a38:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa87_verify_pre_hash_internal (0xa8 bytes)
L9a50:
        stp     x19, x20, [sp, #-400]!
        mov     x20, x0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        ldr     x6, [x0]
        str     x6, [sp, #392]
        mov     x6, #0x0
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        cbnz    w5, L9ab4
L9a84:
        mov     w20, #0xfffffff7
L9a88:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9ae8
        bl      L0e70
L9ab4:
        mov     x0, x19
        bl      L95d4
        mov     x2, x0
        cbz     x0, L9a84
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L92b0
        mov     w20, w0
        b       L9a88
L9ae8:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa87_verify_pre_hash_shake256 (0xb0 bytes)
L9af8:
        stp     x19, x20, [sp, #-144]!
        mov     x20, x0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x3
        ldr     x3, [x0]
        str     x3, [sp, #136]
        mov     x3, #0x0
        mov     x22, x4
        mov     x3, x2
        mov     x23, x5
        mov     x2, x1
        mov     x0, x19
        mov     x1, #0x40
        bl      L1194
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L9a50
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9b94
        bl      L0e70
L9b94:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa87_pk_from_sk (0x20c bytes)
L9ba8:
        mov     x12, #0x2e50
        sub     sp, sp, x12
        mov     x5, #0x2c00
        mov     x3, #0x1c00
        mov     x4, #0x2d40
        mov     x2, #0x2da0
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x25, x26, [sp, #48]
        mov     x25, x1
        stp     x19, x20, [sp]
        add     x19, sp, #0x8f
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x23, x1, #0x320
        mov     x1, #0x2900
        stp     x27, x28, [sp, #64]
        add     x28, x19, x1
        add     x24, x19, x3
        str     x30, [sp, #80]
        add     x27, x19, x4
        add     x26, x19, x2
        ldp     q0, q1, [x25]
        ldr     x1, [x0]
        str     x1, [sp, #11848]
        mov     x1, #0x0
        add     x0, x19, x5
        add     x1, x25, #0x40
        add     x22, x0, #0x1a0
        stp     q0, q1, [x22]
        ldp     q0, q1, [x25, #32]
        stp     q0, q1, [x0, #384]
        add     x0, x0, #0x140
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x1, #32]
        add     x1, x25, #0x80
        stp     q0, q1, [x0, #32]
        mov     x0, x19
        bl      L8520
        mov     w1, #0x3
        mov     x0, x19
        bl      L8390
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x3
        mov     x0, x23
        bl      L8470
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L8304
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L87dc
        mov     x6, #0x2d00
        mov     w22, w0
        add     x23, x19, x6
        cbnz    w0, L9d08
        add     x1, x25, #0x620
        mov     x0, x24
        mov     x2, #0xd00
        bl      L876c
        and     w4, w0, #0xff
        mov     x3, #0xa20
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1194
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L876c
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L9d14
        mov     w22, #0xfffffff9
L9d08:
        mov     x0, x21
        mov     x1, #0xa20
        bl      L87c0
L9d14:
        mov     x0, x24
        mov     x1, #0xd00
        bl      L87c0
        mov     x0, x28
        mov     x1, #0x400
        bl      L87c0
        mov     x0, x19
        mov     x1, #0x1c00
        bl      L87c0
        mov     x1, #0x20
        mov     x0, #0x2d80
        add     x0, x19, x0
        bl      L87c0
        mov     x0, x23
        mov     x1, #0x40
        bl      L87c0
        mov     x0, x27
        mov     x1, #0x40
        bl      L87c0
        mov     x0, x26
        mov     x1, #0x20
        bl      L87c0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #11848]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9d8c
        bl      L0e70
L9d8c:
        ldp     x19, x20, [sp]
        mov     w0, w22
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x2e50
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret

// Padding (0x9db4 to 0x9db8)

        .long   0x00000000

// The read-only data (0x9db8 to 0xa4dc)

// mld_KeccakF_RoundConstants (0xc0 bytes)
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
        .quad   0x2000200024222000
        .long   0x24202422
// oid_map.0 (0xc0 bytes)
        .long   0x00000001
        .quad   0x0365014886600906
        .quad   0x0000000200040204
        .quad   0x0365014886600906
        .quad   0x0000000300010204
        .quad   0x0365014886600906
        .quad   0x0000000400020204
        .quad   0x0365014886600906
        .quad   0x0000000500030204
        .quad   0x0365014886600906
        .quad   0x0000000600050204
        .quad   0x0365014886600906
        .quad   0x0000000700060204
        .quad   0x0365014886600906
        .quad   0x0000000800070204
        .quad   0x0365014886600906
        .quad   0x0000000900080204
        .quad   0x0365014886600906
        .quad   0x0000000a00090204
        .quad   0x0365014886600906
        .quad   0x0000000b000a0204
        .quad   0x0365014886600906
        .quad   0x0000000c000b0204
        .quad   0x0365014886600906
        .quad   0x24222000000c0204
        .quad   0x2420242220002000
// oid_map.0 (0xc0 bytes)
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
        .quad   0x2000200024222000
        .long   0x24202422
// oid_map.0 (0xc0 bytes)
        .long   0x00000001
        .quad   0x0365014886600906
        .quad   0x0000000200040204
        .quad   0x0365014886600906
        .quad   0x0000000300010204
        .quad   0x0365014886600906
        .quad   0x0000000400020204
        .quad   0x0365014886600906
        .quad   0x0000000500030204
        .quad   0x0365014886600906
        .quad   0x0000000600050204
        .quad   0x0365014886600906
        .quad   0x0000000700060204
        .quad   0x0365014886600906
        .quad   0x0000000800070204
        .quad   0x0365014886600906
        .quad   0x0000000900080204
        .quad   0x0365014886600906
        .quad   0x0000000a00090204
        .quad   0x0365014886600906
        .quad   0x0000000b000a0204
        .quad   0x0365014886600906
        .quad   0x0000000c000b0204
        .quad   0x0365014886600906
        .long   0x000c0204

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
