// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mldsa-native's libmldsa.so (gcc 12, -Os)
//
// This is a transcription of the binary
// binaries/aarch64/multilevel/gcc12/Os/libmldsa.so from the binary branch
// of mldsa-native (see README.md), as loaded at an address that is a
// multiple of 4096: the start of its first segment, from address 0 up to
// the end of the read-only data. The ELF header and dynamic linking
// information at the start are given as data, as are the padding and the
// read-only data at the end, while the procedure linkage table and the code
// are given as instructions. The ADRP instructions, which compute addresses
// of pages relative to that of the instruction, are given as words. The
// labels are named after the addresses in the binary.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_native_libmldsa_gcc12_Os)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_native_libmldsa_gcc12_Os)
        .text
        .balign 4

S2N_BN_SYMBOL(mldsa_native_libmldsa_gcc12_Os):

// ELF header and dynamic linking information (0x0 to 0xe20)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x000000000002d5f8
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000000000c428
        .quad   0x000000000000c428
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
        .quad   0x0000000000000e80
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
        .quad   0x000000000000625c
        .quad   0x0000000000000290
        .quad   0x00080012000001f2
        .quad   0x00000000000069cc
        .quad   0x00000000000000b4
        .quad   0x00080012000000f0
        .quad   0x00000000000047ac
        .quad   0x0000000000000100
        .quad   0x0008001200000082
        .quad   0x00000000000042a8
        .quad   0x00000000000000b4
        .quad   0x00080012000003f1
        .quad   0x00000000000098b8
        .quad   0x00000000000000c8
        .quad   0x0008001200000067
        .quad   0x0000000000003e70
        .quad   0x0000000000000438
        .quad   0x000800120000037a
        .quad   0x00000000000092a0
        .quad   0x000000000000030c
        .quad   0x0008001200000439
        .quad   0x0000000000009a40
        .quad   0x00000000000000a8
        .quad   0x0008001200000347
        .quad   0x0000000000008db8
        .quad   0x0000000000000434
        .quad   0x000800120000020a
        .quad   0x0000000000006a80
        .quad   0x0000000000000324
        .quad   0x00080012000002a5
        .quad   0x0000000000007178
        .quad   0x00000000000000c0
        .quad   0x000800120000031e
        .quad   0x0000000000008a20
        .quad   0x0000000000000304
        .quad   0x00080012000002ea
        .quad   0x00000000000072e0
        .quad   0x00000000000000b0
        .quad   0x0008001200000272
        .quad   0x0000000000006ff4
        .quad   0x00000000000000bc
        .quad   0x000800120000004b
        .quad   0x0000000000003ddc
        .quad   0x0000000000000094
        .quad   0x0008001200000111
        .quad   0x0000000000004968
        .quad   0x00000000000000c8
        .quad   0x0008001200000415
        .quad   0x0000000000009980
        .quad   0x00000000000000c0
        .quad   0x0008001200000392
        .quad   0x00000000000095ac
        .quad   0x0000000000000018
        .quad   0x00080012000000b2
        .quad   0x000000000000465c
        .quad   0x0000000000000018
        .quad   0x0008001200000102
        .quad   0x00000000000048ac
        .quad   0x00000000000000bc
        .quad   0x00080012000001d7
        .quad   0x0000000000006580
        .quad   0x000000000000044c
        .quad   0x0008001200000159
        .quad   0x0000000000004af0
        .quad   0x00000000000000a8
        .quad   0x00080012000003e2
        .quad   0x00000000000097fc
        .quad   0x00000000000000bc
        .quad   0x00080012000003d0
        .quad   0x00000000000096fc
        .quad   0x0000000000000100
        .quad   0x000800120000047b
        .quad   0x0000000000009b98
        .quad   0x000000000000020c
        .quad   0x000800120000019b
        .quad   0x0000000000004c48
        .quad   0x0000000000000208
        .quad   0x00080012000000c7
        .quad   0x0000000000004674
        .quad   0x0000000000000138
        .quad   0x0008001200000260
        .quad   0x0000000000006ef4
        .quad   0x0000000000000100
        .quad   0x0008001200000237
        .quad   0x0000000000006dbc
        .quad   0x0000000000000138
        .quad   0x0008001200000032
        .quad   0x0000000000003ba8
        .quad   0x0000000000000234
        .quad   0x00080012000003a7
        .quad   0x00000000000095c4
        .quad   0x0000000000000138
        .quad   0x0008001200000135
        .quad   0x0000000000004a30
        .quad   0x00000000000000c0
        .quad   0x0008001200000337
        .quad   0x0000000000008d24
        .quad   0x0000000000000094
        .quad   0x000800120000045a
        .quad   0x0000000000009ae8
        .quad   0x00000000000000b0
        .quad   0x0008001200000222
        .quad   0x0000000000006da4
        .quad   0x0000000000000018
        .quad   0x00080012000002c9
        .quad   0x0000000000007238
        .quad   0x00000000000000a8
        .quad   0x00080012000001c7
        .quad   0x00000000000064ec
        .quad   0x0000000000000094
        .quad   0x0008001200000281
        .quad   0x00000000000070b0
        .quad   0x00000000000000c8
        .quad   0x000800120000030b
        .quad   0x0000000000007390
        .quad   0x0000000000000210
        .quad   0x0008001200000362
        .quad   0x00000000000091ec
        .quad   0x00000000000000b4
        .quad   0x000800120000009a
        .quad   0x000000000000435c
        .quad   0x0000000000000300
        .quad   0x000800120000017a
        .quad   0x0000000000004b98
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
        .quad   0x622f706d742f006f
        .quad   0x32762d7972616e69
        .quad   0x69756265722d312e
        .quad   0x37446d76492e646c
        .quad   0x2d6173646c6d2f45
        .quad   0x762d65766974616e
        .quad   0x756f2f302e312e32
        .quad   0x756f2f7374757074
        .quad   0x00000062696c2f74
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

// The procedure linkage table and the code (0xe20 to 0x9da4)
// .plt
        stp     x16, x30, [sp, #-16]!
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4040]
        add     x16, x16, #0xfc8
        br      x17
        nop
        nop
        nop
L0e40:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4048]
        add     x16, x16, #0xfd0
        br      x17
L0e50:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4056]
        add     x16, x16, #0xfd8
        br      x17
L0e60:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4064]
        add     x16, x16, #0xfe0
        br      x17
L0e70:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4072]
        add     x16, x16, #0xfe8
        br      x17

// keccak_absorb (0x88 bytes)
L0e80:
        stp     x19, x20, [sp, #-64]!
        mov     w19, w1
        mov     x20, x4
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        mov     x21, x3
        stp     x23, x24, [sp, #32]
        mov     w23, w2
        str     x30, [sp, #48]
L0ea4:
        sub     w24, w23, w19
        sub     w3, w23, w19
        cmp     x24, x20
        b.ls    L0ee0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x21
        mov     x0, x22
        bl      L1584
        ldp     x21, x22, [sp, #16]
        add     w0, w19, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L0ee0:
        mov     w2, w19
        mov     x1, x21
        mov     x0, x22
        bl      L1584
        mov     x0, x22
        sub     x20, x20, x24
        add     x21, x21, x24
        mov     w19, #0x0
        bl      L16b0
        b       L0ea4

// keccak_squeeze (0x8c bytes)
L0f08:
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
L0f30:
        cbnz    x20, L0f4c
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L0f4c:
        cmp     w19, w22
        b.ne    L0f60
        mov     w19, #0x0
        mov     x0, x23
        bl      L16b0
L0f60:
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
        bl      L1560
        b       L0f30

// mldsa_shake128_init (0x20 bytes)
L0f94:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        mov     x2, #0xc8
        mov     w1, #0x0
        bl      L0e70
        str     wzr, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_absorb (0x28 bytes)
L0fb4:
        stp     x19, x30, [sp, #-16]!
        mov     x3, x1
        mov     x19, x0
        ldr     w1, [x0, #200]
        mov     x4, x2
        mov     w2, #0xa8
        bl      L0e80
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_finalize (0x80 bytes)
L0fdc:
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
        bl      L1584
        add     x1, sp, #0x16
        mov     x0, x19
        mov     w2, #0xa7
        mov     w3, #0x1
        bl      L1584
        mov     w0, #0xa8
        str     w0, [x19, #200]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1054
        bl      L0e60
L1054:
        ldp     x19, x30, [sp], #32
        ret

// mldsa_shake128_squeeze (0x20 bytes)
L105c:
        ldr     w3, [x2, #200]
        mov     w4, #0xa8
        stp     x19, x30, [sp, #-16]!
        mov     x19, x2
        bl      L0f08
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_release (0x1c bytes)

// mldsa_shake128_release.localalias (0x1c bytes)
L107c:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0xd0
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_init (0x20 bytes)
L1098:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        mov     x2, #0xc8
        mov     w1, #0x0
        bl      L0e70
        str     wzr, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_absorb (0x28 bytes)
L10b8:
        stp     x19, x30, [sp, #-16]!
        mov     x3, x1
        mov     x19, x0
        ldr     w1, [x0, #200]
        mov     x4, x2
        mov     w2, #0x88
        bl      L0e80
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_finalize (0x80 bytes)
L10e0:
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
        bl      L1584
        add     x1, sp, #0x16
        mov     x0, x19
        mov     w2, #0x87
        mov     w3, #0x1
        bl      L1584
        mov     w0, #0x88
        str     w0, [x19, #200]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1158
        bl      L0e60
L1158:
        ldp     x19, x30, [sp], #32
        ret

// mldsa_shake256_squeeze (0x20 bytes)
L1160:
        ldr     w3, [x2, #200]
        mov     w4, #0x88
        stp     x19, x30, [sp, #-16]!
        mov     x19, x2
        bl      L0f08
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_release (0x4 bytes)
L1180:
        b       L107c

// mldsa_shake256 (0x9c bytes)
L1184:
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
        bl      L1098
        mov     x2, x23
        mov     x1, x22
        mov     x0, x19
        bl      L10b8
        mov     x0, x19
        bl      L10e0
        mov     x2, x19
        mov     x1, x21
        mov     x0, x20
        bl      L1160
        mov     x0, x19
        bl      L1180
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #264]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1210
        bl      L0e60
L1210:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #272
        ret

// mld_keccak_absorb_once_x4.constprop.0 (0x150 bytes)
L1220:
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
L1274:
        add     x4, x27, x22
        add     x3, x26, x22
        add     x2, x25, x22
        add     x1, x24, x22
        add     x22, x22, x23
        cmp     x19, x23
        b.cs    L1304
        mov     w23, w19
        sub     w21, w21, #0x1
        add     x22, sp, #0x57
        cbz     x19, L1324
        mov     w6, w19
        mov     x0, x20
        mov     w5, #0x0
        bl      L1630
        cmp     x19, w21, uxtw
        b.ne    L1324
        ldrb    w0, [sp, #87]
        mov     w5, w19
        mov     w6, #0x1
        orr     w0, w0, #0xffffff80
        strb    w0, [sp, #87]
L12cc:
        mov     x2, x22
        mov     x1, x22
        mov     x0, x20
        mov     x4, x22
        mov     x3, x22
        bl      L1630
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1358
        bl      L0e60
L1304:
        mov     w6, w21
        mov     w5, #0x0
        mov     x0, x20
        bl      L1630
        mov     x0, x20
        sub     x19, x19, x23
        bl      L1ca4
        b       L1274
L1324:
        mov     w5, w23
        mov     x0, x20
        mov     w6, #0x1
        mov     x4, x22
        mov     x3, x22
        mov     x2, x22
        mov     x1, x22
        bl      L1630
        mov     w0, #0xffffff80
        mov     w5, w21
        mov     w6, #0x1
        strb    w0, [sp, #87]
        b       L12cc
L1358:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #96
        ret

// mldsa_shake128x4_absorb_once (0x64 bytes)
L1370:
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
        bl      L0e70
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
        b       L1220

// mldsa_shake128x4_squeezeblocks (0x80 bytes)
L13d4:
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
L13fc:
        cbnz    x19, L1414
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L1414:
        mov     x0, x24
        bl      L1ca4
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
        bl      L15b0
        b       L13fc

// mldsa_shake128x4_init (0x4 bytes)
L1454:
        ret

// mldsa_shake128x4_release (0x1c bytes)

// mldsa_shake128x4_release.localalias (0x1c bytes)
L1458:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0x320
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256x4_absorb_once (0x64 bytes)
L1474:
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
        bl      L0e70
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
        b       L1220

// mldsa_shake256x4_squeezeblocks (0x80 bytes)
L14d8:
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
L1500:
        cbnz    x19, L1518
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L1518:
        mov     x0, x24
        bl      L1ca4
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
        bl      L15b0
        b       L1500

// mldsa_shake256x4_init (0x4 bytes)
L1558:
        ret

// mldsa_shake256x4_release (0x4 bytes)
L155c:
        b       L1458

// mldsa_keccakf1600_extract_bytes (0x24 bytes)
L1560:
        add     x2, x0, w2, uxtw
        mov     x4, #0x0
L1568:
        cmp     w3, w4
        b.hi    L1574
        ret
L1574:
        ldrb    w0, [x2, x4]
        strb    w0, [x1, x4]
        add     x4, x4, #0x1
        b       L1568

// mldsa_keccakf1600_xor_bytes (0x2c bytes)
L1584:
        add     x2, x0, w2, uxtw
        mov     x0, #0x0
L158c:
        cmp     w3, w0
        b.hi    L1598
        ret
L1598:
        ldrb    w5, [x1, x0]
        add     x0, x0, #0x1
        ldrb    w4, [x2]
        eor     w4, w4, w5
        strb    w4, [x2], #1
        b       L158c

// mldsa_keccakf1600x4_extract_bytes (0x80 bytes)
L15b0:
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
        bl      L1560
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L1560
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L1560
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L1560

// mldsa_keccakf1600x4_xor_bytes (0x80 bytes)
L1630:
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
        bl      L1584
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L1584
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L1584
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L1584

// mldsa_keccakf1600_permute (0x5f4 bytes)
L16b0:
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
        add     x24, x2, #0xda8
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
L1728:
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
        b.ne    L1728
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
L1ca4:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L16b0
        add     x0, x19, #0xc8
        bl      L16b0
        add     x0, x19, #0x190
        bl      L16b0
        add     x0, x19, #0x258
        ldp     x19, x30, [sp], #16
        b       L16b0

// mldsa44_unpack_pk_t1 (0x14 bytes)
L1ccc:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25e0

// mldsa44_pack_sk_rho_key_tr (0x28 bytes)
L1ce0:
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
L1d08:
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
        bl      L36e0
        mov     x0, x22
        mov     x22, x20
        bl      L3510
        add     x1, x19, #0x200
        mov     x0, x21
        bl      L3758
        mov     x0, x21
        add     x21, x19, #0x380
        add     x19, x19, #0xa00
        bl      L3604
L1d7c:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L2764
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L1d7c
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L3604

// mldsa44_pack_sig_c (0xc bytes)
L1dac:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ret

// mldsa44_pack_sig_h (0xec bytes)
L1db8:
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
        bl      L0e70
L1e10:
        madd    x1, x19, x26, x24
        mov     x0, x22
        bl      L2984
        mov     w2, #0x8c00
        add     x1, x23, x19, lsl #10
        mov     x4, #0x0
        movk    w2, #0xfffe, lsl #16
L1e2c:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w3, [x22, x4, lsl #2]
        add     w5, w0, w27
        cmp     w5, w28
        b.hi    L1e4c
        cmp     w3, #0x0
        ccmp    w0, w2, #0x0, ne
        b.ne    L1e5c
L1e4c:
        cmp     w20, #0x50
        b.eq    L1e9c
        strb    w4, [x25, w20, uxtw]
        add     w20, w20, #0x1
L1e5c:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L1e2c
        add     x0, x21, #0x970
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x4
        b.ne    L1e10
        mov     w0, #0x0
L1e80:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L1e9c:
        mov     w0, #0xffffffff
        b       L1e80

// mldsa44_pack_sig_z (0x14 bytes)
L1ea4:
        mov     w3, #0x240
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x0, x0, x2
        b       L3180

// mldsa44_sig_unpack_hints (0xdc bytes)
L1eb8:
        stp     x19, x20, [sp, #-48]!
        mov     x3, x0
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, #0x920
        cbz     w2, L1f08
        add     w0, w2, #0x4f
        ldrb    w22, [x23, x0]
L1ee0:
        add     w0, w21, #0x50
        ldrb    w19, [x23, x0]
        cmp     w19, #0x50
        ccmp    w22, w19, #0x2, ls
        b.ls    L1f10
L1ef4:
        mov     w0, #0xffffffff
L1ef8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L1f08:
        mov     w22, #0x0
        b       L1ee0
L1f10:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        add     x2, x20, w22, uxtb
        mov     x3, x0
        mov     w1, w22
        mov     w4, #0x1
L1f30:
        cmp     w1, w19
        b.cc    L1f54
        cmp     w21, #0x3
        b.ne    L1f4c
        add     x20, x20, #0x91f
L1f44:
        cmp     w19, #0x50
        b.ne    L1f84
L1f4c:
        mov     w0, #0x0
        b       L1ef8
L1f54:
        cmp     w1, w22
        b.ls    L1f70
        sub     w0, w1, #0x1
        ldrb    w5, [x2, #2336]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L1ef4
L1f70:
        ldrb    w0, [x2, #2336]
        add     w1, w1, #0x1
        add     x2, x2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L1f30
L1f84:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L1f44
        b       L1ef4

// mld_rej_uniform_c.constprop.0 (0x5c bytes)
L1f94:
        mov     x5, x0
        mov     w0, w1
        mov     w1, #0x3
        sub     w1, w1, w2
L1fa4:
        cmp     w0, #0xff
        b.hi    L1fb8
L1fac:
        add     w4, w1, w2
        cmp     w3, w4
        b.cs    L1fbc
L1fb8:
        ret
L1fbc:
        ldrb    w6, [x2, #2]
        add     x2, x2, #0x3
        ldurb   w4, [x2, #-2]
        ldurb   w7, [x2, #-3]
        lsl     w6, w6, #16
        orr     w4, w6, w4, lsl #8
        orr     w4, w4, w7
        and     w4, w4, #0x7fffff
        cmp     w4, #0x7fe, lsl #12
        b.hi    L1fac
        str     w4, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
        b       L1fa4

// mldsa_poly_reduce (0x2c bytes)
L1ff0:
        mov     x1, #0x0
        mov     w4, #0xff801fff
L1ff8:
        ldr     w3, [x0, x1, lsl #2]
        add     w2, w3, #0x400, lsl #12
        asr     w2, w2, #23
        madd    w2, w2, w4, w3
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L1ff8
        ret

// mldsa_poly_caddq (0x3c bytes)
L201c:
        mov     w5, #0xe001
        mov     x3, #0x0
        movk    w5, #0x7f, lsl #16
L2028:
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
        b.ne    L2028
        ret

// mldsa_poly_add (0x24 bytes)
L2058:
        mov     x2, #0x0
L205c:
        ldr     w3, [x0, x2]
        ldr     w4, [x1, x2]
        add     w3, w3, w4
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L205c
        ret

// mldsa_poly_sub (0x24 bytes)
L207c:
        mov     x2, #0x0
L2080:
        ldr     w3, [x0, x2]
        ldr     w4, [x1, x2]
        sub     w3, w3, w4
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L2080
        ret

// mldsa_poly_shiftl (0x20 bytes)
L20a0:
        mov     x1, #0x0
L20a4:
        ldr     w2, [x0, x1, lsl #2]
        lsl     w2, w2, #13
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L20a4
        ret

// mldsa_poly_ntt (0xa8 bytes)
L20c0:
        mov     w1, #0x1
        .inst   0xf0000028  // adrp x8, 0x9000
        mov     w13, #0x2001
        mov     w11, w1
        add     x8, x8, #0xe68
        mov     w12, #0x100
        movk    w13, #0x380, lsl #16
        mov     w14, #0xff801fff
L20e0:
        sub     w6, w1, #0x1
        lsr     w2, w12, w1
        lsl     w10, w2, #1
        mov     w5, #0x0
        lsl     w6, w11, w6
L20f4:
        mov     w3, w6
        add     w6, w6, #0x1
        ldr     w15, [x8, w3, uxtw #2]
        cmp     w5, w2
        b.cs    L2148
        mov     w3, w5
        add     x9, x0, w2, uxtw #2
L2110:
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
        b.hi    L2110
L2148:
        add     w5, w5, w10
        add     w2, w2, w10
        cmp     w5, #0xff
        b.ls    L20f4
        add     w1, w1, #0x1
        cmp     w1, #0x9
        b.ne    L20e0
        ret

// mldsa_poly_invntt_tomont (0xe0 bytes)
L2168:
        .inst   0xf0000029  // adrp x9, 0x9000
        mov     w14, #0x2001
        add     x9, x9, #0xe68
        mov     w3, #0x8
        mov     w12, #0x100
        mov     w13, #0x1
        movk    w14, #0x380, lsl #16
        mov     w15, #0xff801fff
L2188:
        lsr     w2, w12, w3
        mov     w4, #0x0
        lsl     w5, w13, w3
        lsl     w11, w2, #1
        sub     w5, w5, #0x1
L219c:
        mov     w1, w5
        sub     w5, w5, #0x1
        ldr     w10, [x9, w1, uxtw #2]
        neg     w10, w10
        cmp     w4, w2
        b.cs    L21f4
        mov     w6, w4
        add     x8, x0, w2, uxtw #2
L21bc:
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
        b.hi    L21bc
L21f4:
        add     w4, w4, w11
        add     w2, w2, w11
        cmp     w4, #0xff
        b.ls    L219c
        subs    w3, w3, #0x1
        b.ne    L2188
        mov     w5, #0x2001
        mov     x1, #0x0
        mov     w6, #0xa3fa
        movk    w5, #0x380, lsl #16
        mov     w4, #0xff801fff
L2220:
        ldr     w3, [x0, x1, lsl #2]
        smull   x3, w3, w6
        mul     w2, w3, w5
        smaddl  x2, w2, w4, x3
        asr     x2, x2, #32
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L2220
        ret

// mldsa_poly_pointwise_montgomery (0x3c bytes)
L2248:
        mov     w6, #0x2001
        mov     x2, #0x0
        movk    w6, #0x380, lsl #16
        mov     w5, #0xff801fff
L2258:
        ldr     w3, [x1, x2]
        ldr     w4, [x0, x2]
        smull   x4, w4, w3
        mul     w3, w4, w6
        smaddl  x3, w3, w5, x4
        asr     x3, x3, #32
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L2258
        ret

// mldsa_poly_power2round (0x30 bytes)
L2284:
        mov     x3, #0x0
L2288:
        ldr     w4, [x2, x3]
        add     w5, w4, #0xfff
        asr     w6, w5, #13
        and     w5, w5, #0xffffe000
        str     w6, [x0, x3]
        sub     w4, w4, w5
        str     w4, [x1, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L2288
        ret

// mldsa_poly_uniform (0xf4 bytes)
L22b4:
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
        bl      L0f94
        mov     x1, x20
        mov     x2, #0x22
        mov     x0, x21
        bl      L0fb4
        mov     x0, x21
        bl      L0fdc
        mov     x2, x21
        mov     x1, #0x348
        mov     x0, x19
        bl      L105c
        mov     x2, x19
        mov     w3, #0x348
        mov     w1, #0x0
L2328:
        mov     x0, x22
        bl      L1f94
        mov     w20, w0
        cmp     w0, #0xff
        b.ls    L2374
        mov     x0, x21
        bl      L107c
        mov     x0, x19
        mov     x2, #0x348
        mov     w1, #0x0
        bl      L0e70
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1128]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2394
        bl      L0e60
L2374:
        mov     x2, x21
        mov     x1, #0xa8
        mov     x0, x19
        bl      L105c
        mov     x2, x19
        mov     w1, w20
        mov     w3, #0xa8
        b       L2328
L2394:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x470
        ret

// mldsa_poly_uniform_4x (0x1dc bytes)
L23a8:
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
        bl      L1454
        add     x4, x20, #0xc0
        add     x3, x20, #0x80
        add     x2, x20, #0x40
        mov     x1, x20
        mov     x0, x23
        mov     x5, #0x22
        bl      L1370
        mov     x5, x23
        mov     x4, #0x5
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L13d4
        ldr     x0, [sp, #104]
        mov     w3, #0x348
        mov     x2, x19
        mov     w1, #0x0
        bl      L1f94
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     x2, x28
        mov     w1, #0x0
        bl      L1f94
        mov     w22, w0
        mov     x2, x27
        mov     w1, #0x0
        mov     x0, x24
        bl      L1f94
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L248c:
        mov     x0, x25
        bl      L1f94
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L24f0
        cmp     w22, #0xff
        b.ls    L24f0
        cmp     w20, #0xff
        b.ls    L24f0
        cmp     w0, #0xff
        b.ls    L24f0
        mov     x0, x23
        bl      L1458
        mov     x0, x19
        mov     x2, #0xd80
        mov     w1, #0x0
        bl      L0e70
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2560
        bl      L0e60
L24f0:
        mov     x5, x23
        mov     x4, #0x1
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L13d4
        ldr     x0, [sp, #104]
        mov     w1, w21
        mov     w3, #0xa8
        mov     x2, x19
        bl      L1f94
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     w1, w22
        mov     x2, x28
        bl      L1f94
        mov     w22, w0
        mov     w1, w20
        mov     x2, x27
        mov     x0, x24
        bl      L1f94
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     x2, x26
        mov     w1, w6
        b       L248c
L2560:
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
L2584:
        add     x4, x1, #0x400
L2588:
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
        b.ne    L2588
        ret

// mldsa_polyt1_unpack (0x70 bytes)
L25e0:
        add     x4, x1, #0x140
L25e4:
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
        b.ne    L25e4
        ret

// mldsa_polyt0_pack (0x114 bytes)
L2650:
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-64]!
        add     x11, x0, #0x1a0
        ldr     x3, [x2]
        str     x3, [sp, #56]
        mov     x3, #0x0
        mov     w2, #0x1000
L2670:
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
        b.ne    L2670
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        stp     xzr, xzr, [sp, #40]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #56]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L275c
        bl      L0e60
L275c:
        ldr     x30, [sp], #64
        ret

// mldsa_polyt0_unpack (0x154 bytes)
L2764:
        add     x12, x0, #0x400
        mov     w2, #0x1000
L276c:
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
        b.ne    L276c
        ret

// mldsa_poly_chknorm (0x4c bytes)
L28b8:
        sub     w1, w1, #0x1
        mov     x6, x0
        mov     x4, #0x0
        mov     w0, #0x0
L28c8:
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
        b.ne    L28c8
        ret

// mldsa_polyw1_pack_88 (0x5c bytes)
L2904:
        add     x4, x1, #0x400
L2908:
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
        b.ne    L2908
        ret

// mldsa_polyw1_pack_32 (0x24 bytes)
L2960:
        mov     x2, #0x0
L2964:
        ldr     w3, [x1, #4]
        ldr     w4, [x1], #8
        orr     w3, w4, w3, lsl #4
        strb    w3, [x0, x2]
        add     x2, x2, #0x1
        cmp     x2, #0x80
        b.ne    L2964
        ret

// mldsa_polyw1_unpack_88 (0x60 bytes)
L2984:
        add     x4, x1, #0xc0
L2988:
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
        b.ne    L2988
        ret

// mldsa_polyw1_unpack_32 (0x30 bytes)
L29e4:
        mov     x2, #0x0
L29e8:
        ldrb    w3, [x1, x2]
        add     x0, x0, #0x8
        and     w3, w3, #0xf
        stur    w3, [x0, #-8]
        ldrb    w3, [x1, x2]
        add     x2, x2, #0x1
        lsr     w3, w3, #4
        stur    w3, [x0, #-4]
        cmp     x2, #0x80
        b.ne    L29e8
        ret

// mld_decompose44 (0x68 bytes)
L2a14:
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
L2a7c:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c44.constprop.0 (0x88 bytes)
L2a98:
        mov     x6, x0
        mov     w0, w1
        mov     x5, #0x0
        mov     w9, #0x87
        mov     w7, #0xcd
        mov     w8, #0x2
L2ab0:
        cmp     w0, #0xff
        ccmp    w5, w9, #0x2, ls
        b.ls    L2ac0
        ret
L2ac0:
        ldrb    w1, [x2, x5]
        and     w3, w1, #0xf
        lsr     w1, w1, #4
        cmp     w3, #0xf
        b.eq    L2af0
        mul     w4, w3, w7
        lsr     w4, w4, #10
        add     w4, w4, w4, lsl #2
        sub     w3, w3, w4
        sub     w3, w8, w3
        str     w3, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L2af0:
        cmp     w0, #0xff
        ccmp    w1, #0xe, #0x2, ls
        b.hi    L2b18
        mul     w3, w1, w7
        lsr     w3, w3, #10
        add     w3, w3, w3, lsl #2
        sub     w1, w1, w3
        sub     w1, w8, w1
        str     w1, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L2b18:
        add     x5, x5, #0x1
        b       L2ab0

// mldsa44_poly_decompose (0x34 bytes)
L2b20:
        mov     x8, x0
        mov     x7, x1
        mov     x6, #0x0
        str     x30, [sp, #-16]!
L2b30:
        ldr     w2, [x7, x6]
        add     x1, x8, x6
        add     x0, x7, x6
        add     x6, x6, #0x4
        bl      L2a14
        cmp     x6, #0x400
        b.ne    L2b30
        ldr     x30, [sp], #16
        ret

// mldsa44_poly_use_hint (0xa4 bytes)
L2b54:
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
L2b84:
        ldr     w2, [x7, x6]
        mov     x1, x9
        ldr     w11, [x8, x6]
        bl      L2a14
        ldr     w2, [sp, #20]
        cbz     w11, L2bb0
        ldr     w1, [sp, #16]
        cmp     w1, #0x0
        b.le    L2be0
        cmp     w2, #0x2b
        csinc   w2, wzr, w2, eq
L2bb0:
        str     w2, [x7, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L2b84
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2bf0
        bl      L0e60
L2be0:
        sub     w1, w2, #0x1
        cmp     w2, #0x0
        csel    w2, w1, w10, ne
        b       L2bb0
L2bf0:
        ldr     x30, [sp], #32
        ret

// mldsa44_poly_uniform_eta_4x (0x22c bytes)
L2bf8:
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
        bl      L1558
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1474
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14d8
        ldr     x0, [sp, #96]
        mov     x2, x19
        mov     w1, #0x0
        bl      L2a98
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L2a98
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L2a98
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L2d2c:
        mov     x0, x25
        bl      L2a98
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L2d98
        cmp     w22, #0xff
        b.ls    L2d98
        cmp     w20, #0xff
        b.ls    L2d98
        cmp     w0, #0xff
        b.ls    L2d98
        mov     x0, x23
        bl      L155c
        mov     x0, x19
        mov     x1, #0x280
        bl      L2a7c
        mov     x0, x24
        mov     x1, #0x180
        bl      L2a7c
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1976]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2e04
        bl      L0e60
L2d98:
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14d8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     x2, x19
        bl      L2a98
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L2a98
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L2a98
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L2d2c
L2e04:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7c0
        ret

// mldsa44_poly_challenge (0x160 bytes)
L2e24:
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
        bl      L1098
        mov     x1, x19
        mov     x2, #0x20
        mov     x0, x21
        bl      L10b8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10e0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1160
        mov     x0, #0x0
L2e94:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L2e94
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xd9
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e70
L2ecc:
        cmp     w19, #0x88
        b.ne    L2f68
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1160
        mov     w0, #0x0
L2ee8:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L2ecc
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
        b.ne    L2ecc
        mov     x0, x21
        bl      L1180
        mov     x0, x20
        mov     x1, #0x88
        bl      L2a7c
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L2a7c
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2f70
        bl      L0e60
L2f68:
        mov     w0, w19
        b       L2ee8
L2f70:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa44_polyeta_pack (0x13c bytes)
L2f84:
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x30, [sp, #-32]!
        mov     x8, x0
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x14, x1, #0x400
        mov     w6, #0x2
L2fa8:
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
        b.ne    L2fa8
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
        bl      L2a7c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L30b8
        bl      L0e60
L30b8:
        ldp     x19, x30, [sp], #32
        ret

// mldsa44_polyeta_unpack (0xc0 bytes)
L30c0:
        add     x11, x0, #0x400
        mov     w2, #0x2
L30c8:
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
        b.ne    L30c8
        ret

// mldsa44_polyz_pack (0x108 bytes)
L3180:
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x15, x0, #0x240
        mov     w10, #0x20000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        mov     x2, x0
L31a4:
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
        b.ne    L31a4
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
        bl      L2a7c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3280
        bl      L0e60
L3280:
        ldr     x30, [sp], #48
        ret

// mldsa44_polyz_unpack (0xcc bytes)
L3288:
        add     x8, x0, #0x400
        mov     w6, #0x20000
L3290:
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
        b.ne    L3290
        ret

// mldsa44_poly_uniform_gamma1_4x (0x17c bytes)
L3354:
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
        bl      L1558
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1474
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14d8
        mov     x1, x19
        mov     x0, x25
        bl      L3288
        mov     x1, x27
        mov     x0, x24
        bl      L3288
        mov     x1, x26
        mov     x0, x23
        bl      L3288
        mov     x1, x21
        mov     x0, x22
        bl      L3288
        mov     x0, x28
        bl      L155c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L2a7c
        mov     x0, x20
        mov     x1, #0x180
        bl      L2a7c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L34ac
        bl      L0e60
L34ac:
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
L34d0:
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
        bl      L3354
        ldr     x30, [sp, #16]
        add     sp, sp, #0x20
        ret

// mldsa44_polyvecl_ntt (0x28 bytes)

// mldsa44_polyvecl_ntt.localalias (0x28 bytes)
L3510:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L20c0
        add     x0, x19, #0x400
        bl      L20c0
        add     x0, x19, #0x800
        bl      L20c0
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L20c0

// mldsa44_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L3538:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L3548:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L3554:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x4
        b.ne    L3554
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L3548
        ret

// mldsa44_polyvecl_chknorm (0x4c bytes)
L3590:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     w20, #0x0
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x0, #0x1, lsl #12
        str     x30, [sp, #32]
L35ac:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L28b8
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L35ac
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyveck_caddq (0x28 bytes)
L35dc:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L201c
        add     x0, x19, #0x400
        bl      L201c
        add     x0, x19, #0x800
        bl      L201c
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L201c

// mldsa44_polyveck_ntt (0x4 bytes)
L3604:
        b       L3510

// mldsa44_polyveck_invntt_tomont (0x28 bytes)
L3608:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L2168
        add     x0, x19, #0x400
        bl      L2168
        add     x0, x19, #0x800
        bl      L2168
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L2168

// mldsa44_polyveck_unpack_eta_chknorm (0x5c bytes)
L3630:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x180
L3650:
        mov     x1, x19
        mov     x0, x20
        bl      L30c0
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L28b8
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L3650
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyveck_decompose_pack_w1 (0x54 bytes)
L368c:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, #0x1, lsl #12
        str     x30, [sp, #32]
L36a8:
        mov     x1, x19
        mov     x0, x21
        bl      L2b20
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2904
        add     x20, x20, #0xc0
        cmp     x19, x22
        b.ne    L36a8
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyvecl_unpack_eta (0x3c bytes)

// mldsa44_polyvecl_unpack_eta.localalias (0x3c bytes)
L36e0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x1, lsl #12
L36f4:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L30c0
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L36f4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa44_polyvecl_unpack_z (0x3c bytes)
L371c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x1, lsl #12
L3730:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L3288
        add     x20, x20, #0x240
        cmp     x19, x21
        b.ne    L3730
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa44_polyveck_unpack_eta (0x4 bytes)
L3758:
        b       L36e0

// mldsa44_polyvec_matrix_expand_eager (0x120 bytes)
L375c:
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
L3790:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L3790
        mov     w5, #0x0
        mov     w22, #0x1000
        mov     x23, #0xc00
        mov     x24, #0x800
        mov     x25, #0x400
L37bc:
        mov     x1, x19
        mov     w0, w5
        add     w21, w5, #0x4
L37c8:
        and     w2, w0, #0x3
        strb    w2, [x1, #32]
        lsr     w2, w0, #2
        add     w0, w0, #0x1
        strb    w2, [x1, #33]
        add     x1, x1, #0x40
        cmp     w21, w0
        b.ne    L37c8
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
        bl      L23a8
        cmp     w21, #0x10
        b.eq    L3838
        mov     w5, w21
        b       L37bc
L3838:
        mov     x0, x19
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e70
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #344]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3868
        bl      L0e60
L3868:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #352
        ret

// mldsa44_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L387c:
        ubfiz   x3, x3, #12, #32
        add     x1, x1, x3
        b       L3538

// mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L3888:
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
        bl      L0e40
        mov     x0, x20
        bl      L3510
L38bc:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L387c
        cmp     x19, #0x4
        b.ne    L38bc
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L3608

// mld_ct_memcmp (0x54 bytes)
L38f0:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L38fc:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L3924
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L3924:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L38fc

// mld_zeroize (0x1c bytes)
L3944:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t144 (0x158 bytes)
L3960:
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
        bl      L375c
L39d4:
        ldr     x2, [sp, #104]
        mov     w3, w25
        mov     x1, x20
        mov     x0, x19
        bl      L387c
        mov     x0, x19
        bl      L2168
        madd    x1, x25, x28, x24
        mov     x0, x21
        bl      L30c0
        mov     x1, x21
        mov     x0, x19
        bl      L2058
        mov     x0, x19
        bl      L1ff0
        mov     x0, x19
        bl      L201c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x21
        bl      L2284
        madd    x0, x25, x27, x23
        mov     x1, x21
        bl      L2584
        madd    x0, x25, x26, x22
        mov     x1, x19
        add     x25, x25, #0x1
        bl      L2650
        cmp     x25, #0x4
        b.ne    L39d4
        mov     x0, x21
        mov     x1, #0x400
        bl      L3944
        mov     x0, x19
        mov     x1, #0x400
        bl      L3944
        mov     x0, x20
        mov     x1, #0x4000
        bl      L3944
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #18568]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3a90
        bl      L0e60
L3a90:
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
L3ab8:
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
        bl      L1098
        mov     x2, x27
        mov     x1, x26
        mov     x0, x19
        bl      L10b8
        cbz     x21, L3b30
        mov     x2, x21
        mov     x1, x25
        mov     x0, x19
        bl      L10b8
L3b30:
        cbz     x20, L3b44
        mov     x2, x20
        mov     x1, x24
        mov     x0, x19
        bl      L10b8
L3b44:
        mov     x0, x19
        bl      L10e0
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L1160
        mov     x0, x19
        bl      L1180
        mov     x0, x19
        mov     x1, #0xd0
        bl      L3944
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3b90
        bl      L0e60
L3b90:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa44_keypair_internal (0x234 bytes)
L3ba8:
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
        bl      L1184
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
        bl      L2bf8
        mov     x1, x19
        mov     x0, x27
        bl      L2f84
        mov     x1, x26
        add     x0, x20, #0x260
        bl      L2f84
        mov     x1, x25
        add     x0, x20, #0x2c0
        bl      L2f84
        mov     x1, x23
        add     x0, x20, #0x320
        bl      L2f84
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
        bl      L2bf8
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L2f84
        mov     x1, x26
        add     x0, x20, #0xe0
        bl      L2f84
        mov     x1, x25
        add     x0, x20, #0x140
        bl      L2f84
        mov     x1, x23
        add     x0, x20, #0x1a0
        bl      L2f84
        mov     x0, x19
        bl      L3510
        ldp     q0, q1, [x21]
        mov     x2, x19
        mov     x4, x21
        mov     x3, x27
        add     x1, x20, #0x380
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L3960
        mov     x2, #0x1080
        mov     w23, w0
        add     x25, x19, x2
        cbnz    w0, L3d48
        mov     x2, x22
        mov     x0, x25
        mov     x3, #0x520
        mov     x1, #0x40
        bl      L1184
        add     x3, x21, #0x60
        mov     x2, x25
        mov     x1, x21
        mov     x0, x20
        bl      L1ce0
L3d48:
        mov     x0, x19
        mov     x1, #0x1000
        bl      L3944
        mov     x0, x25
        mov     x1, #0x40
        bl      L3944
        mov     x0, x24
        mov     x1, #0x22
        bl      L3944
        mov     x0, x21
        mov     x1, #0x80
        bl      L3944
        cbz     w23, L3d94
        mov     x0, x22
        mov     x1, #0x520
        bl      L3944
        mov     x0, x20
        mov     x1, #0xa00
        bl      L3944
L3d94:
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3db4
        bl      L0e60
L3db4:
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
L3ddc:
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
        bl      L0e50
        cbnz    w0, L3e58
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L3ba8
        mov     w20, w0
L3e2c:
        mov     x0, x19
        mov     x1, #0x20
        bl      L3944
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3e60
        bl      L0e60
L3e58:
        mov     w20, #0xfffffffd
        b       L3e2c
L3e60:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa44_signature_internal (0x438 bytes)
L3e70:
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
        bl      L1d08
        add     x0, x21, #0x80
        cbnz    w27, L4178
        mov     x3, #0x40
        mov     x7, x25
        mov     x6, x26
        mov     x5, x24
        mov     x4, x22
        mov     x2, x28
        mov     x1, x3
        bl      L3ab8
L3f38:
        mov     x5, #0x20
        mov     x4, x20
        mov     x3, x5
        add     x6, x21, #0x80
        add     x2, x21, #0x60
        mov     x7, #0x40
        add     x0, x21, #0xc0
        mov     x1, x7
        bl      L3ab8
        mov     x0, x19
        mov     x1, x21
        bl      L375c
        str     wzr, [sp, #124]
        mov     x4, #0xa800
        add     x0, x19, x4
        mov     x5, #0xac00
        str     x0, [sp, #104]
        add     x0, x19, x5
        str     x0, [sp, #112]
L3f84:
        ldrh    w2, [sp, #124]
        add     x27, x19, #0x6, lsl #12
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0x5, lsl #12
        add     x24, x19, #0x4, lsl #12
        mov     w26, #0xffb2
        add     x22, x19, #0xa, lsl #12
        bl      L34d0
        mov     x28, #0x0
        mov     x3, x20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x24
        bl      L3888
        movk    w26, #0x1, lsl #16
        mov     x0, x24
        bl      L35dc
        ldr     x0, [sp, #104]
        mov     x3, #0xa400
        mov     x2, x20
        add     x25, x19, x3
        mov     x1, x24
        bl      L368c
        ldp     x4, x0, [sp, #104]
        add     x2, x21, #0x80
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x300
        mov     x3, #0x40
        mov     x1, #0x20
        bl      L3ab8
        ldr     x1, [sp, #112]
        mov     x0, x25
        bl      L2e24
        mov     x0, x25
        bl      L20c0
L4018:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e40
        mov     x1, x25
        mov     x0, x22
        bl      L2248
        mov     x0, x22
        bl      L2168
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x27, x3
        bl      L0e40
        mov     x1, x20
        mov     x0, x22
        bl      L2058
        mov     x0, x22
        bl      L1ff0
        mov     w1, w26
        mov     x0, x22
        bl      L28b8
        cbnz    w0, L418c
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L1ea4
        cmp     x28, #0x4
        b.ne    L4018
        mov     x26, #0x0
L40a0:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x24, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e40
        mov     x1, x25
        mov     x0, x20
        bl      L2248
        mov     x0, x20
        bl      L2168
        mov     x1, x20
        mov     x0, x28
        bl      L207c
        mov     x0, x28
        bl      L1ff0
        mov     w1, #0x73b2
        mov     x0, x28
        movk    w1, #0x1, lsl #16
        bl      L28b8
        cbnz    w0, L418c
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e40
        mov     x1, x25
        mov     x0, x20
        bl      L2248
        mov     x0, x20
        bl      L2168
        mov     x0, x20
        bl      L1ff0
        mov     w1, #0x7400
        mov     x0, x20
        movk    w1, #0x1, lsl #16
        bl      L28b8
        cbnz    w0, L418c
        mov     x1, x20
        mov     x0, x28
        add     x26, x26, #0x400
        bl      L2058
        cmp     x26, #0x1, lsl #12
        b.ne    L40a0
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L1dac
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x24
        mov     x0, x23
        bl      L1db8
        mov     w26, w0
        b       L4190
L4178:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L3f38
L418c:
        mov     w26, #0xffffffff
L4190:
        mov     x0, x22
        mov     x1, #0x400
        bl      L3944
        mov     x0, x25
        mov     x1, #0x400
        bl      L3944
        mov     x0, x24
        mov     x1, #0x1000
        bl      L3944
        ldr     x0, [sp, #104]
        mov     x1, #0x300
        bl      L3944
        mov     x0, x20
        mov     x1, #0x1000
        bl      L3944
        mov     x0, x27
        mov     x1, #0x1000
        bl      L3944
        ldr     x0, [sp, #112]
        mov     x1, #0x20
        bl      L3944
        cbz     w26, L421c
        cmn     w26, #0x1
        b.ne    L4210
        ldr     w0, [sp, #124]
        add     w0, w0, #0x4
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfff8
        cmp     w1, w0, uxth
        b.ne    L3f84
        mov     w26, #0xfffffffc
L4210:
        mov     x0, x23
        mov     x1, #0x974
        bl      L3944
L421c:
        ldr     x0, [sp, #128]
        mov     x1, #0x1000
        bl      L3944
        ldr     x0, [sp, #144]
        mov     x1, #0x1000
        bl      L3944
        ldr     x0, [sp, #136]
        mov     x1, #0x1000
        bl      L3944
        mov     x0, x19
        mov     x1, #0x4000
        bl      L3944
        mov     x0, x21
        mov     x1, #0x100
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x1, #0x8040
        add     x2, sp, x1
        ldr     x3, [x2, #11416]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L4280
        bl      L0e60
L4280:
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
L42a8:
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
        bl      L0e50
        cbnz    w0, L4340
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L3e70
        mov     w20, w0
L4314:
        mov     x0, x19
        mov     x1, #0x20
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4348
        bl      L0e60
L4340:
        mov     w20, #0xfffffffd
        b       L4314
L4348:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa44_verify_internal (0x300 bytes)
L435c:
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
        bl      L371c
        mov     w1, #0xffb2
        mov     x0, x26
        movk    w1, #0x1, lsl #16
        bl      L3590
        mov     x14, #0x5f60
        mov     w20, w0
        add     x0, x19, x14
        str     x0, [sp, #104]
        cbnz    w20, L4584
        ldr     w6, [sp, #140]
        cbnz    w6, L461c
        ldr     x2, [sp, #96]
        mov     x0, x23
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x520
        mov     x1, #0x40
        bl      L3ab8
        ldp     x7, x4, [sp, #112]
        mov     x10, #0x5f00
        ldr     x5, [sp, #128]
        mov     x6, x28
        mov     x2, x23
        mov     x3, #0x40
        add     x0, x19, x10
        mov     x1, x3
        bl      L3ab8
        mov     x0, x23
        mov     x1, #0x40
        bl      L3944
L4468:
        mov     x0, x26
        bl      L3510
        ldr     x1, [sp, #96]
        mov     x0, x19
        mov     x28, x23
        bl      L375c
        mov     x9, #0x5f60
        add     x1, x19, x9
        mov     x0, x27
        bl      L2e24
        mov     x0, x27
        bl      L20c0
L4498:
        mov     w3, w20
        mov     x2, x26
        mov     x1, x19
        mov     x0, x21
        bl      L387c
        ldr     x1, [sp, #96]
        mov     w2, w20
        mov     x0, x22
        bl      L1ccc
        mov     x0, x22
        bl      L20a0
        mov     x0, x22
        bl      L20c0
        mov     x1, x27
        mov     x0, x22
        bl      L2248
        mov     x1, x22
        mov     x0, x21
        bl      L207c
        mov     x0, x21
        bl      L1ff0
        mov     x0, x21
        bl      L2168
        mov     x0, x21
        bl      L201c
        mov     w2, w20
        mov     x1, x24
        mov     x0, x22
        bl      L1eb8
        mov     w25, w0
        cbnz    w0, L4584
        mov     x1, x22
        mov     x0, x21
        bl      L2b54
        add     w20, w20, #0x1
        mov     x0, x28
        mov     x1, x21
        bl      L2904
        add     x28, x28, #0xc0
        cmp     w20, #0x4
        b.ne    L4498
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
        bl      L3ab8
        ldr     x0, [sp, #104]
        mov     x1, x20
        mov     x2, #0x20
        bl      L38f0
        tst     w0, #0xff
        b.eq    L4588
L4584:
        mov     w25, #0xfffffffa
L4588:
        mov     x0, x22
        mov     x1, #0x400
        bl      L3944
        mov     x0, x21
        mov     x1, #0x400
        bl      L3944
        mov     x0, x19
        mov     x1, #0x4000
        bl      L3944
        mov     x0, x27
        mov     x1, #0x400
        bl      L3944
        mov     x0, x26
        mov     x1, #0x1000
        bl      L3944
        mov     x1, #0x20
        mov     x0, #0x5f40
        add     x0, x19, x0
        bl      L3944
        ldr     x0, [sp, #104]
        mov     x1, #0x20
        bl      L3944
        mov     x2, #0x5f00
        mov     x1, #0x40
        add     x0, x19, x2
        bl      L3944
        mov     x0, x23
        mov     x1, #0x300
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24616]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4634
        bl      L0e60
L461c:
        ldp     q0, q1, [x28]
        sub     x0, x25, #0x100
        stp     q0, q1, [x0]
        ldp     q0, q1, [x28, #32]
        stp     q0, q1, [x0, #32]
        b       L4468
L4634:
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
L465c:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L435c

// mldsa44_prepare_domain_separation_prefix (0x138 bytes)
L4674:
        cmp     x4, #0xff
        b.hi    L479c
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L4760
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L47a4
        .inst   0xd0000020  // adrp x0, 0xa000
        add     x0, x0, #0x268
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 46c8 <mldsa44_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L46cc:
        b.ne    L47a4
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L46ec
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e40
L46ec:
        .inst   0xd0000020  // adrp x0, 0xa000
        add     x0, x0, #0x274
        mov     x1, #0x0
L46f8:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L478c
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L4728:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e40
        add     x0, x20, x19
        b       L477c
        cmp     x20, #0x20
        b       L46cc
        cmp     x20, #0x30
        b       L46cc
        cmp     x20, #0x40
        b       L46cc
L4760:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L4778
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e40
L4778:
        add     x0, x19, #0x2
L477c:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L478c:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L46f8
        b       L4728
L479c:
        mov     x0, #0x0
        ret
L47a4:
        mov     x0, #0x0
        b       L477c

// mldsa44_signature (0x100 bytes)
L47ac:
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
        bl      L4674
        cbz     x0, L4884
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e50
        cbnz    w0, L488c
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L3e70
        mov     w19, w0
        cbz     w0, L484c
L4840:
        mov     x0, x21
        mov     x1, #0x974
        bl      L3944
L484c:
        mov     x0, x22
        mov     x1, #0x20
        bl      L3944
        mov     x0, x20
        mov     x1, #0x14c
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4894
        bl      L0e60
L4884:
        mov     w19, #0xfffffff7
        b       L4840
L488c:
        mov     w19, #0xfffffffd
        b       L4840
L4894:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa44_verify (0xbc bytes)
L48ac:
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
        bl      L4674
        cbz     x0, L494c
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L435c
        mov     w20, w0
L4920:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4954
        bl      L0e60
L494c:
        mov     w20, #0xfffffff7
        b       L4920
L4954:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa44_signature_pre_hash_internal (0xc8 bytes)
L4968:
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
        cbnz    w7, L49b0
L499c:
        mov     w19, #0xfffffff7
L49a0:
        mov     x0, x21
        mov     x1, #0x974
        bl      L3944
        b       L49f0
L49b0:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L4674
        mov     x2, x0
        cbz     x0, L499c
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L3e70
        mov     w19, w0
        cbnz    w0, L49a0
L49f0:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4a1c
        bl      L0e60
L4a1c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa44_signature_pre_hash_shake256 (0xc0 bytes)
L4a30:
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
        bl      L1184
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L4968
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4ad8
        bl      L0e60
L4ad8:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa44_verify_pre_hash_internal (0xa8 bytes)
L4af0:
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
        cbnz    w5, L4b54
L4b24:
        mov     w20, #0xfffffff7
L4b28:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4b88
        bl      L0e60
L4b54:
        mov     x0, x19
        bl      L4674
        mov     x2, x0
        cbz     x0, L4b24
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L435c
        mov     w20, w0
        b       L4b28
L4b88:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa44_verify_pre_hash_shake256 (0xb0 bytes)
L4b98:
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
        bl      L1184
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L4af0
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4c34
        bl      L0e60
L4c34:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa44_pk_from_sk (0x208 bytes)
L4c48:
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
        bl      L36e0
        mov     w1, #0x3
        mov     x0, x19
        bl      L3590
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x3
        mov     x0, x23
        bl      L3630
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L3510
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L3960
        mov     x5, #0x1a80
        mov     w22, w0
        add     x23, x19, x5
        cbnz    w0, L4da4
        add     x1, x25, #0x380
        mov     x0, x24
        mov     x2, #0x680
        bl      L38f0
        and     w4, w0, #0xff
        mov     x3, #0x520
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1184
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L38f0
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L4db0
        mov     w22, #0xfffffff9
L4da4:
        mov     x0, x21
        mov     x1, #0x520
        bl      L3944
L4db0:
        mov     x0, x24
        mov     x1, #0x680
        bl      L3944
        mov     x0, x28
        mov     x1, #0x400
        bl      L3944
        mov     x0, x19
        mov     x1, #0x1000
        bl      L3944
        mov     x1, #0x20
        mov     x0, #0x1b00
        add     x0, x19, x0
        bl      L3944
        mov     x0, x23
        mov     x1, #0x40
        bl      L3944
        mov     x0, x27
        mov     x1, #0x40
        bl      L3944
        mov     x0, x26
        mov     x1, #0x20
        bl      L3944
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7112]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4e28
        bl      L0e60
L4e28:
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
L4e50:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25e0

// mldsa65_pack_sk_rho_key_tr (0x28 bytes)
L4e64:
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
L4e8c:
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
        bl      L5d0c
        mov     x0, x22
        mov     x22, x20
        bl      L5ae0
        add     x1, x19, #0x300
        mov     x0, x21
        bl      L5d8c
        mov     x0, x21
        add     x21, x19, #0x600
        add     x19, x19, #0xfc0
        bl      L5bf0
L4f00:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L2764
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L4f00
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L5bf0

// mldsa65_pack_sig_c (0x14 bytes)
L4f30:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldr     q0, [x1, #32]
        str     q0, [x0, #32]
        ret

// mldsa65_pack_sig_h (0xe0 bytes)
L4f44:
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
L4f98:
        add     x1, x25, x19, lsl #7
        mov     x0, x23
        bl      L29e4
        add     x1, x24, x19, lsl #10
        mov     x4, #0x0
L4fac:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w2, [x23, x4, lsl #2]
        add     w3, w0, w26
        cmp     w3, w27
        b.hi    L4fcc
        cmp     w2, #0x0
        ccmp    w0, w28, #0x0, ne
        b.ne    L4fdc
L4fcc:
        cmp     w20, #0x37
        b.eq    L501c
        strb    w4, [x21, w20, uxtw]
        add     w20, w20, #0x1
L4fdc:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L4fac
        add     x0, x22, #0xce7
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x6
        b.ne    L4f98
        mov     w0, #0x0
L5000:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L501c:
        mov     w0, #0xffffffff
        b       L5000

// mldsa65_pack_sig_z (0x14 bytes)
L5024:
        mov     w3, #0x280
        mul     w2, w2, w3
        add     x2, x2, #0x30
        add     x0, x0, x2
        b       L5704

// mldsa65_sig_unpack_hints (0xdc bytes)
L5038:
        stp     x19, x20, [sp, #-48]!
        mov     x3, x0
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, #0xcb0
        cbz     w2, L5088
        add     w0, w2, #0x36
        ldrb    w22, [x23, x0]
L5060:
        add     w0, w21, #0x37
        ldrb    w19, [x23, x0]
        cmp     w19, #0x37
        ccmp    w22, w19, #0x2, ls
        b.ls    L5090
L5074:
        mov     w0, #0xffffffff
L5078:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L5088:
        mov     w22, #0x0
        b       L5060
L5090:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        add     x2, x20, w22, uxtb
        mov     x3, x0
        mov     w1, w22
        mov     w4, #0x1
L50b0:
        cmp     w1, w19
        b.cc    L50d4
        cmp     w21, #0x5
        b.ne    L50cc
        add     x20, x20, #0xcaf
L50c4:
        cmp     w19, #0x37
        b.ne    L5104
L50cc:
        mov     w0, #0x0
        b       L5078
L50d4:
        cmp     w1, w22
        b.ls    L50f0
        sub     w0, w1, #0x1
        ldrb    w5, [x2, #3248]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L5074
L50f0:
        ldrb    w0, [x2, #3248]
        add     w1, w1, #0x1
        add     x2, x2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L50b0
L5104:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L50c4
        b       L5074

// mld_decompose65 (0x4c bytes)
L5114:
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
L5160:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c65.constprop.0 (0x60 bytes)
L517c:
        mov     x5, x0
        mov     w0, w1
        mov     x4, #0x0
        mov     w7, #0x4
L518c:
        cmp     w0, #0xff
        ccmp    w3, w4, #0x0, ls
        b.hi    L519c
        ret
L519c:
        ldrb    w1, [x2, x4]
        and     w6, w1, #0xf
        lsr     w1, w1, #4
        cmp     w6, #0x8
        b.hi    L51bc
        sub     w6, w7, w6
        str     w6, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
L51bc:
        cmp     w0, #0xff
        ccmp    w1, #0x8, #0x2, ls
        b.hi    L51d4
        sub     w1, w7, w1
        str     w1, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
L51d4:
        add     x4, x4, #0x1
        b       L518c

// mldsa65_poly_decompose (0x34 bytes)
L51dc:
        mov     x6, x0
        mov     x5, x1
        mov     x4, #0x0
        str     x30, [sp, #-16]!
L51ec:
        ldr     w2, [x5, x4]
        add     x1, x6, x4
        add     x0, x5, x4
        add     x4, x4, #0x4
        bl      L5114
        cmp     x4, #0x400
        b.ne    L51ec
        ldr     x30, [sp], #16
        ret

// mldsa65_poly_use_hint (0x98 bytes)
L5210:
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
L523c:
        ldr     w2, [x5, x4]
        mov     x1, x7
        ldr     w8, [x6, x4]
        bl      L5114
        ldr     w2, [sp, #20]
        cbz     w8, L5270
        ldr     w1, [sp, #16]
        add     w3, w2, #0x1
        sub     w2, w2, #0x1
        and     w3, w3, #0xf
        and     w2, w2, #0xf
        cmp     w1, #0x0
        csel    w2, w2, w3, le
L5270:
        str     w2, [x5, x4]
        add     x4, x4, #0x4
        cmp     x4, #0x400
        b.ne    L523c
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L52a0
        bl      L0e60
L52a0:
        ldr     x30, [sp], #32
        ret

// mldsa65_poly_uniform_eta_4x (0x234 bytes)
L52a8:
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
        bl      L1558
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1474
        mov     x5, x23
        mov     x4, #0x2
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14d8
        ldr     x0, [sp, #96]
        mov     w3, #0x110
        mov     x2, x19
        mov     w1, #0x0
        bl      L517c
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L517c
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L517c
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L53e0:
        mov     x0, x25
        bl      L517c
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L544c
        cmp     w22, #0xff
        b.ls    L544c
        cmp     w20, #0xff
        b.ls    L544c
        cmp     w0, #0xff
        b.ls    L544c
        mov     x0, x23
        bl      L155c
        mov     x0, x19
        mov     x1, #0x480
        bl      L5160
        mov     x0, x24
        mov     x1, #0x180
        bl      L5160
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L54bc
        bl      L0e60
L544c:
        mov     x5, x23
        mov     x4, #0x1
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14d8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     w3, #0x88
        mov     x2, x19
        bl      L517c
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L517c
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L517c
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L53e0
L54bc:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x9c0
        ret

// mldsa65_poly_challenge (0x160 bytes)
L54dc:
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
        bl      L1098
        mov     x1, x19
        mov     x2, #0x30
        mov     x0, x21
        bl      L10b8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10e0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1160
        mov     x0, #0x0
L554c:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L554c
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xcf
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e70
L5584:
        cmp     w19, #0x88
        b.ne    L5620
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1160
        mov     w0, #0x0
L55a0:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L5584
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
        b.ne    L5584
        mov     x0, x21
        bl      L1180
        mov     x0, x20
        mov     x1, #0x88
        bl      L5160
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L5160
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5628
        bl      L0e60
L5620:
        mov     w0, w19
        b       L55a0
L5628:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa65_polyeta_pack (0x8c bytes)
L563c:
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     x4, #0x0
        mov     w5, #0x4
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
L565c:
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
        b.ne    L565c
        add     x0, sp, #0x10
        mov     x1, #0x8
        strb    w3, [sp, #16]
        strb    w6, [sp, #17]
        bl      L5160
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L56c0
        bl      L0e60
L56c0:
        ldr     x30, [sp], #32
        ret

// mldsa65_polyeta_unpack (0x3c bytes)
L56c8:
        mov     x3, #0x0
        mov     w5, #0x4
L56d0:
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
        b.ne    L56d0
        ret

// mldsa65_polyz_pack (0xb8 bytes)
L5704:
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x9, x0, #0x280
        mov     w8, #0x80000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        mov     x2, x0
L5728:
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
        b.ne    L5728
        add     x1, x0, #0x200
        stp     w3, w5, [sp, #24]
        sturh   w3, [x1, #123]
        mov     x1, #0x10
        strb    w4, [x0, #637]
        strb    w7, [x0, #638]
        strb    w6, [x0, #639]
        add     x0, sp, #0x18
        bl      L5160
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L57b4
        bl      L0e60
L57b4:
        ldr     x30, [sp], #48
        ret

// mldsa65_polyz_unpack (0x70 bytes)
L57bc:
        add     x6, x0, #0x400
        mov     w5, #0x80000
L57c4:
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
        b.ne    L57c4
        ret

// mldsa65_poly_uniform_gamma1 (0xdc bytes)
L582c:
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
        bl      L1098
        mov     x1, x20
        mov     x2, #0x42
        mov     x0, x21
        bl      L10b8
        mov     x0, x21
        bl      L10e0
        mov     x2, x21
        mov     x0, x19
        mov     x1, #0x2a8
        bl      L1160
        mov     x1, x19
        mov     x0, x22
        bl      L57bc
        mov     x0, x21
        bl      L1180
        mov     x0, x19
        mov     x1, #0x2a8
        bl      L5160
        mov     x0, x20
        mov     x1, #0x42
        bl      L5160
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1064]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L58f4
        bl      L0e60
L58f4:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x430
        ret

// mldsa65_poly_uniform_gamma1_4x (0x17c bytes)
L5908:
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
        bl      L1558
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1474
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14d8
        mov     x1, x19
        mov     x0, x25
        bl      L57bc
        mov     x1, x27
        mov     x0, x24
        bl      L57bc
        mov     x1, x26
        mov     x0, x23
        bl      L57bc
        mov     x1, x21
        mov     x0, x22
        bl      L57bc
        mov     x0, x28
        bl      L155c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L5160
        mov     x0, x20
        mov     x1, #0x180
        bl      L5160
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5a60
        bl      L0e60
L5a60:
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
L5a84:
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
        bl      L5908
        add     w2, w20, #0x4
        mov     x1, x21
        ldp     x21, x30, [sp, #32]
        add     x0, x19, #0x1, lsl #12
        ldp     x19, x20, [sp, #16]
        add     sp, sp, #0x30
        b       L582c

// mldsa65_polyvecl_ntt (0x34 bytes)
L5ae0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1400
        add     x20, x19, x0
        str     x30, [sp, #16]
L5af4:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20c0
        cmp     x19, x20
        b.ne    L5af4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L5b14:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L5b24:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L5b30:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x5
        b.ne    L5b30
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L5b24
        ret

// mldsa65_polyvecl_chknorm (0x50 bytes)
L5b6c:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1400
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
L5b8c:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L28b8
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L5b8c
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyveck_caddq (0x34 bytes)
L5bbc:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L5bd0:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L201c
        cmp     x19, x20
        b.ne    L5bd0
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_ntt (0x34 bytes)
L5bf0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L5c04:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20c0
        cmp     x19, x20
        b.ne    L5c04
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_invntt_tomont (0x34 bytes)
L5c24:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L5c38:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2168
        cmp     x19, x20
        b.ne    L5c38
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_unpack_eta_chknorm (0x5c bytes)
L5c58:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L5c78:
        mov     x1, x19
        mov     x0, x20
        bl      L56c8
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x80
        bl      L28b8
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L5c78
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyveck_decompose_pack_w1 (0x58 bytes)
L5cb4:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        mov     x0, #0x1800
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, x0
        str     x30, [sp, #32]
L5cd4:
        mov     x1, x19
        mov     x0, x21
        bl      L51dc
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2960
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L5cd4
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyvecl_unpack_eta (0x40 bytes)
L5d0c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1400
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5d24:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L56c8
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L5d24
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvecl_unpack_z (0x40 bytes)
L5d4c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1400
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5d64:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L57bc
        add     x20, x20, #0x280
        cmp     x19, x21
        b.ne    L5d64
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_unpack_eta (0x40 bytes)
L5d8c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1800
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5da4:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L56c8
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L5da4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvec_matrix_expand_eager (0x15c bytes)
L5dcc:
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
L5dfc:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L5dfc
        mov     w20, #0x0
        mov     w21, #0x5
L5e1c:
        mov     x1, x19
        mov     w0, #0x0
L5e24:
        add     w2, w20, w0
        add     w0, w0, #0x1
        add     x1, x1, #0x40
        udiv    w3, w2, w21
        add     w4, w3, w3, lsl #2
        sturb   w3, [x1, #-31]
        sub     w2, w2, w4
        sturb   w2, [x1, #-32]
        cmp     w0, #0x4
        b.ne    L5e24
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
        bl      L23a8
        cmp     w20, #0x1c
        b.ne    L5e1c
        mov     w0, #0x503
        mov     x1, x19
        strh    w0, [x19, #32]
        add     x0, x22, #0x7, lsl #12
        bl      L22b4
        mov     w0, #0x504
        mov     x1, x19
        strh    w0, [x19, #32]
        mov     x0, #0x7400
        add     x0, x22, x0
        bl      L22b4
        mov     x0, x19
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e70
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5f18
        bl      L0e60
L5f18:
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret

// mldsa65_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L5f28:
        mov     w4, #0x1400
        umaddl  x1, w3, w4, x1
        b       L5b14

// mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L5f34:
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
        bl      L0e40
        mov     x0, x20
        bl      L5ae0
L5f68:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L5f28
        cmp     x19, #0x6
        b.ne    L5f68
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L5c24

// mld_ct_memcmp (0x54 bytes)
L5f9c:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L5fa8:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L5fd0
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L5fd0:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L5fa8

// mld_zeroize (0x1c bytes)
L5ff0:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t165 (0x160 bytes)
L600c:
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
        bl      L5dcc
L6084:
        mov     w3, w21
        mov     x2, x26
        mov     x1, x20
        mov     x0, x19
        bl      L5f28
        mov     x0, x19
        bl      L2168
        add     x1, x25, x21, lsl #7
        mov     x0, x22
        bl      L56c8
        mov     x1, x22
        mov     x0, x19
        bl      L2058
        mov     x0, x19
        bl      L1ff0
        mov     x0, x19
        bl      L201c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x22
        bl      L2284
        madd    x0, x21, x28, x24
        mov     x1, x22
        bl      L2584
        madd    x0, x21, x27, x23
        mov     x1, x19
        add     x21, x21, #0x1
        bl      L2650
        cmp     x21, #0x6
        b.ne    L6084
        mov     x0, x22
        mov     x1, #0x400
        bl      L5ff0
        mov     x0, x19
        mov     x1, #0x400
        bl      L5ff0
        mov     x0, x20
        mov     x1, #0x7800
        bl      L5ff0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x8, lsl #12
        ldr     x3, [x2, #120]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L6144
        bl      L0e60
L6144:
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
L616c:
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
        bl      L1098
        mov     x2, x27
        mov     x1, x26
        mov     x0, x19
        bl      L10b8
        cbz     x21, L61e4
        mov     x2, x21
        mov     x1, x25
        mov     x0, x19
        bl      L10b8
L61e4:
        cbz     x20, L61f8
        mov     x2, x20
        mov     x1, x24
        mov     x0, x19
        bl      L10b8
L61f8:
        mov     x0, x19
        bl      L10e0
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L1160
        mov     x0, x19
        bl      L1180
        mov     x0, x19
        mov     x1, #0xd0
        bl      L5ff0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6244
        bl      L0e60
L6244:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa65_keypair_internal (0x290 bytes)
L625c:
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
        bl      L1184
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
        bl      L52a8
        mov     x1, x19
        add     x0, x20, #0x400
        bl      L563c
        mov     x1, x23
        add     x0, x20, #0x480
        bl      L563c
        mov     x1, x24
        add     x0, x20, #0x500
        bl      L563c
        mov     x1, x26
        add     x0, x20, #0x580
        bl      L563c
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
        bl      L52a8
        ldr     x0, [sp, #120]
        mov     x1, x0
        add     x0, x20, #0x280
        bl      L563c
        mov     x1, x19
        mov     x0, x28
        bl      L563c
        mov     x1, x23
        add     x0, x20, #0x380
        bl      L563c
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
        bl      L52a8
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L563c
        mov     x1, x23
        add     x0, x20, #0x100
        bl      L563c
        mov     x1, x24
        add     x0, x20, #0x180
        bl      L563c
        mov     x1, x26
        add     x0, x20, #0x200
        bl      L563c
        mov     x0, x19
        bl      L5ae0
        ldp     q0, q1, [x21]
        mov     x4, x21
        mov     x3, x28
        mov     x2, x19
        add     x1, x20, #0x600
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L600c
        mov     x4, #0x1480
        mov     w23, w0
        add     x24, x19, x4
        cbnz    w0, L6458
        mov     x2, x22
        mov     x0, x24
        mov     x3, #0x7a0
        mov     x1, #0x40
        bl      L1184
        add     x3, x21, #0x60
        mov     x2, x24
        mov     x1, x21
        mov     x0, x20
        bl      L4e64
L6458:
        mov     x0, x19
        mov     x1, #0x1400
        bl      L5ff0
        mov     x0, x24
        mov     x1, #0x40
        bl      L5ff0
        mov     x0, x25
        mov     x1, #0x22
        bl      L5ff0
        mov     x0, x21
        mov     x1, #0x80
        bl      L5ff0
        cbz     w23, L64a4
        mov     x0, x22
        mov     x1, #0x7a0
        bl      L5ff0
        mov     x0, x20
        mov     x1, #0xfc0
        bl      L5ff0
L64a4:
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5512]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L64c4
        bl      L0e60
L64c4:
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
L64ec:
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
        bl      L0e50
        cbnz    w0, L6568
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L625c
        mov     w20, w0
L653c:
        mov     x0, x19
        mov     x1, #0x20
        bl      L5ff0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6570
        bl      L0e60
L6568:
        mov     w20, #0xfffffffd
        b       L653c
L6570:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa65_signature_internal (0x44c bytes)
L6580:
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
        bl      L4e8c
        add     x0, x21, #0x80
        cbnz    w27, L689c
        mov     x3, #0x40
        mov     x7, x25
        mov     x6, x26
        mov     x5, x24
        mov     x4, x22
        mov     x2, x28
        mov     x1, x3
        bl      L616c
L6654:
        mov     x5, #0x20
        add     x6, x21, #0x80
        mov     x4, x20
        mov     x3, x5
        add     x2, x21, #0x60
        mov     x7, #0x40
        add     x0, x21, #0xc0
        mov     x1, x7
        bl      L616c
        mov     x0, x19
        mov     x1, x21
        bl      L5dcc
        str     wzr, [sp, #124]
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0x400
        str     x0, [sp, #104]
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0x800
        str     x0, [sp, #112]
L66a0:
        ldrh    w2, [sp, #124]
        mov     x0, #0xd400
        add     x27, x19, x0
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0xc, lsl #12
        add     x25, x19, #0x10, lsl #12
        mov     w26, #0xff3c
        bl      L5a84
        mov     x28, #0x0
        mov     x1, #0x7800
        mov     x3, x20
        add     x24, x19, x1
        mov     x2, x27
        mov     x1, x19
        mov     x0, x24
        bl      L5f34
        movk    w26, #0x7, lsl #16
        mov     x0, x24
        bl      L5bbc
        ldr     x0, [sp, #104]
        mov     x3, #0xfc00
        mov     x2, x20
        mov     x1, x24
        add     x22, x19, x3
        bl      L5cb4
        ldp     x4, x0, [sp, #104]
        add     x2, x21, #0x80
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x300
        mov     x3, #0x40
        mov     x1, #0x30
        bl      L616c
        ldr     x1, [sp, #112]
        mov     x0, x25
        bl      L54dc
        mov     x0, x25
        bl      L20c0
L673c:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e40
        mov     x1, x25
        mov     x0, x22
        bl      L2248
        mov     x0, x22
        bl      L2168
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x3, x27
        bl      L0e40
        mov     x1, x20
        mov     x0, x22
        bl      L2058
        mov     x0, x22
        bl      L1ff0
        mov     w1, w26
        mov     x0, x22
        bl      L28b8
        cbnz    w0, L68b0
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L5024
        cmp     x28, #0x5
        b.ne    L673c
        mov     x26, #0x0
L67c4:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x24, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e40
        mov     x1, x25
        mov     x0, x20
        bl      L2248
        mov     x0, x20
        bl      L2168
        mov     x1, x20
        mov     x0, x28
        bl      L207c
        mov     x0, x28
        bl      L1ff0
        mov     w1, #0xfe3c
        mov     x0, x28
        movk    w1, #0x3, lsl #16
        bl      L28b8
        cbnz    w0, L68b0
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x26, x0
        mov     x0, x20
        bl      L0e40
        mov     x1, x25
        mov     x0, x20
        bl      L2248
        mov     x0, x20
        bl      L2168
        mov     x0, x20
        bl      L1ff0
        mov     x0, x20
        mov     w1, #0x3ff00
        bl      L28b8
        cbnz    w0, L68b0
        mov     x0, x28
        mov     x1, x20
        add     x26, x26, #0x400
        bl      L2058
        mov     x0, #0x1800
        cmp     x26, x0
        b.ne    L67c4
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L4f30
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x24
        mov     x0, x23
        bl      L4f44
        mov     w26, w0
        b       L68b4
L689c:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L6654
L68b0:
        mov     w26, #0xffffffff
L68b4:
        mov     x0, x22
        mov     x1, #0x400
        bl      L5ff0
        mov     x0, x25
        mov     x1, #0x400
        bl      L5ff0
        mov     x0, x24
        mov     x1, #0x1800
        bl      L5ff0
        ldr     x0, [sp, #104]
        mov     x1, #0x300
        bl      L5ff0
        mov     x0, x20
        mov     x1, #0x1400
        bl      L5ff0
        mov     x0, x27
        mov     x1, #0x1400
        bl      L5ff0
        ldr     x0, [sp, #112]
        mov     x1, #0x30
        bl      L5ff0
        cbz     w26, L6940
        cmn     w26, #0x1
        b.ne    L6934
        ldr     w0, [sp, #124]
        add     w0, w0, #0x5
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfffa
        cmp     w1, w0, uxth
        b.ne    L66a0
        mov     w26, #0xfffffffc
L6934:
        mov     x0, x23
        mov     x1, #0xced
        bl      L5ff0
L6940:
        ldr     x0, [sp, #128]
        mov     x1, #0x1800
        bl      L5ff0
        ldr     x0, [sp, #144]
        mov     x1, #0x1800
        bl      L5ff0
        ldr     x0, [sp, #136]
        mov     x1, #0x1400
        bl      L5ff0
        mov     x0, x19
        mov     x1, #0x7800
        bl      L5ff0
        mov     x0, x21
        mov     x1, #0x100
        bl      L5ff0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x10, lsl #12
        add     x2, x2, #0x40
        ldr     x3, [x2, #2216]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L69a4
        bl      L0e60
L69a4:
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
L69cc:
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
        bl      L0e50
        cbnz    w0, L6a64
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L6580
        mov     w20, w0
L6a38:
        mov     x0, x19
        mov     x1, #0x20
        bl      L5ff0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6a6c
        bl      L0e60
L6a64:
        mov     w20, #0xfffffffd
        b       L6a38
L6a6c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa65_verify_internal (0x324 bytes)
L6a80:
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
        bl      L5d4c
        mov     w1, #0xff3c
        mov     x0, x26
        movk    w1, #0x7, lsl #16
        bl      L5b6c
        mov     x17, #0x9b80
        mov     w20, w0
        add     x0, x19, x17
        str     x0, [sp, #104]
        cbnz    w20, L6cc4
        ldr     w6, [sp, #140]
        cbnz    w6, L6d64
        ldr     x2, [sp, #96]
        mov     x0, x24
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x7a0
        mov     x1, #0x40
        bl      L616c
        ldp     x7, x4, [sp, #112]
        mov     x10, #0x9b00
        ldr     x5, [sp, #128]
        mov     x6, x28
        mov     x2, x24
        mov     x3, #0x40
        add     x0, x19, x10
        mov     x1, x3
        bl      L616c
        mov     x0, x24
        mov     x1, #0x40
        bl      L5ff0
L6ba8:
        mov     x0, x26
        bl      L5ae0
        ldr     x1, [sp, #96]
        mov     x0, x19
        mov     x28, x24
        bl      L5dcc
        mov     x9, #0x9b80
        add     x1, x19, x9
        mov     x0, x27
        bl      L54dc
        mov     x0, x27
        bl      L20c0
L6bd8:
        mov     w3, w20
        mov     x2, x26
        mov     x1, x19
        mov     x0, x21
        bl      L5f28
        ldr     x1, [sp, #96]
        mov     w2, w20
        mov     x0, x22
        bl      L4e50
        mov     x0, x22
        bl      L20a0
        mov     x0, x22
        bl      L20c0
        mov     x1, x27
        mov     x0, x22
        bl      L2248
        mov     x1, x22
        mov     x0, x21
        bl      L207c
        mov     x0, x21
        bl      L1ff0
        mov     x0, x21
        bl      L2168
        mov     x0, x21
        bl      L201c
        mov     w2, w20
        mov     x1, x23
        mov     x0, x22
        bl      L5038
        mov     w25, w0
        cbnz    w0, L6cc4
        mov     x1, x22
        mov     x0, x21
        bl      L5210
        add     w20, w20, #0x1
        mov     x0, x28
        mov     x1, x21
        bl      L2960
        add     x28, x28, #0x80
        cmp     w20, #0x6
        b.ne    L6bd8
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
        bl      L616c
        ldr     x0, [sp, #104]
        mov     x1, x20
        mov     x2, #0x30
        bl      L5f9c
        tst     w0, #0xff
        b.eq    L6cc8
L6cc4:
        mov     w25, #0xfffffffa
L6cc8:
        mov     x0, x22
        mov     x1, #0x400
        bl      L5ff0
        mov     x0, x21
        mov     x1, #0x400
        bl      L5ff0
        mov     x0, x19
        mov     x1, #0x7800
        bl      L5ff0
        mov     x0, x27
        mov     x1, #0x400
        bl      L5ff0
        mov     x0, x26
        mov     x1, #0x1400
        bl      L5ff0
        mov     x1, #0x30
        mov     x0, #0x9b40
        add     x0, x19, x0
        bl      L5ff0
        ldr     x0, [sp, #104]
        mov     x1, #0x30
        bl      L5ff0
        mov     x2, #0x9b00
        mov     x1, #0x40
        add     x0, x19, x2
        bl      L5ff0
        mov     x0, x24
        mov     x1, #0x300
        bl      L5ff0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x3, #0x8030
        add     x2, sp, x3
        ldr     x3, [x2, #7208]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L6d7c
        bl      L0e60
L6d64:
        ldp     q0, q1, [x28]
        sub     x0, x25, #0x100
        stp     q0, q1, [x0]
        ldp     q0, q1, [x28, #32]
        stp     q0, q1, [x0, #32]
        b       L6ba8
L6d7c:
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
L6da4:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L6a80

// mldsa65_prepare_domain_separation_prefix (0x138 bytes)
L6dbc:
        cmp     x4, #0xff
        b.hi    L6ee4
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L6ea8
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L6eec
        .inst   0x90000020  // adrp x0, 0xa000
        add     x0, x0, #0x334
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 6e10 <mldsa65_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L6e14:
        b.ne    L6eec
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L6e34
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e40
L6e34:
        .inst   0x90000020  // adrp x0, 0xa000
        add     x0, x0, #0x340
        mov     x1, #0x0
L6e40:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L6ed4
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L6e70:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e40
        add     x0, x20, x19
        b       L6ec4
        cmp     x20, #0x20
        b       L6e14
        cmp     x20, #0x30
        b       L6e14
        cmp     x20, #0x40
        b       L6e14
L6ea8:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L6ec0
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e40
L6ec0:
        add     x0, x19, #0x2
L6ec4:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L6ed4:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L6e40
        b       L6e70
L6ee4:
        mov     x0, #0x0
        ret
L6eec:
        mov     x0, #0x0
        b       L6ec4

// mldsa65_signature (0x100 bytes)
L6ef4:
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
        bl      L6dbc
        cbz     x0, L6fcc
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e50
        cbnz    w0, L6fd4
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L6580
        mov     w19, w0
        cbz     w0, L6f94
L6f88:
        mov     x0, x21
        mov     x1, #0xced
        bl      L5ff0
L6f94:
        mov     x0, x22
        mov     x1, #0x20
        bl      L5ff0
        mov     x0, x20
        mov     x1, #0x14c
        bl      L5ff0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6fdc
        bl      L0e60
L6fcc:
        mov     w19, #0xfffffff7
        b       L6f88
L6fd4:
        mov     w19, #0xfffffffd
        b       L6f88
L6fdc:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa65_verify (0xbc bytes)
L6ff4:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x5
        .inst   0xb00000c5  // adrp x5, 0x1f000
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
        bl      L6dbc
        cbz     x0, L7094
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L6a80
        mov     w20, w0
L7068:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L5ff0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L709c
        bl      L0e60
L7094:
        mov     w20, #0xfffffff7
        b       L7068
L709c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa65_signature_pre_hash_internal (0xc8 bytes)
L70b0:
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
        cbnz    w7, L70f8
L70e4:
        mov     w19, #0xfffffff7
L70e8:
        mov     x0, x21
        mov     x1, #0xced
        bl      L5ff0
        b       L7138
L70f8:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L6dbc
        mov     x2, x0
        cbz     x0, L70e4
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L6580
        mov     w19, w0
        cbnz    w0, L70e8
L7138:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L5ff0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7164
        bl      L0e60
L7164:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa65_signature_pre_hash_shake256 (0xc0 bytes)
L7178:
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
        bl      L1184
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L70b0
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L5ff0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7220
        bl      L0e60
L7220:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa65_verify_pre_hash_internal (0xa8 bytes)
L7238:
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
        cbnz    w5, L729c
L726c:
        mov     w20, #0xfffffff7
L7270:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L5ff0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L72d0
        bl      L0e60
L729c:
        mov     x0, x19
        bl      L6dbc
        mov     x2, x0
        cbz     x0, L726c
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L6a80
        mov     w20, w0
        b       L7270
L72d0:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa65_verify_pre_hash_shake256 (0xb0 bytes)
L72e0:
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
        bl      L1184
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L7238
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L5ff0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L737c
        bl      L0e60
L737c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa65_pk_from_sk (0x210 bytes)
L7390:
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
        bl      L5d0c
        mov     w1, #0x5
        mov     x0, x19
        bl      L5b6c
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x5
        mov     x0, x23
        bl      L5c58
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L5ae0
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L600c
        mov     x6, #0x21c0
        mov     w22, w0
        add     x23, x19, x6
        cbnz    w0, L74f4
        add     x1, x25, #0x600
        mov     x0, x24
        mov     x2, #0x9c0
        bl      L5f9c
        and     w4, w0, #0xff
        mov     x3, #0x7a0
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1184
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L5f9c
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L7500
        mov     w22, #0xfffffff9
L74f4:
        mov     x0, x21
        mov     x1, #0x7a0
        bl      L5ff0
L7500:
        mov     x0, x24
        mov     x1, #0x9c0
        bl      L5ff0
        mov     x0, x28
        mov     x1, #0x400
        bl      L5ff0
        mov     x0, x19
        mov     x1, #0x1400
        bl      L5ff0
        mov     x1, #0x20
        mov     x0, #0x2240
        add     x0, x19, x0
        bl      L5ff0
        mov     x0, x23
        mov     x1, #0x40
        bl      L5ff0
        mov     x0, x27
        mov     x1, #0x40
        bl      L5ff0
        mov     x0, x26
        mov     x1, #0x20
        bl      L5ff0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8968]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7578
        bl      L0e60
L7578:
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
L75a0:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25e0

// mldsa87_pack_sk_rho_key_tr (0x28 bytes)
L75b4:
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
L75dc:
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
        bl      L8510
        mov     x0, x22
        mov     x22, x20
        bl      L82f4
        add     x1, x19, #0x320
        mov     x0, x21
        bl      L8590
        mov     x0, x21
        add     x21, x19, #0x620
        bl      L8400
        mov     x0, #0x1320
        add     x19, x19, x0
L7654:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L2764
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L7654
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L8400

// mldsa87_pack_sig_c (0x14 bytes)
L7684:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x1, #32]
        stp     q0, q1, [x0, #32]
        ret

// mldsa87_pack_sig_h (0xe8 bytes)
L7698:
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
        bl      L0e70
L76f0:
        add     x1, x24, x19, lsl #7
        mov     x0, x22
        bl      L29e4
        add     x1, x23, x19, lsl #10
        mov     x4, #0x0
L7704:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w2, [x22, x4, lsl #2]
        add     w3, w0, w26
        cmp     w3, w27
        b.hi    L7724
        cmp     w2, #0x0
        ccmp    w0, w28, #0x0, ne
        b.ne    L7734
L7724:
        cmp     w20, #0x4b
        b.eq    L7778
        strb    w4, [x25, w20, uxtw]
        add     w20, w20, #0x1
L7734:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L7704
        mov     x0, #0x120b
        add     x0, x21, x0
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x8
        b.ne    L76f0
        mov     w0, #0x0
L775c:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L7778:
        mov     w0, #0xffffffff
        b       L775c

// mldsa87_pack_sig_z (0x14 bytes)
L7780:
        mov     w3, #0x280
        mul     w2, w2, w3
        add     x2, x2, #0x40
        add     x0, x0, x2
        b       L7fc0

// mldsa87_sig_unpack_hints (0xe8 bytes)
L7794:
        stp     x19, x20, [sp, #-48]!
        mov     x4, #0x11c0
        mov     x3, x0
        stp     x21, x22, [sp, #16]
        mov     x20, x1
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, x4
        cbz     w2, L77e8
        add     w0, w2, #0x4a
        ldrb    w22, [x23, x0]
L77c0:
        add     w0, w21, #0x4b
        ldrb    w19, [x23, x0]
        cmp     w19, #0x4b
        ccmp    w22, w19, #0x2, ls
        b.ls    L77f0
L77d4:
        mov     w0, #0xffffffff
L77d8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L77e8:
        mov     w22, #0x0
        b       L77c0
L77f0:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     w1, #0x11c0
        add     w1, w22, w1
        mov     x3, x0
        add     x1, x20, x1
        mov     w2, w22
        mov     w4, #0x1
L7818:
        cmp     w2, w19
        b.cc    L7840
        cmp     w21, #0x7
        b.ne    L7838
        mov     x0, #0x11bf
        add     x20, x20, x0
L7830:
        cmp     w19, #0x4b
        b.ne    L786c
L7838:
        mov     w0, #0x0
        b       L77d8
L7840:
        cmp     w2, w22
        b.ls    L785c
        sub     w0, w2, #0x1
        ldrb    w5, [x1]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L77d4
L785c:
        ldrb    w0, [x1], #1
        add     w2, w2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L7818
L786c:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L7830
        b       L77d4

// mld_decompose87 (0x4c bytes)
L787c:
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
L78c8:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c87.constprop.0 (0x88 bytes)
L78e4:
        mov     x6, x0
        mov     w0, w1
        mov     x5, #0x0
        mov     w9, #0x87
        mov     w7, #0xcd
        mov     w8, #0x2
L78fc:
        cmp     w0, #0xff
        ccmp    w5, w9, #0x2, ls
        b.ls    L790c
        ret
L790c:
        ldrb    w1, [x2, x5]
        and     w3, w1, #0xf
        lsr     w1, w1, #4
        cmp     w3, #0xf
        b.eq    L793c
        mul     w4, w3, w7
        lsr     w4, w4, #10
        add     w4, w4, w4, lsl #2
        sub     w3, w3, w4
        sub     w3, w8, w3
        str     w3, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L793c:
        cmp     w0, #0xff
        ccmp    w1, #0xe, #0x2, ls
        b.hi    L7964
        mul     w3, w1, w7
        lsr     w3, w3, #10
        add     w3, w3, w3, lsl #2
        sub     w1, w1, w3
        sub     w1, w8, w1
        str     w1, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L7964:
        add     x5, x5, #0x1
        b       L78fc

// mldsa87_poly_decompose (0x34 bytes)
L796c:
        mov     x6, x0
        mov     x5, x1
        mov     x4, #0x0
        str     x30, [sp, #-16]!
L797c:
        ldr     w2, [x5, x4]
        add     x1, x6, x4
        add     x0, x5, x4
        add     x4, x4, #0x4
        bl      L787c
        cmp     x4, #0x400
        b.ne    L797c
        ldr     x30, [sp], #16
        ret

// mldsa87_poly_use_hint (0x98 bytes)
L79a0:
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
L79cc:
        ldr     w2, [x5, x4]
        mov     x1, x7
        ldr     w8, [x6, x4]
        bl      L787c
        ldr     w2, [sp, #20]
        cbz     w8, L7a00
        ldr     w1, [sp, #16]
        add     w3, w2, #0x1
        sub     w2, w2, #0x1
        and     w3, w3, #0xf
        and     w2, w2, #0xf
        cmp     w1, #0x0
        csel    w2, w2, w3, le
L7a00:
        str     w2, [x5, x4]
        add     x4, x4, #0x4
        cmp     x4, #0x400
        b.ne    L79cc
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7a30
        bl      L0e60
L7a30:
        ldr     x30, [sp], #32
        ret

// mldsa87_poly_uniform_eta_4x (0x22c bytes)
L7a38:
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
        bl      L1558
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1474
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14d8
        ldr     x0, [sp, #96]
        mov     x2, x19
        mov     w1, #0x0
        bl      L78e4
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L78e4
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L78e4
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L7b6c:
        mov     x0, x25
        bl      L78e4
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L7bd8
        cmp     w22, #0xff
        b.ls    L7bd8
        cmp     w20, #0xff
        b.ls    L7bd8
        cmp     w0, #0xff
        b.ls    L7bd8
        mov     x0, x23
        bl      L155c
        mov     x0, x19
        mov     x1, #0x280
        bl      L78c8
        mov     x0, x24
        mov     x1, #0x180
        bl      L78c8
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1976]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7c44
        bl      L0e60
L7bd8:
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14d8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     x2, x19
        bl      L78e4
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L78e4
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L78e4
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L7b6c
L7c44:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7c0
        ret

// mldsa87_poly_challenge (0x160 bytes)
L7c64:
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
        bl      L1098
        mov     x1, x19
        mov     x2, #0x40
        mov     x0, x21
        bl      L10b8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10e0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1160
        mov     x0, #0x0
L7cd4:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L7cd4
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xc4
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e70
L7d0c:
        cmp     w19, #0x88
        b.ne    L7da8
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1160
        mov     w0, #0x0
L7d28:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L7d0c
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
        b.ne    L7d0c
        mov     x0, x21
        bl      L1180
        mov     x0, x20
        mov     x1, #0x88
        bl      L78c8
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L78c8
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7db0
        bl      L0e60
L7da8:
        mov     w0, w19
        b       L7d28
L7db0:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa87_polyeta_pack (0x13c bytes)
L7dc4:
        .inst   0x900000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x30, [sp, #-32]!
        mov     x8, x0
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x14, x1, #0x400
        mov     w6, #0x2
L7de8:
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
        b.ne    L7de8
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
        bl      L78c8
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7ef8
        bl      L0e60
L7ef8:
        ldp     x19, x30, [sp], #32
        ret

// mldsa87_polyeta_unpack (0xc0 bytes)
L7f00:
        add     x11, x0, #0x400
        mov     w2, #0x2
L7f08:
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
        b.ne    L7f08
        ret

// mldsa87_polyz_pack (0xb8 bytes)
L7fc0:
        .inst   0x900000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x9, x0, #0x280
        mov     w8, #0x80000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        mov     x2, x0
L7fe4:
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
        b.ne    L7fe4
        add     x1, x0, #0x200
        stp     w3, w5, [sp, #24]
        sturh   w3, [x1, #123]
        mov     x1, #0x10
        strb    w4, [x0, #637]
        strb    w7, [x0, #638]
        strb    w6, [x0, #639]
        add     x0, sp, #0x18
        bl      L78c8
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8070
        bl      L0e60
L8070:
        ldr     x30, [sp], #48
        ret

// mldsa87_polyz_unpack (0x70 bytes)
L8078:
        add     x6, x0, #0x400
        mov     w5, #0x80000
L8080:
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
        b.ne    L8080
        ret

// mldsa87_poly_uniform_gamma1_4x (0x17c bytes)
L80e8:
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
        bl      L1558
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1474
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14d8
        mov     x1, x19
        mov     x0, x25
        bl      L8078
        mov     x1, x27
        mov     x0, x24
        bl      L8078
        mov     x1, x26
        mov     x0, x23
        bl      L8078
        mov     x1, x21
        mov     x0, x22
        bl      L8078
        mov     x0, x28
        bl      L155c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L78c8
        mov     x0, x20
        mov     x1, #0x180
        bl      L78c8
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8240
        bl      L0e60
L8240:
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
L8264:
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
        bl      L80e8
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
        bl      L80e8
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, #0x40
        ret

// mldsa87_polyvecl_ntt (0x34 bytes)
L82f4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1c00
        add     x20, x19, x0
        str     x30, [sp, #16]
L8308:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20c0
        cmp     x19, x20
        b.ne    L8308
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L8328:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L8338:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L8344:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x7
        b.ne    L8344
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L8338
        ret

// mldsa87_polyvecl_chknorm (0x50 bytes)
L8380:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1c00
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
L83a0:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L28b8
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L83a0
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyveck_caddq (0x30 bytes)
L83d0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L83e0:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L201c
        cmp     x19, x20
        b.ne    L83e0
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_ntt (0x30 bytes)
L8400:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L8410:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20c0
        cmp     x19, x20
        b.ne    L8410
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_invntt_tomont (0x30 bytes)
L8430:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L8440:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2168
        cmp     x19, x20
        b.ne    L8440
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta_chknorm (0x5c bytes)
L8460:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L8480:
        mov     x1, x19
        mov     x0, x20
        bl      L7f00
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L28b8
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L8480
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyveck_decompose_pack_w1 (0x54 bytes)
L84bc:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, #0x2, lsl #12
        str     x30, [sp, #32]
L84d8:
        mov     x1, x19
        mov     x0, x21
        bl      L796c
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2960
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L84d8
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyvecl_unpack_eta (0x40 bytes)
L8510:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1c00
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L8528:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L7f00
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L8528
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvecl_unpack_z (0x40 bytes)
L8550:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1c00
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L8568:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L8078
        add     x20, x20, #0x280
        cmp     x19, x21
        b.ne    L8568
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta (0x3c bytes)
L8590:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x2, lsl #12
L85a4:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L7f00
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L85a4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvec_matrix_expand_eager (0x11c bytes)
L85cc:
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
L85fc:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L85fc
        mov     w20, #0x0
        mov     w19, #0x7
L861c:
        mov     x1, x21
        mov     w0, #0x0
L8624:
        add     w2, w20, w0
        add     w0, w0, #0x1
        add     x1, x1, #0x40
        udiv    w3, w2, w19
        msub    w2, w3, w19, w2
        sturb   w3, [x1, #-31]
        sturb   w2, [x1, #-32]
        cmp     w0, #0x4
        b.ne    L8624
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
        bl      L23a8
        cmp     w20, #0x38
        b.ne    L861c
        mov     x0, x21
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e70
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L86d8
        bl      L0e60
L86d8:
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret

// mldsa87_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L86e8:
        mov     w4, #0x1c00
        umaddl  x1, w3, w4, x1
        b       L8328

// mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L86f4:
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
        bl      L0e40
        mov     x0, x20
        bl      L82f4
L8728:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L86e8
        cmp     x19, #0x8
        b.ne    L8728
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L8430

// mld_ct_memcmp (0x54 bytes)
L875c:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L8768:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L8790
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L8790:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L8768

// mld_zeroize (0x1c bytes)
L87b0:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t187 (0x168 bytes)
L87cc:
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
        bl      L85cc
L8848:
        ldr     x2, [sp, #104]
        mov     w3, w25
        mov     x1, x20
        mov     x0, x19
        bl      L86e8
        mov     x0, x19
        bl      L2168
        madd    x1, x25, x28, x24
        mov     x0, x21
        bl      L7f00
        mov     x1, x21
        mov     x0, x19
        bl      L2058
        mov     x0, x19
        bl      L1ff0
        mov     x0, x19
        bl      L201c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x21
        bl      L2284
        madd    x0, x25, x27, x23
        mov     x1, x21
        bl      L2584
        madd    x0, x25, x26, x22
        mov     x1, x19
        add     x25, x25, #0x1
        bl      L2650
        cmp     x25, #0x8
        b.ne    L8848
        mov     x0, x21
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x19
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x20
        mov     x1, #0xe000
        bl      L87b0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x1, #0xc010
        add     x2, sp, x1
        ldr     x3, [x2, #10360]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L890c
        bl      L0e60
L890c:
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
L8934:
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
        bl      L1098
        mov     x2, x26
        mov     x1, x25
        mov     x0, x19
        bl      L10b8
        cbz     x21, L89a8
        mov     x2, x21
        mov     x1, x24
        mov     x0, x19
        bl      L10b8
L89a8:
        cbz     x20, L89bc
        mov     x2, x20
        mov     x1, x23
        mov     x0, x19
        bl      L10b8
L89bc:
        mov     x0, x19
        bl      L10e0
        mov     x2, x19
        mov     x1, #0x40
        mov     x0, x22
        bl      L1160
        mov     x0, x19
        bl      L1180
        mov     x0, x19
        mov     x1, #0xd0
        bl      L87b0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8a08
        bl      L0e60
L8a08:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa87_keypair_internal (0x304 bytes)
L8a20:
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
        bl      L1184
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
        bl      L7a38
        mov     x1, x19
        add     x0, x20, #0x4a0
        bl      L7dc4
        mov     x1, x25
        add     x0, x20, #0x500
        bl      L7dc4
        mov     x1, x24
        add     x0, x20, #0x560
        bl      L7dc4
        mov     x1, x23
        add     x0, x20, #0x5c0
        bl      L7dc4
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
        bl      L7a38
        mov     x1, x19
        mov     x0, x28
        bl      L7dc4
        mov     x1, x25
        add     x0, x20, #0x380
        bl      L7dc4
        mov     x1, x24
        add     x0, x20, #0x3e0
        bl      L7dc4
        mov     x1, x23
        add     x0, x20, #0x440
        bl      L7dc4
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
        bl      L7a38
        ldr     x0, [sp, #120]
        mov     x1, x0
        add     x0, x20, #0x200
        bl      L7dc4
        ldr     x8, [sp, #128]
        add     x0, x20, #0x260
        mov     x1, x8
        bl      L7dc4
        ldr     x2, [sp, #136]
        add     x0, x20, #0x2c0
        mov     x1, x2
        bl      L7dc4
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
        bl      L7a38
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L7dc4
        mov     x1, x25
        add     x0, x20, #0xe0
        bl      L7dc4
        mov     x1, x24
        add     x0, x20, #0x140
        bl      L7dc4
        mov     x1, x23
        add     x0, x20, #0x1a0
        bl      L7dc4
        mov     x0, x19
        bl      L82f4
        ldp     q0, q1, [x21]
        mov     x4, x21
        mov     x3, x28
        mov     x2, x19
        add     x1, x20, #0x620
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L87cc
        mov     x6, #0x1c80
        mov     w23, w0
        add     x24, x19, x6
        cbnz    w0, L8c90
        mov     x2, x22
        mov     x0, x24
        mov     x3, #0xa20
        mov     x1, #0x40
        bl      L1184
        add     x3, x21, #0x60
        mov     x2, x24
        mov     x1, x21
        mov     x0, x20
        bl      L75b4
L8c90:
        mov     x0, x19
        mov     x1, #0x1c00
        bl      L87b0
        mov     x0, x24
        mov     x1, #0x40
        bl      L87b0
        mov     x0, x26
        mov     x1, #0x22
        bl      L87b0
        mov     x0, x21
        mov     x1, #0x80
        bl      L87b0
        cbz     w23, L8cdc
        mov     x0, x22
        mov     x1, #0xa20
        bl      L87b0
        mov     x0, x20
        mov     x1, #0x1320
        bl      L87b0
L8cdc:
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7576]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8cfc
        bl      L0e60
L8cfc:
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
L8d24:
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
        bl      L0e50
        cbnz    w0, L8da0
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L8a20
        mov     w20, w0
L8d74:
        mov     x0, x19
        mov     x1, #0x20
        bl      L87b0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8da8
        bl      L0e60
L8da0:
        mov     w20, #0xfffffffd
        b       L8d74
L8da8:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa87_signature_internal (0x434 bytes)
L8db8:
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
        bl      L75dc
        add     x0, x21, #0x80
        cbnz    w27, L90bc
        mov     x6, x25
        mov     x5, x26
        mov     x4, x24
        mov     x3, x22
        mov     x1, x28
        mov     x2, #0x40
        bl      L8934
L8e80:
        mov     x4, #0x20
        add     x5, x21, #0x80
        mov     x3, x20
        mov     x2, x4
        mov     x6, #0x40
        add     x1, x21, #0x60
        add     x0, x21, #0xc0
        bl      L8934
        mov     x0, x19
        mov     x1, x21
        bl      L85cc
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
L8ed8:
        ldrh    w2, [sp, #124]
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0x14, lsl #12
        add     x25, x19, #0xe, lsl #12
        add     x22, x19, #0x19, lsl #12
        mov     w26, #0xff88
        add     x22, x22, #0x400
        bl      L8264
        mov     x28, #0x0
        mov     x3, x20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x25
        bl      L86f4
        movk    w26, #0x7, lsl #16
        mov     x0, x25
        bl      L83d0
        ldr     x0, [sp, #104]
        mov     x2, x20
        mov     x1, x25
        bl      L84bc
        ldp     x3, x0, [sp, #104]
        add     x1, x21, #0x80
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x400
        mov     x2, #0x40
        bl      L8934
        ldr     x1, [sp, #112]
        mov     x0, x24
        bl      L7c64
        mov     x0, x24
        bl      L20c0
L8f60:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e40
        mov     x1, x24
        mov     x0, x22
        bl      L2248
        mov     x0, x22
        bl      L2168
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x3, x27
        bl      L0e40
        mov     x1, x20
        mov     x0, x22
        bl      L2058
        mov     x0, x22
        bl      L1ff0
        mov     w1, w26
        mov     x0, x22
        bl      L28b8
        cbnz    w0, L90d0
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L7780
        cmp     x28, #0x7
        b.ne    L8f60
        mov     x26, #0x0
L8fe8:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x25, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e40
        mov     x1, x24
        mov     x0, x20
        bl      L2248
        mov     x0, x20
        bl      L2168
        mov     x1, x20
        mov     x0, x28
        bl      L207c
        mov     x0, x28
        bl      L1ff0
        mov     w1, #0xfe88
        mov     x0, x28
        movk    w1, #0x3, lsl #16
        bl      L28b8
        cbnz    w0, L90d0
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e40
        mov     x1, x24
        mov     x0, x20
        bl      L2248
        mov     x0, x20
        bl      L2168
        mov     x0, x20
        bl      L1ff0
        mov     x0, x20
        mov     w1, #0x3ff00
        bl      L28b8
        cbnz    w0, L90d0
        mov     x1, x20
        mov     x0, x28
        add     x26, x26, #0x400
        bl      L2058
        cmp     x26, #0x2, lsl #12
        b.ne    L8fe8
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L7684
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x25
        mov     x0, x23
        bl      L7698
        mov     w26, w0
        b       L90d4
L90bc:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L8e80
L90d0:
        mov     w26, #0xffffffff
L90d4:
        mov     x0, x22
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x24
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x25
        mov     x1, #0x2000
        bl      L87b0
        ldr     x0, [sp, #104]
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x20
        mov     x1, #0x1c00
        bl      L87b0
        mov     x0, x27
        mov     x1, #0x1c00
        bl      L87b0
        ldr     x0, [sp, #112]
        mov     x1, #0x40
        bl      L87b0
        cbz     w26, L9160
        cmn     w26, #0x1
        b.ne    L9154
        ldr     w0, [sp, #124]
        add     w0, w0, #0x7
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfff7
        cmp     w1, w0, uxth
        b.ne    L8ed8
        mov     w26, #0xfffffffc
L9154:
        mov     x0, x23
        mov     x1, #0x1213
        bl      L87b0
L9160:
        ldr     x0, [sp, #128]
        mov     x1, #0x2000
        bl      L87b0
        ldr     x0, [sp, #144]
        mov     x1, #0x2000
        bl      L87b0
        ldr     x0, [sp, #136]
        mov     x1, #0x1c00
        bl      L87b0
        mov     x0, x19
        mov     x1, #0xe000
        bl      L87b0
        mov     x0, x21
        mov     x1, #0x100
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x18, lsl #12
        add     x2, x2, #0x40
        ldr     x3, [x2, #8632]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L91c4
        bl      L0e60
L91c4:
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
L91ec:
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
        bl      L0e50
        cbnz    w0, L9284
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L8db8
        mov     w20, w0
L9258:
        mov     x0, x19
        mov     x1, #0x20
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L928c
        bl      L0e60
L9284:
        mov     w20, #0xfffffffd
        b       L9258
L928c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa87_verify_internal (0x30c bytes)
L92a0:
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
        bl      L8550
        mov     w1, #0xff88
        mov     x0, x27
        movk    w1, #0x7, lsl #16
        bl      L8380
        mov     w20, w0
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0xc40
        str     x0, [sp, #112]
        cbnz    w20, L94d0
        ldr     w6, [sp, #140]
        cbnz    w6, L956c
        ldr     x1, [sp, #104]
        mov     x0, x24
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0xa20
        bl      L8934
        ldp     x3, x4, [sp, #120]
        mov     x5, x25
        ldr     x6, [sp, #96]
        add     x0, x19, #0x10, lsl #12
        mov     x2, #0x40
        mov     x1, x24
        add     x0, x0, #0xc80
        bl      L8934
        mov     x0, x24
        mov     x1, #0x40
        bl      L87b0
L93b8:
        mov     x0, x27
        bl      L82f4
        ldr     x1, [sp, #104]
        mov     x0, x19
        bl      L85cc
        add     x1, x19, #0x10, lsl #12
        mov     x0, x28
        add     x1, x1, #0xc40
        bl      L7c64
        mov     x0, x28
        bl      L20c0
        str     x24, [sp, #96]
L93e8:
        mov     w3, w20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x21
        bl      L86e8
        ldr     x1, [sp, #104]
        mov     w2, w20
        mov     x0, x22
        bl      L75a0
        mov     x0, x22
        bl      L20a0
        mov     x0, x22
        bl      L20c0
        mov     x1, x28
        mov     x0, x22
        bl      L2248
        mov     x1, x22
        mov     x0, x21
        bl      L207c
        mov     x0, x21
        bl      L1ff0
        mov     x0, x21
        bl      L2168
        mov     x0, x21
        bl      L201c
        mov     w2, w20
        mov     x1, x23
        mov     x0, x22
        bl      L7794
        mov     w25, w0
        cbnz    w0, L94d0
        mov     x1, x22
        mov     x0, x21
        bl      L79a0
        add     w20, w20, #0x1
        ldr     x0, [sp, #96]
        mov     x1, x21
        bl      L2960
        ldr     x0, [sp, #96]
        add     x0, x0, #0x80
        str     x0, [sp, #96]
        cmp     w20, #0x8
        b.ne    L93e8
        add     x1, x19, #0x10, lsl #12
        mov     x0, x26
        add     x1, x1, #0xc80
        mov     x2, #0x40
        mov     x3, x24
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x400
        bl      L8934
        ldr     x0, [sp, #112]
        mov     x1, x26
        mov     x2, #0x40
        bl      L875c
        tst     w0, #0xff
        b.eq    L94d4
L94d0:
        mov     w25, #0xfffffffa
L94d4:
        mov     x0, x22
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x21
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x19
        mov     x1, #0xe000
        bl      L87b0
        mov     x0, x28
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x27
        mov     x1, #0x1c00
        bl      L87b0
        mov     x0, x26
        mov     x1, #0x40
        bl      L87b0
        ldr     x0, [sp, #112]
        mov     x1, #0x40
        bl      L87b0
        add     x0, x19, #0x10, lsl #12
        mov     x1, #0x40
        add     x0, x0, #0xc80
        bl      L87b0
        mov     x0, x24
        mov     x1, #0x400
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x10, lsl #12
        add     x2, x2, #0x30
        ldr     x3, [x2, #3384]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L9584
        bl      L0e60
L956c:
        ldp     q0, q1, [x25]
        add     x0, x26, #0x80
        stp     q0, q1, [x0]
        ldp     q0, q1, [x25, #32]
        stp     q0, q1, [x0, #32]
        b       L93b8
L9584:
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
L95ac:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L92a0

// mldsa87_prepare_domain_separation_prefix (0x138 bytes)
L95c4:
        cmp     x4, #0xff
        b.hi    L96ec
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L96b0
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L96f4
        .inst   0xb0000000  // adrp x0, 0xa000
        add     x0, x0, #0x400
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 9618 <mldsa87_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L961c:
        b.ne    L96f4
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L963c
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e40
L963c:
        .inst   0xb0000000  // adrp x0, 0xa000
        add     x0, x0, #0x40c
        mov     x1, #0x0
L9648:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L96dc
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L9678:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e40
        add     x0, x20, x19
        b       L96cc
        cmp     x20, #0x20
        b       L961c
        cmp     x20, #0x30
        b       L961c
        cmp     x20, #0x40
        b       L961c
L96b0:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L96c8
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e40
L96c8:
        add     x0, x19, #0x2
L96cc:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L96dc:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L9648
        b       L9678
L96ec:
        mov     x0, #0x0
        ret
L96f4:
        mov     x0, #0x0
        b       L96cc

// mldsa87_signature (0x100 bytes)
L96fc:
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
        bl      L95c4
        cbz     x0, L97d4
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e50
        cbnz    w0, L97dc
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L8db8
        mov     w19, w0
        cbz     w0, L979c
L9790:
        mov     x0, x21
        mov     x1, #0x1213
        bl      L87b0
L979c:
        mov     x0, x22
        mov     x1, #0x20
        bl      L87b0
        mov     x0, x20
        mov     x1, #0x14c
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L97e4
        bl      L0e60
L97d4:
        mov     w19, #0xfffffff7
        b       L9790
L97dc:
        mov     w19, #0xfffffffd
        b       L9790
L97e4:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa87_verify (0xbc bytes)
L97fc:
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
        bl      L95c4
        cbz     x0, L989c
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L92a0
        mov     w20, w0
L9870:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L98a4
        bl      L0e60
L989c:
        mov     w20, #0xfffffff7
        b       L9870
L98a4:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa87_signature_pre_hash_internal (0xc8 bytes)
L98b8:
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
        cbnz    w7, L9900
L98ec:
        mov     w19, #0xfffffff7
L98f0:
        mov     x0, x21
        mov     x1, #0x1213
        bl      L87b0
        b       L9940
L9900:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L95c4
        mov     x2, x0
        cbz     x0, L98ec
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L8db8
        mov     w19, w0
        cbnz    w0, L98f0
L9940:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L996c
        bl      L0e60
L996c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa87_signature_pre_hash_shake256 (0xc0 bytes)
L9980:
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
        bl      L1184
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L98b8
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9a28
        bl      L0e60
L9a28:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa87_verify_pre_hash_internal (0xa8 bytes)
L9a40:
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
        cbnz    w5, L9aa4
L9a74:
        mov     w20, #0xfffffff7
L9a78:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9ad8
        bl      L0e60
L9aa4:
        mov     x0, x19
        bl      L95c4
        mov     x2, x0
        cbz     x0, L9a74
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L92a0
        mov     w20, w0
        b       L9a78
L9ad8:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa87_verify_pre_hash_shake256 (0xb0 bytes)
L9ae8:
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
        bl      L1184
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L9a40
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9b84
        bl      L0e60
L9b84:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa87_pk_from_sk (0x20c bytes)
L9b98:
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
        bl      L8510
        mov     w1, #0x3
        mov     x0, x19
        bl      L8380
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x3
        mov     x0, x23
        bl      L8460
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L82f4
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L87cc
        mov     x6, #0x2d00
        mov     w22, w0
        add     x23, x19, x6
        cbnz    w0, L9cf8
        add     x1, x25, #0x620
        mov     x0, x24
        mov     x2, #0xd00
        bl      L875c
        and     w4, w0, #0xff
        mov     x3, #0xa20
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1184
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L875c
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L9d04
        mov     w22, #0xfffffff9
L9cf8:
        mov     x0, x21
        mov     x1, #0xa20
        bl      L87b0
L9d04:
        mov     x0, x24
        mov     x1, #0xd00
        bl      L87b0
        mov     x0, x28
        mov     x1, #0x400
        bl      L87b0
        mov     x0, x19
        mov     x1, #0x1c00
        bl      L87b0
        mov     x1, #0x20
        mov     x0, #0x2d80
        add     x0, x19, x0
        bl      L87b0
        mov     x0, x23
        mov     x1, #0x40
        bl      L87b0
        mov     x0, x27
        mov     x1, #0x40
        bl      L87b0
        mov     x0, x26
        mov     x1, #0x20
        bl      L87b0
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #11848]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9d7c
        bl      L0e60
L9d7c:
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

// Padding (0x9da4 to 0x9da8)

        .long   0x00000000

// The read-only data (0x9da8 to 0xa4cc)

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
