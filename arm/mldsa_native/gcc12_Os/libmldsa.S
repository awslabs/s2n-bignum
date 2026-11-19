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

// ELF header and dynamic linking information (0x0 to 0xe10)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x000000000002d208
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000000000c090
        .quad   0x000000000000c090
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
        .quad   0x0000000000000e70
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
        .quad   0x000000000000601c
        .quad   0x0000000000000290
        .quad   0x00080012000001f2
        .quad   0x000000000000678c
        .quad   0x00000000000000b4
        .quad   0x00080012000000f0
        .quad   0x000000000000462c
        .quad   0x0000000000000100
        .quad   0x0008001200000082
        .quad   0x0000000000004128
        .quad   0x00000000000000b4
        .quad   0x00080012000003f1
        .quad   0x000000000000956c
        .quad   0x00000000000000c8
        .quad   0x0008001200000067
        .quad   0x0000000000003cf0
        .quad   0x0000000000000438
        .quad   0x000800120000037a
        .quad   0x0000000000008f54
        .quad   0x000000000000030c
        .quad   0x0008001200000439
        .quad   0x00000000000096f4
        .quad   0x00000000000000a8
        .quad   0x0008001200000347
        .quad   0x0000000000008a6c
        .quad   0x0000000000000434
        .quad   0x000800120000020a
        .quad   0x0000000000006840
        .quad   0x0000000000000324
        .quad   0x00080012000002a5
        .quad   0x0000000000006f38
        .quad   0x00000000000000c0
        .quad   0x000800120000031e
        .quad   0x00000000000086d4
        .quad   0x0000000000000304
        .quad   0x00080012000002ea
        .quad   0x00000000000070a0
        .quad   0x00000000000000b0
        .quad   0x0008001200000272
        .quad   0x0000000000006db4
        .quad   0x00000000000000bc
        .quad   0x000800120000004b
        .quad   0x0000000000003c5c
        .quad   0x0000000000000094
        .quad   0x0008001200000111
        .quad   0x00000000000047e8
        .quad   0x00000000000000c8
        .quad   0x0008001200000415
        .quad   0x0000000000009634
        .quad   0x00000000000000c0
        .quad   0x0008001200000392
        .quad   0x0000000000009260
        .quad   0x0000000000000018
        .quad   0x00080012000000b2
        .quad   0x00000000000044dc
        .quad   0x0000000000000018
        .quad   0x0008001200000102
        .quad   0x000000000000472c
        .quad   0x00000000000000bc
        .quad   0x00080012000001d7
        .quad   0x0000000000006340
        .quad   0x000000000000044c
        .quad   0x0008001200000159
        .quad   0x0000000000004970
        .quad   0x00000000000000a8
        .quad   0x00080012000003e2
        .quad   0x00000000000094b0
        .quad   0x00000000000000bc
        .quad   0x00080012000003d0
        .quad   0x00000000000093b0
        .quad   0x0000000000000100
        .quad   0x000800120000047b
        .quad   0x000000000000984c
        .quad   0x000000000000020c
        .quad   0x000800120000019b
        .quad   0x0000000000004ac8
        .quad   0x0000000000000208
        .quad   0x00080012000000c7
        .quad   0x00000000000044f4
        .quad   0x0000000000000138
        .quad   0x0008001200000260
        .quad   0x0000000000006cb4
        .quad   0x0000000000000100
        .quad   0x0008001200000237
        .quad   0x0000000000006b7c
        .quad   0x0000000000000138
        .quad   0x0008001200000032
        .quad   0x0000000000003a28
        .quad   0x0000000000000234
        .quad   0x00080012000003a7
        .quad   0x0000000000009278
        .quad   0x0000000000000138
        .quad   0x0008001200000135
        .quad   0x00000000000048b0
        .quad   0x00000000000000c0
        .quad   0x0008001200000337
        .quad   0x00000000000089d8
        .quad   0x0000000000000094
        .quad   0x000800120000045a
        .quad   0x000000000000979c
        .quad   0x00000000000000b0
        .quad   0x0008001200000222
        .quad   0x0000000000006b64
        .quad   0x0000000000000018
        .quad   0x00080012000002c9
        .quad   0x0000000000006ff8
        .quad   0x00000000000000a8
        .quad   0x00080012000001c7
        .quad   0x00000000000062ac
        .quad   0x0000000000000094
        .quad   0x0008001200000281
        .quad   0x0000000000006e70
        .quad   0x00000000000000c8
        .quad   0x000800120000030b
        .quad   0x0000000000007150
        .quad   0x0000000000000210
        .quad   0x0008001200000362
        .quad   0x0000000000008ea0
        .quad   0x00000000000000b4
        .quad   0x000800120000009a
        .quad   0x00000000000041dc
        .quad   0x0000000000000300
        .quad   0x000800120000017a
        .quad   0x0000000000004a18
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
        .quad   0x702f706d742f006f
        .quad   0x756f732d736f2d71
        .quad   0x6c75506f2e656372
        .quad   0x646c6d2f52446642
        .quad   0x757074756f2f6173
        .quad   0x6c2f74756f2f7374
        .quad   0x0000000000006269
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

// The procedure linkage table and the code (0xe10 to 0x9a58)
// .plt
        stp     x16, x30, [sp, #-16]!
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4040]
        add     x16, x16, #0xfc8
        br      x17
        nop
        nop
        nop
L0e30:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4048]
        add     x16, x16, #0xfd0
        br      x17
L0e40:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4056]
        add     x16, x16, #0xfd8
        br      x17
L0e50:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4064]
        add     x16, x16, #0xfe0
        br      x17
L0e60:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4072]
        add     x16, x16, #0xfe8
        br      x17

// keccak_absorb (0x88 bytes)
L0e70:
        stp     x19, x20, [sp, #-64]!
        mov     w19, w1
        mov     x20, x4
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        mov     x21, x3
        stp     x23, x24, [sp, #32]
        mov     w23, w2
        str     x30, [sp, #48]
L0e94:
        sub     w24, w23, w19
        sub     w3, w23, w19
        cmp     x24, x20
        b.ls    L0ed0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x21
        mov     x0, x22
        bl      L1574
        ldp     x21, x22, [sp, #16]
        add     w0, w19, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L0ed0:
        mov     w2, w19
        mov     x1, x21
        mov     x0, x22
        bl      L1574
        mov     x0, x22
        sub     x20, x20, x24
        add     x21, x21, x24
        mov     w19, #0x0
        bl      L16a0
        b       L0e94

// keccak_squeeze (0x8c bytes)
L0ef8:
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
L0f20:
        cbnz    x20, L0f3c
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L0f3c:
        cmp     w19, w22
        b.ne    L0f50
        mov     w19, #0x0
        mov     x0, x23
        bl      L16a0
L0f50:
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
        bl      L1550
        b       L0f20

// mldsa_shake128_init (0x20 bytes)
L0f84:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        mov     x2, #0xc8
        mov     w1, #0x0
        bl      L0e60
        str     wzr, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_absorb (0x28 bytes)
L0fa4:
        stp     x19, x30, [sp, #-16]!
        mov     x3, x1
        mov     x19, x0
        ldr     w1, [x0, #200]
        mov     x4, x2
        mov     w2, #0xa8
        bl      L0e70
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_finalize (0x80 bytes)
L0fcc:
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
        bl      L1574
        add     x1, sp, #0x16
        mov     x0, x19
        mov     w2, #0xa7
        mov     w3, #0x1
        bl      L1574
        mov     w0, #0xa8
        str     w0, [x19, #200]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1044
        bl      L0e50
L1044:
        ldp     x19, x30, [sp], #32
        ret

// mldsa_shake128_squeeze (0x20 bytes)
L104c:
        ldr     w3, [x2, #200]
        mov     w4, #0xa8
        stp     x19, x30, [sp, #-16]!
        mov     x19, x2
        bl      L0ef8
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake128_release (0x1c bytes)

// mldsa_shake128_release.localalias (0x1c bytes)
L106c:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0xd0
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e60
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_init (0x20 bytes)
L1088:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        mov     x2, #0xc8
        mov     w1, #0x0
        bl      L0e60
        str     wzr, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_absorb (0x28 bytes)
L10a8:
        stp     x19, x30, [sp, #-16]!
        mov     x3, x1
        mov     x19, x0
        ldr     w1, [x0, #200]
        mov     x4, x2
        mov     w2, #0x88
        bl      L0e70
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_finalize (0x80 bytes)
L10d0:
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
        bl      L1574
        add     x1, sp, #0x16
        mov     x0, x19
        mov     w2, #0x87
        mov     w3, #0x1
        bl      L1574
        mov     w0, #0x88
        str     w0, [x19, #200]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1148
        bl      L0e50
L1148:
        ldp     x19, x30, [sp], #32
        ret

// mldsa_shake256_squeeze (0x20 bytes)
L1150:
        ldr     w3, [x2, #200]
        mov     w4, #0x88
        stp     x19, x30, [sp, #-16]!
        mov     x19, x2
        bl      L0ef8
        str     w0, [x19, #200]
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256_release (0x4 bytes)
L1170:
        b       L106c

// mldsa_shake256 (0x9c bytes)
L1174:
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
        bl      L1088
        mov     x2, x23
        mov     x1, x22
        mov     x0, x19
        bl      L10a8
        mov     x0, x19
        bl      L10d0
        mov     x2, x19
        mov     x1, x21
        mov     x0, x20
        bl      L1150
        mov     x0, x19
        bl      L1170
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #264]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1200
        bl      L0e50
L1200:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #272
        ret

// mld_keccak_absorb_once_x4.constprop.0 (0x150 bytes)
L1210:
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
L1264:
        add     x4, x27, x22
        add     x3, x26, x22
        add     x2, x25, x22
        add     x1, x24, x22
        add     x22, x22, x23
        cmp     x19, x23
        b.cs    L12f4
        mov     w23, w19
        sub     w21, w21, #0x1
        add     x22, sp, #0x57
        cbz     x19, L1314
        mov     w6, w19
        mov     x0, x20
        mov     w5, #0x0
        bl      L1620
        cmp     x19, w21, uxtw
        b.ne    L1314
        ldrb    w0, [sp, #87]
        mov     w5, w19
        mov     w6, #0x1
        orr     w0, w0, #0xffffff80
        strb    w0, [sp, #87]
L12bc:
        mov     x2, x22
        mov     x1, x22
        mov     x0, x20
        mov     x4, x22
        mov     x3, x22
        bl      L1620
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1348
        bl      L0e50
L12f4:
        mov     w6, w21
        mov     w5, #0x0
        mov     x0, x20
        bl      L1620
        mov     x0, x20
        sub     x19, x19, x23
        bl      L1c94
        b       L1264
L1314:
        mov     w5, w23
        mov     x0, x20
        mov     w6, #0x1
        mov     x4, x22
        mov     x3, x22
        mov     x2, x22
        mov     x1, x22
        bl      L1620
        mov     w0, #0xffffff80
        mov     w5, w21
        mov     w6, #0x1
        strb    w0, [sp, #87]
        b       L12bc
L1348:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #96
        ret

// mldsa_shake128x4_absorb_once (0x64 bytes)
L1360:
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
        bl      L0e60
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
        b       L1210

// mldsa_shake128x4_squeezeblocks (0x80 bytes)
L13c4:
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
L13ec:
        cbnz    x19, L1404
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L1404:
        mov     x0, x24
        bl      L1c94
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
        bl      L15a0
        b       L13ec

// mldsa_shake128x4_init (0x4 bytes)
L1444:
        ret

// mldsa_shake128x4_release (0x1c bytes)

// mldsa_shake128x4_release.localalias (0x1c bytes)
L1448:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0x320
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e60
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256x4_absorb_once (0x64 bytes)
L1464:
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
        bl      L0e60
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
        b       L1210

// mldsa_shake256x4_squeezeblocks (0x80 bytes)
L14c8:
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
L14f0:
        cbnz    x19, L1508
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L1508:
        mov     x0, x24
        bl      L1c94
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
        bl      L15a0
        b       L14f0

// mldsa_shake256x4_init (0x4 bytes)
L1548:
        ret

// mldsa_shake256x4_release (0x4 bytes)
L154c:
        b       L1448

// mldsa_keccakf1600_extract_bytes (0x24 bytes)
L1550:
        add     x2, x0, w2, uxtw
        mov     x4, #0x0
L1558:
        cmp     w3, w4
        b.hi    L1564
        ret
L1564:
        ldrb    w0, [x2, x4]
        strb    w0, [x1, x4]
        add     x4, x4, #0x1
        b       L1558

// mldsa_keccakf1600_xor_bytes (0x2c bytes)
L1574:
        add     x2, x0, w2, uxtw
        mov     x0, #0x0
L157c:
        cmp     w3, w0
        b.hi    L1588
        ret
L1588:
        ldrb    w5, [x1, x0]
        add     x0, x0, #0x1
        ldrb    w4, [x2]
        eor     w4, w4, w5
        strb    w4, [x2], #1
        b       L157c

// mldsa_keccakf1600x4_extract_bytes (0x80 bytes)
L15a0:
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
        bl      L1550
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L1550
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L1550
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L1550

// mldsa_keccakf1600x4_xor_bytes (0x80 bytes)
L1620:
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
        bl      L1574
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L1574
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L1574
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L1574

// mldsa_keccakf1600_permute (0x5f4 bytes)
L16a0:
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
        add     x24, x2, #0xa58
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
L1718:
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
        b.ne    L1718
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
L1c94:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L16a0
        add     x0, x19, #0xc8
        bl      L16a0
        add     x0, x19, #0x190
        bl      L16a0
        add     x0, x19, #0x258
        ldp     x19, x30, [sp], #16
        b       L16a0

// mldsa44_unpack_pk_t1 (0x14 bytes)
L1cbc:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25d0

// mldsa44_pack_sk_rho_key_tr (0x28 bytes)
L1cd0:
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
L1cf8:
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
        bl      L3560
        mov     x0, x22
        mov     x22, x20
        bl      L3390
        add     x1, x19, #0x200
        mov     x0, x21
        bl      L35d8
        mov     x0, x21
        add     x21, x19, #0x380
        add     x19, x19, #0xa00
        bl      L3484
L1d6c:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L270c
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L1d6c
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L3484

// mldsa44_pack_sig_c (0xc bytes)
L1d9c:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ret

// mldsa44_pack_sig_h (0xec bytes)
L1da8:
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
        bl      L0e60
L1e00:
        madd    x1, x19, x26, x24
        mov     x0, x22
        bl      L292c
        mov     w2, #0x8c00
        add     x1, x23, x19, lsl #10
        mov     x4, #0x0
        movk    w2, #0xfffe, lsl #16
L1e1c:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w3, [x22, x4, lsl #2]
        add     w5, w0, w27
        cmp     w5, w28
        b.hi    L1e3c
        cmp     w3, #0x0
        ccmp    w0, w2, #0x0, ne
        b.ne    L1e4c
L1e3c:
        cmp     w20, #0x50
        b.eq    L1e8c
        strb    w4, [x25, w20, uxtw]
        add     w20, w20, #0x1
L1e4c:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L1e1c
        add     x0, x21, #0x970
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x4
        b.ne    L1e00
        mov     w0, #0x0
L1e70:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L1e8c:
        mov     w0, #0xffffffff
        b       L1e70

// mldsa44_pack_sig_z (0x14 bytes)
L1e94:
        mov     w3, #0x240
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x0, x0, x2
        b       L3084

// mldsa44_sig_unpack_hints (0xdc bytes)
L1ea8:
        stp     x19, x20, [sp, #-48]!
        mov     x3, x0
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, #0x920
        cbz     w2, L1ef8
        add     w0, w2, #0x4f
        ldrb    w22, [x23, x0]
L1ed0:
        add     w0, w21, #0x50
        ldrb    w19, [x23, x0]
        cmp     w19, #0x50
        ccmp    w22, w19, #0x2, ls
        b.ls    L1f00
L1ee4:
        mov     w0, #0xffffffff
L1ee8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L1ef8:
        mov     w22, #0x0
        b       L1ed0
L1f00:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e60
        add     x2, x20, w22, uxtb
        mov     x3, x0
        mov     w1, w22
        mov     w4, #0x1
L1f20:
        cmp     w1, w19
        b.cc    L1f44
        cmp     w21, #0x3
        b.ne    L1f3c
        add     x20, x20, #0x91f
L1f34:
        cmp     w19, #0x50
        b.ne    L1f74
L1f3c:
        mov     w0, #0x0
        b       L1ee8
L1f44:
        cmp     w1, w22
        b.ls    L1f60
        sub     w0, w1, #0x1
        ldrb    w5, [x2, #2336]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L1ee4
L1f60:
        ldrb    w0, [x2, #2336]
        add     w1, w1, #0x1
        add     x2, x2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L1f20
L1f74:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L1f34
        b       L1ee4

// mld_rej_uniform_c.constprop.0 (0x5c bytes)
L1f84:
        mov     x5, x0
        mov     w0, w1
        mov     w1, #0x3
        sub     w1, w1, w2
L1f94:
        cmp     w0, #0xff
        b.hi    L1fa8
L1f9c:
        add     w4, w1, w2
        cmp     w3, w4
        b.cs    L1fac
L1fa8:
        ret
L1fac:
        ldrb    w6, [x2, #2]
        add     x2, x2, #0x3
        ldurb   w4, [x2, #-2]
        ldurb   w7, [x2, #-3]
        lsl     w6, w6, #16
        orr     w4, w6, w4, lsl #8
        orr     w4, w4, w7
        and     w4, w4, #0x7fffff
        cmp     w4, #0x7fe, lsl #12
        b.hi    L1f9c
        str     w4, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
        b       L1f94

// mldsa_poly_reduce (0x2c bytes)
L1fe0:
        mov     x1, #0x0
        mov     w4, #0xff801fff
L1fe8:
        ldr     w3, [x0, x1, lsl #2]
        add     w2, w3, #0x400, lsl #12
        asr     w2, w2, #23
        madd    w2, w2, w4, w3
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L1fe8
        ret

// mldsa_poly_caddq (0x3c bytes)
L200c:
        mov     w5, #0xe001
        mov     x3, #0x0
        movk    w5, #0x7f, lsl #16
L2018:
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
        b.ne    L2018
        ret

// mldsa_poly_add (0x24 bytes)
L2048:
        mov     x2, #0x0
L204c:
        ldr     w3, [x0, x2]
        ldr     w4, [x1, x2]
        add     w3, w3, w4
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L204c
        ret

// mldsa_poly_sub (0x24 bytes)
L206c:
        mov     x2, #0x0
L2070:
        ldr     w3, [x0, x2]
        ldr     w4, [x1, x2]
        sub     w3, w3, w4
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L2070
        ret

// mldsa_poly_shiftl (0x20 bytes)
L2090:
        mov     x1, #0x0
L2094:
        ldr     w2, [x0, x1, lsl #2]
        lsl     w2, w2, #13
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L2094
        ret

// mldsa_poly_ntt (0xa8 bytes)
L20b0:
        mov     w1, #0x1
        .inst   0xf0000028  // adrp x8, 0x9000
        mov     w13, #0x2001
        mov     w11, w1
        add     x8, x8, #0xb18
        mov     w12, #0x100
        movk    w13, #0x380, lsl #16
        mov     w14, #0xff801fff
L20d0:
        sub     w6, w1, #0x1
        lsr     w2, w12, w1
        lsl     w10, w2, #1
        mov     w5, #0x0
        lsl     w6, w11, w6
L20e4:
        mov     w3, w6
        add     w6, w6, #0x1
        ldr     w15, [x8, w3, uxtw #2]
        cmp     w5, w2
        b.cs    L2138
        mov     w3, w5
        add     x9, x0, w2, uxtw #2
L2100:
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
        b.hi    L2100
L2138:
        add     w5, w5, w10
        add     w2, w2, w10
        cmp     w5, #0xff
        b.ls    L20e4
        add     w1, w1, #0x1
        cmp     w1, #0x9
        b.ne    L20d0
        ret

// mldsa_poly_invntt_tomont (0xe0 bytes)
L2158:
        .inst   0xf0000029  // adrp x9, 0x9000
        mov     w14, #0x2001
        add     x9, x9, #0xb18
        mov     w3, #0x8
        mov     w12, #0x100
        mov     w13, #0x1
        movk    w14, #0x380, lsl #16
        mov     w15, #0xff801fff
L2178:
        lsr     w2, w12, w3
        mov     w4, #0x0
        lsl     w5, w13, w3
        lsl     w11, w2, #1
        sub     w5, w5, #0x1
L218c:
        mov     w1, w5
        sub     w5, w5, #0x1
        ldr     w10, [x9, w1, uxtw #2]
        neg     w10, w10
        cmp     w4, w2
        b.cs    L21e4
        mov     w6, w4
        add     x8, x0, w2, uxtw #2
L21ac:
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
        b.hi    L21ac
L21e4:
        add     w4, w4, w11
        add     w2, w2, w11
        cmp     w4, #0xff
        b.ls    L218c
        subs    w3, w3, #0x1
        b.ne    L2178
        mov     w5, #0x2001
        mov     x1, #0x0
        mov     w6, #0xa3fa
        movk    w5, #0x380, lsl #16
        mov     w4, #0xff801fff
L2210:
        ldr     w3, [x0, x1, lsl #2]
        smull   x3, w3, w6
        mul     w2, w3, w5
        smaddl  x2, w2, w4, x3
        asr     x2, x2, #32
        str     w2, [x0, x1, lsl #2]
        add     x1, x1, #0x1
        cmp     x1, #0x100
        b.ne    L2210
        ret

// mldsa_poly_pointwise_montgomery (0x3c bytes)
L2238:
        mov     w6, #0x2001
        mov     x2, #0x0
        movk    w6, #0x380, lsl #16
        mov     w5, #0xff801fff
L2248:
        ldr     w3, [x1, x2]
        ldr     w4, [x0, x2]
        smull   x4, w4, w3
        mul     w3, w4, w6
        smaddl  x3, w3, w5, x4
        asr     x3, x3, #32
        str     w3, [x0, x2]
        add     x2, x2, #0x4
        cmp     x2, #0x400
        b.ne    L2248
        ret

// mldsa_poly_power2round (0x30 bytes)
L2274:
        mov     x3, #0x0
L2278:
        ldr     w4, [x2, x3]
        add     w5, w4, #0xfff
        asr     w6, w5, #13
        and     w5, w5, #0xffffe000
        str     w6, [x0, x3]
        sub     w4, w4, w5
        str     w4, [x1, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L2278
        ret

// mldsa_poly_uniform (0xf4 bytes)
L22a4:
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
        bl      L0f84
        mov     x1, x20
        mov     x2, #0x22
        mov     x0, x21
        bl      L0fa4
        mov     x0, x21
        bl      L0fcc
        mov     x2, x21
        mov     x1, #0x348
        mov     x0, x19
        bl      L104c
        mov     x2, x19
        mov     w3, #0x348
        mov     w1, #0x0
L2318:
        mov     x0, x22
        bl      L1f84
        mov     w20, w0
        cmp     w0, #0xff
        b.ls    L2364
        mov     x0, x21
        bl      L106c
        mov     x0, x19
        mov     x2, #0x348
        mov     w1, #0x0
        bl      L0e60
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1128]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2384
        bl      L0e50
L2364:
        mov     x2, x21
        mov     x1, #0xa8
        mov     x0, x19
        bl      L104c
        mov     x2, x19
        mov     w1, w20
        mov     w3, #0xa8
        b       L2318
L2384:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x470
        ret

// mldsa_poly_uniform_4x (0x1dc bytes)
L2398:
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
        bl      L1444
        add     x4, x20, #0xc0
        add     x3, x20, #0x80
        add     x2, x20, #0x40
        mov     x1, x20
        mov     x0, x23
        mov     x5, #0x22
        bl      L1360
        mov     x5, x23
        mov     x4, #0x5
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L13c4
        ldr     x0, [sp, #104]
        mov     w3, #0x348
        mov     x2, x19
        mov     w1, #0x0
        bl      L1f84
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     x2, x28
        mov     w1, #0x0
        bl      L1f84
        mov     w22, w0
        mov     x2, x27
        mov     w1, #0x0
        mov     x0, x24
        bl      L1f84
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L247c:
        mov     x0, x25
        bl      L1f84
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L24e0
        cmp     w22, #0xff
        b.ls    L24e0
        cmp     w20, #0xff
        b.ls    L24e0
        cmp     w0, #0xff
        b.ls    L24e0
        mov     x0, x23
        bl      L1448
        mov     x0, x19
        mov     x2, #0xd80
        mov     w1, #0x0
        bl      L0e60
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2550
        bl      L0e50
L24e0:
        mov     x5, x23
        mov     x4, #0x1
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L13c4
        ldr     x0, [sp, #104]
        mov     w1, w21
        mov     w3, #0xa8
        mov     x2, x19
        bl      L1f84
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     w1, w22
        mov     x2, x28
        bl      L1f84
        mov     w22, w0
        mov     w1, w20
        mov     x2, x27
        mov     x0, x24
        bl      L1f84
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     x2, x26
        mov     w1, w6
        b       L247c
L2550:
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
L2574:
        add     x4, x1, #0x400
L2578:
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
        b.ne    L2578
        ret

// mldsa_polyt1_unpack (0x70 bytes)
L25d0:
        add     x4, x1, #0x140
L25d4:
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
        b.ne    L25d4
        ret

// mldsa_polyt0_pack (0xcc bytes)
L2640:
        add     x11, x0, #0x1a0
        mov     w2, #0x1000
L2648:
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
        b.ne    L2648
        ret

// mldsa_polyt0_unpack (0x154 bytes)
L270c:
        add     x12, x0, #0x400
        mov     w2, #0x1000
L2714:
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
        b.ne    L2714
        ret

// mldsa_poly_chknorm (0x4c bytes)
L2860:
        sub     w1, w1, #0x1
        mov     x6, x0
        mov     x4, #0x0
        mov     w0, #0x0
L2870:
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
        b.ne    L2870
        ret

// mldsa_polyw1_pack_88 (0x5c bytes)
L28ac:
        add     x4, x1, #0x400
L28b0:
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
        b.ne    L28b0
        ret

// mldsa_polyw1_pack_32 (0x24 bytes)
L2908:
        mov     x2, #0x0
L290c:
        ldr     w3, [x1, #4]
        ldr     w4, [x1], #8
        orr     w3, w4, w3, lsl #4
        strb    w3, [x0, x2]
        add     x2, x2, #0x1
        cmp     x2, #0x80
        b.ne    L290c
        ret

// mldsa_polyw1_unpack_88 (0x60 bytes)
L292c:
        add     x4, x1, #0xc0
L2930:
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
        b.ne    L2930
        ret

// mldsa_polyw1_unpack_32 (0x30 bytes)
L298c:
        mov     x2, #0x0
L2990:
        ldrb    w3, [x1, x2]
        add     x0, x0, #0x8
        and     w3, w3, #0xf
        stur    w3, [x0, #-8]
        ldrb    w3, [x1, x2]
        add     x2, x2, #0x1
        lsr     w3, w3, #4
        stur    w3, [x0, #-4]
        cmp     x2, #0x80
        b.ne    L2990
        ret

// mld_decompose44 (0x68 bytes)
L29bc:
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
L2a24:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e60
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c44.constprop.0 (0x88 bytes)
L2a40:
        mov     x6, x0
        mov     w0, w1
        mov     x5, #0x0
        mov     w9, #0x87
        mov     w7, #0xcd
        mov     w8, #0x2
L2a58:
        cmp     w0, #0xff
        ccmp    w5, w9, #0x2, ls
        b.ls    L2a68
        ret
L2a68:
        ldrb    w1, [x2, x5]
        and     w3, w1, #0xf
        lsr     w1, w1, #4
        cmp     w3, #0xf
        b.eq    L2a98
        mul     w4, w3, w7
        lsr     w4, w4, #10
        add     w4, w4, w4, lsl #2
        sub     w3, w3, w4
        sub     w3, w8, w3
        str     w3, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L2a98:
        cmp     w0, #0xff
        ccmp    w1, #0xe, #0x2, ls
        b.hi    L2ac0
        mul     w3, w1, w7
        lsr     w3, w3, #10
        add     w3, w3, w3, lsl #2
        sub     w1, w1, w3
        sub     w1, w8, w1
        str     w1, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L2ac0:
        add     x5, x5, #0x1
        b       L2a58

// mldsa44_poly_decompose (0x34 bytes)
L2ac8:
        mov     x8, x0
        mov     x7, x1
        mov     x6, #0x0
        str     x30, [sp, #-16]!
L2ad8:
        ldr     w2, [x7, x6]
        add     x1, x8, x6
        add     x0, x7, x6
        add     x6, x6, #0x4
        bl      L29bc
        cmp     x6, #0x400
        b.ne    L2ad8
        ldr     x30, [sp], #16
        ret

// mldsa44_poly_use_hint (0xa4 bytes)
L2afc:
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
L2b2c:
        ldr     w2, [x7, x6]
        mov     x1, x9
        ldr     w11, [x8, x6]
        bl      L29bc
        ldr     w2, [sp, #20]
        cbz     w11, L2b58
        ldr     w1, [sp, #16]
        cmp     w1, #0x0
        b.le    L2b88
        cmp     w2, #0x2b
        csinc   w2, wzr, w2, eq
L2b58:
        str     w2, [x7, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L2b2c
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2b98
        bl      L0e50
L2b88:
        sub     w1, w2, #0x1
        cmp     w2, #0x0
        csel    w2, w1, w10, ne
        b       L2b58
L2b98:
        ldr     x30, [sp], #32
        ret

// mldsa44_poly_uniform_eta_4x (0x22c bytes)
L2ba0:
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
        bl      L1548
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1464
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14c8
        ldr     x0, [sp, #96]
        mov     x2, x19
        mov     w1, #0x0
        bl      L2a40
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L2a40
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L2a40
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L2cd4:
        mov     x0, x25
        bl      L2a40
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L2d40
        cmp     w22, #0xff
        b.ls    L2d40
        cmp     w20, #0xff
        b.ls    L2d40
        cmp     w0, #0xff
        b.ls    L2d40
        mov     x0, x23
        bl      L154c
        mov     x0, x19
        mov     x1, #0x280
        bl      L2a24
        mov     x0, x24
        mov     x1, #0x180
        bl      L2a24
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1976]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2dac
        bl      L0e50
L2d40:
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14c8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     x2, x19
        bl      L2a40
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L2a40
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L2a40
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L2cd4
L2dac:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7c0
        ret

// mldsa44_poly_challenge (0x160 bytes)
L2dcc:
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
        bl      L1088
        mov     x1, x19
        mov     x2, #0x20
        mov     x0, x21
        bl      L10a8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10d0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1150
        mov     x0, #0x0
L2e3c:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L2e3c
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xd9
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e60
L2e74:
        cmp     w19, #0x88
        b.ne    L2f10
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1150
        mov     w0, #0x0
L2e90:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L2e74
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
        b.ne    L2e74
        mov     x0, x21
        bl      L1170
        mov     x0, x20
        mov     x1, #0x88
        bl      L2a24
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L2a24
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2f18
        bl      L0e50
L2f10:
        mov     w0, w19
        b       L2e90
L2f18:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa44_polyeta_pack (0x98 bytes)
L2f2c:
        add     x9, x1, #0x400
        mov     w5, #0x2
L2f34:
        ldp     w2, w4, [x1, #8]
        add     x0, x0, #0x3
        ldp     w10, w7, [x1, #16]
        sub     w6, w5, w4
        ldr     w4, [x1, #4]
        sub     w2, w5, w2
        ldp     w3, w8, [x1, #24]
        sub     w4, w5, w4
        ubfiz   w11, w2, #6, #8
        sub     w7, w5, w7
        ubfiz   w4, w4, #3, #8
        sub     w10, w5, w10
        orr     w4, w4, w11
        ldr     w11, [x1], #32
        ubfx    x2, x2, #2, #6
        sub     w3, w5, w3
        sub     w11, w5, w11
        sub     w8, w5, w8
        orr     w4, w4, w11
        sturb   w4, [x0, #-3]
        ubfiz   w4, w7, #7, #8
        ubfx    x7, x7, #1, #7
        orr     w2, w2, w4
        ubfiz   w4, w6, #1, #8
        ubfiz   w6, w10, #4, #8
        orr     w4, w4, w6
        orr     w2, w2, w4
        sturb   w2, [x0, #-2]
        ubfiz   w2, w3, #2, #8
        ubfiz   w3, w8, #5, #8
        orr     w2, w2, w3
        orr     w2, w2, w7
        sturb   w2, [x0, #-1]
        cmp     x9, x1
        b.ne    L2f34
        ret

// mldsa44_polyeta_unpack (0xc0 bytes)
L2fc4:
        add     x11, x0, #0x400
        mov     w2, #0x2
L2fcc:
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
        b.ne    L2fcc
        ret

// mldsa44_polyz_pack (0x84 bytes)
L3084:
        add     x7, x0, #0x240
        mov     w6, #0x20000
L308c:
        ldp     w5, w4, [x1]
        add     x0, x0, #0x9
        ldp     w3, w2, [x1, #8]
        sub     w5, w6, w5
        sub     w4, w6, w4
        sturb   w5, [x0, #-9]
        lsr     w8, w5, #8
        sturb   w8, [x0, #-8]
        ubfiz   w8, w4, #2, #6
        sub     w3, w6, w3
        orr     w5, w8, w5, lsr #16
        sturb   w5, [x0, #-7]
        lsr     w5, w4, #6
        sturb   w5, [x0, #-6]
        ubfiz   w5, w3, #4, #4
        sub     w2, w6, w2
        orr     w4, w5, w4, lsr #14
        sturb   w4, [x0, #-5]
        lsr     w4, w3, #4
        sturb   w4, [x0, #-4]
        ubfiz   w4, w2, #6, #2
        add     x1, x1, #0x10
        orr     w3, w4, w3, lsr #12
        sturb   w3, [x0, #-3]
        lsr     w3, w2, #2
        lsr     w2, w2, #10
        sturb   w3, [x0, #-2]
        sturb   w2, [x0, #-1]
        cmp     x7, x0
        b.ne    L308c
        ret

// mldsa44_polyz_unpack (0xcc bytes)
L3108:
        add     x8, x0, #0x400
        mov     w6, #0x20000
L3110:
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
        b.ne    L3110
        ret

// mldsa44_poly_uniform_gamma1_4x (0x17c bytes)
L31d4:
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
        bl      L1548
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1464
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14c8
        mov     x1, x19
        mov     x0, x25
        bl      L3108
        mov     x1, x27
        mov     x0, x24
        bl      L3108
        mov     x1, x26
        mov     x0, x23
        bl      L3108
        mov     x1, x21
        mov     x0, x22
        bl      L3108
        mov     x0, x28
        bl      L154c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L2a24
        mov     x0, x20
        mov     x1, #0x180
        bl      L2a24
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L332c
        bl      L0e50
L332c:
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
L3350:
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
        bl      L31d4
        ldr     x30, [sp, #16]
        add     sp, sp, #0x20
        ret

// mldsa44_polyvecl_ntt (0x28 bytes)

// mldsa44_polyvecl_ntt.localalias (0x28 bytes)
L3390:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L20b0
        add     x0, x19, #0x400
        bl      L20b0
        add     x0, x19, #0x800
        bl      L20b0
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L20b0

// mldsa44_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L33b8:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L33c8:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L33d4:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x4
        b.ne    L33d4
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L33c8
        ret

// mldsa44_polyvecl_chknorm (0x4c bytes)
L3410:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     w20, #0x0
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x0, #0x1, lsl #12
        str     x30, [sp, #32]
L342c:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L2860
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L342c
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyveck_caddq (0x28 bytes)
L345c:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L200c
        add     x0, x19, #0x400
        bl      L200c
        add     x0, x19, #0x800
        bl      L200c
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L200c

// mldsa44_polyveck_ntt (0x4 bytes)
L3484:
        b       L3390

// mldsa44_polyveck_invntt_tomont (0x28 bytes)
L3488:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L2158
        add     x0, x19, #0x400
        bl      L2158
        add     x0, x19, #0x800
        bl      L2158
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L2158

// mldsa44_polyveck_unpack_eta_chknorm (0x5c bytes)
L34b0:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x180
L34d0:
        mov     x1, x19
        mov     x0, x20
        bl      L2fc4
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L2860
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L34d0
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyveck_decompose_pack_w1 (0x54 bytes)
L350c:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, #0x1, lsl #12
        str     x30, [sp, #32]
L3528:
        mov     x1, x19
        mov     x0, x21
        bl      L2ac8
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L28ac
        add     x20, x20, #0xc0
        cmp     x19, x22
        b.ne    L3528
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyvecl_unpack_eta (0x3c bytes)

// mldsa44_polyvecl_unpack_eta.localalias (0x3c bytes)
L3560:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x1, lsl #12
L3574:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2fc4
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L3574
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa44_polyvecl_unpack_z (0x3c bytes)
L359c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x1, lsl #12
L35b0:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L3108
        add     x20, x20, #0x240
        cmp     x19, x21
        b.ne    L35b0
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa44_polyveck_unpack_eta (0x4 bytes)
L35d8:
        b       L3560

// mldsa44_polyvec_matrix_expand_eager (0x120 bytes)
L35dc:
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
L3610:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L3610
        mov     w5, #0x0
        mov     w22, #0x1000
        mov     x23, #0xc00
        mov     x24, #0x800
        mov     x25, #0x400
L363c:
        mov     x1, x19
        mov     w0, w5
        add     w21, w5, #0x4
L3648:
        and     w2, w0, #0x3
        strb    w2, [x1, #32]
        lsr     w2, w0, #2
        add     w0, w0, #0x1
        strb    w2, [x1, #33]
        add     x1, x1, #0x40
        cmp     w21, w0
        b.ne    L3648
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
        bl      L2398
        cmp     w21, #0x10
        b.eq    L36b8
        mov     w5, w21
        b       L363c
L36b8:
        mov     x0, x19
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e60
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #344]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L36e8
        bl      L0e50
L36e8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #352
        ret

// mldsa44_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L36fc:
        ubfiz   x3, x3, #12, #32
        add     x1, x1, x3
        b       L33b8

// mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L3708:
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
        bl      L0e30
        mov     x0, x20
        bl      L3390
L373c:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L36fc
        cmp     x19, #0x4
        b.ne    L373c
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L3488

// mld_ct_memcmp (0x54 bytes)
L3770:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L377c:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L37a4
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L37a4:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L377c

// mld_zeroize (0x1c bytes)
L37c4:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e60
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t144 (0x158 bytes)
L37e0:
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
        bl      L35dc
L3854:
        ldr     x2, [sp, #104]
        mov     w3, w25
        mov     x1, x20
        mov     x0, x19
        bl      L36fc
        mov     x0, x19
        bl      L2158
        madd    x1, x25, x28, x24
        mov     x0, x21
        bl      L2fc4
        mov     x1, x21
        mov     x0, x19
        bl      L2048
        mov     x0, x19
        bl      L1fe0
        mov     x0, x19
        bl      L200c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x21
        bl      L2274
        madd    x0, x25, x27, x23
        mov     x1, x21
        bl      L2574
        madd    x0, x25, x26, x22
        mov     x1, x19
        add     x25, x25, #0x1
        bl      L2640
        cmp     x25, #0x4
        b.ne    L3854
        mov     x0, x21
        mov     x1, #0x400
        bl      L37c4
        mov     x0, x19
        mov     x1, #0x400
        bl      L37c4
        mov     x0, x20
        mov     x1, #0x4000
        bl      L37c4
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #18568]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3910
        bl      L0e50
L3910:
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
L3938:
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
        bl      L1088
        mov     x2, x27
        mov     x1, x26
        mov     x0, x19
        bl      L10a8
        cbz     x21, L39b0
        mov     x2, x21
        mov     x1, x25
        mov     x0, x19
        bl      L10a8
L39b0:
        cbz     x20, L39c4
        mov     x2, x20
        mov     x1, x24
        mov     x0, x19
        bl      L10a8
L39c4:
        mov     x0, x19
        bl      L10d0
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L1150
        mov     x0, x19
        bl      L1170
        mov     x0, x19
        mov     x1, #0xd0
        bl      L37c4
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3a10
        bl      L0e50
L3a10:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa44_keypair_internal (0x234 bytes)
L3a28:
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
        bl      L1174
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
        bl      L2ba0
        mov     x1, x19
        mov     x0, x27
        bl      L2f2c
        mov     x1, x26
        add     x0, x20, #0x260
        bl      L2f2c
        mov     x1, x25
        add     x0, x20, #0x2c0
        bl      L2f2c
        mov     x1, x23
        add     x0, x20, #0x320
        bl      L2f2c
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
        bl      L2ba0
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L2f2c
        mov     x1, x26
        add     x0, x20, #0xe0
        bl      L2f2c
        mov     x1, x25
        add     x0, x20, #0x140
        bl      L2f2c
        mov     x1, x23
        add     x0, x20, #0x1a0
        bl      L2f2c
        mov     x0, x19
        bl      L3390
        ldp     q0, q1, [x21]
        mov     x2, x19
        mov     x4, x21
        mov     x3, x27
        add     x1, x20, #0x380
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L37e0
        mov     x2, #0x1080
        mov     w23, w0
        add     x25, x19, x2
        cbnz    w0, L3bc8
        mov     x2, x22
        mov     x0, x25
        mov     x3, #0x520
        mov     x1, #0x40
        bl      L1174
        add     x3, x21, #0x60
        mov     x2, x25
        mov     x1, x21
        mov     x0, x20
        bl      L1cd0
L3bc8:
        mov     x0, x19
        mov     x1, #0x1000
        bl      L37c4
        mov     x0, x25
        mov     x1, #0x40
        bl      L37c4
        mov     x0, x24
        mov     x1, #0x22
        bl      L37c4
        mov     x0, x21
        mov     x1, #0x80
        bl      L37c4
        cbz     w23, L3c14
        mov     x0, x22
        mov     x1, #0x520
        bl      L37c4
        mov     x0, x20
        mov     x1, #0xa00
        bl      L37c4
L3c14:
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3c34
        bl      L0e50
L3c34:
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
L3c5c:
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
        bl      L0e40
        cbnz    w0, L3cd8
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L3a28
        mov     w20, w0
L3cac:
        mov     x0, x19
        mov     x1, #0x20
        bl      L37c4
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3ce0
        bl      L0e50
L3cd8:
        mov     w20, #0xfffffffd
        b       L3cac
L3ce0:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa44_signature_internal (0x438 bytes)
L3cf0:
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
        bl      L1cf8
        add     x0, x21, #0x80
        cbnz    w27, L3ff8
        mov     x3, #0x40
        mov     x7, x25
        mov     x6, x26
        mov     x5, x24
        mov     x4, x22
        mov     x2, x28
        mov     x1, x3
        bl      L3938
L3db8:
        mov     x5, #0x20
        mov     x4, x20
        mov     x3, x5
        add     x6, x21, #0x80
        add     x2, x21, #0x60
        mov     x7, #0x40
        add     x0, x21, #0xc0
        mov     x1, x7
        bl      L3938
        mov     x0, x19
        mov     x1, x21
        bl      L35dc
        str     wzr, [sp, #124]
        mov     x4, #0xa800
        add     x0, x19, x4
        mov     x5, #0xac00
        str     x0, [sp, #104]
        add     x0, x19, x5
        str     x0, [sp, #112]
L3e04:
        ldrh    w2, [sp, #124]
        add     x27, x19, #0x6, lsl #12
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0x5, lsl #12
        add     x24, x19, #0x4, lsl #12
        mov     w26, #0xffb2
        add     x22, x19, #0xa, lsl #12
        bl      L3350
        mov     x28, #0x0
        mov     x3, x20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x24
        bl      L3708
        movk    w26, #0x1, lsl #16
        mov     x0, x24
        bl      L345c
        ldr     x0, [sp, #104]
        mov     x3, #0xa400
        mov     x2, x20
        add     x25, x19, x3
        mov     x1, x24
        bl      L350c
        ldp     x4, x0, [sp, #104]
        add     x2, x21, #0x80
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x300
        mov     x3, #0x40
        mov     x1, #0x20
        bl      L3938
        ldr     x1, [sp, #112]
        mov     x0, x25
        bl      L2dcc
        mov     x0, x25
        bl      L20b0
L3e98:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e30
        mov     x1, x25
        mov     x0, x22
        bl      L2238
        mov     x0, x22
        bl      L2158
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x27, x3
        bl      L0e30
        mov     x1, x20
        mov     x0, x22
        bl      L2048
        mov     x0, x22
        bl      L1fe0
        mov     w1, w26
        mov     x0, x22
        bl      L2860
        cbnz    w0, L400c
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L1e94
        cmp     x28, #0x4
        b.ne    L3e98
        mov     x26, #0x0
L3f20:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x24, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e30
        mov     x1, x25
        mov     x0, x20
        bl      L2238
        mov     x0, x20
        bl      L2158
        mov     x1, x20
        mov     x0, x28
        bl      L206c
        mov     x0, x28
        bl      L1fe0
        mov     w1, #0x73b2
        mov     x0, x28
        movk    w1, #0x1, lsl #16
        bl      L2860
        cbnz    w0, L400c
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e30
        mov     x1, x25
        mov     x0, x20
        bl      L2238
        mov     x0, x20
        bl      L2158
        mov     x0, x20
        bl      L1fe0
        mov     w1, #0x7400
        mov     x0, x20
        movk    w1, #0x1, lsl #16
        bl      L2860
        cbnz    w0, L400c
        mov     x1, x20
        mov     x0, x28
        add     x26, x26, #0x400
        bl      L2048
        cmp     x26, #0x1, lsl #12
        b.ne    L3f20
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L1d9c
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x24
        mov     x0, x23
        bl      L1da8
        mov     w26, w0
        b       L4010
L3ff8:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L3db8
L400c:
        mov     w26, #0xffffffff
L4010:
        mov     x0, x22
        mov     x1, #0x400
        bl      L37c4
        mov     x0, x25
        mov     x1, #0x400
        bl      L37c4
        mov     x0, x24
        mov     x1, #0x1000
        bl      L37c4
        ldr     x0, [sp, #104]
        mov     x1, #0x300
        bl      L37c4
        mov     x0, x20
        mov     x1, #0x1000
        bl      L37c4
        mov     x0, x27
        mov     x1, #0x1000
        bl      L37c4
        ldr     x0, [sp, #112]
        mov     x1, #0x20
        bl      L37c4
        cbz     w26, L409c
        cmn     w26, #0x1
        b.ne    L4090
        ldr     w0, [sp, #124]
        add     w0, w0, #0x4
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfff8
        cmp     w1, w0, uxth
        b.ne    L3e04
        mov     w26, #0xfffffffc
L4090:
        mov     x0, x23
        mov     x1, #0x974
        bl      L37c4
L409c:
        ldr     x0, [sp, #128]
        mov     x1, #0x1000
        bl      L37c4
        ldr     x0, [sp, #144]
        mov     x1, #0x1000
        bl      L37c4
        ldr     x0, [sp, #136]
        mov     x1, #0x1000
        bl      L37c4
        mov     x0, x19
        mov     x1, #0x4000
        bl      L37c4
        mov     x0, x21
        mov     x1, #0x100
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x1, #0x8040
        add     x2, sp, x1
        ldr     x3, [x2, #11416]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L4100
        bl      L0e50
L4100:
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
L4128:
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
        bl      L0e40
        cbnz    w0, L41c0
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L3cf0
        mov     w20, w0
L4194:
        mov     x0, x19
        mov     x1, #0x20
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L41c8
        bl      L0e50
L41c0:
        mov     w20, #0xfffffffd
        b       L4194
L41c8:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa44_verify_internal (0x300 bytes)
L41dc:
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
        bl      L359c
        mov     w1, #0xffb2
        mov     x0, x26
        movk    w1, #0x1, lsl #16
        bl      L3410
        mov     x14, #0x5f60
        mov     w20, w0
        add     x0, x19, x14
        str     x0, [sp, #104]
        cbnz    w20, L4404
        ldr     w6, [sp, #140]
        cbnz    w6, L449c
        ldr     x2, [sp, #96]
        mov     x0, x23
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x520
        mov     x1, #0x40
        bl      L3938
        ldp     x7, x4, [sp, #112]
        mov     x10, #0x5f00
        ldr     x5, [sp, #128]
        mov     x6, x28
        mov     x2, x23
        mov     x3, #0x40
        add     x0, x19, x10
        mov     x1, x3
        bl      L3938
        mov     x0, x23
        mov     x1, #0x40
        bl      L37c4
L42e8:
        mov     x0, x26
        bl      L3390
        ldr     x1, [sp, #96]
        mov     x0, x19
        mov     x28, x23
        bl      L35dc
        mov     x9, #0x5f60
        add     x1, x19, x9
        mov     x0, x27
        bl      L2dcc
        mov     x0, x27
        bl      L20b0
L4318:
        mov     w3, w20
        mov     x2, x26
        mov     x1, x19
        mov     x0, x21
        bl      L36fc
        ldr     x1, [sp, #96]
        mov     w2, w20
        mov     x0, x22
        bl      L1cbc
        mov     x0, x22
        bl      L2090
        mov     x0, x22
        bl      L20b0
        mov     x1, x27
        mov     x0, x22
        bl      L2238
        mov     x1, x22
        mov     x0, x21
        bl      L206c
        mov     x0, x21
        bl      L1fe0
        mov     x0, x21
        bl      L2158
        mov     x0, x21
        bl      L200c
        mov     w2, w20
        mov     x1, x24
        mov     x0, x22
        bl      L1ea8
        mov     w25, w0
        cbnz    w0, L4404
        mov     x1, x22
        mov     x0, x21
        bl      L2afc
        add     w20, w20, #0x1
        mov     x0, x28
        mov     x1, x21
        bl      L28ac
        add     x28, x28, #0xc0
        cmp     w20, #0x4
        b.ne    L4318
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
        bl      L3938
        ldr     x0, [sp, #104]
        mov     x1, x20
        mov     x2, #0x20
        bl      L3770
        tst     w0, #0xff
        b.eq    L4408
L4404:
        mov     w25, #0xfffffffa
L4408:
        mov     x0, x22
        mov     x1, #0x400
        bl      L37c4
        mov     x0, x21
        mov     x1, #0x400
        bl      L37c4
        mov     x0, x19
        mov     x1, #0x4000
        bl      L37c4
        mov     x0, x27
        mov     x1, #0x400
        bl      L37c4
        mov     x0, x26
        mov     x1, #0x1000
        bl      L37c4
        mov     x1, #0x20
        mov     x0, #0x5f40
        add     x0, x19, x0
        bl      L37c4
        ldr     x0, [sp, #104]
        mov     x1, #0x20
        bl      L37c4
        mov     x2, #0x5f00
        mov     x1, #0x40
        add     x0, x19, x2
        bl      L37c4
        mov     x0, x23
        mov     x1, #0x300
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24616]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L44b4
        bl      L0e50
L449c:
        ldp     q0, q1, [x28]
        sub     x0, x25, #0x100
        stp     q0, q1, [x0]
        ldp     q0, q1, [x28, #32]
        stp     q0, q1, [x0, #32]
        b       L42e8
L44b4:
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
L44dc:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L41dc

// mldsa44_prepare_domain_separation_prefix (0x138 bytes)
L44f4:
        cmp     x4, #0xff
        b.hi    L461c
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L45e0
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L4624
        .inst   0xb0000020  // adrp x0, 0x9000
        add     x0, x0, #0xf18
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 4548 <mldsa44_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L454c:
        b.ne    L4624
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L456c
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e30
L456c:
        .inst   0xb0000020  // adrp x0, 0x9000
        add     x0, x0, #0xf24
        mov     x1, #0x0
L4578:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L460c
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L45a8:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e30
        add     x0, x20, x19
        b       L45fc
        cmp     x20, #0x20
        b       L454c
        cmp     x20, #0x30
        b       L454c
        cmp     x20, #0x40
        b       L454c
L45e0:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L45f8
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e30
L45f8:
        add     x0, x19, #0x2
L45fc:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L460c:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L4578
        b       L45a8
L461c:
        mov     x0, #0x0
        ret
L4624:
        mov     x0, #0x0
        b       L45fc

// mldsa44_signature (0x100 bytes)
L462c:
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
        bl      L44f4
        cbz     x0, L4704
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e40
        cbnz    w0, L470c
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L3cf0
        mov     w19, w0
        cbz     w0, L46cc
L46c0:
        mov     x0, x21
        mov     x1, #0x974
        bl      L37c4
L46cc:
        mov     x0, x22
        mov     x1, #0x20
        bl      L37c4
        mov     x0, x20
        mov     x1, #0x14c
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4714
        bl      L0e50
L4704:
        mov     w19, #0xfffffff7
        b       L46c0
L470c:
        mov     w19, #0xfffffffd
        b       L46c0
L4714:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa44_verify (0xbc bytes)
L472c:
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
        bl      L44f4
        cbz     x0, L47cc
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L41dc
        mov     w20, w0
L47a0:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L47d4
        bl      L0e50
L47cc:
        mov     w20, #0xfffffff7
        b       L47a0
L47d4:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa44_signature_pre_hash_internal (0xc8 bytes)
L47e8:
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
        cbnz    w7, L4830
L481c:
        mov     w19, #0xfffffff7
L4820:
        mov     x0, x21
        mov     x1, #0x974
        bl      L37c4
        b       L4870
L4830:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L44f4
        mov     x2, x0
        cbz     x0, L481c
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L3cf0
        mov     w19, w0
        cbnz    w0, L4820
L4870:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L489c
        bl      L0e50
L489c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa44_signature_pre_hash_shake256 (0xc0 bytes)
L48b0:
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
        bl      L1174
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L47e8
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4958
        bl      L0e50
L4958:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa44_verify_pre_hash_internal (0xa8 bytes)
L4970:
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
        cbnz    w5, L49d4
L49a4:
        mov     w20, #0xfffffff7
L49a8:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4a08
        bl      L0e50
L49d4:
        mov     x0, x19
        bl      L44f4
        mov     x2, x0
        cbz     x0, L49a4
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L41dc
        mov     w20, w0
        b       L49a8
L4a08:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa44_verify_pre_hash_shake256 (0xb0 bytes)
L4a18:
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
        bl      L1174
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L4970
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4ab4
        bl      L0e50
L4ab4:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa44_pk_from_sk (0x208 bytes)
L4ac8:
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
        bl      L3560
        mov     w1, #0x3
        mov     x0, x19
        bl      L3410
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x3
        mov     x0, x23
        bl      L34b0
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L3390
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L37e0
        mov     x5, #0x1a80
        mov     w22, w0
        add     x23, x19, x5
        cbnz    w0, L4c24
        add     x1, x25, #0x380
        mov     x0, x24
        mov     x2, #0x680
        bl      L3770
        and     w4, w0, #0xff
        mov     x3, #0x520
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1174
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L3770
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L4c30
        mov     w22, #0xfffffff9
L4c24:
        mov     x0, x21
        mov     x1, #0x520
        bl      L37c4
L4c30:
        mov     x0, x24
        mov     x1, #0x680
        bl      L37c4
        mov     x0, x28
        mov     x1, #0x400
        bl      L37c4
        mov     x0, x19
        mov     x1, #0x1000
        bl      L37c4
        mov     x1, #0x20
        mov     x0, #0x1b00
        add     x0, x19, x0
        bl      L37c4
        mov     x0, x23
        mov     x1, #0x40
        bl      L37c4
        mov     x0, x27
        mov     x1, #0x40
        bl      L37c4
        mov     x0, x26
        mov     x1, #0x20
        bl      L37c4
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7112]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4ca8
        bl      L0e50
L4ca8:
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
L4cd0:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25d0

// mldsa65_pack_sk_rho_key_tr (0x28 bytes)
L4ce4:
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
L4d0c:
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
        bl      L5acc
        mov     x0, x22
        mov     x22, x20
        bl      L58a0
        add     x1, x19, #0x300
        mov     x0, x21
        bl      L5b4c
        mov     x0, x21
        add     x21, x19, #0x600
        add     x19, x19, #0xfc0
        bl      L59b0
L4d80:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L270c
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L4d80
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L59b0

// mldsa65_pack_sig_c (0x14 bytes)
L4db0:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldr     q0, [x1, #32]
        str     q0, [x0, #32]
        ret

// mldsa65_pack_sig_h (0xe0 bytes)
L4dc4:
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
L4e18:
        add     x1, x25, x19, lsl #7
        mov     x0, x23
        bl      L298c
        add     x1, x24, x19, lsl #10
        mov     x4, #0x0
L4e2c:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w2, [x23, x4, lsl #2]
        add     w3, w0, w26
        cmp     w3, w27
        b.hi    L4e4c
        cmp     w2, #0x0
        ccmp    w0, w28, #0x0, ne
        b.ne    L4e5c
L4e4c:
        cmp     w20, #0x37
        b.eq    L4e9c
        strb    w4, [x21, w20, uxtw]
        add     w20, w20, #0x1
L4e5c:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L4e2c
        add     x0, x22, #0xce7
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x6
        b.ne    L4e18
        mov     w0, #0x0
L4e80:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L4e9c:
        mov     w0, #0xffffffff
        b       L4e80

// mldsa65_pack_sig_z (0x14 bytes)
L4ea4:
        mov     w3, #0x280
        mul     w2, w2, w3
        add     x2, x2, #0x30
        add     x0, x0, x2
        b       L552c

// mldsa65_sig_unpack_hints (0xdc bytes)
L4eb8:
        stp     x19, x20, [sp, #-48]!
        mov     x3, x0
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, #0xcb0
        cbz     w2, L4f08
        add     w0, w2, #0x36
        ldrb    w22, [x23, x0]
L4ee0:
        add     w0, w21, #0x37
        ldrb    w19, [x23, x0]
        cmp     w19, #0x37
        ccmp    w22, w19, #0x2, ls
        b.ls    L4f10
L4ef4:
        mov     w0, #0xffffffff
L4ef8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L4f08:
        mov     w22, #0x0
        b       L4ee0
L4f10:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e60
        add     x2, x20, w22, uxtb
        mov     x3, x0
        mov     w1, w22
        mov     w4, #0x1
L4f30:
        cmp     w1, w19
        b.cc    L4f54
        cmp     w21, #0x5
        b.ne    L4f4c
        add     x20, x20, #0xcaf
L4f44:
        cmp     w19, #0x37
        b.ne    L4f84
L4f4c:
        mov     w0, #0x0
        b       L4ef8
L4f54:
        cmp     w1, w22
        b.ls    L4f70
        sub     w0, w1, #0x1
        ldrb    w5, [x2, #3248]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L4ef4
L4f70:
        ldrb    w0, [x2, #3248]
        add     w1, w1, #0x1
        add     x2, x2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L4f30
L4f84:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L4f44
        b       L4ef4

// mld_decompose65 (0x4c bytes)
L4f94:
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
L4fe0:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e60
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c65.constprop.0 (0x60 bytes)
L4ffc:
        mov     x5, x0
        mov     w0, w1
        mov     x4, #0x0
        mov     w7, #0x4
L500c:
        cmp     w0, #0xff
        ccmp    w3, w4, #0x0, ls
        b.hi    L501c
        ret
L501c:
        ldrb    w1, [x2, x4]
        and     w6, w1, #0xf
        lsr     w1, w1, #4
        cmp     w6, #0x8
        b.hi    L503c
        sub     w6, w7, w6
        str     w6, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
L503c:
        cmp     w0, #0xff
        ccmp    w1, #0x8, #0x2, ls
        b.hi    L5054
        sub     w1, w7, w1
        str     w1, [x5, w0, uxtw #2]
        add     w0, w0, #0x1
L5054:
        add     x4, x4, #0x1
        b       L500c

// mldsa65_poly_decompose (0x34 bytes)
L505c:
        mov     x6, x0
        mov     x5, x1
        mov     x4, #0x0
        str     x30, [sp, #-16]!
L506c:
        ldr     w2, [x5, x4]
        add     x1, x6, x4
        add     x0, x5, x4
        add     x4, x4, #0x4
        bl      L4f94
        cmp     x4, #0x400
        b.ne    L506c
        ldr     x30, [sp], #16
        ret

// mldsa65_poly_use_hint (0x98 bytes)
L5090:
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
L50bc:
        ldr     w2, [x5, x4]
        mov     x1, x7
        ldr     w8, [x6, x4]
        bl      L4f94
        ldr     w2, [sp, #20]
        cbz     w8, L50f0
        ldr     w1, [sp, #16]
        add     w3, w2, #0x1
        sub     w2, w2, #0x1
        and     w3, w3, #0xf
        and     w2, w2, #0xf
        cmp     w1, #0x0
        csel    w2, w2, w3, le
L50f0:
        str     w2, [x5, x4]
        add     x4, x4, #0x4
        cmp     x4, #0x400
        b.ne    L50bc
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5120
        bl      L0e50
L5120:
        ldr     x30, [sp], #32
        ret

// mldsa65_poly_uniform_eta_4x (0x234 bytes)
L5128:
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
        bl      L1548
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1464
        mov     x5, x23
        mov     x4, #0x2
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14c8
        ldr     x0, [sp, #96]
        mov     w3, #0x110
        mov     x2, x19
        mov     w1, #0x0
        bl      L4ffc
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L4ffc
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L4ffc
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L5260:
        mov     x0, x25
        bl      L4ffc
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L52cc
        cmp     w22, #0xff
        b.ls    L52cc
        cmp     w20, #0xff
        b.ls    L52cc
        cmp     w0, #0xff
        b.ls    L52cc
        mov     x0, x23
        bl      L154c
        mov     x0, x19
        mov     x1, #0x480
        bl      L4fe0
        mov     x0, x24
        mov     x1, #0x180
        bl      L4fe0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L533c
        bl      L0e50
L52cc:
        mov     x5, x23
        mov     x4, #0x1
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14c8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     w3, #0x88
        mov     x2, x19
        bl      L4ffc
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L4ffc
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L4ffc
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L5260
L533c:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x9c0
        ret

// mldsa65_poly_challenge (0x160 bytes)
L535c:
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
        bl      L1088
        mov     x1, x19
        mov     x2, #0x30
        mov     x0, x21
        bl      L10a8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10d0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1150
        mov     x0, #0x0
L53cc:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L53cc
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xcf
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e60
L5404:
        cmp     w19, #0x88
        b.ne    L54a0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1150
        mov     w0, #0x0
L5420:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L5404
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
        b.ne    L5404
        mov     x0, x21
        bl      L1170
        mov     x0, x20
        mov     x1, #0x88
        bl      L4fe0
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L4fe0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L54a8
        bl      L0e50
L54a0:
        mov     w0, w19
        b       L5420
L54a8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa65_polyeta_pack (0x34 bytes)
L54bc:
        mov     x3, #0x0
        mov     w5, #0x4
L54c4:
        ldr     w2, [x1, #4]
        ldr     w4, [x1], #8
        sub     w2, w5, w2
        sub     w4, w5, w4
        ubfiz   w2, w2, #4, #8
        orr     w2, w2, w4
        strb    w2, [x0, x3]
        add     x3, x3, #0x1
        cmp     x3, #0x80
        b.ne    L54c4
        ret

// mldsa65_polyeta_unpack (0x3c bytes)
L54f0:
        mov     x3, #0x0
        mov     w5, #0x4
L54f8:
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
        b.ne    L54f8
        ret

// mldsa65_polyz_pack (0x50 bytes)
L552c:
        add     x5, x0, #0x280
        mov     w4, #0x80000
L5534:
        ldp     w3, w2, [x1]
        add     x0, x0, #0x5
        add     x1, x1, #0x8
        sub     w3, w4, w3
        sub     w2, w4, w2
        sturb   w3, [x0, #-5]
        lsr     w6, w3, #8
        sturb   w6, [x0, #-4]
        ubfiz   w6, w2, #4, #4
        orr     w3, w6, w3, lsr #16
        sturb   w3, [x0, #-3]
        lsr     w3, w2, #4
        lsr     w2, w2, #12
        sturb   w3, [x0, #-2]
        sturb   w2, [x0, #-1]
        cmp     x5, x0
        b.ne    L5534
        ret

// mldsa65_polyz_unpack (0x70 bytes)
L557c:
        add     x6, x0, #0x400
        mov     w5, #0x80000
L5584:
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
        b.ne    L5584
        ret

// mldsa65_poly_uniform_gamma1 (0xdc bytes)
L55ec:
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
        bl      L1088
        mov     x1, x20
        mov     x2, #0x42
        mov     x0, x21
        bl      L10a8
        mov     x0, x21
        bl      L10d0
        mov     x2, x21
        mov     x0, x19
        mov     x1, #0x2a8
        bl      L1150
        mov     x1, x19
        mov     x0, x22
        bl      L557c
        mov     x0, x21
        bl      L1170
        mov     x0, x19
        mov     x1, #0x2a8
        bl      L4fe0
        mov     x0, x20
        mov     x1, #0x42
        bl      L4fe0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1064]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L56b4
        bl      L0e50
L56b4:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x430
        ret

// mldsa65_poly_uniform_gamma1_4x (0x17c bytes)
L56c8:
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
        bl      L1548
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1464
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14c8
        mov     x1, x19
        mov     x0, x25
        bl      L557c
        mov     x1, x27
        mov     x0, x24
        bl      L557c
        mov     x1, x26
        mov     x0, x23
        bl      L557c
        mov     x1, x21
        mov     x0, x22
        bl      L557c
        mov     x0, x28
        bl      L154c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L4fe0
        mov     x0, x20
        mov     x1, #0x180
        bl      L4fe0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5820
        bl      L0e50
L5820:
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
L5844:
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
        bl      L56c8
        add     w2, w20, #0x4
        mov     x1, x21
        ldp     x21, x30, [sp, #32]
        add     x0, x19, #0x1, lsl #12
        ldp     x19, x20, [sp, #16]
        add     sp, sp, #0x30
        b       L55ec

// mldsa65_polyvecl_ntt (0x34 bytes)
L58a0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1400
        add     x20, x19, x0
        str     x30, [sp, #16]
L58b4:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20b0
        cmp     x19, x20
        b.ne    L58b4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L58d4:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L58e4:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L58f0:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x5
        b.ne    L58f0
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L58e4
        ret

// mldsa65_polyvecl_chknorm (0x50 bytes)
L592c:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1400
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
L594c:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L2860
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L594c
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyveck_caddq (0x34 bytes)
L597c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L5990:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L200c
        cmp     x19, x20
        b.ne    L5990
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_ntt (0x34 bytes)
L59b0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L59c4:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20b0
        cmp     x19, x20
        b.ne    L59c4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_invntt_tomont (0x34 bytes)
L59e4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
L59f8:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2158
        cmp     x19, x20
        b.ne    L59f8
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_unpack_eta_chknorm (0x5c bytes)
L5a18:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L5a38:
        mov     x1, x19
        mov     x0, x20
        bl      L54f0
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x80
        bl      L2860
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L5a38
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyveck_decompose_pack_w1 (0x58 bytes)
L5a74:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        mov     x0, #0x1800
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, x0
        str     x30, [sp, #32]
L5a94:
        mov     x1, x19
        mov     x0, x21
        bl      L505c
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2908
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L5a94
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyvecl_unpack_eta (0x40 bytes)
L5acc:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1400
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5ae4:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L54f0
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L5ae4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvecl_unpack_z (0x40 bytes)
L5b0c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1400
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5b24:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L557c
        add     x20, x20, #0x280
        cmp     x19, x21
        b.ne    L5b24
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_unpack_eta (0x40 bytes)
L5b4c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1800
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5b64:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L54f0
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L5b64
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvec_matrix_expand_eager (0x15c bytes)
L5b8c:
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
L5bbc:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L5bbc
        mov     w20, #0x0
        mov     w21, #0x5
L5bdc:
        mov     x1, x19
        mov     w0, #0x0
L5be4:
        add     w2, w20, w0
        add     w0, w0, #0x1
        add     x1, x1, #0x40
        udiv    w3, w2, w21
        add     w4, w3, w3, lsl #2
        sturb   w3, [x1, #-31]
        sub     w2, w2, w4
        sturb   w2, [x1, #-32]
        cmp     w0, #0x4
        b.ne    L5be4
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
        bl      L2398
        cmp     w20, #0x1c
        b.ne    L5bdc
        mov     w0, #0x503
        mov     x1, x19
        strh    w0, [x19, #32]
        add     x0, x22, #0x7, lsl #12
        bl      L22a4
        mov     w0, #0x504
        mov     x1, x19
        strh    w0, [x19, #32]
        mov     x0, #0x7400
        add     x0, x22, x0
        bl      L22a4
        mov     x0, x19
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e60
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5cd8
        bl      L0e50
L5cd8:
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret

// mldsa65_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L5ce8:
        mov     w4, #0x1400
        umaddl  x1, w3, w4, x1
        b       L58d4

// mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L5cf4:
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
        bl      L0e30
        mov     x0, x20
        bl      L58a0
L5d28:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L5ce8
        cmp     x19, #0x6
        b.ne    L5d28
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L59e4

// mld_ct_memcmp (0x54 bytes)
L5d5c:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L5d68:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L5d90
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L5d90:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L5d68

// mld_zeroize (0x1c bytes)
L5db0:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e60
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t165 (0x160 bytes)
L5dcc:
        mov     x12, #0x8080
        sub     sp, sp, x12
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x1
        .inst   0xd00000c0  // adrp x0, 0x1f000
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
        bl      L5b8c
L5e44:
        mov     w3, w21
        mov     x2, x26
        mov     x1, x20
        mov     x0, x19
        bl      L5ce8
        mov     x0, x19
        bl      L2158
        add     x1, x25, x21, lsl #7
        mov     x0, x22
        bl      L54f0
        mov     x1, x22
        mov     x0, x19
        bl      L2048
        mov     x0, x19
        bl      L1fe0
        mov     x0, x19
        bl      L200c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x22
        bl      L2274
        madd    x0, x21, x28, x24
        mov     x1, x22
        bl      L2574
        madd    x0, x21, x27, x23
        mov     x1, x19
        add     x21, x21, #0x1
        bl      L2640
        cmp     x21, #0x6
        b.ne    L5e44
        mov     x0, x22
        mov     x1, #0x400
        bl      L5db0
        mov     x0, x19
        mov     x1, #0x400
        bl      L5db0
        mov     x0, x20
        mov     x1, #0x7800
        bl      L5db0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x8, lsl #12
        ldr     x3, [x2, #120]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L5f04
        bl      L0e50
L5f04:
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
L5f2c:
        stp     x19, x20, [sp, #-304]!
        mov     x20, x7
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        add     x19, sp, #0x58
        .inst   0xd00000c0  // adrp x0, 0x1f000
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
        bl      L1088
        mov     x2, x27
        mov     x1, x26
        mov     x0, x19
        bl      L10a8
        cbz     x21, L5fa4
        mov     x2, x21
        mov     x1, x25
        mov     x0, x19
        bl      L10a8
L5fa4:
        cbz     x20, L5fb8
        mov     x2, x20
        mov     x1, x24
        mov     x0, x19
        bl      L10a8
L5fb8:
        mov     x0, x19
        bl      L10d0
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L1150
        mov     x0, x19
        bl      L1170
        mov     x0, x19
        mov     x1, #0xd0
        bl      L5db0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6004
        bl      L0e50
L6004:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa65_keypair_internal (0x290 bytes)
L601c:
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
        bl      L1174
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
        bl      L5128
        mov     x1, x19
        add     x0, x20, #0x400
        bl      L54bc
        mov     x1, x23
        add     x0, x20, #0x480
        bl      L54bc
        mov     x1, x24
        add     x0, x20, #0x500
        bl      L54bc
        mov     x1, x26
        add     x0, x20, #0x580
        bl      L54bc
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
        bl      L5128
        ldr     x0, [sp, #120]
        mov     x1, x0
        add     x0, x20, #0x280
        bl      L54bc
        mov     x1, x19
        mov     x0, x28
        bl      L54bc
        mov     x1, x23
        add     x0, x20, #0x380
        bl      L54bc
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
        bl      L5128
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L54bc
        mov     x1, x23
        add     x0, x20, #0x100
        bl      L54bc
        mov     x1, x24
        add     x0, x20, #0x180
        bl      L54bc
        mov     x1, x26
        add     x0, x20, #0x200
        bl      L54bc
        mov     x0, x19
        bl      L58a0
        ldp     q0, q1, [x21]
        mov     x4, x21
        mov     x3, x28
        mov     x2, x19
        add     x1, x20, #0x600
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L5dcc
        mov     x4, #0x1480
        mov     w23, w0
        add     x24, x19, x4
        cbnz    w0, L6218
        mov     x2, x22
        mov     x0, x24
        mov     x3, #0x7a0
        mov     x1, #0x40
        bl      L1174
        add     x3, x21, #0x60
        mov     x2, x24
        mov     x1, x21
        mov     x0, x20
        bl      L4ce4
L6218:
        mov     x0, x19
        mov     x1, #0x1400
        bl      L5db0
        mov     x0, x24
        mov     x1, #0x40
        bl      L5db0
        mov     x0, x25
        mov     x1, #0x22
        bl      L5db0
        mov     x0, x21
        mov     x1, #0x80
        bl      L5db0
        cbz     w23, L6264
        mov     x0, x22
        mov     x1, #0x7a0
        bl      L5db0
        mov     x0, x20
        mov     x1, #0xfc0
        bl      L5db0
L6264:
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5512]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6284
        bl      L0e50
L6284:
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
L62ac:
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
        bl      L0e40
        cbnz    w0, L6328
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L601c
        mov     w20, w0
L62fc:
        mov     x0, x19
        mov     x1, #0x20
        bl      L5db0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6330
        bl      L0e50
L6328:
        mov     w20, #0xfffffffd
        b       L62fc
L6330:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa65_signature_internal (0x44c bytes)
L6340:
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
        bl      L4d0c
        add     x0, x21, #0x80
        cbnz    w27, L665c
        mov     x3, #0x40
        mov     x7, x25
        mov     x6, x26
        mov     x5, x24
        mov     x4, x22
        mov     x2, x28
        mov     x1, x3
        bl      L5f2c
L6414:
        mov     x5, #0x20
        add     x6, x21, #0x80
        mov     x4, x20
        mov     x3, x5
        add     x2, x21, #0x60
        mov     x7, #0x40
        add     x0, x21, #0xc0
        mov     x1, x7
        bl      L5f2c
        mov     x0, x19
        mov     x1, x21
        bl      L5b8c
        str     wzr, [sp, #124]
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0x400
        str     x0, [sp, #104]
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0x800
        str     x0, [sp, #112]
L6460:
        ldrh    w2, [sp, #124]
        mov     x0, #0xd400
        add     x27, x19, x0
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0xc, lsl #12
        add     x25, x19, #0x10, lsl #12
        mov     w26, #0xff3c
        bl      L5844
        mov     x28, #0x0
        mov     x1, #0x7800
        mov     x3, x20
        add     x24, x19, x1
        mov     x2, x27
        mov     x1, x19
        mov     x0, x24
        bl      L5cf4
        movk    w26, #0x7, lsl #16
        mov     x0, x24
        bl      L597c
        ldr     x0, [sp, #104]
        mov     x3, #0xfc00
        mov     x2, x20
        mov     x1, x24
        add     x22, x19, x3
        bl      L5a74
        ldp     x4, x0, [sp, #104]
        add     x2, x21, #0x80
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x300
        mov     x3, #0x40
        mov     x1, #0x30
        bl      L5f2c
        ldr     x1, [sp, #112]
        mov     x0, x25
        bl      L535c
        mov     x0, x25
        bl      L20b0
L64fc:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e30
        mov     x1, x25
        mov     x0, x22
        bl      L2238
        mov     x0, x22
        bl      L2158
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x3, x27
        bl      L0e30
        mov     x1, x20
        mov     x0, x22
        bl      L2048
        mov     x0, x22
        bl      L1fe0
        mov     w1, w26
        mov     x0, x22
        bl      L2860
        cbnz    w0, L6670
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L4ea4
        cmp     x28, #0x5
        b.ne    L64fc
        mov     x26, #0x0
L6584:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x24, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e30
        mov     x1, x25
        mov     x0, x20
        bl      L2238
        mov     x0, x20
        bl      L2158
        mov     x1, x20
        mov     x0, x28
        bl      L206c
        mov     x0, x28
        bl      L1fe0
        mov     w1, #0xfe3c
        mov     x0, x28
        movk    w1, #0x3, lsl #16
        bl      L2860
        cbnz    w0, L6670
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x26, x0
        mov     x0, x20
        bl      L0e30
        mov     x1, x25
        mov     x0, x20
        bl      L2238
        mov     x0, x20
        bl      L2158
        mov     x0, x20
        bl      L1fe0
        mov     x0, x20
        mov     w1, #0x3ff00
        bl      L2860
        cbnz    w0, L6670
        mov     x0, x28
        mov     x1, x20
        add     x26, x26, #0x400
        bl      L2048
        mov     x0, #0x1800
        cmp     x26, x0
        b.ne    L6584
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L4db0
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x24
        mov     x0, x23
        bl      L4dc4
        mov     w26, w0
        b       L6674
L665c:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L6414
L6670:
        mov     w26, #0xffffffff
L6674:
        mov     x0, x22
        mov     x1, #0x400
        bl      L5db0
        mov     x0, x25
        mov     x1, #0x400
        bl      L5db0
        mov     x0, x24
        mov     x1, #0x1800
        bl      L5db0
        ldr     x0, [sp, #104]
        mov     x1, #0x300
        bl      L5db0
        mov     x0, x20
        mov     x1, #0x1400
        bl      L5db0
        mov     x0, x27
        mov     x1, #0x1400
        bl      L5db0
        ldr     x0, [sp, #112]
        mov     x1, #0x30
        bl      L5db0
        cbz     w26, L6700
        cmn     w26, #0x1
        b.ne    L66f4
        ldr     w0, [sp, #124]
        add     w0, w0, #0x5
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfffa
        cmp     w1, w0, uxth
        b.ne    L6460
        mov     w26, #0xfffffffc
L66f4:
        mov     x0, x23
        mov     x1, #0xced
        bl      L5db0
L6700:
        ldr     x0, [sp, #128]
        mov     x1, #0x1800
        bl      L5db0
        ldr     x0, [sp, #144]
        mov     x1, #0x1800
        bl      L5db0
        ldr     x0, [sp, #136]
        mov     x1, #0x1400
        bl      L5db0
        mov     x0, x19
        mov     x1, #0x7800
        bl      L5db0
        mov     x0, x21
        mov     x1, #0x100
        bl      L5db0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x10, lsl #12
        add     x2, x2, #0x40
        ldr     x3, [x2, #2216]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L6764
        bl      L0e50
L6764:
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
L678c:
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
        bl      L0e40
        cbnz    w0, L6824
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L6340
        mov     w20, w0
L67f8:
        mov     x0, x19
        mov     x1, #0x20
        bl      L5db0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L682c
        bl      L0e50
L6824:
        mov     w20, #0xfffffffd
        b       L67f8
L682c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa65_verify_internal (0x324 bytes)
L6840:
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
        bl      L5b0c
        mov     w1, #0xff3c
        mov     x0, x26
        movk    w1, #0x7, lsl #16
        bl      L592c
        mov     x17, #0x9b80
        mov     w20, w0
        add     x0, x19, x17
        str     x0, [sp, #104]
        cbnz    w20, L6a84
        ldr     w6, [sp, #140]
        cbnz    w6, L6b24
        ldr     x2, [sp, #96]
        mov     x0, x24
        mov     x7, #0x0
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x7a0
        mov     x1, #0x40
        bl      L5f2c
        ldp     x7, x4, [sp, #112]
        mov     x10, #0x9b00
        ldr     x5, [sp, #128]
        mov     x6, x28
        mov     x2, x24
        mov     x3, #0x40
        add     x0, x19, x10
        mov     x1, x3
        bl      L5f2c
        mov     x0, x24
        mov     x1, #0x40
        bl      L5db0
L6968:
        mov     x0, x26
        bl      L58a0
        ldr     x1, [sp, #96]
        mov     x0, x19
        mov     x28, x24
        bl      L5b8c
        mov     x9, #0x9b80
        add     x1, x19, x9
        mov     x0, x27
        bl      L535c
        mov     x0, x27
        bl      L20b0
L6998:
        mov     w3, w20
        mov     x2, x26
        mov     x1, x19
        mov     x0, x21
        bl      L5ce8
        ldr     x1, [sp, #96]
        mov     w2, w20
        mov     x0, x22
        bl      L4cd0
        mov     x0, x22
        bl      L2090
        mov     x0, x22
        bl      L20b0
        mov     x1, x27
        mov     x0, x22
        bl      L2238
        mov     x1, x22
        mov     x0, x21
        bl      L206c
        mov     x0, x21
        bl      L1fe0
        mov     x0, x21
        bl      L2158
        mov     x0, x21
        bl      L200c
        mov     w2, w20
        mov     x1, x23
        mov     x0, x22
        bl      L4eb8
        mov     w25, w0
        cbnz    w0, L6a84
        mov     x1, x22
        mov     x0, x21
        bl      L5090
        add     w20, w20, #0x1
        mov     x0, x28
        mov     x1, x21
        bl      L2908
        add     x28, x28, #0x80
        cmp     w20, #0x6
        b.ne    L6998
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
        bl      L5f2c
        ldr     x0, [sp, #104]
        mov     x1, x20
        mov     x2, #0x30
        bl      L5d5c
        tst     w0, #0xff
        b.eq    L6a88
L6a84:
        mov     w25, #0xfffffffa
L6a88:
        mov     x0, x22
        mov     x1, #0x400
        bl      L5db0
        mov     x0, x21
        mov     x1, #0x400
        bl      L5db0
        mov     x0, x19
        mov     x1, #0x7800
        bl      L5db0
        mov     x0, x27
        mov     x1, #0x400
        bl      L5db0
        mov     x0, x26
        mov     x1, #0x1400
        bl      L5db0
        mov     x1, #0x30
        mov     x0, #0x9b40
        add     x0, x19, x0
        bl      L5db0
        ldr     x0, [sp, #104]
        mov     x1, #0x30
        bl      L5db0
        mov     x2, #0x9b00
        mov     x1, #0x40
        add     x0, x19, x2
        bl      L5db0
        mov     x0, x24
        mov     x1, #0x300
        bl      L5db0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x3, #0x8030
        add     x2, sp, x3
        ldr     x3, [x2, #7208]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L6b3c
        bl      L0e50
L6b24:
        ldp     q0, q1, [x28]
        sub     x0, x25, #0x100
        stp     q0, q1, [x0]
        ldp     q0, q1, [x28, #32]
        stp     q0, q1, [x0, #32]
        b       L6968
L6b3c:
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
L6b64:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L6840

// mldsa65_prepare_domain_separation_prefix (0x138 bytes)
L6b7c:
        cmp     x4, #0xff
        b.hi    L6ca4
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L6c68
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L6cac
        .inst   0xf0000000  // adrp x0, 0x9000
        add     x0, x0, #0xfe4
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 6bd0 <mldsa65_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L6bd4:
        b.ne    L6cac
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L6bf4
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e30
L6bf4:
        .inst   0xf0000000  // adrp x0, 0x9000
        add     x0, x0, #0xff0
        mov     x1, #0x0
L6c00:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L6c94
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L6c30:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e30
        add     x0, x20, x19
        b       L6c84
        cmp     x20, #0x20
        b       L6bd4
        cmp     x20, #0x30
        b       L6bd4
        cmp     x20, #0x40
        b       L6bd4
L6c68:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L6c80
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e30
L6c80:
        add     x0, x19, #0x2
L6c84:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L6c94:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L6c00
        b       L6c30
L6ca4:
        mov     x0, #0x0
        ret
L6cac:
        mov     x0, #0x0
        b       L6c84

// mldsa65_signature (0x100 bytes)
L6cb4:
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
        bl      L6b7c
        cbz     x0, L6d8c
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e40
        cbnz    w0, L6d94
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L6340
        mov     w19, w0
        cbz     w0, L6d54
L6d48:
        mov     x0, x21
        mov     x1, #0xced
        bl      L5db0
L6d54:
        mov     x0, x22
        mov     x1, #0x20
        bl      L5db0
        mov     x0, x20
        mov     x1, #0x14c
        bl      L5db0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6d9c
        bl      L0e50
L6d8c:
        mov     w19, #0xfffffff7
        b       L6d48
L6d94:
        mov     w19, #0xfffffffd
        b       L6d48
L6d9c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa65_verify (0xbc bytes)
L6db4:
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
        bl      L6b7c
        cbz     x0, L6e54
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L6840
        mov     w20, w0
L6e28:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L5db0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6e5c
        bl      L0e50
L6e54:
        mov     w20, #0xfffffff7
        b       L6e28
L6e5c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa65_signature_pre_hash_internal (0xc8 bytes)
L6e70:
        stp     x19, x20, [sp, #-416]!
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     x22, x6
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #32]
        add     x20, sp, #0x4f
        ldr     x6, [x0]
        str     x6, [sp, #408]
        mov     x6, #0x0
        and     x20, x20, #0xffffffffffffffe0
        cbnz    w7, L6eb8
L6ea4:
        mov     w19, #0xfffffff7
L6ea8:
        mov     x0, x21
        mov     x1, #0xced
        bl      L5db0
        b       L6ef8
L6eb8:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L6b7c
        mov     x2, x0
        cbz     x0, L6ea4
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L6340
        mov     w19, w0
        cbnz    w0, L6ea8
L6ef8:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L5db0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6f24
        bl      L0e50
L6f24:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa65_signature_pre_hash_shake256 (0xc0 bytes)
L6f38:
        stp     x19, x20, [sp, #-160]!
        mov     x20, x0
        .inst   0xb00000c0  // adrp x0, 0x1f000
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
        bl      L1174
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L6e70
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L5db0
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L6fe0
        bl      L0e50
L6fe0:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa65_verify_pre_hash_internal (0xa8 bytes)
L6ff8:
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
        cbnz    w5, L705c
L702c:
        mov     w20, #0xfffffff7
L7030:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L5db0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7090
        bl      L0e50
L705c:
        mov     x0, x19
        bl      L6b7c
        mov     x2, x0
        cbz     x0, L702c
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L6840
        mov     w20, w0
        b       L7030
L7090:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa65_verify_pre_hash_shake256 (0xb0 bytes)
L70a0:
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
        bl      L1174
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L6ff8
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L5db0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L713c
        bl      L0e50
L713c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa65_pk_from_sk (0x210 bytes)
L7150:
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
        bl      L5acc
        mov     w1, #0x5
        mov     x0, x19
        bl      L592c
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x5
        mov     x0, x23
        bl      L5a18
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L58a0
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L5dcc
        mov     x6, #0x21c0
        mov     w22, w0
        add     x23, x19, x6
        cbnz    w0, L72b4
        add     x1, x25, #0x600
        mov     x0, x24
        mov     x2, #0x9c0
        bl      L5d5c
        and     w4, w0, #0xff
        mov     x3, #0x7a0
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1174
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L5d5c
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L72c0
        mov     w22, #0xfffffff9
L72b4:
        mov     x0, x21
        mov     x1, #0x7a0
        bl      L5db0
L72c0:
        mov     x0, x24
        mov     x1, #0x9c0
        bl      L5db0
        mov     x0, x28
        mov     x1, #0x400
        bl      L5db0
        mov     x0, x19
        mov     x1, #0x1400
        bl      L5db0
        mov     x1, #0x20
        mov     x0, #0x2240
        add     x0, x19, x0
        bl      L5db0
        mov     x0, x23
        mov     x1, #0x40
        bl      L5db0
        mov     x0, x27
        mov     x1, #0x40
        bl      L5db0
        mov     x0, x26
        mov     x1, #0x20
        bl      L5db0
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8968]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7338
        bl      L0e50
L7338:
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
L7360:
        mov     w3, #0x140
        mul     w2, w2, w3
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L25d0

// mldsa87_pack_sk_rho_key_tr (0x28 bytes)
L7374:
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
L739c:
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
        bl      L81c4
        mov     x0, x22
        mov     x22, x20
        bl      L7fa8
        add     x1, x19, #0x320
        mov     x0, x21
        bl      L8244
        mov     x0, x21
        add     x21, x19, #0x620
        bl      L80b4
        mov     x0, #0x1320
        add     x19, x19, x0
L7414:
        mov     x1, x21
        mov     x0, x22
        add     x21, x21, #0x1a0
        bl      L270c
        add     x22, x22, #0x400
        cmp     x21, x19
        b.ne    L7414
        ldp     x21, x22, [sp, #16]
        mov     x0, x20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L80b4

// mldsa87_pack_sig_c (0x14 bytes)
L7444:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x1, #32]
        stp     q0, q1, [x0, #32]
        ret

// mldsa87_pack_sig_h (0xe8 bytes)
L7458:
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
        bl      L0e60
L74b0:
        add     x1, x24, x19, lsl #7
        mov     x0, x22
        bl      L298c
        add     x1, x23, x19, lsl #10
        mov     x4, #0x0
L74c4:
        ldr     w0, [x1, x4, lsl #2]
        ldr     w2, [x22, x4, lsl #2]
        add     w3, w0, w26
        cmp     w3, w27
        b.hi    L74e4
        cmp     w2, #0x0
        ccmp    w0, w28, #0x0, ne
        b.ne    L74f4
L74e4:
        cmp     w20, #0x4b
        b.eq    L7538
        strb    w4, [x25, w20, uxtw]
        add     w20, w20, #0x1
L74f4:
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.ne    L74c4
        mov     x0, #0x120b
        add     x0, x21, x0
        strb    w20, [x0, x19]
        add     x19, x19, #0x1
        cmp     x19, #0x8
        b.ne    L74b0
        mov     w0, #0x0
L751c:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L7538:
        mov     w0, #0xffffffff
        b       L751c

// mldsa87_pack_sig_z (0x14 bytes)
L7540:
        mov     w3, #0x280
        mul     w2, w2, w3
        add     x2, x2, #0x40
        add     x0, x0, x2
        b       L7cdc

// mldsa87_sig_unpack_hints (0xe8 bytes)
L7554:
        stp     x19, x20, [sp, #-48]!
        mov     x4, #0x11c0
        mov     x3, x0
        stp     x21, x22, [sp, #16]
        mov     x20, x1
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        add     x23, x1, x4
        cbz     w2, L75a8
        add     w0, w2, #0x4a
        ldrb    w22, [x23, x0]
L7580:
        add     w0, w21, #0x4b
        ldrb    w19, [x23, x0]
        cmp     w19, #0x4b
        ccmp    w22, w19, #0x2, ls
        b.ls    L75b0
L7594:
        mov     w0, #0xffffffff
L7598:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L75a8:
        mov     w22, #0x0
        b       L7580
L75b0:
        mov     x0, x3
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e60
        mov     w1, #0x11c0
        add     w1, w22, w1
        mov     x3, x0
        add     x1, x20, x1
        mov     w2, w22
        mov     w4, #0x1
L75d8:
        cmp     w2, w19
        b.cc    L7600
        cmp     w21, #0x7
        b.ne    L75f8
        mov     x0, #0x11bf
        add     x20, x20, x0
L75f0:
        cmp     w19, #0x4b
        b.ne    L762c
L75f8:
        mov     w0, #0x0
        b       L7598
L7600:
        cmp     w2, w22
        b.ls    L761c
        sub     w0, w2, #0x1
        ldrb    w5, [x1]
        ldrb    w0, [x23, x0]
        cmp     w5, w0
        b.ls    L7594
L761c:
        ldrb    w0, [x1], #1
        add     w2, w2, #0x1
        str     w4, [x3, x0, lsl #2]
        b       L75d8
L762c:
        add     x19, x19, #0x1
        ldrb    w0, [x20, x19]
        cbz     w0, L75f0
        b       L7594

// mld_decompose87 (0x4c bytes)
L763c:
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
L7688:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e60
        ldp     x19, x30, [sp], #16
        ret

// mld_rej_eta_c87.constprop.0 (0x88 bytes)
L76a4:
        mov     x6, x0
        mov     w0, w1
        mov     x5, #0x0
        mov     w9, #0x87
        mov     w7, #0xcd
        mov     w8, #0x2
L76bc:
        cmp     w0, #0xff
        ccmp    w5, w9, #0x2, ls
        b.ls    L76cc
        ret
L76cc:
        ldrb    w1, [x2, x5]
        and     w3, w1, #0xf
        lsr     w1, w1, #4
        cmp     w3, #0xf
        b.eq    L76fc
        mul     w4, w3, w7
        lsr     w4, w4, #10
        add     w4, w4, w4, lsl #2
        sub     w3, w3, w4
        sub     w3, w8, w3
        str     w3, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L76fc:
        cmp     w0, #0xff
        ccmp    w1, #0xe, #0x2, ls
        b.hi    L7724
        mul     w3, w1, w7
        lsr     w3, w3, #10
        add     w3, w3, w3, lsl #2
        sub     w1, w1, w3
        sub     w1, w8, w1
        str     w1, [x6, w0, uxtw #2]
        add     w0, w0, #0x1
L7724:
        add     x5, x5, #0x1
        b       L76bc

// mldsa87_poly_decompose (0x34 bytes)
L772c:
        mov     x6, x0
        mov     x5, x1
        mov     x4, #0x0
        str     x30, [sp, #-16]!
L773c:
        ldr     w2, [x5, x4]
        add     x1, x6, x4
        add     x0, x5, x4
        add     x4, x4, #0x4
        bl      L763c
        cmp     x4, #0x400
        b.ne    L773c
        ldr     x30, [sp], #16
        ret

// mldsa87_poly_use_hint (0x98 bytes)
L7760:
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
L778c:
        ldr     w2, [x5, x4]
        mov     x1, x7
        ldr     w8, [x6, x4]
        bl      L763c
        ldr     w2, [sp, #20]
        cbz     w8, L77c0
        ldr     w1, [sp, #16]
        add     w3, w2, #0x1
        sub     w2, w2, #0x1
        and     w3, w3, #0xf
        and     w2, w2, #0xf
        cmp     w1, #0x0
        csel    w2, w2, w3, le
L77c0:
        str     w2, [x5, x4]
        add     x4, x4, #0x4
        cmp     x4, #0x400
        b.ne    L778c
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L77f0
        bl      L0e50
L77f0:
        ldr     x30, [sp], #32
        ret

// mldsa87_poly_uniform_eta_4x (0x22c bytes)
L77f8:
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
        bl      L1548
        mov     x4, x22
        mov     x3, x21
        mov     x2, x20
        mov     x1, x24
        mov     x0, x23
        mov     x5, #0x42
        bl      L1464
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L14c8
        ldr     x0, [sp, #96]
        mov     x2, x19
        mov     w1, #0x0
        bl      L76a4
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     x2, x28
        mov     w1, #0x0
        bl      L76a4
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     x2, x27
        mov     w1, #0x0
        bl      L76a4
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L792c:
        mov     x0, x25
        bl      L76a4
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L7998
        cmp     w22, #0xff
        b.ls    L7998
        cmp     w20, #0xff
        b.ls    L7998
        cmp     w0, #0xff
        b.ls    L7998
        mov     x0, x23
        bl      L154c
        mov     x0, x19
        mov     x1, #0x280
        bl      L7688
        mov     x0, x24
        mov     x1, #0x180
        bl      L7688
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1976]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7a04
        bl      L0e50
L7998:
        mov     x5, x23
        mov     x3, x26
        mov     x4, #0x1
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L14c8
        ldr     x0, [sp, #96]
        mov     w1, w21
        mov     x2, x19
        bl      L76a4
        mov     w21, w0
        ldr     x0, [sp, #104]
        mov     w1, w22
        mov     x2, x28
        bl      L76a4
        mov     w22, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x27
        bl      L76a4
        mov     x2, x26
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     w1, w6
        b       L792c
L7a04:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7c0
        ret

// mldsa87_poly_challenge (0x160 bytes)
L7a24:
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
        bl      L1088
        mov     x1, x19
        mov     x2, #0x40
        mov     x0, x21
        bl      L10a8
        mov     x0, x21
        mov     x19, #0x0
        bl      L10d0
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1150
        mov     x0, #0x0
L7a94:
        ldrb    w1, [x19, x20]
        lsl     w2, w19, #3
        add     x19, x19, #0x1
        lsl     x1, x1, x2
        orr     x0, x0, x1
        cmp     x19, #0x8
        b.ne    L7a94
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x23, #0xc4
        mov     w24, #0x1
        str     x0, [sp, #72]
        mov     x0, x22
        bl      L0e60
L7acc:
        cmp     w19, #0x88
        b.ne    L7b68
        mov     x0, x20
        mov     x2, x21
        mov     x1, #0x88
        bl      L1150
        mov     w0, #0x0
L7ae8:
        add     w19, w0, #0x1
        ldrb    w0, [x20, w0, uxtw]
        cmp     w0, w23
        b.hi    L7acc
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
        b.ne    L7acc
        mov     x0, x21
        bl      L1170
        mov     x0, x20
        mov     x1, #0x88
        bl      L7688
        add     x0, sp, #0x48
        mov     x1, #0x8
        bl      L7688
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #456]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7b70
        bl      L0e50
L7b68:
        mov     w0, w19
        b       L7ae8
L7b70:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #464
        ret

// mldsa87_polyeta_pack (0x98 bytes)
L7b84:
        add     x9, x1, #0x400
        mov     w5, #0x2
L7b8c:
        ldp     w2, w4, [x1, #8]
        add     x0, x0, #0x3
        ldp     w10, w7, [x1, #16]
        sub     w6, w5, w4
        ldr     w4, [x1, #4]
        sub     w2, w5, w2
        ldp     w3, w8, [x1, #24]
        sub     w4, w5, w4
        ubfiz   w11, w2, #6, #8
        sub     w7, w5, w7
        ubfiz   w4, w4, #3, #8
        sub     w10, w5, w10
        orr     w4, w4, w11
        ldr     w11, [x1], #32
        ubfx    x2, x2, #2, #6
        sub     w3, w5, w3
        sub     w11, w5, w11
        sub     w8, w5, w8
        orr     w4, w4, w11
        sturb   w4, [x0, #-3]
        ubfiz   w4, w7, #7, #8
        ubfx    x7, x7, #1, #7
        orr     w2, w2, w4
        ubfiz   w4, w6, #1, #8
        ubfiz   w6, w10, #4, #8
        orr     w4, w4, w6
        orr     w2, w2, w4
        sturb   w2, [x0, #-2]
        ubfiz   w2, w3, #2, #8
        ubfiz   w3, w8, #5, #8
        orr     w2, w2, w3
        orr     w2, w2, w7
        sturb   w2, [x0, #-1]
        cmp     x9, x1
        b.ne    L7b8c
        ret

// mldsa87_polyeta_unpack (0xc0 bytes)
L7c1c:
        add     x11, x0, #0x400
        mov     w2, #0x2
L7c24:
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
        b.ne    L7c24
        ret

// mldsa87_polyz_pack (0x50 bytes)
L7cdc:
        add     x5, x0, #0x280
        mov     w4, #0x80000
L7ce4:
        ldp     w3, w2, [x1]
        add     x0, x0, #0x5
        add     x1, x1, #0x8
        sub     w3, w4, w3
        sub     w2, w4, w2
        sturb   w3, [x0, #-5]
        lsr     w6, w3, #8
        sturb   w6, [x0, #-4]
        ubfiz   w6, w2, #4, #4
        orr     w3, w6, w3, lsr #16
        sturb   w3, [x0, #-3]
        lsr     w3, w2, #4
        lsr     w2, w2, #12
        sturb   w3, [x0, #-2]
        sturb   w2, [x0, #-1]
        cmp     x5, x0
        b.ne    L7ce4
        ret

// mldsa87_polyz_unpack (0x70 bytes)
L7d2c:
        add     x6, x0, #0x400
        mov     w5, #0x80000
L7d34:
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
        b.ne    L7d34
        ret

// mldsa87_poly_uniform_gamma1_4x (0x17c bytes)
L7d9c:
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
        .inst   0x900000c0  // adrp x0, 0x1f000
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
        bl      L1548
        mov     x4, x27
        mov     x3, x26
        mov     x2, x21
        mov     x1, x20
        mov     x0, x28
        add     x21, x19, #0x840
        add     x26, x19, #0x580
        mov     x5, #0x42
        bl      L1464
        add     x27, x19, #0x2c0
        mov     x2, x26
        mov     x5, x28
        mov     x3, x21
        mov     x4, #0x5
        mov     x1, x27
        mov     x0, x19
        bl      L14c8
        mov     x1, x19
        mov     x0, x25
        bl      L7d2c
        mov     x1, x27
        mov     x0, x24
        bl      L7d2c
        mov     x1, x26
        mov     x0, x23
        bl      L7d2c
        mov     x1, x21
        mov     x0, x22
        bl      L7d2c
        mov     x0, x28
        bl      L154c
        mov     x0, x19
        mov     x1, #0xb00
        bl      L7688
        mov     x0, x20
        mov     x1, #0x180
        bl      L7688
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L7ef4
        bl      L0e50
L7ef4:
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
L7f18:
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
        bl      L7d9c
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
        bl      L7d9c
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, #0x40
        ret

// mldsa87_polyvecl_ntt (0x34 bytes)
L7fa8:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1c00
        add     x20, x19, x0
        str     x30, [sp, #16]
L7fbc:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20b0
        cmp     x19, x20
        b.ne    L7fbc
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvecl_pointwise_acc_montgomery (0x58 bytes)
L7fdc:
        mov     w7, #0x2001
        mov     x3, #0x0
        movk    w7, #0x380, lsl #16
        mov     w8, #0xff801fff
L7fec:
        mov     x4, x3
        mov     x5, #0x0
        mov     w6, #0x0
L7ff8:
        ldr     w10, [x1, x4]
        add     w6, w6, #0x1
        ldr     w9, [x2, x4]
        add     x4, x4, #0x400
        smaddl  x5, w10, w9, x5
        cmp     w6, #0x7
        b.ne    L7ff8
        mul     w4, w5, w7
        smaddl  x4, w4, w8, x5
        asr     x4, x4, #32
        str     w4, [x0, x3]
        add     x3, x3, #0x4
        cmp     x3, #0x400
        b.ne    L7fec
        ret

// mldsa87_polyvecl_chknorm (0x50 bytes)
L8034:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1c00
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
L8054:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L2860
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L8054
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyveck_caddq (0x30 bytes)
L8084:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L8094:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L200c
        cmp     x19, x20
        b.ne    L8094
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_ntt (0x30 bytes)
L80b4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L80c4:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20b0
        cmp     x19, x20
        b.ne    L80c4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_invntt_tomont (0x30 bytes)
L80e4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L80f4:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2158
        cmp     x19, x20
        b.ne    L80f4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta_chknorm (0x5c bytes)
L8114:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L8134:
        mov     x1, x19
        mov     x0, x20
        bl      L7c1c
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L2860
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L8134
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyveck_decompose_pack_w1 (0x54 bytes)
L8170:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, #0x2, lsl #12
        str     x30, [sp, #32]
L818c:
        mov     x1, x19
        mov     x0, x21
        bl      L772c
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2908
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L818c
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyvecl_unpack_eta (0x40 bytes)
L81c4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1c00
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L81dc:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L7c1c
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L81dc
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvecl_unpack_z (0x40 bytes)
L8204:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1c00
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L821c:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L7d2c
        add     x20, x20, #0x280
        cmp     x19, x21
        b.ne    L821c
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta (0x3c bytes)
L8244:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x2, lsl #12
L8258:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L7c1c
        add     x20, x20, #0x60
        cmp     x19, x21
        b.ne    L8258
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvec_matrix_expand_eager (0x11c bytes)
L8280:
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
L82b0:
        ldp     q0, q1, [x1]
        add     w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     w2, #0x4
        b.ne    L82b0
        mov     w20, #0x0
        mov     w19, #0x7
L82d0:
        mov     x1, x21
        mov     w0, #0x0
L82d8:
        add     w2, w20, w0
        add     w0, w0, #0x1
        add     x1, x1, #0x40
        udiv    w3, w2, w19
        msub    w2, w3, w19, w2
        sturb   w3, [x1, #-31]
        sturb   w2, [x1, #-32]
        cmp     w0, #0x4
        b.ne    L82d8
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
        bl      L2398
        cmp     w20, #0x38
        b.ne    L82d0
        mov     x0, x21
        mov     x2, #0x100
        mov     w1, #0x0
        bl      L0e60
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L838c
        bl      L0e50
L838c:
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret

// mldsa87_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L839c:
        mov     w4, #0x1c00
        umaddl  x1, w3, w4, x1
        b       L7fdc

// mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager (0x68 bytes)
L83a8:
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
        bl      L0e30
        mov     x0, x20
        bl      L7fa8
L83dc:
        mov     w3, w19
        add     x0, x21, x19, lsl #10
        mov     x2, x20
        mov     x1, x22
        add     x19, x19, #0x1
        bl      L839c
        cmp     x19, #0x8
        b.ne    L83dc
        ldr     x30, [sp, #32]
        mov     x0, x21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        b       L80e4

// mld_ct_memcmp (0x54 bytes)
L8410:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L841c:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L8444
        mov     w1, w3
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w5, w1
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L8444:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L841c

// mld_zeroize (0x1c bytes)
L8464:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e60
        ldp     x19, x30, [sp], #16
        ret

// mld_compute_pack_t0_t187 (0x168 bytes)
L8480:
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
        bl      L8280
L84fc:
        ldr     x2, [sp, #104]
        mov     w3, w25
        mov     x1, x20
        mov     x0, x19
        bl      L839c
        mov     x0, x19
        bl      L2158
        madd    x1, x25, x28, x24
        mov     x0, x21
        bl      L7c1c
        mov     x1, x21
        mov     x0, x19
        bl      L2048
        mov     x0, x19
        bl      L1fe0
        mov     x0, x19
        bl      L200c
        mov     x2, x19
        mov     x1, x19
        mov     x0, x21
        bl      L2274
        madd    x0, x25, x27, x23
        mov     x1, x21
        bl      L2574
        madd    x0, x25, x26, x22
        mov     x1, x19
        add     x25, x25, #0x1
        bl      L2640
        cmp     x25, #0x8
        b.ne    L84fc
        mov     x0, x21
        mov     x1, #0x400
        bl      L8464
        mov     x0, x19
        mov     x1, #0x400
        bl      L8464
        mov     x0, x20
        mov     x1, #0xe000
        bl      L8464
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x1, #0xc010
        add     x2, sp, x1
        ldr     x3, [x2, #10360]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L85c0
        bl      L0e50
L85c0:
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
L85e8:
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
        bl      L1088
        mov     x2, x26
        mov     x1, x25
        mov     x0, x19
        bl      L10a8
        cbz     x21, L865c
        mov     x2, x21
        mov     x1, x24
        mov     x0, x19
        bl      L10a8
L865c:
        cbz     x20, L8670
        mov     x2, x20
        mov     x1, x23
        mov     x0, x19
        bl      L10a8
L8670:
        mov     x0, x19
        bl      L10d0
        mov     x2, x19
        mov     x1, #0x40
        mov     x0, x22
        bl      L1150
        mov     x0, x19
        bl      L1170
        mov     x0, x19
        mov     x1, #0xd0
        bl      L8464
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L86bc
        bl      L0e50
L86bc:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret

// mldsa87_keypair_internal (0x304 bytes)
L86d4:
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
        bl      L1174
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
        bl      L77f8
        mov     x1, x19
        add     x0, x20, #0x4a0
        bl      L7b84
        mov     x1, x25
        add     x0, x20, #0x500
        bl      L7b84
        mov     x1, x24
        add     x0, x20, #0x560
        bl      L7b84
        mov     x1, x23
        add     x0, x20, #0x5c0
        bl      L7b84
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
        bl      L77f8
        mov     x1, x19
        mov     x0, x28
        bl      L7b84
        mov     x1, x25
        add     x0, x20, #0x380
        bl      L7b84
        mov     x1, x24
        add     x0, x20, #0x3e0
        bl      L7b84
        mov     x1, x23
        add     x0, x20, #0x440
        bl      L7b84
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
        bl      L77f8
        ldr     x0, [sp, #120]
        mov     x1, x0
        add     x0, x20, #0x200
        bl      L7b84
        ldr     x8, [sp, #128]
        add     x0, x20, #0x260
        mov     x1, x8
        bl      L7b84
        ldr     x2, [sp, #136]
        add     x0, x20, #0x2c0
        mov     x1, x2
        bl      L7b84
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
        bl      L77f8
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L7b84
        mov     x1, x25
        add     x0, x20, #0xe0
        bl      L7b84
        mov     x1, x24
        add     x0, x20, #0x140
        bl      L7b84
        mov     x1, x23
        add     x0, x20, #0x1a0
        bl      L7b84
        mov     x0, x19
        bl      L7fa8
        ldp     q0, q1, [x21]
        mov     x4, x21
        mov     x3, x28
        mov     x2, x19
        add     x1, x20, #0x620
        add     x0, x22, #0x20
        stp     q0, q1, [x22]
        bl      L8480
        mov     x6, #0x1c80
        mov     w23, w0
        add     x24, x19, x6
        cbnz    w0, L8944
        mov     x2, x22
        mov     x0, x24
        mov     x3, #0xa20
        mov     x1, #0x40
        bl      L1174
        add     x3, x21, #0x60
        mov     x2, x24
        mov     x1, x21
        mov     x0, x20
        bl      L7374
L8944:
        mov     x0, x19
        mov     x1, #0x1c00
        bl      L8464
        mov     x0, x24
        mov     x1, #0x40
        bl      L8464
        mov     x0, x26
        mov     x1, #0x22
        bl      L8464
        mov     x0, x21
        mov     x1, #0x80
        bl      L8464
        cbz     w23, L8990
        mov     x0, x22
        mov     x1, #0xa20
        bl      L8464
        mov     x0, x20
        mov     x1, #0x1320
        bl      L8464
L8990:
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7576]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L89b0
        bl      L0e50
L89b0:
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
L89d8:
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
        bl      L0e40
        cbnz    w0, L8a54
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L86d4
        mov     w20, w0
L8a28:
        mov     x0, x19
        mov     x1, #0x20
        bl      L8464
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8a5c
        bl      L0e50
L8a54:
        mov     w20, #0xfffffffd
        b       L8a28
L8a5c:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mldsa87_signature_internal (0x434 bytes)
L8a6c:
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
        bl      L739c
        add     x0, x21, #0x80
        cbnz    w27, L8d70
        mov     x6, x25
        mov     x5, x26
        mov     x4, x24
        mov     x3, x22
        mov     x1, x28
        mov     x2, #0x40
        bl      L85e8
L8b34:
        mov     x4, #0x20
        add     x5, x21, #0x80
        mov     x3, x20
        mov     x2, x4
        mov     x6, #0x40
        add     x1, x21, #0x60
        add     x0, x21, #0xc0
        bl      L85e8
        mov     x0, x19
        mov     x1, x21
        bl      L8280
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
L8b8c:
        ldrh    w2, [sp, #124]
        add     x1, x21, #0xc0
        mov     x0, x27
        add     x20, x19, #0x14, lsl #12
        add     x25, x19, #0xe, lsl #12
        add     x22, x19, #0x19, lsl #12
        mov     w26, #0xff88
        add     x22, x22, #0x400
        bl      L7f18
        mov     x28, #0x0
        mov     x3, x20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x25
        bl      L83a8
        movk    w26, #0x7, lsl #16
        mov     x0, x25
        bl      L8084
        ldr     x0, [sp, #104]
        mov     x2, x20
        mov     x1, x25
        bl      L8170
        ldp     x3, x0, [sp, #104]
        add     x1, x21, #0x80
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x400
        mov     x2, #0x40
        bl      L85e8
        ldr     x1, [sp, #112]
        mov     x0, x24
        bl      L7a24
        mov     x0, x24
        bl      L20b0
L8c14:
        ldr     x0, [sp, #136]
        lsl     x3, x28, #10
        mov     x2, #0x400
        str     x3, [sp, #152]
        add     x1, x0, x28, lsl #10
        mov     x0, x22
        bl      L0e30
        mov     x1, x24
        mov     x0, x22
        bl      L2238
        mov     x0, x22
        bl      L2158
        ldr     x3, [sp, #152]
        mov     x2, #0x400
        mov     x0, x20
        add     x1, x3, x27
        bl      L0e30
        mov     x1, x20
        mov     x0, x22
        bl      L2048
        mov     x0, x22
        bl      L1fe0
        mov     w1, w26
        mov     x0, x22
        bl      L2860
        cbnz    w0, L8d84
        mov     w2, w28
        mov     x1, x22
        mov     x0, x23
        add     x28, x28, #0x1
        bl      L7540
        cmp     x28, #0x7
        b.ne    L8c14
        mov     x26, #0x0
L8c9c:
        ldr     x0, [sp, #128]
        mov     x2, #0x400
        add     x28, x25, x26
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e30
        mov     x1, x24
        mov     x0, x20
        bl      L2238
        mov     x0, x20
        bl      L2158
        mov     x1, x20
        mov     x0, x28
        bl      L206c
        mov     x0, x28
        bl      L1fe0
        mov     w1, #0xfe88
        mov     x0, x28
        movk    w1, #0x3, lsl #16
        bl      L2860
        cbnz    w0, L8d84
        ldr     x0, [sp, #144]
        mov     x2, #0x400
        add     x1, x0, x26
        mov     x0, x20
        bl      L0e30
        mov     x1, x24
        mov     x0, x20
        bl      L2238
        mov     x0, x20
        bl      L2158
        mov     x0, x20
        bl      L1fe0
        mov     x0, x20
        mov     w1, #0x3ff00
        bl      L2860
        cbnz    w0, L8d84
        mov     x1, x20
        mov     x0, x28
        add     x26, x26, #0x400
        bl      L2048
        cmp     x26, #0x2, lsl #12
        b.ne    L8c9c
        ldr     x1, [sp, #112]
        mov     x0, x23
        bl      L7444
        ldr     x2, [sp, #104]
        mov     x3, x20
        mov     x1, x25
        mov     x0, x23
        bl      L7458
        mov     w26, w0
        b       L8d88
L8d70:
        ldp     q0, q1, [x26]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x26, #32]
        stp     q0, q1, [x0, #32]
        b       L8b34
L8d84:
        mov     w26, #0xffffffff
L8d88:
        mov     x0, x22
        mov     x1, #0x400
        bl      L8464
        mov     x0, x24
        mov     x1, #0x400
        bl      L8464
        mov     x0, x25
        mov     x1, #0x2000
        bl      L8464
        ldr     x0, [sp, #104]
        mov     x1, #0x400
        bl      L8464
        mov     x0, x20
        mov     x1, #0x1c00
        bl      L8464
        mov     x0, x27
        mov     x1, #0x1c00
        bl      L8464
        ldr     x0, [sp, #112]
        mov     x1, #0x40
        bl      L8464
        cbz     w26, L8e14
        cmn     w26, #0x1
        b.ne    L8e08
        ldr     w0, [sp, #124]
        add     w0, w0, #0x7
        and     w1, w0, #0xffff
        str     w1, [sp, #124]
        mov     w1, #0xfff7
        cmp     w1, w0, uxth
        b.ne    L8b8c
        mov     w26, #0xfffffffc
L8e08:
        mov     x0, x23
        mov     x1, #0x1213
        bl      L8464
L8e14:
        ldr     x0, [sp, #128]
        mov     x1, #0x2000
        bl      L8464
        ldr     x0, [sp, #144]
        mov     x1, #0x2000
        bl      L8464
        ldr     x0, [sp, #136]
        mov     x1, #0x1c00
        bl      L8464
        mov     x0, x19
        mov     x1, #0xe000
        bl      L8464
        mov     x0, x21
        mov     x1, #0x100
        bl      L8464
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x18, lsl #12
        add     x2, x2, #0x40
        ldr     x3, [x2, #8632]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L8e78
        bl      L0e50
L8e78:
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
L8ea0:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xf00000a0  // adrp x0, 0x1f000
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
        bl      L0e40
        cbnz    w0, L8f38
        mov     x0, x20
        mov     x6, x22
        mov     x5, x19
        mov     x1, x21
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L8a6c
        mov     w20, w0
L8f0c:
        mov     x0, x19
        mov     x1, #0x20
        bl      L8464
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L8f40
        bl      L0e50
L8f38:
        mov     w20, #0xfffffffd
        b       L8f0c
L8f40:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mldsa87_verify_internal (0x30c bytes)
L8f54:
        sub     sp, sp, #0xd70
        mov     x7, #0xfc00
        sub     sp, sp, #0x10, lsl #12
        stp     x19, x20, [sp]
        add     x19, sp, #0xaf
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        add     x24, x19, #0x10, lsl #12
        .inst   0xf00000a0  // adrp x0, 0x1f000
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
        bl      L8204
        mov     w1, #0xff88
        mov     x0, x27
        movk    w1, #0x7, lsl #16
        bl      L8034
        mov     w20, w0
        add     x0, x19, #0x10, lsl #12
        add     x0, x0, #0xc40
        str     x0, [sp, #112]
        cbnz    w20, L9184
        ldr     w6, [sp, #140]
        cbnz    w6, L9220
        ldr     x1, [sp, #104]
        mov     x0, x24
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0xa20
        bl      L85e8
        ldp     x3, x4, [sp, #120]
        mov     x5, x25
        ldr     x6, [sp, #96]
        add     x0, x19, #0x10, lsl #12
        mov     x2, #0x40
        mov     x1, x24
        add     x0, x0, #0xc80
        bl      L85e8
        mov     x0, x24
        mov     x1, #0x40
        bl      L8464
L906c:
        mov     x0, x27
        bl      L7fa8
        ldr     x1, [sp, #104]
        mov     x0, x19
        bl      L8280
        add     x1, x19, #0x10, lsl #12
        mov     x0, x28
        add     x1, x1, #0xc40
        bl      L7a24
        mov     x0, x28
        bl      L20b0
        str     x24, [sp, #96]
L909c:
        mov     w3, w20
        mov     x2, x27
        mov     x1, x19
        mov     x0, x21
        bl      L839c
        ldr     x1, [sp, #104]
        mov     w2, w20
        mov     x0, x22
        bl      L7360
        mov     x0, x22
        bl      L2090
        mov     x0, x22
        bl      L20b0
        mov     x1, x28
        mov     x0, x22
        bl      L2238
        mov     x1, x22
        mov     x0, x21
        bl      L206c
        mov     x0, x21
        bl      L1fe0
        mov     x0, x21
        bl      L2158
        mov     x0, x21
        bl      L200c
        mov     w2, w20
        mov     x1, x23
        mov     x0, x22
        bl      L7554
        mov     w25, w0
        cbnz    w0, L9184
        mov     x1, x22
        mov     x0, x21
        bl      L7760
        add     w20, w20, #0x1
        ldr     x0, [sp, #96]
        mov     x1, x21
        bl      L2908
        ldr     x0, [sp, #96]
        add     x0, x0, #0x80
        str     x0, [sp, #96]
        cmp     w20, #0x8
        b.ne    L909c
        add     x1, x19, #0x10, lsl #12
        mov     x0, x26
        add     x1, x1, #0xc80
        mov     x2, #0x40
        mov     x3, x24
        mov     x6, #0x0
        mov     x5, #0x0
        mov     x4, #0x400
        bl      L85e8
        ldr     x0, [sp, #112]
        mov     x1, x26
        mov     x2, #0x40
        bl      L8410
        tst     w0, #0xff
        b.eq    L9188
L9184:
        mov     w25, #0xfffffffa
L9188:
        mov     x0, x22
        mov     x1, #0x400
        bl      L8464
        mov     x0, x21
        mov     x1, #0x400
        bl      L8464
        mov     x0, x19
        mov     x1, #0xe000
        bl      L8464
        mov     x0, x28
        mov     x1, #0x400
        bl      L8464
        mov     x0, x27
        mov     x1, #0x1c00
        bl      L8464
        mov     x0, x26
        mov     x1, #0x40
        bl      L8464
        ldr     x0, [sp, #112]
        mov     x1, #0x40
        bl      L8464
        add     x0, x19, #0x10, lsl #12
        mov     x1, #0x40
        add     x0, x0, #0xc80
        bl      L8464
        mov     x0, x24
        mov     x1, #0x400
        bl      L8464
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x10, lsl #12
        add     x2, x2, #0x30
        ldr     x3, [x2, #3384]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.eq    L9238
        bl      L0e50
L9220:
        ldp     q0, q1, [x25]
        add     x0, x26, #0x80
        stp     q0, q1, [x0]
        ldp     q0, q1, [x25, #32]
        stp     q0, q1, [x0, #32]
        b       L906c
L9238:
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
L9260:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L8f54

// mldsa87_prepare_domain_separation_prefix (0x138 bytes)
L9278:
        cmp     x4, #0xff
        b.hi    L93a0
        stp     x19, x20, [sp, #-48]!
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        mov     w22, w5
        stp     x23, x30, [sp, #32]
        mov     x23, x1
        mov     x1, x3
        cbz     w5, L9364
        mov     x20, x2
        sub     w2, w5, #0x1
        cmp     w2, #0xb
        b.hi    L93a8
        .inst   0xb0000000  // adrp x0, 0xa000
        add     x0, x0, #0xb0
        ldrb    w0, [x0, w2, uxtw]
        .inst   0x10000062  // adr     x2, 92cc <mldsa87_prepare_domain_separation_prefix+0x54>
        add     x0, x2, w0, sxtb #2
        br      x0
        cmp     x20, #0x1c
L92d0:
        b.ne    L93a8
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbz     x19, L92f0
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e30
L92f0:
        .inst   0xb0000000  // adrp x0, 0xa000
        add     x0, x0, #0xbc
        mov     x1, #0x0
L92fc:
        lsl     x2, x1, #4
        ldr     w3, [x2, x0]
        cmp     w22, w3
        b.ne    L9390
        add     x2, x2, #0x4
        add     x1, x19, #0x2
        add     x4, x0, x2
        add     x3, x21, x1
        ldr     x0, [x0, x2]
        str     x0, [x21, x1]
        ldur    w0, [x4, #7]
        stur    w0, [x3, #7]
L932c:
        add     x0, x19, #0xd
        mov     x2, x20
        mov     x1, x23
        add     x0, x21, x0
        add     x20, x20, #0xd
        bl      L0e30
        add     x0, x20, x19
        b       L9380
        cmp     x20, #0x20
        b       L92d0
        cmp     x20, #0x30
        b       L92d0
        cmp     x20, #0x40
        b       L92d0
L9364:
        strb    wzr, [x0]
        strb    w4, [x0, #1]
        cbz     x4, L937c
        mov     x2, x19
        add     x0, x21, #0x2
        bl      L0e30
L937c:
        add     x0, x19, #0x2
L9380:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L9390:
        add     x1, x1, #0x1
        cmp     x1, #0xc
        b.ne    L92fc
        b       L932c
L93a0:
        mov     x0, #0x0
        ret
L93a8:
        mov     x0, #0x0
        b       L9380

// mldsa87_signature (0x100 bytes)
L93b0:
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
        bl      L9278
        cbz     x0, L9488
        mov     x19, x0
        mov     x1, #0x20
        mov     x0, x22
        bl      L0e40
        cbnz    w0, L9490
        mov     x4, x19
        mov     x6, x25
        mov     x5, x22
        mov     x3, x20
        mov     x2, x24
        mov     x1, x23
        mov     x0, x21
        mov     w7, #0x0
        bl      L8a6c
        mov     w19, w0
        cbz     w0, L9450
L9444:
        mov     x0, x21
        mov     x1, #0x1213
        bl      L8464
L9450:
        mov     x0, x22
        mov     x1, #0x20
        bl      L8464
        mov     x0, x20
        mov     x1, #0x14c
        bl      L8464
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9498
        bl      L0e50
L9488:
        mov     w19, #0xfffffff7
        b       L9444
L9490:
        mov     w19, #0xfffffffd
        b       L9444
L9498:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #480
        ret

// mldsa87_verify (0xbc bytes)
L94b0:
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
        bl      L9278
        cbz     x0, L9550
        mov     x4, x0
        mov     x5, x20
        mov     x3, x19
        mov     x2, x23
        mov     x1, x22
        mov     x0, x21
        mov     w6, #0x0
        bl      L8f54
        mov     w20, w0
L9524:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L8464
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9558
        bl      L0e50
L9550:
        mov     w20, #0xfffffff7
        b       L9524
L9558:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa87_signature_pre_hash_internal (0xc8 bytes)
L956c:
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
        cbnz    w7, L95b4
L95a0:
        mov     w19, #0xfffffff7
L95a4:
        mov     x0, x21
        mov     x1, #0x1213
        bl      L8464
        b       L95f4
L95b4:
        mov     x19, x5
        mov     x0, x20
        mov     w5, w7
        bl      L9278
        mov     x2, x0
        cbz     x0, L95a0
        mov     x5, x19
        mov     x6, x22
        mov     x1, x20
        mov     x0, x21
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L8a6c
        mov     w19, w0
        cbnz    w0, L95a4
L95f4:
        mov     x0, x20
        mov     x1, #0x14c
        bl      L8464
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9620
        bl      L0e50
L9620:
        ldp     x21, x22, [sp, #16]
        mov     w0, w19
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret

// mldsa87_signature_pre_hash_shake256 (0xc0 bytes)
L9634:
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
        bl      L1174
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w7, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L956c
        mov     w20, w0
        mov     x1, #0x40
        mov     x0, x19
        bl      L8464
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L96dc
        bl      L0e50
L96dc:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret

// mldsa87_verify_pre_hash_internal (0xa8 bytes)
L96f4:
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
        cbnz    w5, L9758
L9728:
        mov     w20, #0xfffffff7
L972c:
        mov     x0, x19
        mov     x1, #0x14c
        bl      L8464
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L978c
        bl      L0e50
L9758:
        mov     x0, x19
        bl      L9278
        mov     x2, x0
        cbz     x0, L9728
        mov     x0, x20
        mov     x5, x21
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L8f54
        mov     w20, w0
        b       L972c
L978c:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret

// mldsa87_verify_pre_hash_shake256 (0xb0 bytes)
L979c:
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
        bl      L1174
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x2, #0x40
        mov     w6, #0xc
        mov     x1, x19
        mov     x0, x20
        bl      L96f4
        mov     x1, #0x40
        mov     w20, w0
        mov     x0, x19
        bl      L8464
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #136]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9838
        bl      L0e50
L9838:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret

// mldsa87_pk_from_sk (0x20c bytes)
L984c:
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
        bl      L81c4
        mov     w1, #0x3
        mov     x0, x19
        bl      L8034
        mov     w20, w0
        mov     x2, x28
        mov     w1, #0x3
        mov     x0, x23
        bl      L8114
        str     w0, [sp, #104]
        mov     x0, x19
        bl      L7fa8
        ldp     q0, q1, [x22]
        mov     x3, x23
        mov     x4, x26
        mov     x2, x19
        mov     x1, x24
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L8480
        mov     x6, #0x2d00
        mov     w22, w0
        add     x23, x19, x6
        cbnz    w0, L99ac
        add     x1, x25, #0x620
        mov     x0, x24
        mov     x2, #0xd00
        bl      L8410
        and     w4, w0, #0xff
        mov     x3, #0xa20
        mov     x2, x21
        mov     x0, x23
        mov     x1, #0x40
        str     w4, [sp, #108]
        bl      L1174
        mov     x1, x23
        mov     x0, x27
        mov     x2, #0x40
        bl      L8410
        ldp     w1, w4, [sp, #104]
        and     w0, w0, #0xff
        orr     w20, w20, w1
        orr     w4, w4, w0
        orr     w20, w20, w4
        tst     w20, #0xff
        b.eq    L99b8
        mov     w22, #0xfffffff9
L99ac:
        mov     x0, x21
        mov     x1, #0xa20
        bl      L8464
L99b8:
        mov     x0, x24
        mov     x1, #0xd00
        bl      L8464
        mov     x0, x28
        mov     x1, #0x400
        bl      L8464
        mov     x0, x19
        mov     x1, #0x1c00
        bl      L8464
        mov     x1, #0x20
        mov     x0, #0x2d80
        add     x0, x19, x0
        bl      L8464
        mov     x0, x23
        mov     x1, #0x40
        bl      L8464
        mov     x0, x27
        mov     x1, #0x40
        bl      L8464
        mov     x0, x26
        mov     x1, #0x20
        bl      L8464
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #11848]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L9a30
        bl      L0e50
L9a30:
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

// Padding (0x9a58 to 0x9a58)


// The read-only data (0x9a58 to 0xa17c)

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
