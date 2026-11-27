// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mldsa-native's libmldsa.so (gcc 12, -O2, reduced RAM)
//
// This is a transcription of the binary
// binaries/aarch64/reduced-ram/multilevel/gcc12/O2/libmldsa.so from the
// binary branch of mldsa-native (see README.md), as loaded at an address
// that is a multiple of 4096: the start of its first segment, from address
// 0 up to the end of the read-only data. The ELF header and dynamic linking
// information at the start are given as data, as are the padding and the
// read-only data at the end, while the procedure linkage table and the code
// are given as instructions. The ADRP instructions, which compute addresses
// of pages relative to that of the instruction, are given as words. The
// labels are named after the addresses in the binary.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_native_libmldsa_gcc12_O2_reduced_ram)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_native_libmldsa_gcc12_O2_reduced_ram)
        .text
        .balign 4

S2N_BN_SYMBOL(mldsa_native_libmldsa_gcc12_O2_reduced_ram):

// ELF header and dynamic linking information (0x0 to 0xe20)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x000000000002efb0
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000000000c820
        .quad   0x000000000000c820
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
        .quad   0x0000001000000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00000010000000e9
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000054
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000013
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000024
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00080012000001ae
        .quad   0x00000000000062a0
        .quad   0x00000000000002a0
        .quad   0x00080012000001f2
        .quad   0x0000000000006ad0
        .quad   0x00000000000000a8
        .quad   0x00080012000000f0
        .quad   0x00000000000048d0
        .quad   0x000000000000010c
        .quad   0x000800120000007b
        .quad   0x00000000000041e0
        .quad   0x00000000000000a8
        .quad   0x00080012000003f1
        .quad   0x0000000000009e40
        .quad   0x00000000000000d0
        .quad   0x0008001200000060
        .quad   0x0000000000003ce0
        .quad   0x00000000000004f8
        .quad   0x000800120000037a
        .quad   0x0000000000009620
        .quad   0x0000000000000490
        .quad   0x0008001200000439
        .quad   0x0000000000009fd0
        .quad   0x00000000000000bc
        .quad   0x0008001200000347
        .quad   0x0000000000009070
        .quad   0x00000000000004f8
        .quad   0x000800120000020a
        .quad   0x0000000000006b80
        .quad   0x00000000000004b4
        .quad   0x00080012000002a5
        .quad   0x0000000000007490
        .quad   0x00000000000000bc
        .quad   0x000800120000031e
        .quad   0x0000000000008cc0
        .quad   0x000000000000031c
        .quad   0x00080012000002ea
        .quad   0x0000000000007610
        .quad   0x00000000000000ac
        .quad   0x0008001200000272
        .quad   0x0000000000007300
        .quad   0x00000000000000bc
        .quad   0x0008001200000044
        .quad   0x0000000000003c50
        .quad   0x0000000000000088
        .quad   0x0008001200000111
        .quad   0x0000000000004aa0
        .quad   0x00000000000000d0
        .quad   0x0008001200000415
        .quad   0x0000000000009f10
        .quad   0x00000000000000bc
        .quad   0x0008001200000392
        .quad   0x0000000000009ab0
        .quad   0x0000000000000018
        .quad   0x00080012000000ab
        .quad   0x0000000000004710
        .quad   0x0000000000000018
        .quad   0x0008001200000102
        .quad   0x00000000000049e0
        .quad   0x00000000000000bc
        .quad   0x00080012000001d7
        .quad   0x00000000000065d0
        .quad   0x00000000000004f8
        .quad   0x0008001200000159
        .quad   0x0000000000004c30
        .quad   0x00000000000000bc
        .quad   0x00080012000003e2
        .quad   0x0000000000009d80
        .quad   0x00000000000000bc
        .quad   0x00080012000003d0
        .quad   0x0000000000009c70
        .quad   0x000000000000010c
        .quad   0x000800120000047b
        .quad   0x000000000000a140
        .quad   0x0000000000000320
        .quad   0x000800120000019b
        .quad   0x0000000000004da0
        .quad   0x0000000000000320
        .quad   0x00080012000000c0
        .quad   0x0000000000004730
        .quad   0x000000000000019c
        .quad   0x0008001200000260
        .quad   0x00000000000071f0
        .quad   0x000000000000010c
        .quad   0x0008001200000237
        .quad   0x0000000000007050
        .quad   0x000000000000019c
        .quad   0x000800120000002b
        .quad   0x0000000000003a00
        .quad   0x0000000000000248
        .quad   0x00080012000003a7
        .quad   0x0000000000009ad0
        .quad   0x000000000000019c
        .quad   0x0008001200000135
        .quad   0x0000000000004b70
        .quad   0x00000000000000bc
        .quad   0x0008001200000337
        .quad   0x0000000000008fe0
        .quad   0x0000000000000088
        .quad   0x000800120000045a
        .quad   0x000000000000a090
        .quad   0x00000000000000ac
        .quad   0x0008001200000222
        .quad   0x0000000000007034
        .quad   0x0000000000000018
        .quad   0x00080012000002c9
        .quad   0x0000000000007550
        .quad   0x00000000000000bc
        .quad   0x00080012000001c7
        .quad   0x0000000000006540
        .quad   0x0000000000000088
        .quad   0x0008001200000281
        .quad   0x00000000000073c0
        .quad   0x00000000000000d0
        .quad   0x000800120000030b
        .quad   0x00000000000076c0
        .quad   0x0000000000000328
        .quad   0x0008001200000362
        .quad   0x0000000000009570
        .quad   0x00000000000000a8
        .quad   0x0008001200000093
        .quad   0x0000000000004290
        .quad   0x0000000000000478
        .quad   0x000800120000017a
        .quad   0x0000000000004cf0
        .quad   0x00000000000000ac
        .quad   0x6b636174735f5f00
        .quad   0x6175675f6b68635f
        .quad   0x6174735f5f006472
        .quad   0x665f6b68635f6b63
        .quad   0x736d656d006c6961
        .quad   0x6173646c6d007465
        .quad   0x617079656b5f3434
        .quad   0x7265746e695f7269
        .quad   0x73646c6d006c616e
        .quad   0x7079656b5f343461
        .quad   0x646e617200726961
        .quad   0x0073657479626d6f
        .quad   0x5f34346173646c6d
        .quad   0x727574616e676973
        .quad   0x6e7265746e695f65
        .quad   0x6173646c6d006c61
        .quad   0x616e6769735f3434
        .quad   0x7478655f65727574
        .quad   0x6173646c6d00756d
        .quad   0x66697265765f3434
        .quad   0x6e7265746e695f79
        .quad   0x6173646c6d006c61
        .quad   0x66697265765f3434
        .quad   0x00756d7478655f79
        .quad   0x5f34346173646c6d
        .quad   0x5f65726170657270
        .quad   0x735f6e69616d6f64
        .quad   0x6f69746172617065
        .quad   0x7869666572705f6e
        .quad   0x007970636d656d00
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

// The procedure linkage table and the code (0xe20 to 0xa460)
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

// mldsa_shake128_init (0x28 bytes)
L0e80:
        movi    v0.4s, #0x0
        str     xzr, [x0, #192]
        str     wzr, [x0, #200]
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        ret
        nop
        nop

// mldsa_shake128_absorb (0x90 bytes)
L0eb0:
        stp     x19, x20, [sp, #-64]!
        mov     x19, x2
        mov     w3, #0xa8
        ldr     w2, [x0, #200]
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        sub     w21, w3, w2
        str     x30, [sp, #32]
        sub     w3, w3, w2
        cmp     x21, x19
        b.hi    L0f10
L0ee0:
        mov     x1, x20
        mov     x0, x22
        bl      L15a0
        sub     x19, x19, x21
        mov     x0, x22
        add     x20, x20, x21
        bl      L16e0
        mov     x21, #0xa8
        mov     w2, #0x0
        mov     w3, #0xa8
        cmp     x19, #0xa7
        b.hi    L0ee0
L0f10:
        mov     x1, x20
        mov     w3, w19
        mov     x0, x22
        str     w2, [sp, #60]
        bl      L15a0
        ldr     w2, [sp, #60]
        ldr     x30, [sp, #32]
        add     w2, w2, w19
        str     w2, [x22, #200]
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        ret

// mldsa_shake128_finalize (0x80 bytes)
L0f40:
        stp     x19, x30, [sp, #-32]!
        mov     w5, #0x1f
        mov     w6, #0xffffff80
        .inst   0xf00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x19, x0
        ldr     w2, [x0, #200]
        add     x1, sp, #0x17
        ldr     x7, [x4]
        str     x7, [sp, #24]
        mov     x7, #0x0
        mov     w3, #0x1
        strb    w6, [sp, #22]
        strb    w5, [sp, #23]
        bl      L15a0
        mov     x0, x19
        add     x1, sp, #0x16
        mov     w2, #0xa7
        mov     w3, #0x1
        bl      L15a0
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     w1, #0xa8
        str     w1, [x19, #200]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L0fbc
        ldp     x19, x30, [sp], #32
        ret
L0fbc:
        bl      L0e60

// mldsa_shake128_squeeze (0xb0 bytes)
L0fc0:
        stp     x19, x20, [sp, #-64]!
        stp     x21, x22, [sp, #16]
        ldr     w21, [x2, #200]
        stp     x23, x24, [sp, #32]
        mov     x23, x2
        str     x30, [sp, #56]
        cbz     x1, L1058
        mov     x19, x1
        mov     x22, #0x0
        mov     w24, #0xa8
        str     x25, [sp, #48]
        mov     x25, x0
        b       L1034
L0ff4:
        sub     w3, w24, w21
        sub     w20, w24, w21
        mov     w4, w21
L1000:
        add     x1, x25, x22
        mov     w2, w4
        mov     x0, x23
        mov     w21, #0xa8
        cmp     x20, x19
        b.ls    L1024
        add     w21, w4, w19
        mov     w3, w19
        mov     x20, x19
L1024:
        bl      L1570
        add     x22, x22, x20
        subs    x19, x19, x20
        b.eq    L1054
L1034:
        cmp     w21, #0xa8
        b.ne    L0ff4
        mov     x0, x23
        bl      L16e0
        mov     w3, w21
        mov     x20, #0xa8
        mov     w4, #0x0
        b       L1000
L1054:
        ldr     x25, [sp, #48]
L1058:
        ldr     x30, [sp, #56]
        str     w21, [x23, #200]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret

// mldsa_shake128_release (0x24 bytes)
L1070:
        movi    v0.4s, #0x0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        str     q0, [x0, #192]
        ret

// mldsa_shake256_init (0x28 bytes)
L1094:
        movi    v0.4s, #0x0
        str     xzr, [x0, #192]
        str     wzr, [x0, #200]
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        ret
        nop

// mldsa_shake256_absorb (0x90 bytes)
L10c0:
        stp     x19, x20, [sp, #-64]!
        mov     x19, x2
        mov     w3, #0x88
        ldr     w2, [x0, #200]
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        sub     w21, w3, w2
        str     x30, [sp, #32]
        sub     w3, w3, w2
        cmp     x21, x19
        b.hi    L1120
L10f0:
        mov     x1, x20
        mov     x0, x22
        bl      L15a0
        sub     x19, x19, x21
        mov     x0, x22
        add     x20, x20, x21
        bl      L16e0
        mov     x21, #0x88
        mov     w2, #0x0
        mov     w3, #0x88
        cmp     x19, #0x87
        b.hi    L10f0
L1120:
        mov     x1, x20
        mov     w3, w19
        mov     x0, x22
        str     w2, [sp, #60]
        bl      L15a0
        ldr     w2, [sp, #60]
        ldr     x30, [sp, #32]
        add     w2, w2, w19
        str     w2, [x22, #200]
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        ret

// mldsa_shake256_finalize (0x80 bytes)
L1150:
        stp     x19, x30, [sp, #-32]!
        mov     w5, #0x1f
        mov     w6, #0xffffff80
        .inst   0xd00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x19, x0
        ldr     w2, [x0, #200]
        add     x1, sp, #0x17
        ldr     x7, [x4]
        str     x7, [sp, #24]
        mov     x7, #0x0
        mov     w3, #0x1
        strb    w6, [sp, #22]
        strb    w5, [sp, #23]
        bl      L15a0
        mov     x0, x19
        add     x1, sp, #0x16
        mov     w2, #0x87
        mov     w3, #0x1
        bl      L15a0
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     w1, #0x88
        str     w1, [x19, #200]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L11cc
        ldp     x19, x30, [sp], #32
        ret
L11cc:
        bl      L0e60

// mldsa_shake256_squeeze (0xb0 bytes)
L11d0:
        stp     x19, x20, [sp, #-64]!
        stp     x21, x22, [sp, #16]
        ldr     w21, [x2, #200]
        stp     x23, x24, [sp, #32]
        mov     x23, x2
        str     x30, [sp, #56]
        cbz     x1, L1268
        mov     x19, x1
        mov     x22, #0x0
        mov     w24, #0x88
        str     x25, [sp, #48]
        mov     x25, x0
        b       L1244
L1204:
        sub     w3, w24, w21
        sub     w20, w24, w21
        mov     w4, w21
L1210:
        add     x1, x25, x22
        mov     w2, w4
        mov     x0, x23
        mov     w21, #0x88
        cmp     x20, x19
        b.ls    L1234
        add     w21, w4, w19
        mov     w3, w19
        mov     x20, x19
L1234:
        bl      L1570
        add     x22, x22, x20
        subs    x19, x19, x20
        b.eq    L1264
L1244:
        cmp     w21, #0x88
        b.ne    L1204
        mov     x0, x23
        bl      L16e0
        mov     w3, w21
        mov     x20, #0x88
        mov     w4, #0x0
        b       L1210
L1264:
        ldr     x25, [sp, #48]
L1268:
        ldr     x30, [sp, #56]
        str     w21, [x23, #200]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret

// mldsa_shake256_release (0x24 bytes)
L1280:
        movi    v0.4s, #0x0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        str     q0, [x0, #192]
        ret

// mldsa_shake256 (0x9c bytes)
L12a4:
        stp     x19, x20, [sp, #-272]!
        mov     x20, x0
        .inst   0xd00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x38
        stp     x23, x30, [sp, #32]
        mov     x21, x1
        mov     x23, x3
        ldr     x0, [x4]
        str     x0, [sp, #264]
        mov     x0, #0x0
        mov     x22, x2
        mov     x0, x19
        bl      L1094
        mov     x2, x23
        mov     x1, x22
        mov     x0, x19
        bl      L10c0
        mov     x0, x19
        bl      L1150
        mov     x2, x19
        mov     x1, x21
        mov     x0, x20
        bl      L11d0
        mov     x0, x19
        bl      L1280
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #264]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L133c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #272
        ret
L133c:
        bl      L0e60

// mldsa_shake256x4_absorb_once (0x17c bytes)
L1340:
        stp     x19, x20, [sp, #-80]!
        mov     x20, x1
        mov     x19, x5
        .inst   0xd00000e6  // adrp x6, 0x1f000
        ldr     x6, [x6, #4088]
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        stp     x23, x24, [sp, #32]
        mov     x22, x3
        mov     x23, x4
        stp     x25, x30, [sp, #48]
        mov     x24, x0
        mov     x2, #0x320
        ldr     x1, [x6]
        str     x1, [sp, #72]
        mov     x1, #0x0
        bl      L0e70
        mov     w0, #0x1f
        strb    w0, [sp, #71]
        cmp     x19, #0x87
        b.ls    L13dc
        nop
L1398:
        mov     x4, x23
        mov     x3, x22
        mov     x2, x21
        mov     x1, x20
        mov     w6, #0x88
        mov     w5, #0x0
        mov     x0, x24
        bl      L1660
        mov     x0, x24
        sub     x19, x19, #0x88
        bl      L1cb0
        add     x23, x23, #0x88
        add     x22, x22, #0x88
        add     x21, x21, #0x88
        add     x20, x20, #0x88
        cmp     x19, #0x87
        b.hi    L1398
L13dc:
        mov     w25, w19
        cbnz    x19, L1460
L13e4:
        add     x19, sp, #0x47
        mov     w5, w25
        mov     x4, x19
        mov     x3, x19
        mov     x2, x19
        mov     x1, x19
        mov     x0, x24
        mov     w6, #0x1
        bl      L1660
        mov     w7, #0xffffff80
        mov     x0, x24
        mov     x4, x19
        mov     x3, x19
        mov     x2, x19
        mov     x1, x19
        mov     w6, #0x1
        mov     w5, #0x87
        strb    w7, [sp, #71]
        bl      L1660
L1430:
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #72]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L14b8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #80
        ret
L1460:
        mov     x4, x23
        mov     x3, x22
        mov     x2, x21
        mov     x1, x20
        mov     w6, w19
        mov     x0, x24
        mov     w5, #0x0
        bl      L1660
        cmp     x19, #0x87
        b.ne    L13e4
        ldrb    w7, [sp, #71]
        add     x4, sp, #0x47
        mov     w5, w19
        mov     x0, x24
        orr     w7, w7, #0xffffff80
        mov     x3, x4
        mov     x2, x4
        mov     x1, x4
        mov     w6, #0x1
        strb    w7, [sp, #71]
        bl      L1660
        b       L1430
L14b8:
        bl      L0e60
        nop

// mldsa_shake256x4_squeezeblocks (0x88 bytes)
L14c0:
        cbz     x4, L1544
        stp     x19, x20, [sp, #-64]!
        mov     x20, x2
        mov     x19, x3
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        mov     x21, x1
        stp     x23, x24, [sp, #32]
        mov     x23, x4
        mov     x24, x5
        str     x30, [sp, #48]
        nop
L14f0:
        mov     x0, x24
        bl      L1cb0
        mov     x4, x19
        mov     x3, x20
        mov     x2, x21
        mov     x1, x22
        mov     x0, x24
        mov     w6, #0x88
        mov     w5, #0x0
        bl      L15e0
        add     x19, x19, #0x88
        add     x20, x20, #0x88
        add     x21, x21, #0x88
        add     x22, x22, #0x88
        subs    x23, x23, #0x1
        b.ne    L14f0
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L1544:
        ret
        nop
        nop

// mldsa_shake256x4_init (0x4 bytes)
L1550:
        ret

// mldsa_shake256x4_release (0x1c bytes)
L1554:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0x320
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e70
        ldp     x19, x30, [sp], #16
        ret

// mldsa_keccakf1600_extract_bytes (0x30 bytes)
L1570:
        mov     w2, w2
        cbz     w3, L159c
        mov     w3, w3
        add     x4, x0, x2
        mov     x0, #0x0
        nop
L1588:
        ldrb    w2, [x4, x0]
        strb    w2, [x1, x0]
        add     x0, x0, #0x1
        cmp     x3, x0
        b.ne    L1588
L159c:
        ret

// mldsa_keccakf1600_xor_bytes (0x38 bytes)
L15a0:
        mov     w2, w2
        cbz     w3, L15d4
        mov     w5, w3
        add     x3, x0, x2
        mov     x0, #0x0
        nop
L15b8:
        ldrb    w2, [x3, x0]
        ldrb    w4, [x1, x0]
        eor     w2, w2, w4
        strb    w2, [x3, x0]
        add     x0, x0, #0x1
        cmp     x5, x0
        b.ne    L15b8
L15d4:
        ret
        nop
        nop

// mldsa_keccakf1600x4_extract_bytes (0x80 bytes)
L15e0:
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
L1660:
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
        bl      L15a0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L15a0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L15a0
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L15a0

// mldsa_keccakf1600_permute (0x5d0 bytes)
L16e0:
        stp     x19, x20, [sp, #-192]!
        .inst   0xb0000041  // adrp x1, 0xa000
        add     x1, x1, #0x460
        ldp     x9, x4, [x0, #56]
        str     x1, [sp, #96]
        add     x1, x1, #0xc0
        str     x1, [sp, #176]
        ldr     x1, [x0]
        str     x1, [sp, #104]
        ldr     x1, [x0, #16]
        str     x4, [sp, #112]
        ldr     x4, [x0, #112]
        stp     x21, x22, [sp, #16]
        mov     x18, x9
        ldr     x2, [x0, #8]
        stp     x23, x24, [sp, #32]
        ldr     x3, [x0, #40]
        stp     x25, x26, [sp, #48]
        ldp     x26, x23, [x0, #24]
        stp     x27, x28, [sp, #64]
        ldp     x7, x21, [x0, #72]
        str     x4, [sp, #120]
        ldp     x20, x16, [x0, #88]
        str     x1, [sp, #136]
        ldr     x1, [x0, #48]
        mov     x28, x23
        ldr     x11, [x0, #104]
        str     x30, [sp, #80]
        ldp     x22, x12, [x0, #120]
        mov     x14, x20
        ldp     x4, x25, [x0, #184]
        mov     x23, x21
        ldp     x6, x5, [x0, #136]
        mov     x20, x2
        ldp     x13, x10, [x0, #152]
        mov     x30, x22
        ldp     x19, x15, [x0, #168]
        mov     x9, x25
        mov     x27, x11
        mov     x22, x7
        mov     x17, x12
        mov     x25, x3
        str     x26, [sp, #128]
        str     x0, [sp, #184]
L1790:
        ldp     x11, x24, [sp, #128]
        eor     x12, x16, x6
        ldp     x0, x21, [sp, #104]
        eor     x2, x23, x30
        eor     x26, x14, x17
        eor     x7, x24, x18
        eor     x7, x7, x12
        ldr     x12, [sp, #120]
        eor     x3, x0, x25
        eor     x8, x11, x21
        eor     x11, x27, x5
        eor     x0, x20, x1
        eor     x3, x3, x2
        eor     x8, x8, x11
        eor     x7, x7, x15
        eor     x3, x3, x10
        eor     x8, x8, x4
        eor     x26, x26, x0
        eor     x2, x28, x22
        eor     x0, x12, x13
        eor     x26, x26, x19
        eor     x2, x2, x0
        eor     x0, x3, x7, ror #63
        eor     x3, x8, x3, ror #63
        eor     x8, x26, x8, ror #63
        eor     x2, x2, x9
        eor     x1, x0, x1
        eor     x21, x0, x20
        eor     x17, x0, x17
        eor     x20, x8, x18
        eor     x14, x0, x14
        eor     x0, x0, x19
        eor     x26, x2, x26, ror #63
        ldp     x18, x19, [sp, #112]
        eor     x2, x7, x2, ror #63
        ldr     x7, [sp, #96]
        eor     x12, x8, x6
        ldr     x6, [sp, #128]
        eor     x16, x8, x16
        eor     x15, x8, x15
        eor     x9, x3, x9
        eor     x8, x8, x24
        eor     x5, x2, x5
        ldr     x7, [x7]
        ror     x9, x9, #50
        eor     x11, x3, x13
        ror     x5, x5, #43
        eor     x13, x2, x27
        eor     x4, x2, x4
        eor     x6, x2, x6
        eor     x2, x2, x18
        ror     x18, x1, #20
        ror     x1, x8, #2
        ldr     x8, [sp, #104]
        str     x18, [sp, #104]
        eor     x22, x3, x22
        ror     x16, x16, #21
        stp     x7, x1, [sp, #136]
        eor     x7, x3, x28
        eor     x3, x3, x19
        bic     x19, x9, x5
        eor     x24, x26, x23
        eor     x1, x26, x30
        bic     x30, x16, x18
        bic     x18, x5, x16
        eor     x16, x19, x16
        ldr     x19, [sp, #104]
        ror     x17, x17, #19
        eor     x23, x26, x25
        ror     x24, x24, #61
        ldr     x25, [sp, #136]
        eor     x10, x26, x10
        eor     x8, x26, x8
        eor     x19, x18, x19
        ror     x22, x22, #44
        bic     x18, x17, x24
        ror     x6, x6, #36
        ror     x15, x15, #3
        ror     x20, x20, #58
        ror     x13, x13, #39
        ror     x11, x11, #56
        bic     x27, x24, x22
        ror     x10, x10, #46
        eor     x18, x18, x22
        bic     x22, x22, x6
        str     x16, [sp, #112]
        bic     x16, x8, x9
        eor     x27, x27, x6
        bic     x26, x13, x20
        eor     x16, x16, x5
        ror     x21, x21, #63
        bic     x5, x15, x17
        eor     x28, x8, x25
        bic     x6, x6, x15
        eor     x22, x22, x15
        bic     x15, x10, x11
        ror     x14, x14, #54
        eor     x28, x30, x28
        ror     x23, x23, #28
        eor     x30, x26, x21
        eor     x15, x15, x13
        eor     x26, x5, x24
        eor     x5, x6, x17
        bic     x6, x11, x13
        bic     x13, x20, x21
        bic     x21, x21, x10
        ror     x4, x4, #8
        bic     x25, x14, x23
        ror     x7, x7, #37
        eor     x11, x21, x11
        ror     x12, x12, #49
        eor     x25, x25, x7
        stp     x5, x11, [sp, #120]
        bic     x11, x23, x7
        bic     x7, x7, x4
        eor     x10, x13, x10
        bic     x5, x4, x12
        bic     x13, x12, x14
        eor     x7, x7, x12
        ror     x3, x3, #25
        ldr     x12, [sp, #104]
        ror     x1, x1, #23
        ldr     x21, [sp, #144]
        ror     x0, x0, #62
        str     x10, [sp, #136]
        ror     x2, x2, #9
        bic     x24, x1, x3
        eor     x5, x5, x14
        bic     x8, x12, x8
        bic     x14, x0, x1
        ldr     x12, [sp, #112]
        eor     x24, x24, x2
        bic     x17, x2, x21
        eor     x14, x14, x3
        bic     x10, x3, x2
        eor     x13, x13, x23
        ldp     x3, x2, [sp, #128]
        eor     x23, x15, x5
        eor     x12, x12, x26
        eor     x8, x8, x9
        eor     x9, x12, x23
        eor     x6, x6, x20
        ldr     x23, [sp, #120]
        eor     x20, x28, x27
        eor     x17, x17, x0
        eor     x11, x11, x4
        eor     x4, x30, x25
        eor     x9, x9, x14
        eor     x12, x16, x23
        eor     x20, x20, x4
        eor     x23, x22, x2
        eor     x10, x10, x21
        eor     x4, x6, x13
        eor     x2, x11, x17
        bic     x0, x21, x0
        eor     x3, x3, x7
        eor     x21, x19, x18
        eor     x0, x0, x1
        eor     x4, x21, x4
        eor     x1, x20, x10
        eor     x3, x12, x3
        eor     x2, x23, x2
        eor     x12, x1, x9, ror #63
        eor     x4, x4, x24
        eor     x3, x3, x0
        eor     x2, x2, x8
        eor     x21, x19, x12
        eor     x18, x18, x12
        eor     x13, x13, x12
        eor     x6, x6, x12
        eor     x24, x24, x12
        eor     x1, x3, x1, ror #63
        ldr     x12, [sp, #112]
        eor     x3, x4, x3, ror #63
        eor     x4, x2, x4, ror #63
        eor     x2, x9, x2, ror #63
        ldr     x9, [sp, #96]
        eor     x19, x26, x3
        eor     x15, x15, x3
        eor     x14, x14, x3
        eor     x5, x5, x3
        eor     x3, x12, x3
        ldr     x12, [sp, #136]
        eor     x23, x16, x2
        ldr     x20, [x9, #8]
        eor     x22, x22, x1
        ldr     x16, [sp, #128]
        eor     x17, x17, x1
        eor     x11, x11, x1
        eor     x8, x8, x1
        str     x20, [sp, #104]
        eor     x20, x12, x1
        eor     x1, x25, x4
        eor     x7, x7, x2
        ldr     x25, [sp, #120]
        eor     x0, x0, x2
        eor     x16, x16, x2
        ror     x26, x20, #25
        eor     x2, x25, x2
        ror     x20, x1, #23
        ldr     x25, [sp, #104]
        ror     x1, x2, #9
        ror     x18, x18, #20
        ror     x17, x17, #50
        ror     x7, x7, #43
        eor     x9, x30, x4
        ror     x15, x15, #21
        eor     x12, x27, x4
        eor     x10, x10, x4
        eor     x4, x28, x4
        stp     x1, x20, [sp, #144]
        bic     x30, x15, x18
        ldr     x1, [sp, #96]
        eor     x20, x4, x25
        bic     x25, x17, x7
        str     x25, [sp, #112]
        ror     x14, x14, #3
        bic     x28, x7, x15
        ror     x23, x23, #36
        bic     x27, x18, x4
        eor     x30, x30, x20
        ror     x22, x22, #44
        ror     x9, x9, #61
        bic     x4, x4, x17
        ror     x13, x13, #19
        eor     x20, x28, x18
        add     x1, x1, #0x10
        eor     x28, x27, x17
        stp     x1, x30, [sp, #96]
        bic     x30, x23, x14
        ldr     x17, [sp, #112]
        str     x30, [sp, #120]
        ror     x11, x11, #56
        bic     x2, x22, x23
        ror     x16, x16, #39
        eor     x4, x4, x7
        bic     x1, x13, x9
        ror     x19, x19, #58
        ror     x10, x10, #46
        ror     x0, x0, #8
        bic     x25, x9, x22
        ror     x5, x5, #49
        eor     x1, x1, x22
        eor     x22, x2, x14
        ldr     x2, [sp, #120]
        str     x4, [sp, #128]
        bic     x4, x11, x16
        bic     x18, x14, x13
        eor     x15, x17, x15
        eor     x14, x4, x19
        bic     x17, x10, x11
        bic     x4, x0, x5
        stp     x17, x4, [sp, #160]
        eor     x13, x2, x13
        ror     x21, x21, #63
        ldr     x2, [sp, #160]
        bic     x27, x16, x19
        ldr     x4, [sp, #144]
        eor     x16, x2, x16
        ldr     x2, [sp, #168]
        bic     x7, x19, x21
        ror     x8, x8, #37
        ror     x12, x12, #28
        eor     x18, x18, x9
        ror     x6, x6, #54
        eor     x9, x7, x10
        stp     x13, x9, [sp, #112]
        bic     x13, x12, x8
        ldr     x7, [sp, #152]
        bic     x17, x5, x6
        bic     x30, x6, x12
        eor     x25, x25, x23
        eor     x6, x2, x6
        eor     x23, x27, x21
        ldr     x2, [sp, #176]
        eor     x13, x13, x0
        str     x15, [sp, #136]
        bic     x15, x21, x10
        bic     x21, x8, x0
        ror     x24, x24, #62
        ldr     x0, [sp, #96]
        ror     x3, x3, #2
        eor     x27, x15, x11
        mov     x11, x4
        bic     x10, x26, x4
        bic     x19, x7, x26
        bic     x15, x24, x7
        bic     x4, x3, x24
        bic     x9, x11, x3
        eor     x30, x30, x8
        eor     x17, x17, x12
        eor     x5, x21, x5
        eor     x15, x15, x26
        eor     x10, x10, x3
        eor     x19, x19, x11
        eor     x4, x4, x7
        eor     x9, x9, x24
        cmp     x2, x0
        b.ne    L1790
        ldr     x0, [sp, #184]
        mov     x7, x25
        ldr     x2, [sp, #104]
        stp     x7, x1, [x0, #40]
        ldr     x1, [sp, #112]
        stp     x2, x20, [x0]
        ldr     x26, [sp, #128]
        str     x1, [x0, #64]
        ldr     x1, [sp, #120]
        stp     x26, x28, [x0, #24]
        ldr     x2, [sp, #136]
        str     x2, [x0, #16]
        str     x18, [x0, #56]
        stp     x22, x23, [x0, #72]
        stp     x14, x16, [x0, #88]
        str     x27, [x0, #104]
        str     x1, [x0, #112]
        stp     x30, x17, [x0, #120]
        stp     x6, x5, [x0, #136]
        stp     x13, x10, [x0, #152]
        stp     x19, x15, [x0, #168]
        stp     x4, x9, [x0, #184]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #192
        ret

// mldsa_keccakf1600x4_permute (0x28 bytes)
L1cb0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L16e0
        add     x0, x19, #0xc8
        bl      L16e0
        add     x0, x19, #0x190
        bl      L16e0
        add     x0, x19, #0x258
        ldp     x19, x30, [sp], #16
        b       L16e0
        nop
        nop

// mldsa44_unpack_pk_t1 (0x14 bytes)
L1ce0:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #6
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L24d0

// mldsa44_pack_sk_rho_key_tr (0x28 bytes)
L1cf4:
        ldp     q0, q1, [x1]
        add     x4, x0, #0x40
        stp     q0, q1, [x0]
        ldp     q0, q1, [x3]
        stp     q0, q1, [x0, #32]
        ldp     q0, q1, [x2]
        stp     q0, q1, [x4]
        ldp     q0, q1, [x2, #32]
        stp     q0, q1, [x4, #32]
        ret
        nop

// mldsa44_unpack_sk (0x40 bytes)
L1d20:
        ldp     q0, q1, [x6]
        add     x7, x6, #0x40
        add     x10, x6, #0x80
        add     x9, x6, #0x200
        add     x8, x6, #0x380
        stp     q0, q1, [x0]
        ldp     q0, q1, [x6, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x7]
        stp     q0, q1, [x1]
        ldp     q0, q1, [x7, #32]
        stp     q0, q1, [x1, #32]
        str     x10, [x4]
        str     x9, [x5]
        str     x8, [x3]
        ret

// mldsa44_pack_sig_c (0xc bytes)
L1d60:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ret
        nop

// mldsa44_pack_sig_h (0xf8 bytes)
L1d70:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-96]!
        mov     x20, x3
        stp     x25, x26, [sp, #48]
        add     x26, x0, #0x920
        mov     w25, #0x7400
        stp     x21, x22, [sp, #16]
        mov     w22, #0xe800
        mov     x21, x1
        stp     x23, x24, [sp, #32]
        add     x23, x0, #0x970
        add     x24, x2, #0x300
        stp     x27, x28, [sp, #64]
        mov     w27, #0x8c00
        mov     x28, x2
        str     x30, [sp, #80]
        mov     w19, #0x0
        movk    w25, #0x1, lsl #16
        movk    w22, #0x2, lsl #16
        movk    w27, #0xfffe, lsl #16
        str     wzr, [x26, #80]
        stp     q0, q0, [x26]
        stp     q0, q0, [x26, #32]
        str     q0, [x26, #64]
L1dd0:
        mov     x1, x28
        mov     x0, x20
        bl      L2894
        mov     x4, #0x0
        b       L1dfc
L1de4:
        cmp     w7, #0x0
        ccmp    w5, w27, #0x0, ne
        b.eq    L1e10
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.eq    L1e2c
L1dfc:
        ldr     w5, [x21, x4, lsl #2]
        ldr     w7, [x20, x4, lsl #2]
        add     w6, w5, w25
        cmp     w6, w22
        b.ls    L1de4
L1e10:
        cmp     w19, #0x50
        b.eq    L1e48
        strb    w4, [x26, w19, uxtw]
        add     x4, x4, #0x1
        add     w19, w19, #0x1
        cmp     x4, #0x100
        b.ne    L1dfc
L1e2c:
        add     x28, x28, #0xc0
        strb    w19, [x23], #1
        add     x21, x21, #0x400
        cmp     x28, x24
        b.ne    L1dd0
        mov     w0, #0x0
        b       L1e4c
L1e48:
        mov     w0, #0xffffffff
L1e4c:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
        nop
        nop

// mldsa44_pack_sig_z (0x14 bytes)
L1e70:
        add     w2, w2, w2, lsl #3
        lsl     w2, w2, #6
        add     x2, x2, #0x20
        add     x0, x0, x2
        b       L3084

// mldsa44_sig_unpack_hints (0x100 bytes)
L1e84:
        stp     x19, x20, [sp, #-48]!
        mov     x6, x0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        add     x22, x1, #0x920
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        mov     w23, w2
        cbz     w2, L1eb0
        add     w0, w2, #0x4f
        ldrb    w21, [x22, w0, uxtw]
L1eb0:
        add     w0, w23, #0x50
        ldrb    w20, [x22, w0, uxtw]
        cmp     w20, #0x50
        ccmp    w21, w20, #0x2, ls
        b.hi    L1f24
        mov     x0, x6
        mov     w1, #0x0
        mov     x2, #0x400
        bl      L0e70
        add     x3, x19, w21, uxtb
        mov     x6, x0
        mov     w1, w21
        mov     w7, #0x1
        cmp     w21, w20
        b.cs    L1f38
        nop
L1ef0:
        ldrb    w4, [x3, #2336]
        mov     w5, w1
        add     w1, w1, #0x1
        add     x3, x3, #0x1
        str     w7, [x6, x4, lsl #2]
        cmp     w20, w1
        b.ls    L1f38
        cmp     w21, w1
        b.cs    L1ef0
        ldrb    w0, [x22, w5, uxtw]
        ldrb    w4, [x3, #2336]
        cmp     w4, w0
        b.hi    L1ef0
L1f24:
        mov     w0, #0xffffffff
L1f28:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L1f38:
        cmp     w23, #0x3
        b.eq    L1f54
L1f40:
        mov     w0, #0x0
L1f44:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L1f54:
        cmp     w20, #0x50
        b.eq    L1f40
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbnz    w0, L1f24
L1f68:
        cmp     w20, #0x50
        b.eq    L1f44
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbz     w0, L1f68
        mov     w0, #0xffffffff
        b       L1f28
        nop
        nop
        nop

// mld_rej_uniform_c.constprop.0 (0x6c bytes)
L1f90:
        mov     x9, x0
        cmp     w1, #0xff
        b.hi    L1ff4
        mov     w8, #0x3
        sub     w8, w8, w2
        b       L1fb4
L1fa8:
        mov     w1, w0
L1fac:
        cmp     w3, w7
        b.cc    L1ff4
L1fb4:
        ldrb    w5, [x2, #2]
        add     x2, x2, #0x3
        ldurb   w4, [x2, #-2]
        add     w0, w1, #0x1
        ldurb   w6, [x2, #-3]
        add     w7, w8, w2
        lsl     w5, w5, #16
        orr     w4, w5, w4, lsl #8
        orr     w4, w4, w6
        and     w4, w4, #0x7fffff
        cmp     w4, #0x7fe, lsl #12
        b.hi    L1fac
        str     w4, [x9, w1, uxtw #2]
        cmp     w1, #0xff
        b.ne    L1fa8
        ret
L1ff4:
        mov     w0, w1
        ret
        nop

// mldsa_poly_reduce (0x30 bytes)
L2000:
        .inst   0x90000042  // adrp x2, 0xa000
        add     x1, x0, #0x400
        movi    v3.4s, #0x40, lsl #16
        ldr     q2, [x2, #1312]
L2010:
        ldr     q0, [x0]
        add     v1.4s, v0.4s, v3.4s
        sshr    v1.4s, v1.4s, #23
        mla     v0.4s, v1.4s, v2.4s
        str     q0, [x0], #16
        cmp     x1, x0
        b.ne    L2010
        ret

// mldsa_poly_caddq (0x3c bytes)
L2030:
        mov     w5, #0xe001
        add     x4, x0, #0x400
        movk    w5, #0x7f, lsl #16
        nop
L2040:
        ldr     w3, [x0]
        sxtw    x1, w3
        asr     x1, x1, #31
        add     w2, w3, w5
        eor     w2, w2, w3
        and     w1, w2, w1
        eor     w1, w1, w3
        str     w1, [x0], #4
        cmp     x0, x4
        b.ne    L2040
        ret
        nop

// mldsa_poly_add (0x28 bytes)
L2070:
        mov     x2, #0x0
        nop
L2078:
        ldr     q0, [x0, x2]
        ldr     q1, [x1, x2]
        add     v0.4s, v0.4s, v1.4s
        str     q0, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x400
        b.ne    L2078
        ret
        nop
        nop

// mldsa_poly_sub (0x28 bytes)
L20a0:
        mov     x2, #0x0
        nop
L20a8:
        ldr     q0, [x0, x2]
        ldr     q1, [x1, x2]
        sub     v0.4s, v0.4s, v1.4s
        str     q0, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x400
        b.ne    L20a8
        ret
        nop
        nop

// mldsa_poly_shiftl (0x20 bytes)
L20d0:
        add     x1, x0, #0x400
        nop
L20d8:
        ldr     q0, [x0]
        shl     v0.4s, v0.4s, #13
        str     q0, [x0], #16
        cmp     x0, x1
        b.ne    L20d8
        ret

// mldsa_poly_ntt (0xcc bytes)
L20f0:
        .inst   0x90000049  // adrp x9, 0xa000
        mov     w15, #0x2001
        mov     x6, x0
        add     x9, x9, #0x550
        mov     w3, #0x0
        mov     w8, #0x64f7
        mov     w13, #0x1
        mov     w16, #0x100
        movk    w15, #0x380, lsl #16
        mov     w14, #0xff801fff
L2118:
        add     w12, w3, #0x1
        mov     w0, #0x0
        lsl     w3, w13, w3
        lsr     w2, w16, w12
        lsl     w5, w2, #1
        nop
L2130:
        add     w3, w3, #0x1
        cmp     w0, w2
        b.cs    L2188
        mov     w4, w0
        neg     x1, x4, lsl #2
        add     x1, x1, w2, uxtw #2
        add     x1, x6, x1
        nop
L2150:
        ldr     w10, [x1, x4, lsl #2]
        ldr     w11, [x6, x4, lsl #2]
        smull   x10, w8, w10
        mul     w7, w10, w15
        smaddl  x7, w7, w14, x10
        asr     x7, x7, #32
        sub     w10, w11, w7
        str     w10, [x1, x4, lsl #2]
        ldr     w10, [x6, x4, lsl #2]
        add     w7, w10, w7
        str     w7, [x6, x4, lsl #2]
        add     x4, x4, #0x1
        cmp     w2, w4
        b.hi    L2150
L2188:
        add     w0, w0, w5
        add     w2, w2, w5
        cmp     w0, #0xff
        b.hi    L21a0
        ldr     w8, [x9, w3, uxtw #2]
        b       L2130
L21a0:
        cmp     w12, #0x8
        b.eq    L21b8
        lsl     w0, w13, w12
        mov     w3, w12
        ldr     w8, [x9, x0, lsl #2]
        b       L2118
L21b8:
        ret
        nop

// mldsa_poly_invntt_tomont (0x118 bytes)
L21c0:
        .inst   0x9000004a  // adrp x10, 0xa000
        mov     w14, #0x2001
        mov     x7, x0
        add     x10, x10, #0x550
        add     x11, x0, #0x4
        mov     w12, #0x8
        mov     w16, #0x100
        mov     w15, #0x1
        movk    w14, #0x380, lsl #16
        mov     w13, #0xff801fff
L21e8:
        lsr     w1, w16, w12
        mov     w2, #0x0
        lsl     w5, w15, w12
        lsl     w8, w1, #1
        sub     w5, w5, #0x1
        nop
L2200:
        mov     w0, w5
        sub     w5, w5, #0x1
        ldr     w3, [x10, w0, uxtw #2]
        neg     w6, w3
        cmp     w1, w2
        b.ls    L226c
        sub     w0, w1, w2
        mov     w4, w1
        sub     w0, w0, #0x1
        mov     w3, w2
        add     x0, x0, x4
        sub     x3, x3, x4
        add     x4, x7, w1, uxtw #2
        add     x0, x11, x0, lsl #2
L2238:
        ldr     w9, [x4, x3, lsl #2]
        ldr     w17, [x4]
        add     w17, w17, w9
        str     w17, [x4, x3, lsl #2]
        ldr     w17, [x4]
        sub     w9, w9, w17
        smull   x9, w9, w6
        mul     w17, w9, w14
        smaddl  x9, w17, w13, x9
        asr     x9, x9, #32
        str     w9, [x4], #4
        cmp     x4, x0
        b.ne    L2238
L226c:
        add     w2, w2, w8
        add     w1, w1, w8
        cmp     w2, #0xff
        b.ls    L2200
        subs    w12, w12, #0x1
        b.ne    L21e8
        .inst   0x90000042  // adrp x2, 0xa000
        .inst   0x90000041  // adrp x1, 0xa000
        mov     x0, x7
        ldr     q5, [x2, #1344]
        .inst   0x90000042  // adrp x2, 0xa000
        ldr     q4, [x1, #1328]
        add     x1, x7, #0x400
        ldr     q3, [x2, #1312]
        nop
L22a8:
        ldr     q0, [x0]
        smull   v1.2d, v0.2s, v4.2s
        smull2  v0.2d, v0.4s, v4.4s
        uzp1    v2.4s, v1.4s, v0.4s
        mul     v2.4s, v2.4s, v5.4s
        smlal   v1.2d, v2.2s, v3.2s
        smlal2  v0.2d, v2.4s, v3.4s
        uzp2    v1.4s, v1.4s, v0.4s
        str     q1, [x0], #16
        cmp     x1, x0
        b.ne    L22a8
        ret
        nop
        nop

// mldsa_poly_pointwise_montgomery (0x50 bytes)
L22e0:
        .inst   0x90000042  // adrp x2, 0xa000
        ldr     q4, [x2, #1344]
        .inst   0x90000042  // adrp x2, 0xa000
        ldr     q3, [x2, #1312]
        mov     x2, #0x0
        nop
L22f8:
        ldr     q2, [x0, x2]
        ldr     q0, [x1, x2]
        smull   v1.2d, v0.2s, v2.2s
        smull2  v0.2d, v0.4s, v2.4s
        uzp1    v2.4s, v1.4s, v0.4s
        mul     v2.4s, v2.4s, v4.4s
        smlal   v1.2d, v2.2s, v3.2s
        smlal2  v0.2d, v2.4s, v3.4s
        uzp2    v1.4s, v1.4s, v0.4s
        str     q1, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x400
        b.ne    L22f8
        ret

// mldsa_poly_power2round (0x3c bytes)
L2330:
        movi    v4.4s, #0xf, msl #8
        mov     x3, #0x0
        mvni    v3.4s, #0x1f, msl #8
        nop
L2340:
        ldr     q0, [x2, x3]
        add     v1.4s, v0.4s, v4.4s
        and     v2.16b, v1.16b, v3.16b
        sshr    v1.4s, v1.4s, #13
        sub     v0.4s, v0.4s, v2.4s
        str     q1, [x0, x3]
        str     q0, [x1, x3]
        add     x3, x3, #0x10
        cmp     x3, #0x400
        b.ne    L2340
        ret
        nop

// mldsa_poly_uniform (0x104 bytes)
L2370:
        sub     sp, sp, #0x470
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x20, [sp]
        mov     x19, x1
        add     x20, sp, #0x4f
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0x398
        mov     x22, x0
        str     x30, [sp, #32]
        and     x20, x20, #0xffffffffffffffe0
        ldr     x0, [x2]
        str     x0, [sp, #1128]
        mov     x0, #0x0
        mov     x0, x21
        bl      L0e80
        mov     x1, x19
        mov     x2, #0x22
        mov     x0, x21
        bl      L0eb0
        mov     x0, x21
        bl      L0f40
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x348
        bl      L0fc0
        mov     x2, x20
        mov     x0, x22
        mov     w3, #0x348
        mov     w1, #0x0
        bl      L1f90
        cmp     w0, #0xff
        b.hi    L2428
        mov     w19, w0
L23f8:
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0xa8
        bl      L0fc0
        mov     w1, w19
        mov     x2, x20
        mov     x0, x22
        mov     w3, #0xa8
        bl      L1f90
        mov     w19, w0
        cmp     w0, #0xff
        b.ls    L23f8
L2428:
        mov     x0, x21
        bl      L1070
        mov     x0, x20
        mov     x2, #0x348
        mov     w1, #0x0
        bl      L0e70
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1128]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2470
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x470
        ret
L2470:
        bl      L0e60

// mldsa_polyt1_pack (0x5c bytes)
L2474:
        add     x4, x0, #0x140
L2478:
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
        cmp     x0, x4
        b.ne    L2478
        ret

// mldsa_polyt1_unpack (0x74 bytes)
L24d0:
        add     x4, x1, #0x140
        nop
L24d8:
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
        b.ne    L24d8
        ret

// mldsa_polyt0_pack (0x128 bytes)
L2544:
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-64]!
        add     x10, x0, #0x1a0
        ldr     x3, [x2]
        str     x3, [sp, #56]
        mov     x3, #0x0
        mov     w3, #0x1000
        nop
L2568:
        ldp     w9, w6, [x1]
        add     x0, x0, #0xd
        ldp     w7, w4, [x1, #8]
        sub     w6, w3, w6
        sub     w9, w3, w9
        fmov    s0, w6
        ubfiz   w2, w6, #5, #3
        sub     w7, w3, w7
        ushr    v1.2s, v0.2s, #3
        orr     w2, w2, w9, lsr #8
        fmov    d0, x9
        ubfiz   w11, w7, #2, #6
        orr     w6, w11, w6, lsr #11
        sub     w4, w3, w4
        mov     v0.b[1], w2
        fmov    s2, w4
        ubfiz   w2, w4, #7, #1
        orr     w9, w2, w7, lsr #6
        ushr    v2.2s, v2.2s, #1
        ldp     w5, w8, [x1, #16]
        mov     v0.b[2], v1.b[0]
        sub     w5, w3, w5
        fmov    s1, w5
        sub     w8, w3, w8
        mov     v0.b[3], w6
        ubfiz   w7, w5, #4, #4
        orr     w4, w7, w4, lsr #9
        ushr    v1.2s, v1.2s, #4
        ldp     w2, w7, [x1, #24]
        ubfiz   w12, w8, #1, #7
        mov     v0.b[4], w9
        orr     w5, w12, w5, lsr #12
        sub     w2, w3, w2
        sub     w6, w3, w7
        sturb   w5, [x0, #-5]
        add     x1, x1, #0x20
        ubfiz   w11, w2, #6, #2
        ubfiz   w7, w6, #3, #5
        mov     v0.b[5], v2.b[0]
        orr     w7, w7, w2, lsr #10
        orr     w8, w11, w8, lsr #7
        lsr     w2, w2, #2
        lsr     w6, w6, #5
        sturb   w8, [x0, #-4]
        sturb   w2, [x0, #-3]
        mov     v0.b[6], w4
        sturb   w7, [x0, #-2]
        sturb   w6, [x0, #-1]
        mov     v0.b[7], v1.b[0]
        stur    d0, [x0, #-13]
        cmp     x0, x10
        b.ne    L2568
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        stp     xzr, xzr, [sp, #40]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #56]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2668
        ldr     x30, [sp], #64
        ret
L2668:
        bl      L0e60
        nop

// mldsa_polyt0_unpack (0x154 bytes)
L2670:
        add     x10, x1, #0x1a0
        mov     w9, #0x1000
L2678:
        ldrb    w3, [x1]
        add     x1, x1, #0xd
        str     w3, [x0]
        ldurb   w2, [x1, #-12]
        orr     w2, w3, w2, lsl #8
        and     w2, w2, #0x1fff
        str     w2, [x0]
        sub     w8, w9, w2
        ldurb   w2, [x1, #-12]
        lsr     w2, w2, #5
        str     w2, [x0, #4]
        ldurb   w3, [x1, #-11]
        orr     w3, w2, w3, lsl #3
        str     w3, [x0, #4]
        ldurb   w2, [x1, #-10]
        orr     w2, w3, w2, lsl #11
        and     w2, w2, #0x1fff
        str     w2, [x0, #4]
        sub     w7, w9, w2
        ldurb   w3, [x1, #-10]
        lsr     w3, w3, #2
        str     w3, [x0, #8]
        ldurb   w2, [x1, #-9]
        orr     w2, w3, w2, lsl #6
        and     w2, w2, #0x1fff
        str     w2, [x0, #8]
        sub     w6, w9, w2
        ldurb   w2, [x1, #-9]
        lsr     w2, w2, #7
        str     w2, [x0, #12]
        ldurb   w3, [x1, #-8]
        orr     w3, w2, w3, lsl #1
        str     w3, [x0, #12]
        ldurb   w2, [x1, #-7]
        orr     w2, w3, w2, lsl #9
        and     w2, w2, #0x1fff
        str     w2, [x0, #12]
        sub     w5, w9, w2
        ldurb   w2, [x1, #-7]
        lsr     w2, w2, #4
        str     w2, [x0, #16]
        ldurb   w3, [x1, #-6]
        orr     w3, w2, w3, lsl #4
        str     w3, [x0, #16]
        ldurb   w2, [x1, #-5]
        orr     w2, w3, w2, lsl #12
        and     w2, w2, #0x1fff
        str     w2, [x0, #16]
        sub     w4, w9, w2
        ldurb   w3, [x1, #-5]
        lsr     w3, w3, #1
        str     w3, [x0, #20]
        ldurb   w2, [x1, #-4]
        orr     w2, w3, w2, lsl #7
        and     w2, w2, #0x1fff
        str     w2, [x0, #20]
        sub     w3, w9, w2
        ldurb   w2, [x1, #-4]
        lsr     w2, w2, #6
        str     w2, [x0, #24]
        ldurb   w11, [x1, #-3]
        orr     w11, w2, w11, lsl #2
        str     w11, [x0, #24]
        ldurb   w2, [x1, #-2]
        orr     w2, w11, w2, lsl #10
        and     w2, w2, #0x1fff
        str     w2, [x0, #24]
        sub     w2, w9, w2
        ldurb   w12, [x1, #-2]
        lsr     w12, w12, #3
        str     w12, [x0, #28]
        ldurb   w11, [x1, #-1]
        stp     w8, w7, [x0]
        stp     w6, w5, [x0, #8]
        orr     w7, w12, w11, lsl #5
        stp     w4, w3, [x0, #16]
        sub     w6, w9, w7
        str     w2, [x0, #24]
        str     w6, [x0, #28]
        add     x0, x0, #0x20
        cmp     x10, x1
        b.ne    L2678
        ret

// mldsa_poly_chknorm (0x4c bytes)
L27c4:
        sub     w5, w1, #0x1
        mov     x4, x0
        add     x6, x0, #0x400
        mov     w0, #0x0
        nop
L27d8:
        ldr     w3, [x4], #4
        sxtw    x2, w3
        asr     x2, x2, #31
        neg     w1, w3
        eor     w1, w1, w3
        and     w1, w1, w2
        eor     w1, w1, w3
        sub     w1, w5, w1
        sxtw    x1, w1
        asr     x1, x1, #31
        orr     w0, w0, w1
        cmp     x4, x6
        b.ne    L27d8
        ret

// mldsa_polyw1_pack_88 (0x60 bytes)
L2810:
        add     x4, x0, #0xc0
        nop
L2818:
        ldrb    w3, [x1]
        add     x0, x0, #0x3
        sturb   w3, [x0, #-3]
        add     x1, x1, #0x10
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
        cmp     x0, x4
        b.ne    L2818
        ret

// mldsa_polyw1_pack_32 (0x24 bytes)
L2870:
        add     x4, x1, #0x400
        nop
L2878:
        ldr     w2, [x1, #4]
        ldr     w3, [x1], #8
        orr     w2, w3, w2, lsl #4
        strb    w2, [x0], #1
        cmp     x4, x1
        b.ne    L2878
        ret

// mldsa_polyw1_unpack_88 (0x60 bytes)
L2894:
        add     x4, x1, #0xc0
L2898:
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
        b.ne    L2898
        ret

// mldsa_polyw1_unpack_32 (0x2c bytes)
L28f4:
        add     x3, x0, #0x400
L28f8:
        ldrb    w2, [x1]
        add     x0, x0, #0x8
        and     w2, w2, #0xf
        stur    w2, [x0, #-8]
        ldrb    w2, [x1], #1
        lsr     w2, w2, #4
        stur    w2, [x0, #-4]
        cmp     x0, x3
        b.ne    L28f8
        ret

// mld_rej_eta_c44.constprop.0 (0xa8 bytes)
L2920:
        mov     x8, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    L29c4
        mov     w9, #0x1
        sub     w9, w9, w2
        mov     w7, #0xcd
        mov     w10, #0x2
L2940:
        ldrb    w3, [x2]
        add     w5, w9, w2
        add     x2, x2, #0x1
        and     w4, w3, #0xf
        lsr     w3, w3, #4
        cmp     w4, #0xf
        b.eq    L2978
        mul     w1, w4, w7
        lsr     w1, w1, #10
        add     w1, w1, w1, lsl #2
        sub     w4, w4, w1
        sub     w4, w10, w4
        str     w4, [x8, w0, uxtw #2]
        add     w0, w0, #0x1
L2978:
        cmp     w0, #0xff
        mul     w1, w3, w7
        cset    w4, ls
        add     w6, w0, #0x1
        cmp     w4, #0x0
        ccmp    w3, #0xe, #0x2, ne
        b.hi    L29b4
        lsr     w1, w1, #10
        cmp     w6, #0xff
        cset    w4, ls
        add     w1, w1, w1, lsl #2
        sub     w3, w3, w1
        sub     w3, w10, w3
        str     w3, [x8, w0, uxtw #2]
        mov     w0, w6
L29b4:
        cmp     w5, #0x87
        cset    w1, ls
        tst     w4, w1
        b.ne    L2940
L29c4:
        ret
        nop
        nop

// mldsa44_poly_decompose (0x80 bytes)
L29d0:
        mov     w8, #0x1800
        mov     x5, #0x0
        mov     w10, #0x2c0b
        mov     w9, #0x2b
        movk    w8, #0xfffd, lsl #16
        mov     w7, #0x3ff000
        mov     w6, #0xff801fff
        nop
L29f0:
        ldr     w4, [x1, x5]
        add     w3, w4, #0x7f
        asr     w3, w3, #7
        mul     w3, w3, w10
        add     w3, w3, #0x800, lsl #12
        asr     w3, w3, #24
        sub     w2, w9, w3
        sxtw    x2, w2
        asr     x2, x2, #31
        bic     w2, w3, w2
        str     w2, [x0, x5]
        madd    w2, w2, w8, w4
        sub     w3, w7, w2
        sxtw    x3, w3
        asr     x3, x3, #31
        add     w4, w2, w6
        eor     w4, w4, w2
        and     w3, w4, w3
        eor     w2, w3, w2
        str     w2, [x1, x5]
        add     x5, x5, #0x4
        cmp     x5, #0x400
        b.ne    L29f0
        ret

// mldsa44_poly_use_hint (0xb0 bytes)
L2a50:
        mov     w10, #0x1800
        mov     x6, #0x0
        mov     w11, #0x2c0b
        mov     w7, #0x2b
        movk    w10, #0xfffd, lsl #16
        mov     w9, #0x3ff000
        mov     w8, #0xff801fff
        b       L2a88
L2a70:
        cmp     w2, #0x2b
        csinc   w2, wzr, w2, eq
L2a78:
        str     w2, [x0, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.eq    L2afc
L2a88:
        ldr     w4, [x0, x6]
        add     w3, w4, #0x7f
        asr     w3, w3, #7
        mul     w3, w3, w11
        add     w3, w3, #0x800, lsl #12
        asr     w3, w3, #24
        sub     w2, w7, w3
        sxtw    x2, w2
        asr     x2, x2, #31
        bic     w2, w3, w2
        madd    w4, w2, w10, w4
        sub     w3, w9, w4
        sxtw    x3, w3
        asr     x3, x3, #31
        ldr     w12, [x1, x6]
        add     w5, w4, w8
        eor     w5, w5, w4
        and     w3, w5, w3
        eor     w3, w3, w4
        cbz     w12, L2a78
        sub     w4, w2, #0x1
        cmp     w3, #0x0
        b.gt    L2a70
        cmp     w2, #0x0
        csel    w2, w4, w7, ne
        str     w2, [x0, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L2a88
L2afc:
        ret

// mldsa44_poly_uniform_eta_4x (0x268 bytes)
L2b00:
        sub     sp, sp, #0x7d0
        mov     x8, x4
        .inst   0xb00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0xaf
        and     x22, x22, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x9, x22, #0x280
        add     x19, x22, #0x2e0
        stp     x25, x26, [sp, #48]
        add     x20, x22, #0x340
        add     x21, x22, #0x3a0
        stp     x27, x28, [sp, #64]
        add     x26, sp, #0x4a8
        mov     x28, x9
        str     x30, [sp, #80]
        add     x23, x22, #0x1e0
        str     x9, [sp, #136]
        add     x24, x22, #0x140
        ldp     q2, q3, [x8, #32]
        add     x25, x22, #0xa0
        ldp     q0, q1, [x8]
        ldr     x8, [x4]
        str     x8, [sp, #1992]
        mov     x8, #0x0
        ldrb    w4, [sp, #2000]
        mov     w27, #0xff
        stp     q2, q3, [x9, #32]
        stp     q2, q3, [x19, #32]
        stp     q0, q1, [x19]
        stp     q0, q1, [x20]
        stp     q2, q3, [x20, #32]
        stp     x0, x1, [sp, #104]
        mov     x0, x26
        stp     x2, x3, [sp, #120]
        stp     q0, q1, [x21]
        stp     q2, q3, [x21, #32]
        stp     q0, q1, [x9]
        strb    w5, [x9, #64]
        strb    wzr, [x9, #65]
        strb    w6, [x9, #160]
        strb    wzr, [x9, #161]
        strb    w7, [x9, #256]
        strb    wzr, [x9, #257]
        strb    w4, [x9, #352]
        strb    wzr, [x9, #353]
        bl      L1550
        mov     x4, x21
        mov     x3, x20
        mov     x2, x19
        mov     x1, x28
        mov     x0, x26
        mov     x5, #0x42
        bl      L1340
        mov     x3, x23
        mov     x5, x26
        mov     x4, #0x1
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L14c0
        ldr     x0, [sp, #104]
        mov     x2, x22
        mov     w1, #0x0
        bl      L2920
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     x2, x25
        mov     w1, #0x0
        bl      L2920
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     x2, x24
        mov     w1, #0x0
        bl      L2920
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, #0x0
        mov     x2, x23
        bl      L2920
        mov     w28, w0
        cmp     w21, w27
        ccmp    w0, w27, #0x0, hi
        cset    w0, ls
        cmp     w20, w27
        ccmp    w19, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0, L2cfc
        nop
L2c70:
        mov     x5, x26
        mov     x3, x23
        mov     x4, #0x1
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L14c0
        ldr     x0, [sp, #104]
        mov     w1, w19
        mov     x2, x22
        bl      L2920
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x25
        bl      L2920
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     w1, w21
        mov     x2, x24
        bl      L2920
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, w28
        mov     x2, x23
        bl      L2920
        cmp     w0, #0xff
        ccmp    w21, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0, L2c70
L2cfc:
        mov     x0, x26
        bl      L1554
        mov     x0, x22
        mov     x2, #0x280
        mov     w1, #0x0
        bl      L0e70
        ldr     x19, [sp, #136]
        mov     x2, #0x180
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1992]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2d64
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7d0
        ret
L2d64:
        bl      L0e60
        nop
        nop

// mldsa44_poly_challenge (0x168 bytes)
L2d70:
        stp     x19, x20, [sp, #-448]!
        mov     x19, x1
        .inst   0xb00000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        add     x2, sp, #0x5f
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0xe8
        and     x20, x2, #0xffffffffffffffe0
        stp     x23, x30, [sp, #32]
        mov     x23, x0
        ldr     x0, [x3]
        str     x0, [sp, #440]
        mov     x0, #0x0
        mov     x0, x21
        bl      L1094
        mov     x1, x19
        mov     x2, #0x20
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x88
        bl      L11d0
        mov     x2, x20
        mov     w0, #0x0
        mov     x3, #0x0
L2de0:
        ldrb    w1, [x2], #1
        lsl     x1, x1, x0
        add     w0, w0, #0x8
        orr     x3, x3, x1
        cmp     w0, #0x40
        b.ne    L2de0
        mov     x0, x23
        mov     x2, #0x400
        mov     w1, #0x0
        str     x3, [sp, #56]
        bl      L0e70
        mov     x19, #0xd9
        mov     w22, #0x1
        mov     w0, #0x8
        b       L2e2c
L2e1c:
        ldrb    w1, [x20, w0, uxtw]
        add     w0, w0, #0x1
        cmp     w1, w19
        b.ls    L2e54
L2e2c:
        cmp     w0, #0x88
        b.ne    L2e1c
        mov     x0, x20
        mov     x1, #0x88
        mov     x2, x21
        bl      L11d0
        ldrb    w1, [x20]
        mov     w0, #0x1
        cmp     w1, w19
        b.hi    L2e1c
L2e54:
        ldr     x2, [sp, #56]
        ldr     w4, [x23, x1, lsl #2]
        str     w4, [x23, x19, lsl #2]
        add     x19, x19, #0x1
        ubfiz   x3, x2, #1, #1
        lsr     x2, x2, #1
        sub     w3, w22, w3
        str     w3, [x23, x1, lsl #2]
        str     x2, [sp, #56]
        cmp     x19, #0x100
        b.ne    L2e2c
        mov     x0, x21
        bl      L1280
        movi    v0.4s, #0x0
        str     xzr, [x20, #128]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        add     x0, sp, #0x38
        str     xzr, [sp, #56]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #440]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2ed4
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #448
        ret
L2ed4:
        bl      L0e60
        nop
        nop

// mldsa44_polyeta_pack (0xdc bytes)
L2ee0:
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        add     x10, x1, #0x400
        mov     w5, #0x2
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
L2f00:
        ldp     w4, w2, [x1, #4]
        add     x0, x0, #0x3
        ldp     w6, w9, [x1, #12]
        sub     w2, w5, w2
        ldp     w7, w3, [x1, #20]
        sub     w4, w5, w4
        ldr     w8, [x1, #28]
        sub     w6, w5, w6
        sub     w7, w5, w7
        sub     w9, w5, w9
        sub     w3, w5, w3
        sub     w8, w5, w8
        ldr     w11, [x1], #32
        ubfiz   w13, w2, #6, #8
        ubfiz   w8, w8, #5, #8
        ubfiz   w12, w7, #7, #8
        ubfx    x2, x2, #2, #6
        ubfiz   w4, w4, #3, #8
        ubfiz   w6, w6, #1, #8
        ubfiz   w9, w9, #4, #8
        ubfiz   w3, w3, #2, #8
        orr     w4, w4, w13
        orr     w3, w3, w8
        orr     w6, w6, w9
        sub     w8, w5, w11
        orr     w2, w2, w12
        ubfx    x7, x7, #1, #7
        orr     w4, w4, w8
        orr     w2, w2, w6
        orr     w3, w3, w7
        sturb   w4, [x0, #-3]
        sturb   w2, [x0, #-2]
        sturb   w3, [x0, #-1]
        cmp     x10, x1
        b.ne    L2f00
        add     x0, sp, #0x10
        str     xzr, [sp, #16]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2fb8
        ldr     x30, [sp], #32
        ret
L2fb8:
        bl      L0e60
        nop

// mldsa44_polyeta_unpack (0xc4 bytes)
L2fc0:
        movi    v2.4s, #0x2
        add     x5, x1, #0x60
L2fc8:
        ldrb    w2, [x1]
        add     x1, x1, #0x3
        add     x0, x0, #0x20
        and     w2, w2, #0x7
        stur    w2, [x0, #-32]
        fmov    s1, w2
        ldurb   w3, [x1, #-3]
        ubfx    x3, x3, #3, #3
        stur    w3, [x0, #-28]
        ldurb   w4, [x1, #-2]
        mov     v1.s[1], w3
        ldurb   w2, [x1, #-3]
        lsl     w3, w4, #2
        orr     w2, w3, w2, lsr #6
        and     w2, w2, #0x7
        stur    w2, [x0, #-24]
        ldurb   w3, [x1, #-2]
        mov     v1.s[2], w2
        ubfx    x3, x3, #1, #3
        stur    w3, [x0, #-20]
        ldurb   w2, [x1, #-2]
        mov     v1.s[3], w3
        ubfx    x2, x2, #4, #3
        stur    w2, [x0, #-16]
        fmov    d0, x2
        ldurb   w3, [x1, #-1]
        sub     v1.4s, v2.4s, v1.4s
        ldurb   w2, [x1, #-2]
        lsl     w3, w3, #1
        orr     w2, w3, w2, lsr #7
        and     w2, w2, #0x7
        stur    w2, [x0, #-12]
        ldurb   w3, [x1, #-1]
        mov     v0.s[1], w2
        ubfx    x2, x3, #2, #3
        stur    w2, [x0, #-8]
        ldurb   w3, [x1, #-1]
        mov     v0.s[2], w2
        stur    q1, [x0, #-32]
        fmov    s1, w3
        ushr    v1.2s, v1.2s, #5
        mov     v0.s[3], v1.s[0]
        sub     v0.4s, v2.4s, v0.4s
        stur    q0, [x0, #-16]
        cmp     x5, x1
        b.ne    L2fc8
        ret

// mldsa44_polyz_pack (0xe0 bytes)
L3084:
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x9, x1, #0x400
        mov     w6, #0x20000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        nop
L30a8:
        ldp     w2, w4, [x1]
        add     x0, x0, #0x9
        ldp     w3, w5, [x1, #8]
        sub     w2, w6, w2
        fmov    s0, w2
        sub     w4, w6, w4
        sub     w3, w6, w3
        add     x1, x1, #0x10
        ushr    v1.2s, v0.2s, #8
        fmov    s0, w4
        ubfiz   w7, w4, #2, #6
        ubfiz   w8, w3, #4, #4
        ushr    v3.2s, v0.2s, #6
        fmov    d0, x2
        orr     w7, w7, w2, lsr #16
        orr     w4, w8, w4, lsr #14
        mov     v0.b[1], v1.b[0]
        fmov    s1, w3
        sub     w2, w6, w5
        ushr    v2.2s, v1.2s, #4
        fmov    s1, w2
        ubfiz   w5, w2, #6, #2
        lsr     w2, w2, #10
        mov     v0.b[2], w7
        orr     w3, w5, w3, lsr #12
        ushr    v1.2s, v1.2s, #2
        sturb   w2, [x0, #-1]
        mov     v0.b[3], v3.b[0]
        mov     v0.b[4], w4
        mov     v0.b[5], v2.b[0]
        mov     v0.b[6], w3
        mov     v0.b[7], v1.b[0]
        stur    d0, [x0, #-9]
        cmp     x9, x1
        b.ne    L30a8
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3160
        ldr     x30, [sp], #48
        ret
L3160:
        bl      L0e60

// mldsa44_polyz_unpack (0xd0 bytes)
L3164:
        add     x8, x1, #0x240
        mov     w7, #0x20000
        nop
L3170:
        ldrb    w2, [x1]
        add     x1, x1, #0x9
        str     w2, [x0]
        ldurb   w3, [x1, #-8]
        orr     w3, w2, w3, lsl #8
        str     w3, [x0]
        ldurb   w2, [x1, #-7]
        orr     w2, w3, w2, lsl #16
        and     w2, w2, #0x3ffff
        str     w2, [x0]
        sub     w4, w7, w2
        ldurb   w2, [x1, #-7]
        lsr     w2, w2, #2
        str     w2, [x0, #4]
        ldurb   w3, [x1, #-6]
        orr     w3, w2, w3, lsl #6
        str     w3, [x0, #4]
        ldurb   w2, [x1, #-5]
        orr     w2, w3, w2, lsl #14
        and     w2, w2, #0x3ffff
        str     w2, [x0, #4]
        sub     w3, w7, w2
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
        sub     w2, w7, w2
        ldurb   w5, [x1, #-3]
        lsr     w5, w5, #6
        str     w5, [x0, #12]
        ldurb   w6, [x1, #-2]
        orr     w6, w5, w6, lsl #2
        str     w6, [x0, #12]
        ldurb   w5, [x1, #-1]
        stp     w4, w3, [x0]
        add     x0, x0, #0x10
        stur    w2, [x0, #-8]
        orr     w3, w6, w5, lsl #10
        sub     w2, w7, w3
        stur    w2, [x0, #-4]
        cmp     x8, x1
        b.ne    L3170
        ret

// mldsa44_poly_uniform_gamma1 (0xe4 bytes)
L3234:
        sub     sp, sp, #0x430
        .inst   0x900000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x4f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x19, x20, #0x2c0
        add     x21, sp, #0x358
        str     x30, [sp, #32]
        mov     x22, x0
        mov     x0, x21
        ldp     q2, q3, [x1]
        ldr     x4, [x3]
        str     x4, [sp, #1064]
        mov     x4, #0x0
        ldp     q0, q1, [x1, #32]
        stp     q2, q3, [x19]
        stp     q0, q1, [x19, #32]
        strh    w2, [x20, #768]
        bl      L1094
        mov     x1, x19
        mov     x2, #0x42
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x2a8
        bl      L11d0
        mov     x1, x20
        mov     x0, x22
        bl      L3164
        mov     x0, x21
        bl      L1280
        mov     x0, x20
        mov     x2, #0x2a8
        mov     w1, #0x0
        bl      L0e70
        movi    v0.4s, #0x0
        strh    wzr, [x19, #64]
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1064]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3314
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x430
        ret
L3314:
        bl      L0e60
        nop
        nop

// mldsa44_polyvecl_ntt (0x28 bytes)
L3320:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L20f0
        add     x0, x19, #0x400
        bl      L20f0
        add     x0, x19, #0x800
        bl      L20f0
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L20f0
        nop
        nop

// mldsa44_polyvecl_chknorm (0x4c bytes)
L3350:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     w20, #0x0
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x0, #0x1, lsl #12
        str     x30, [sp, #32]
L336c:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L27c4
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L336c
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
        nop

// mldsa44_polyveck_reduce (0x28 bytes)
L33a0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L2000
        add     x0, x19, #0x400
        bl      L2000
        add     x0, x19, #0x800
        bl      L2000
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L2000
        nop
        nop

// mldsa44_polyveck_caddq (0x28 bytes)
L33d0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L2030
        add     x0, x19, #0x400
        bl      L2030
        add     x0, x19, #0x800
        bl      L2030
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L2030
        nop
        nop

// mldsa44_polyveck_invntt_tomont (0x28 bytes)
L3400:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L21c0
        add     x0, x19, #0x400
        bl      L21c0
        add     x0, x19, #0x800
        bl      L21c0
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L21c0
        nop
        nop

// mldsa44_polyveck_unpack_eta_chknorm (0x5c bytes)
L3430:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x20, x2
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x180
L3450:
        mov     x1, x19
        mov     x0, x20
        bl      L2fc0
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L27c4
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L3450
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
        nop

// mldsa44_polyveck_decompose_pack_w1 (0x54 bytes)
L3490:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x0, #0x300
        str     x30, [sp, #32]
L34ac:
        mov     x1, x20
        mov     x0, x21
        bl      L29d0
        add     x20, x20, #0x400
        mov     x0, x19
        mov     x1, x21
        add     x19, x19, #0xc0
        bl      L2810
        cmp     x19, x22
        b.ne    L34ac
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyvecl_unpack_eta (0x3c bytes)
L34e4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x180
L34f8:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L2fc0
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L34f8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa44_polyvecl_unpack_z (0x3c bytes)
L3520:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x900
L3534:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x240
        bl      L3164
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L3534
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mldsa44_polyvec_matrix_expand_lazy (0x10 bytes)
L3560:
        ldp     q0, q1, [x1]
        add     x0, x0, #0x400
        stp     q0, q1, [x0]
        ret

// mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy (0xf0 bytes)
L3570:
        stp     x19, x20, [sp, #-160]!
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        add     x22, x2, #0x400
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        and     w24, w3, #0xff
        stp     x25, x30, [sp, #48]
        mov     x25, x2
        mov     x1, x19
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        mov     x23, x0
        ldr     q0, [x20, #1024]
        ldr     x3, [x2]
        str     x3, [sp, #152]
        mov     x3, #0x0
        ldr     q1, [x20, #1040]
        strb    wzr, [x19, #32]
        strb    w24, [x19, #33]
        mov     w21, #0x1
        stp     q0, q1, [x19]
        bl      L2370
        mov     x1, x25
        mov     x0, x23
        bl      L22e0
L35dc:
        mov     x1, x19
        mov     x0, x20
        strb    w21, [x19, #32]
        add     w21, w21, #0x1
        strb    w24, [x19, #33]
        bl      L2370
        mov     x1, x22
        mov     x0, x20
        bl      L22e0
        add     x22, x22, #0x400
        mov     x1, x20
        mov     x0, x23
        bl      L2070
        cmp     w21, #0x4
        b.ne    L35dc
        mov     x0, x23
        bl      L2000
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L365c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
L365c:
        bl      L0e60

// mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy (0x134 bytes)
L3660:
        stp     x19, x20, [sp, #-176]!
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        add     x20, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x20, x20, #0xffffffffffffffe0
        mov     x24, x3
        stp     x25, x26, [sp, #48]
        mov     x26, x0
        mov     x25, x2
        str     x30, [sp, #64]
        mov     w22, #0x0
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     q0, [x23, #1024]
        ldr     x1, [x0]
        str     x1, [sp, #168]
        mov     x1, #0x0
        ldr     q1, [x23, #1040]
        stp     q0, q1, [x20]
L36b0:
        ldrh    w2, [x25, #8]
        ldr     x1, [x25]
        add     w2, w22, w2
        mov     x0, x24
        mov     x21, x26
        mov     w19, #0x0
        bl      L3234
        mov     x0, x24
        bl      L20f0
L36d4:
        mov     x1, x20
        cbz     w22, L3770
        mov     x0, x23
        strb    w22, [x20, #32]
        strb    w19, [x20, #33]
        bl      L2370
        mov     x1, x24
        mov     x0, x23
        bl      L22e0
        mov     x1, x23
        mov     x0, x21
        bl      L2070
L3704:
        add     w19, w19, #0x1
        add     x21, x21, #0x400
        cmp     w19, #0x4
        b.ne    L36d4
        add     w22, w22, #0x1
        cmp     w22, #0x4
        b.ne    L36b0
        movi    v0.4s, #0x0
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        mov     x0, x26
        bl      L33a0
        mov     x0, x26
        bl      L3400
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #168]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3790
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #176
        ret
L3770:
        mov     x0, x21
        strb    wzr, [x20, #32]
        strb    w19, [x20, #33]
        bl      L2370
        mov     x1, x24
        mov     x0, x21
        bl      L22e0
        b       L3704
L3790:
        bl      L0e60
        nop
        nop
        nop

// mld_compute_pack_t0_t144 (0x150 bytes)
L37a0:
        sub     sp, sp, #0xc90
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        mov     w21, #0x0
        .inst   0x900000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        stp     x23, x24, [sp, #32]
        mov     x23, x2
        mov     x24, x1
        stp     x25, x26, [sp, #48]
        add     x26, sp, #0x6f
        and     x26, x26, #0xffffffffffffffe0
        str     x30, [sp, #64]
        mov     x25, x0
        add     x19, x26, #0x820
        add     x20, x26, #0x420
        ldr     x2, [x3]
        str     x2, [sp, #3208]
        mov     x2, #0x0
        mov     x1, x4
        mov     x0, x26
        bl      L3560
L37fc:
        mov     w3, w21
        mov     x2, x23
        mov     x1, x26
        mov     x0, x19
        bl      L3570
        add     w21, w21, #0x1
        mov     x0, x19
        bl      L21c0
        mov     x1, x22
        mov     x0, x20
        bl      L2fc0
        add     x22, x22, #0x60
        mov     x1, x20
        mov     x0, x19
        bl      L2070
        mov     x0, x19
        bl      L2000
        mov     x0, x19
        bl      L2030
        mov     x2, x19
        mov     x1, x19
        mov     x0, x20
        bl      L2330
        mov     x0, x25
        mov     x1, x20
        bl      L2474
        add     x25, x25, #0x140
        mov     x0, x24
        mov     x1, x19
        bl      L2544
        add     x24, x24, #0x1a0
        cmp     w21, #0x4
        b.ne    L37fc
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x420
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e70
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3208]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L38ec
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, #0xc90
        ret
L38ec:
        bl      L0e60

// mld_H44 (0x10c bytes)
L38f0:
        stp     x19, x20, [sp, #-304]!
        mov     x20, x7
        .inst   0x900000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x58
        stp     x23, x24, [sp, #32]
        mov     x22, x0
        mov     x24, x2
        stp     x25, x26, [sp, #48]
        mov     x23, x1
        mov     x25, x3
        stp     x27, x30, [sp, #64]
        mov     x21, x5
        mov     x26, x4
        ldr     x0, [x8]
        str     x0, [sp, #296]
        mov     x0, #0x0
        mov     x27, x6
        mov     x0, x19
        bl      L1094
        mov     x2, x25
        mov     x1, x24
        mov     x0, x19
        bl      L10c0
        cbnz    x21, L39d0
        cbnz    x20, L39e4
L395c:
        mov     x0, x19
        bl      L1150
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L11d0
        mov     x0, x19
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     q0, [x19, #192]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L39f8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret
L39d0:
        mov     x2, x21
        mov     x1, x26
        mov     x0, x19
        bl      L10c0
        cbz     x20, L395c
L39e4:
        mov     x2, x20
        mov     x1, x27
        mov     x0, x19
        bl      L10c0
        b       L395c
L39f8:
        bl      L0e60
        nop

// mldsa44_keypair_internal (0x248 bytes)
L3a00:
        mov     x12, #0x1180
        sub     sp, sp, x12
        mov     x3, #0x10c0
        mov     w4, #0x404
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x8f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x22, x19, x3
        add     x20, x19, #0x1, lsl #12
        stp     x23, x24, [sp, #48]
        mov     x23, x0
        mov     x21, x1
        stp     x25, x26, [sp, #64]
        add     x24, x19, #0xc00
        add     x25, x19, #0x800
        stp     x27, x28, [sp, #80]
        mov     x3, #0x22
        add     x28, x20, #0x20
        str     x30, [sp, #96]
        mov     x1, #0x80
        add     x26, x19, #0x400
        add     x27, x21, #0x200
        ldp     q0, q1, [x2]
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #4472]
        mov     x0, #0x0
        stp     q0, q1, [x22]
        mov     x2, x22
        mov     x0, x20
        strh    w4, [x19, #4320]
        bl      L12a4
        mov     x3, x24
        mov     x2, x25
        mov     x4, x28
        mov     w0, #0x7
        strb    w0, [sp]
        mov     w7, #0x6
        mov     w6, #0x5
        mov     w5, #0x4
        mov     x1, x26
        mov     x0, x19
        bl      L2b00
        mov     x1, x19
        mov     x0, x27
        bl      L2ee0
        mov     x1, x26
        add     x0, x21, #0x260
        bl      L2ee0
        mov     x1, x25
        add     x0, x21, #0x2c0
        bl      L2ee0
        mov     x1, x24
        add     x0, x21, #0x320
        bl      L2ee0
        mov     x3, x24
        mov     x2, x25
        mov     x4, x28
        mov     w0, #0x3
        strb    w0, [sp]
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x1, x26
        mov     x0, x19
        bl      L2b00
        mov     x1, x19
        add     x0, x21, #0x80
        bl      L2ee0
        mov     x1, x26
        add     x0, x21, #0xe0
        bl      L2ee0
        mov     x1, x25
        add     x0, x21, #0x140
        bl      L2ee0
        mov     x1, x24
        add     x0, x21, #0x1a0
        bl      L2ee0
        mov     x0, x19
        bl      L3320
        ldp     q0, q1, [x20]
        mov     x4, x20
        mov     x3, x27
        mov     x2, x19
        add     x1, x21, #0x380
        add     x0, x23, #0x20
        stp     q0, q1, [x23]
        bl      L37a0
        mov     x4, #0x1080
        mov     w25, w0
        add     x24, x19, x4
        cbnz    w0, L3ba0
        mov     x0, x24
        mov     x2, x23
        mov     x3, #0x520
        mov     x1, #0x40
        bl      L12a4
        mov     x2, x24
        add     x3, x20, #0x60
        mov     x1, x20
        mov     x0, x21
        bl      L1cf4
L3ba0:
        mov     x0, x19
        mov     x2, #0x1000
        mov     w1, #0x0
        bl      L0e70
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     xzr, xzr, [x22]
        stp     xzr, xzr, [x22, #16]
        strh    wzr, [x22, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        cbnz    w25, L3c20
L3bdc:
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3c44
        ldp     x19, x20, [sp, #16]
        mov     w0, w25
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x1180
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L3c20:
        mov     x0, x23
        mov     x2, #0x520
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0xa00
        mov     x0, x21
        mov     w1, #0x0
        bl      L0e70
        b       L3bdc
L3c44:
        bl      L0e60
        nop
        nop

// mldsa44_keypair (0x88 bytes)
L3c50:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        ldr     x1, [x2]
        str     x1, [sp, #88]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e50
        cbnz    w0, L3ccc
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L3a00
L3c9c:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0x900000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L3cd4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L3ccc:
        mov     w0, #0xfffffffd
        b       L3c9c
L3cd4:
        bl      L0e60
        nop
        nop

// mldsa44_signature_internal (0x4f8 bytes)
L3ce0:
        mov     x12, #0x2650
        sub     sp, sp, x12
        mov     x11, #0x2320
        mov     x12, #0x2460
        .inst   0x900000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0xcf
        and     x22, x22, #0xffffffffffffffe0
        mov     x13, #0x24a0
        add     x9, x22, x11
        add     x10, x22, x12
        add     x11, x22, x13
        mov     x14, #0x2480
        add     x12, x22, x14
        stp     x19, x20, [sp]
        mov     x21, x4
        stp     x23, x24, [sp, #32]
        mov     x20, x3
        mov     x24, x1
        stp     x25, x26, [sp, #48]
        mov     w25, w7
        add     x26, x9, #0x20
        stp     x27, x28, [sp, #64]
        mov     x23, x2
        mov     x19, x5
        str     x30, [sp, #80]
        mov     x1, x26
        str     x0, [sp, #104]
        mov     x27, x9
        str     x9, [sp, #136]
        add     x2, x9, #0x60
        stp     x11, x10, [sp, #152]
        mov     x5, x10
        mov     x4, x11
        str     x12, [sp, #168]
        mov     x3, x12
        mov     x0, x9
        ldr     x7, [x8]
        str     x7, [sp, #9800]
        mov     x7, #0x0
        bl      L1d20
        cbnz    w25, L41b8
        mov     x3, #0x40
        mov     x7, x23
        mov     x6, x24
        mov     x5, x21
        mov     x4, x20
        mov     x2, x26
        add     x0, x27, #0x80
        mov     x1, x3
        bl      L38f0
L3db0:
        ldr     x23, [sp, #136]
        mov     x1, #0x1c20
        mov     x2, #0x2440
        mov     x6, #0x2578
        mov     x4, x19
        mov     x5, #0x20
        mov     x7, #0x2420
        mov     x8, #0x1820
        mov     x9, #0x1420
        mov     x10, #0x2020
        mov     x3, x5
        add     x19, x22, x1
        add     x21, sp, x6
        add     x1, x22, x2
        add     x6, x23, #0x80
        add     x2, x23, #0x60
        mov     x0, #0x2400
        add     x28, x22, x7
        mov     x7, #0x40
        str     x1, [sp, #128]
        add     x1, x22, x10
        add     x25, x22, x0
        add     x24, x22, x8
        add     x0, x23, #0xc0
        add     x20, x22, x9
        str     x1, [sp, #120]
        mov     x1, x7
        bl      L38f0
        add     x0, x22, #0x1, lsl #12
        mov     x1, x23
        str     wzr, [sp, #116]
        str     x0, [sp, #144]
        bl      L3560
        nop
L3e38:
        ldp     x2, x23, [sp, #128]
        mov     x3, x19
        ldr     x1, [sp, #144]
        mov     x0, x22
        add     x4, x23, #0xc0
        str     x4, [x25, #64]
        ldrh    w4, [sp, #116]
        strh    w4, [x25, #72]
        bl      L3660
        mov     x0, x22
        bl      L33d0
        ldr     x26, [sp, #120]
        mov     x2, x19
        mov     x1, x22
        mov     x0, x26
        bl      L3490
        mov     x0, x21
        bl      L1094
        add     x1, x23, #0x80
        mov     x0, x21
        mov     x2, #0x40
        bl      L10c0
        mov     x1, x26
        mov     x2, #0x300
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x1, #0x20
        mov     x0, x28
        bl      L11d0
        mov     x0, x21
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        str     q0, [x21, #192]
        mov     x1, x28
        mov     x0, x24
        bl      L2d70
        mov     x26, #0x0
        mov     x0, x24
        mov     w23, #0x0
        bl      L20f0
L3efc:
        ldr     x1, [x22, #9376]
        mov     x0, x20
        add     x1, x1, x26
        bl      L2fc0
        mov     x0, x20
        bl      L20f0
        mov     x1, x24
        mov     x0, x20
        bl      L22e0
        mov     x0, x20
        bl      L21c0
        ldr     x1, [x25, #64]
        mov     x0, x19
        ldrh    w2, [x25, #72]
        add     w2, w23, w2
        bl      L3234
        mov     x1, x19
        mov     x0, x20
        bl      L2070
        mov     x0, x20
        bl      L2000
        mov     w1, #0xffb2
        mov     x0, x20
        movk    w1, #0x1, lsl #16
        bl      L27c4
        cbnz    w0, L41b0
        ldr     x0, [sp, #104]
        mov     w2, w23
        mov     x1, x20
        add     w23, w23, #0x1
        add     x26, x26, #0x60
        bl      L1e70
        cmp     w23, #0x4
        b.ne    L3efc
        mov     x23, x22
        mov     x26, #0x0
        mov     x27, #0x0
L3f90:
        ldr     x1, [x22, #9312]
        mov     x0, x19
        add     x1, x1, x27
        bl      L2fc0
        mov     x0, x19
        bl      L20f0
        mov     x1, x24
        mov     x0, x19
        bl      L22e0
        mov     x0, x19
        bl      L21c0
        mov     x1, x19
        mov     x0, x23
        bl      L20a0
        mov     x0, x23
        bl      L2000
        mov     w1, #0x73b2
        mov     x0, x23
        movk    w1, #0x1, lsl #16
        bl      L27c4
        cbnz    w0, L41b0
        ldr     x1, [x22, #9344]
        mov     x0, x19
        add     x1, x1, x26
        bl      L2670
        mov     x0, x19
        bl      L20f0
        mov     x1, x24
        mov     x0, x19
        bl      L22e0
        mov     x0, x19
        bl      L21c0
        mov     x0, x19
        bl      L2000
        mov     w1, #0x7400
        mov     x0, x19
        movk    w1, #0x1, lsl #16
        bl      L27c4
        cbnz    w0, L41b0
        mov     x0, x23
        mov     x1, x19
        add     x26, x26, #0x1a0
        bl      L2070
        add     x27, x27, #0x60
        add     x23, x23, #0x400
        cmp     x26, #0x680
        b.ne    L3f90
        ldr     x23, [sp, #104]
        mov     x1, x28
        mov     x0, x23
        bl      L1d60
        ldr     x2, [sp, #120]
        mov     x0, x23
        mov     x3, x19
        mov     x1, x22
        bl      L1d70
        mov     w23, w0
L4074:
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x24
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1000
        mov     x0, x22
        mov     w1, #0x0
        bl      L0e70
        ldr     x26, [sp, #120]
        mov     x2, #0x300
        mov     w1, #0x0
        mov     x0, x26
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        ldr     x0, [sp, #128]
        stp     xzr, xzr, [x0]
        stp     xzr, xzr, [x28]
        stp     xzr, xzr, [x28, #16]
        cbz     w23, L4118
        cmn     w23, #0x1
        b.ne    L4104
        ldr     w0, [sp, #116]
        mov     w1, #0xfff8
        add     w0, w0, #0x4
        and     w2, w0, #0xffff
        str     w2, [sp, #116]
        cmp     w1, w0, uxth
        b.ne    L3e38
        mov     w23, #0xfffffffc
L4104:
        ldr     x19, [sp, #104]
        mov     x2, #0x974
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
L4118:
        ldr     x0, [sp, #160]
        str     xzr, [x22, #9312]
        ldr     x0, [sp, #168]
        str     xzr, [x22, #9344]
        ldr     x0, [sp, #152]
        str     xzr, [x22, #9376]
        ldr     x19, [sp, #144]
        mov     x2, #0x420
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        ldr     x0, [sp, #136]
        movi    v0.4s, #0x0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        stp     q0, q0, [x0, #192]
        stp     q0, q0, [x0, #224]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #9800]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L41d4
        ldp     x19, x20, [sp]
        mov     w0, w23
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x2650
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L41b0:
        mov     w23, #0xffffffff
        b       L4074
L41b8:
        ldr     x0, [sp, #136]
        ldp     q2, q3, [x24]
        add     x0, x0, #0x80
        ldp     q0, q1, [x24, #32]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
        b       L3db0
L41d4:
        bl      L0e60
        nop
        nop

// mldsa44_signature_extmu (0xa8 bytes)
L41e0:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xf00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        mov     x22, x2
        ldr     x1, [x3]
        str     x1, [sp, #104]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e50
        cbnz    w0, L427c
        mov     x6, x22
        mov     x1, x21
        mov     x0, x20
        mov     x5, x19
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L3ce0
L4248:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4284
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L427c:
        mov     w0, #0xfffffffd
        b       L4248
L4284:
        bl      L0e60
        nop
        nop

// mldsa44_verify_internal (0x478 bytes)
L4290:
        mov     x12, #0x2510
        sub     sp, sp, x12
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        mov     x26, x1
        stp     x19, x20, [sp]
        add     x20, sp, #0x9f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        mov     x19, #0x2400
        add     x19, x20, x19
        stp     x23, x24, [sp, #32]
        mov     x21, x3
        mov     x24, x2
        stp     x27, x28, [sp, #64]
        mov     x23, x4
        mov     w27, w6
        str     x30, [sp, #80]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x5, [sp, #104]
        ldp     q0, q1, [x25]
        ldr     x1, [x0]
        str     x1, [sp, #9480]
        mov     x1, #0x0
        add     x1, x25, #0x20
        mov     x0, x20
        stp     q0, q1, [x19, #-128]
        bl      L3520
        mov     w1, #0xffb2
        mov     x0, x20
        movk    w1, #0x1, lsl #16
        bl      L3350
        cbnz    w0, L46b8
        mov     w22, w0
        cbz     w27, L4604
        ldp     q2, q3, [x26]
        sub     x19, x19, #0xe0
        ldp     q0, q1, [x26, #32]
        mov     x7, #0x2020
        mov     x8, #0x2320
        add     x28, x20, x7
        add     x27, x20, x8
        stp     q2, q3, [x19]
        stp     q0, q1, [x19, #32]
L4344:
        add     x1, x20, #0x1, lsl #12
        mov     x3, #0x1820
        mov     x4, #0x1c20
        mov     x19, x1
        add     x26, x20, x4
        add     x21, x20, x3
        mov     x0, x20
        str     x1, [sp, #112]
        bl      L3320
        ldr     x1, [sp, #104]
        mov     x5, #0x2380
        add     x2, x20, x5
        mov     x0, x19
        mov     x19, x2
        str     x2, [sp, #120]
        mov     x24, x28
        bl      L3560
        mov     x1, x19
        mov     x6, #0x1420
        mov     x0, x26
        add     x19, x20, x6
        bl      L2d70
        mov     x0, x26
        bl      L20f0
L43a4:
        ldr     x1, [sp, #112]
        mov     w3, w22
        mov     x2, x20
        mov     x0, x21
        bl      L3570
        ldr     x1, [sp, #104]
        mov     w2, w22
        mov     x0, x19
        bl      L1ce0
        mov     x0, x19
        bl      L20d0
        mov     x0, x19
        bl      L20f0
        mov     x1, x26
        mov     x0, x19
        bl      L22e0
        mov     x1, x19
        mov     x0, x21
        bl      L20a0
        mov     x0, x21
        bl      L2000
        mov     x0, x21
        bl      L21c0
        mov     x0, x21
        bl      L2030
        mov     w2, w22
        mov     x1, x25
        mov     x0, x19
        bl      L1e84
        mov     w23, w0
        cbnz    w0, L46a8
        mov     x1, x19
        mov     x0, x21
        bl      L2a50
        add     w22, w22, #0x1
        mov     x0, x24
        mov     x1, x21
        bl      L2810
        add     x24, x24, #0xc0
        cmp     w22, #0x4
        b.ne    L43a4
        mov     x1, #0x2360
        mov     x0, #0x2438
        add     x24, sp, x0
        add     x22, x20, x1
        mov     x0, x24
        bl      L1094
        mov     x0, x24
        mov     x1, x27
        mov     x2, #0x40
        bl      L10c0
        mov     x1, x28
        mov     x2, #0x300
        mov     x0, x24
        bl      L10c0
        mov     x0, x24
        bl      L1150
        mov     x2, x24
        mov     x1, #0x20
        mov     x0, x22
        bl      L11d0
        mov     x0, x24
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     q0, q0, [x24, #64]
        stp     q0, q0, [x24, #96]
        stp     q0, q0, [x24, #128]
        stp     q0, q0, [x24, #160]
        str     q0, [x24, #192]
        ldr     q4, [x20, #9056]
        ldr     q3, [x20, #9072]
        ldr     q1, [x20, #9088]
        ldr     q2, [x20, #9104]
        eor     v1.16b, v1.16b, v4.16b
        eor     v2.16b, v2.16b, v3.16b
        orr     v4.16b, v1.16b, v2.16b
        eor     v1.16b, v1.16b, v2.16b
        ext     v3.16b, v4.16b, v0.16b, #8
        ext     v2.16b, v1.16b, v0.16b, #8
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v1.16b
        ext     v4.16b, v3.16b, v0.16b, #4
        ext     v1.16b, v2.16b, v0.16b, #4
        orr     v4.16b, v4.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        ext     v3.16b, v4.16b, v0.16b, #2
        ext     v2.16b, v1.16b, v0.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v1.16b
        ext     v1.16b, v3.16b, v0.16b, #1
        ext     v0.16b, v2.16b, v0.16b, #1
        orr     v1.16b, v1.16b, v3.16b
        eor     v0.16b, v0.16b, v2.16b
        umov    w1, v1.b[0]
        umov    w0, v0.b[0]
        neg     x1, x1
        asr     x1, x1, #32
        eor     w1, w0, w1
        cmp     w0, w1, uxtb
        b.ne    L46b0
L453c:
        mov     x0, x19
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x21
        mov     w1, #0x0
        bl      L0e70
        ldr     x19, [sp, #112]
        mov     x2, #0x420
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1000
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e70
        stp     xzr, xzr, [x22]
        stp     xzr, xzr, [x22, #16]
        ldr     x0, [sp, #120]
        stp     xzr, xzr, [x0]
        stp     xzr, xzr, [x0, #16]
        movi    v0.4s, #0x0
        stp     q0, q0, [x27]
        stp     q0, q0, [x27, #32]
        mov     x2, #0x300
        mov     x0, x28
        mov     w1, #0x0
        bl      L0e70
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #9480]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4704
        ldp     x19, x20, [sp]
        mov     w0, w23
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x2510
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L4604:
        mov     x9, #0x2438
        mov     x10, #0x2020
        add     x19, sp, x9
        add     x28, x20, x10
        mov     x0, x19
        bl      L1094
        ldr     x1, [sp, #104]
        mov     x2, #0x520
        mov     x0, x19
        bl      L10c0
        mov     x0, x19
        bl      L1150
        mov     x2, x19
        mov     x1, #0x40
        mov     x0, x28
        bl      L11d0
        mov     x0, x19
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     q0, [x19, #192]
        mov     x11, #0x2320
        add     x27, x20, x11
        mov     x3, #0x40
        mov     x7, x24
        mov     x6, x26
        mov     x5, x23
        mov     x4, x21
        mov     x0, x27
        mov     x2, x28
        mov     x1, x3
        bl      L38f0
        movi    v0.4s, #0x0
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        b       L4344
L46a8:
        mov     x2, #0x2360
        add     x22, x20, x2
L46b0:
        mov     w23, #0xfffffffa
        b       L453c
L46b8:
        add     x0, x20, #0x1, lsl #12
        mov     x12, #0x2020
        mov     x13, #0x2320
        mov     x14, #0x1c20
        mov     x15, #0x1820
        mov     x16, #0x1420
        mov     x17, #0x2360
        mov     x18, #0x2380
        add     x28, x20, x12
        add     x27, x20, x13
        add     x26, x20, x14
        add     x21, x20, x15
        add     x19, x20, x16
        add     x22, x20, x17
        mov     w23, #0xfffffffa
        str     x0, [sp, #112]
        add     x0, x20, x18
        str     x0, [sp, #120]
        b       L453c
L4704:
        bl      L0e60
        nop
        nop

// mldsa44_verify_extmu (0x18 bytes)
L4710:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L4290
        nop
        nop

// mldsa44_prepare_domain_separation_prefix (0x19c bytes)
L4730:
        cmp     x4, #0xff
        b.hi    L4790
        stp     x19, x21, [sp, #-64]!
        mov     x19, x4
        mov     x21, x0
        str     x30, [sp, #32]
        cbz     w5, L4774
        stp     x22, x23, [sp, #16]
        mov     x23, x1
        sub     w1, w5, #0x1
        mov     x0, #0x0
        cmp     w1, #0xb
        b.ls    L4798
        ldp     x22, x23, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L4774:
        strb    wzr, [x0]
        strb    w4, [x21, #1]
        cbnz    x4, L47b4
L4780:
        add     x0, x19, #0x2
L4784:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L4790:
        mov     x0, #0x0
        ret
L4798:
        .inst   0xd0000020  // adrp x0, 0xa000
        mov     x22, x2
        add     x0, x0, #0x950
        ldrb    w0, [x0, w1, uxtw]
        .inst   0x10000061  // adr     x1, 47b4 <mldsa44_prepare_domain_separation_prefix+0x84>
        add     x0, x1, w0, sxtb #2
        br      x0
L47b4:
        mov     x1, x3
        mov     x2, x4
        add     x0, x0, #0x2
        bl      L0e40
        b       L4780
        cmp     x2, #0x20
        b.ne    L4840
L47d0:
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbnz    x19, L48b0
L47e0:
        .inst   0xd0000021  // adrp x1, 0xa000
        add     x4, x1, #0x960
        mov     w3, #0x0
        nop
L47f0:
        ldr     w0, [x4]
        cmp     w5, w0
        b.eq    L4864
        add     w3, w3, #0x1
        add     x4, x4, #0x10
        cmp     w3, #0xc
        b.ne    L47f0
        add     x0, x19, #0xd
        mov     x1, x23
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e40
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
L482c:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
        cmp     x2, #0x1c
        b.eq    L47d0
L4840:
        ldp     x22, x23, [sp, #16]
        mov     x0, #0x0
        b       L4784
        cmp     x2, #0x40
        b.eq    L47d0
        b       L4840
        cmp     x2, #0x30
        b.eq    L47d0
        b       L4840
L4864:
        mov     x0, #0x4
        add     x1, x1, #0x960
        add     x3, x0, w3, uxtw #4
        add     x0, x19, #0x2
        add     x4, x1, x3
        add     x2, x21, x0
        ldr     x1, [x1, x3]
        str     x1, [x21, x0]
        mov     x1, x23
        ldur    w0, [x4, #7]
        stur    w0, [x2, #7]
        add     x0, x19, #0xd
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e40
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
        b       L482c
L48b0:
        mov     x1, x3
        mov     x2, x19
        add     x0, x21, #0x2
        str     w5, [sp, #60]
        bl      L0e40
        ldr     w5, [sp, #60]
        b       L47e0
        nop

// mldsa44_signature (0x10c bytes)
L48d0:
        stp     x19, x20, [sp, #-496]!
        mov     x20, x0
        .inst   0xf00000c7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        add     x19, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x24, x2
        stp     x25, x26, [sp, #48]
        mov     x2, #0x0
        mov     x25, x5
        str     x30, [sp, #64]
        mov     w5, #0x0
        ldr     x1, [x7]
        str     x1, [sp, #488]
        mov     x1, #0x0
        bl      L4730
        cbnz    x0, L498c
        add     x22, x19, #0x160
        mov     w26, #0xfffffff7
L492c:
        mov     x0, x20
        mov     x2, #0x974
        mov     w1, #0x0
        bl      L0e70
L493c:
        stp     xzr, xzr, [x19, #352]
        stp     xzr, xzr, [x22, #16]
        mov     x2, #0x14c
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L49d8
        ldp     x21, x22, [sp, #16]
        mov     w0, w26
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #496
        ret
L498c:
        add     x22, x19, #0x160
        mov     x21, x0
        mov     x1, #0x20
        mov     x0, x22
        mov     w26, #0xfffffffd
        bl      L0e50
        cbnz    w0, L492c
        mov     x6, x25
        mov     x4, x21
        mov     x2, x24
        mov     x1, x23
        mov     x5, x22
        mov     x3, x19
        mov     x0, x20
        mov     w7, #0x0
        bl      L3ce0
        mov     w26, w0
        cbz     w0, L493c
        b       L492c
L49d8:
        bl      L0e60
        nop

// mldsa44_verify (0xbc bytes)
L49e0:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x0
        .inst   0xf00000c6  // adrp x6, 0x1f000
        ldr     x6, [x6, #4088]
        add     x19, sp, #0x4f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        stp     x23, x30, [sp, #32]
        mov     x22, x5
        mov     x23, x2
        mov     x0, x19
        ldr     x1, [x6]
        str     x1, [sp, #408]
        mov     x1, #0x0
        mov     w5, #0x0
        mov     x2, #0x0
        bl      L4730
        cbz     x0, L4a90
        mov     x4, x0
        mov     x5, x22
        mov     x0, x20
        mov     x2, x23
        mov     x1, x21
        mov     x3, x19
        mov     w6, #0x0
        bl      L4290
        mov     w20, w0
L4a50:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4a98
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret
L4a90:
        mov     w20, #0xfffffff7
        b       L4a50
L4a98:
        bl      L0e60
        nop

// mldsa44_signature_pre_hash_internal (0xd0 bytes)
L4aa0:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x0
        .inst   0xf00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        ldr     x9, [x8]
        str     x9, [sp, #408]
        mov     x9, #0x0
        cbnz    w7, L4b24
L4ad0:
        mov     w21, #0xfffffff7
L4ad4:
        mov     x0, x20
        mov     x2, #0x974
        mov     w1, #0x0
        bl      L0e70
L4ae4:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4b6c
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #416
        ret
L4b24:
        mov     x21, x5
        mov     x22, x6
        mov     w5, w7
        mov     x0, x19
        bl      L4730
        cbz     x0, L4ad0
        mov     x5, x21
        mov     x2, x0
        mov     x6, x22
        mov     x1, x19
        mov     x0, x20
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L3ce0
        mov     w21, w0
        cbz     w0, L4ae4
        b       L4ad4
L4b6c:
        bl      L0e60

// mldsa44_signature_pre_hash_shake256 (0xbc bytes)
L4b70:
        stp     x19, x20, [sp, #-160]!
        mov     x8, x2
        mov     x2, x1
        .inst   0xf00000c7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x0
        str     x30, [sp, #48]
        mov     x21, x3
        mov     x22, x4
        mov     x3, x8
        ldr     x1, [x7]
        str     x1, [sp, #152]
        mov     x1, #0x0
        mov     x23, x5
        mov     x24, x6
        mov     x0, x19
        mov     x1, #0x40
        bl      L12a4
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w7, #0xc
        mov     x2, #0x40
        bl      L4aa0
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #152]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4c28
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
L4c28:
        bl      L0e60
        nop

// mldsa44_verify_pre_hash_internal (0xbc bytes)
L4c30:
        stp     x19, x20, [sp, #-400]!
        .inst   0xf00000c7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        str     x30, [sp, #24]
        add     x19, sp, #0x3f
        ldr     x8, [x7]
        str     x8, [sp, #392]
        mov     x8, #0x0
        and     x19, x19, #0xffffffffffffffe0
        cbz     w6, L4cdc
        mov     x20, x0
        mov     x0, x19
        str     x21, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        bl      L4730
        mov     x2, x0
        cbz     x0, L4cd8
        mov     x5, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L4290
        mov     w20, w0
        ldr     x21, [sp, #16]
L4c9c:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4ce4
        ldr     x30, [sp, #24]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret
L4cd8:
        ldr     x21, [sp, #16]
L4cdc:
        mov     w20, #0xfffffff7
        b       L4c9c
L4ce4:
        str     x21, [sp, #16]
        bl      L0e60
        nop

// mldsa44_verify_pre_hash_shake256 (0xac bytes)
L4cf0:
        stp     x19, x20, [sp, #-144]!
        mov     x7, x2
        mov     x2, x1
        .inst   0xf00000c6  // adrp x6, 0x1f000
        ldr     x6, [x6, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x0
        ldr     x1, [x6]
        str     x1, [sp, #136]
        mov     x1, #0x0
        mov     x21, x3
        mov     x22, x4
        mov     x3, x7
        mov     x23, x5
        mov     x0, x19
        mov     x1, #0x40
        bl      L12a4
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0xc
        mov     x2, #0x40
        bl      L4c30
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #136]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4d98
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret
L4d98:
        bl      L0e60
        nop

// mldsa44_pk_from_sk (0x320 bytes)
L4da0:
        mov     x12, #0x1bd0
        sub     sp, sp, x12
        .inst   0xf00000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x8, #0x1c00
        stp     x19, x20, [sp]
        mov     x20, x1
        add     x1, x1, #0x40
        add     x19, sp, #0x8f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x3, x19, x8
        sub     x2, x3, #0x140
        stp     x25, x26, [sp, #48]
        sub     x22, x3, #0xe0
        mov     x9, #0x1680
        stp     x27, x28, [sp, #64]
        mov     x10, #0x1b20
        add     x26, x19, x9
        str     x30, [sp, #80]
        add     x23, x19, x10
        mov     x21, x0
        mov     x0, x19
        ldp     q4, q5, [x1]
        ldr     x5, [x4]
        str     x5, [sp, #7112]
        mov     x5, #0x0
        ldp     q2, q3, [x20]
        add     x28, x20, #0x200
        ldp     q0, q1, [x1, #32]
        add     x1, x20, #0x80
        ldp     q6, q7, [x20, #32]
        stp     q4, q5, [x2]
        add     x24, x19, #0x1, lsl #12
        stp     q2, q3, [x22]
        stp     q6, q7, [x3, #-256]
        stp     q0, q1, [x2, #32]
        bl      L34e4
        mov     w1, #0x3
        mov     x0, x19
        bl      L3350
        mov     x2, x26
        mov     w1, #0x3
        mov     w25, w0
        mov     x0, x28
        bl      L3430
        mov     w27, w0
        mov     x0, x19
        bl      L3320
        ldp     q0, q1, [x22]
        mov     x3, x28
        mov     x4, x23
        mov     x1, x24
        mov     x2, x19
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L37a0
        mov     w22, w0
        cbz     w0, L4f50
        mov     x6, #0x1a80
        mov     x7, #0x1ac0
        add     x28, x19, x6
        add     x20, x19, x7
L4ea0:
        mov     x0, x21
        mov     x2, #0x520
        mov     w1, #0x0
        bl      L0e70
L4eb0:
        mov     x0, x24
        mov     x2, #0x680
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1000
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        mov     x0, #0x1b00
        add     x19, x19, x0
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        movi    v0.4s, #0x0
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     xzr, xzr, [x23]
        stp     xzr, xzr, [x23, #16]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7112]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L50bc
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
L4f50:
        movi    v1.4s, #0x0
        add     x20, x20, #0x380
        mov     x0, x24
        add     x1, x24, #0x680
        mov     v2.16b, v1.16b
        nop
L4f68:
        ldr     q0, [x20], #16
        ldr     q3, [x0], #16
        eor     v0.16b, v0.16b, v3.16b
        orr     v2.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v0.16b
        cmp     x1, x0
        b.ne    L4f68
        movi    v0.4s, #0x0
        ext     v4.16b, v2.16b, v0.16b, #8
        ext     v3.16b, v1.16b, v0.16b, #8
        orr     v4.16b, v4.16b, v2.16b
        eor     v3.16b, v3.16b, v1.16b
        ext     v2.16b, v4.16b, v0.16b, #4
        ext     v1.16b, v3.16b, v0.16b, #4
        orr     v2.16b, v2.16b, v4.16b
        eor     v1.16b, v1.16b, v3.16b
        ext     v4.16b, v2.16b, v0.16b, #2
        ext     v3.16b, v1.16b, v0.16b, #2
        orr     v4.16b, v4.16b, v2.16b
        eor     v3.16b, v3.16b, v1.16b
        ext     v1.16b, v4.16b, v0.16b, #1
        ext     v2.16b, v3.16b, v0.16b, #1
        orr     v1.16b, v1.16b, v4.16b
        eor     v2.16b, v2.16b, v3.16b
        umov    w0, v1.b[0]
        umov    w1, v2.b[0]
        neg     x0, x0
        asr     x0, x0, #32
        eor     w0, w1, w0
        and     w0, w0, #0xff
        mov     x5, #0x1ac0
        eor     w4, w0, w1
        mov     x2, #0x1a80
        add     x28, x19, x2
        add     x20, x19, x5
        mov     x0, x28
        mov     x2, x21
        mov     x1, #0x40
        mov     x3, #0x520
        str     w4, [sp, #108]
        bl      L12a4
        movi    v0.4s, #0x0
        ldr     w4, [sp, #108]
        mov     x0, x28
        add     x2, x28, #0x40
        mov     x1, x20
        mov     v2.16b, v0.16b
L5024:
        ldr     q1, [x0], #16
        ldr     q3, [x1], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x0, x2
        b.ne    L5024
        movi    v1.4s, #0x0
        ext     v5.16b, v2.16b, v1.16b, #8
        ext     v3.16b, v0.16b, v1.16b, #8
        orr     v5.16b, v5.16b, v2.16b
        eor     v2.16b, v3.16b, v0.16b
        ext     v4.16b, v5.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v5.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #2
        ext     v2.16b, v0.16b, v1.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v3.16b, v1.16b, #1
        ext     v1.16b, v2.16b, v1.16b, #1
        orr     v0.16b, v0.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w0, v0.b[0]
        umov    w1, v1.b[0]
        neg     x0, x0
        asr     x0, x0, #32
        eor     w0, w1, w0
        and     w0, w0, #0xff
        orr     w25, w25, w27
        eor     w0, w0, w1
        orr     w0, w4, w0
        orr     w0, w0, w25
        tst     w0, #0xff
        b.eq    L4eb0
        mov     w22, #0xfffffff9
        b       L4ea0
L50bc:
        bl      L0e60

// mldsa65_unpack_pk_t1 (0x14 bytes)
L50c0:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #6
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L24d0

// mldsa65_pack_sk_rho_key_tr (0x28 bytes)
L50d4:
        ldp     q0, q1, [x1]
        add     x4, x0, #0x40
        stp     q0, q1, [x0]
        ldp     q0, q1, [x3]
        stp     q0, q1, [x0, #32]
        ldp     q0, q1, [x2]
        stp     q0, q1, [x4]
        ldp     q0, q1, [x2, #32]
        stp     q0, q1, [x4, #32]
        ret
        nop

// mldsa65_unpack_sk (0x40 bytes)
L5100:
        ldp     q0, q1, [x6]
        add     x7, x6, #0x40
        add     x10, x6, #0x80
        add     x9, x6, #0x300
        add     x8, x6, #0x600
        stp     q0, q1, [x0]
        ldp     q0, q1, [x6, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x7]
        stp     q0, q1, [x1]
        ldp     q0, q1, [x7, #32]
        stp     q0, q1, [x1, #32]
        str     x10, [x4]
        str     x9, [x5]
        str     x8, [x3]
        ret

// mldsa65_pack_sig_c (0x14 bytes)
L5140:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldr     q0, [x1, #32]
        str     q0, [x0, #32]
        ret

// mldsa65_pack_sig_h (0xec bytes)
L5154:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-96]!
        mov     x20, x3
        stp     x25, x26, [sp, #48]
        add     x26, x0, #0xcb0
        mov     w19, #0x0
        stp     x21, x22, [sp, #16]
        mov     x21, x1
        mov     w25, #0x3ff00
        stp     x23, x24, [sp, #32]
        add     x23, x0, #0xce7
        add     x24, x2, #0x300
        stp     x27, x28, [sp, #64]
        mov     w27, #0x100
        mov     x28, x2
        str     x30, [sp, #80]
        mov     w22, #0x7fe00
        movk    w27, #0xfffc, lsl #16
        str     q0, [x26, #32]
        stp     q0, q0, [x26]
        stur    q0, [x26, #45]
L51a8:
        mov     x1, x28
        mov     x0, x20
        bl      L28f4
        mov     x4, #0x0
        b       L51d4
L51bc:
        cmp     w7, #0x0
        ccmp    w5, w27, #0x0, ne
        b.eq    L51e8
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.eq    L5204
L51d4:
        ldr     w5, [x21, x4, lsl #2]
        ldr     w7, [x20, x4, lsl #2]
        add     w6, w5, w25
        cmp     w6, w22
        b.ls    L51bc
L51e8:
        cmp     w19, #0x37
        b.eq    L5220
        strb    w4, [x26, w19, uxtw]
        add     x4, x4, #0x1
        add     w19, w19, #0x1
        cmp     x4, #0x100
        b.ne    L51d4
L5204:
        add     x28, x28, #0x80
        strb    w19, [x23], #1
        add     x21, x21, #0x400
        cmp     x28, x24
        b.ne    L51a8
        mov     w0, #0x0
        b       L5224
L5220:
        mov     w0, #0xffffffff
L5224:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret

// mldsa65_pack_sig_z (0x14 bytes)
L5240:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #7
        add     x2, x2, #0x30
        add     x0, x0, x2
        b       L5960

// mldsa65_sig_unpack_hints (0x100 bytes)
L5254:
        stp     x19, x20, [sp, #-48]!
        mov     x6, x0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        add     x22, x1, #0xcb0
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        mov     w23, w2
        cbz     w2, L5280
        add     w0, w2, #0x36
        ldrb    w21, [x22, w0, uxtw]
L5280:
        add     w0, w23, #0x37
        ldrb    w20, [x22, w0, uxtw]
        cmp     w20, #0x37
        ccmp    w21, w20, #0x2, ls
        b.hi    L52f4
        mov     x0, x6
        mov     w1, #0x0
        mov     x2, #0x400
        bl      L0e70
        add     x3, x19, w21, uxtb
        mov     x6, x0
        mov     w1, w21
        mov     w7, #0x1
        cmp     w21, w20
        b.cs    L5308
        nop
L52c0:
        ldrb    w4, [x3, #3248]
        mov     w5, w1
        add     w1, w1, #0x1
        add     x3, x3, #0x1
        str     w7, [x6, x4, lsl #2]
        cmp     w20, w1
        b.ls    L5308
        cmp     w21, w1
        b.cs    L52c0
        ldrb    w0, [x22, w5, uxtw]
        ldrb    w4, [x3, #3248]
        cmp     w4, w0
        b.hi    L52c0
L52f4:
        mov     w0, #0xffffffff
L52f8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L5308:
        cmp     w23, #0x5
        b.eq    L5324
L5310:
        mov     w0, #0x0
L5314:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L5324:
        cmp     w20, #0x37
        b.eq    L5310
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbnz    w0, L52f4
L5338:
        cmp     w20, #0x37
        b.eq    L5314
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbz     w0, L5338
        mov     w0, #0xffffffff
        b       L52f8
        nop
        nop
        nop

// mld_rej_eta_c65.constprop.0 (0x88 bytes)
L5360:
        mov     x9, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    L53e4
        mov     w10, #0x1
        sub     w10, w10, w2
        mov     w5, #0x4
        nop
L5380:
        ldrb    w4, [x2]
        add     w6, w10, w2
        add     x2, x2, #0x1
        and     w1, w4, #0xf
        lsr     w4, w4, #4
        sub     w7, w5, w1
        sub     w8, w5, w4
        cmp     w1, #0x8
        b.hi    L53ac
        str     w7, [x9, w0, uxtw #2]
        add     w0, w0, #0x1
L53ac:
        cmp     w0, #0xff
        add     w7, w0, #0x1
        cset    w1, ls
        cmp     w1, #0x0
        ccmp    w4, #0x8, #0x2, ne
        b.hi    L53d4
        cmp     w7, #0xff
        str     w8, [x9, w0, uxtw #2]
        cset    w1, ls
        mov     w0, w7
L53d4:
        cmp     w6, w3
        cset    w4, cc
        tst     w1, w4
        b.ne    L5380
L53e4:
        ret
        nop
        nop

// mldsa65_poly_decompose (0x64 bytes)
L53f0:
        mov     x5, #0x0
        mov     w7, #0x3ff000
        mov     w6, #0xff801fff
        nop
L5400:
        ldr     w3, [x1, x5]
        add     w2, w3, #0x7f
        asr     w2, w2, #7
        add     w2, w2, w2, lsl #10
        add     w2, w2, #0x200, lsl #12
        ubfx    x2, x2, #22, #4
        str     w2, [x0, x5]
        sub     w2, w2, w2, lsl #10
        add     w2, w3, w2, lsl #9
        sub     w3, w7, w2
        sxtw    x3, w3
        asr     x3, x3, #31
        add     w4, w2, w6
        eor     w4, w4, w2
        and     w3, w4, w3
        eor     w2, w3, w2
        str     w2, [x1, x5]
        add     x5, x5, #0x4
        cmp     x5, #0x400
        b.ne    L5400
        ret

// mldsa65_poly_use_hint (0x7c bytes)
L5454:
        mov     x6, #0x0
        mov     w10, #0x3ff000
        mov     w9, #0xff801fff
L5460:
        ldr     w3, [x0, x6]
        add     w2, w3, #0x7f
        asr     w2, w2, #7
        add     w2, w2, w2, lsl #10
        add     w2, w2, #0x200, lsl #12
        ubfx    x2, x2, #22, #4
        sub     w5, w2, w2, lsl #10
        add     w5, w3, w5, lsl #9
        sub     w3, w10, w5
        sxtw    x3, w3
        asr     x3, x3, #31
        add     w4, w5, w9
        add     w7, w2, #0x1
        eor     w4, w4, w5
        sub     w8, w2, #0x1
        and     w3, w4, w3
        ldr     w4, [x1, x6]
        eor     w3, w3, w5
        and     w7, w7, #0xf
        cmp     w3, #0x0
        and     w8, w8, #0xf
        cbz     w4, L54bc
        csel    w2, w8, w7, le
L54bc:
        str     w2, [x0, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L5460
        ret

// mldsa65_poly_uniform_eta_4x (0x26c bytes)
L54d0:
        sub     sp, sp, #0x9d0
        mov     x8, x4
        .inst   0xd00000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0xaf
        and     x22, x22, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x9, x22, #0x480
        add     x19, x22, #0x4e0
        stp     x25, x26, [sp, #48]
        add     x20, x22, #0x540
        add     x21, x22, #0x5a0
        stp     x27, x28, [sp, #64]
        add     x26, sp, #0x6a8
        mov     x28, x9
        str     x30, [sp, #80]
        add     x23, x22, #0x360
        str     x9, [sp, #136]
        add     x24, x22, #0x240
        ldp     q2, q3, [x8, #32]
        add     x25, x22, #0x120
        ldp     q0, q1, [x8]
        ldr     x8, [x4]
        str     x8, [sp, #2504]
        mov     x8, #0x0
        ldrb    w4, [sp, #2512]
        mov     w27, #0xff
        stp     q2, q3, [x9, #32]
        stp     q2, q3, [x19, #32]
        stp     q0, q1, [x19]
        stp     q0, q1, [x20]
        stp     q2, q3, [x20, #32]
        stp     x0, x1, [sp, #104]
        mov     x0, x26
        stp     x2, x3, [sp, #120]
        stp     q0, q1, [x21]
        stp     q2, q3, [x21, #32]
        stp     q0, q1, [x9]
        strb    w5, [x9, #64]
        strb    wzr, [x9, #65]
        strb    w6, [x9, #160]
        strb    wzr, [x9, #161]
        strb    w7, [x9, #256]
        strb    wzr, [x9, #257]
        strb    w4, [x9, #352]
        strb    wzr, [x9, #353]
        bl      L1550
        mov     x4, x21
        mov     x3, x20
        mov     x2, x19
        mov     x1, x28
        mov     x0, x26
        mov     x5, #0x42
        bl      L1340
        mov     x5, x26
        mov     x4, #0x2
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L14c0
        ldr     x0, [sp, #104]
        mov     w3, #0x110
        mov     x2, x22
        mov     w1, #0x0
        bl      L5360
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     x2, x25
        mov     w1, #0x0
        bl      L5360
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     x2, x24
        mov     w1, #0x0
        bl      L5360
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, #0x0
        mov     x2, x23
        bl      L5360
        mov     w28, w0
        cmp     w21, w27
        ccmp    w0, w27, #0x0, hi
        cset    w0, ls
        cmp     w20, w27
        ccmp    w19, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0, L56d0
L5640:
        mov     x5, x26
        mov     x4, #0x1
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L14c0
        ldr     x0, [sp, #104]
        mov     w3, #0x88
        mov     w1, w19
        mov     x2, x22
        bl      L5360
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x25
        bl      L5360
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     w1, w21
        mov     x2, x24
        bl      L5360
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, w28
        mov     x2, x23
        bl      L5360
        cmp     w0, #0xff
        ccmp    w21, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0, L5640
L56d0:
        mov     x0, x26
        bl      L1554
        mov     x0, x22
        mov     x2, #0x480
        mov     w1, #0x0
        bl      L0e70
        ldr     x19, [sp, #136]
        mov     x2, #0x180
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2504]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5738
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x9d0
        ret
L5738:
        bl      L0e60
        nop

// mldsa65_poly_challenge (0x168 bytes)
L5740:
        stp     x19, x20, [sp, #-448]!
        mov     x19, x1
        .inst   0xd00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        add     x2, sp, #0x5f
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0xe8
        and     x20, x2, #0xffffffffffffffe0
        stp     x23, x30, [sp, #32]
        mov     x23, x0
        ldr     x0, [x3]
        str     x0, [sp, #440]
        mov     x0, #0x0
        mov     x0, x21
        bl      L1094
        mov     x1, x19
        mov     x2, #0x30
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x88
        bl      L11d0
        mov     x2, x20
        mov     w0, #0x0
        mov     x3, #0x0
L57b0:
        ldrb    w1, [x2], #1
        lsl     x1, x1, x0
        add     w0, w0, #0x8
        orr     x3, x3, x1
        cmp     w0, #0x40
        b.ne    L57b0
        mov     x0, x23
        mov     x2, #0x400
        mov     w1, #0x0
        str     x3, [sp, #56]
        bl      L0e70
        mov     x19, #0xcf
        mov     w22, #0x1
        mov     w0, #0x8
        b       L57fc
L57ec:
        ldrb    w1, [x20, w0, uxtw]
        add     w0, w0, #0x1
        cmp     w1, w19
        b.ls    L5824
L57fc:
        cmp     w0, #0x88
        b.ne    L57ec
        mov     x0, x20
        mov     x1, #0x88
        mov     x2, x21
        bl      L11d0
        ldrb    w1, [x20]
        mov     w0, #0x1
        cmp     w1, w19
        b.hi    L57ec
L5824:
        ldr     x2, [sp, #56]
        ldr     w4, [x23, x1, lsl #2]
        str     w4, [x23, x19, lsl #2]
        add     x19, x19, #0x1
        ubfiz   x3, x2, #1, #1
        lsr     x2, x2, #1
        sub     w3, w22, w3
        str     w3, [x23, x1, lsl #2]
        str     x2, [sp, #56]
        cmp     x19, #0x100
        b.ne    L57fc
        mov     x0, x21
        bl      L1280
        movi    v0.4s, #0x0
        str     xzr, [x20, #128]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        add     x0, sp, #0x38
        str     xzr, [sp, #56]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #440]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L58a4
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #448
        ret
L58a4:
        bl      L0e60
        nop
        nop

// mldsa65_polyeta_pack (0x74 bytes)
L58b0:
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        add     x5, x1, #0x400
        mov     w4, #0x4
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
L58d0:
        ldr     w2, [x1, #4]
        ldr     w3, [x1], #8
        sub     w2, w4, w2
        sub     w3, w4, w3
        ubfiz   w2, w2, #4, #8
        orr     w2, w2, w3
        strb    w2, [x0], #1
        cmp     x5, x1
        b.ne    L58d0
        add     x0, sp, #0x10
        str     xzr, [sp, #16]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5920
        ldr     x30, [sp], #32
        ret
L5920:
        bl      L0e60

// mldsa65_polyeta_unpack (0x3c bytes)
L5924:
        add     x5, x0, #0x400
        mov     w4, #0x4
        nop
L5930:
        ldrb    w2, [x1]
        add     x0, x0, #0x8
        and     w2, w2, #0xf
        stur    w2, [x0, #-8]
        sub     w2, w4, w2
        ldrb    w3, [x1], #1
        stur    w2, [x0, #-8]
        sub     w2, w4, w3, lsr #4
        stur    w2, [x0, #-4]
        cmp     x0, x5
        b.ne    L5930
        ret

// mldsa65_polyz_pack (0x94 bytes)
L5960:
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x7, x0, #0x280
        mov     w5, #0x80000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
L5980:
        ldp     w3, w2, [x1]
        add     x0, x0, #0x5
        add     x1, x1, #0x8
        sub     w2, w5, w2
        sub     w3, w5, w3
        sturb   w3, [x0, #-5]
        ubfiz   w4, w2, #4, #4
        lsr     w6, w2, #4
        orr     w4, w4, w3, lsr #16
        lsr     w2, w2, #12
        lsr     w3, w3, #8
        sturb   w3, [x0, #-4]
        sturb   w4, [x0, #-3]
        sturb   w6, [x0, #-2]
        sturb   w2, [x0, #-1]
        cmp     x7, x0
        b.ne    L5980
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L59f0
        ldr     x30, [sp], #48
        ret
L59f0:
        bl      L0e60

// mldsa65_polyz_unpack (0x74 bytes)
L59f4:
        add     x6, x1, #0x280
        mov     w5, #0x80000
        nop
L5a00:
        ldrb    w2, [x1]
        add     x1, x1, #0x5
        str     w2, [x0]
        add     x0, x0, #0x8
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
        orr     w2, w4, w3, lsl #12
        sub     w2, w5, w2
        stur    w2, [x0, #-4]
        cmp     x6, x1
        b.ne    L5a00
        ret
        nop
        nop

// mldsa65_poly_uniform_gamma1 (0xe4 bytes)
L5a70:
        sub     sp, sp, #0x430
        .inst   0xd00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x4f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x19, x20, #0x2c0
        add     x21, sp, #0x358
        str     x30, [sp, #32]
        mov     x22, x0
        mov     x0, x21
        ldp     q2, q3, [x1]
        ldr     x4, [x3]
        str     x4, [sp, #1064]
        mov     x4, #0x0
        ldp     q0, q1, [x1, #32]
        stp     q2, q3, [x19]
        stp     q0, q1, [x19, #32]
        strh    w2, [x20, #768]
        bl      L1094
        mov     x1, x19
        mov     x2, #0x42
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x2a8
        bl      L11d0
        mov     x1, x20
        mov     x0, x22
        bl      L59f4
        mov     x0, x21
        bl      L1280
        mov     x0, x20
        mov     x2, #0x2a8
        mov     w1, #0x0
        bl      L0e70
        movi    v0.4s, #0x0
        strh    wzr, [x19, #64]
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1064]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5b50
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x430
        ret
L5b50:
        bl      L0e60
        nop
        nop
        nop

// mldsa65_polyvecl_ntt (0x38 bytes)
L5b60:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1400
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L5b78:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20f0
        cmp     x19, x20
        b.ne    L5b78
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa65_polyvecl_chknorm (0x50 bytes)
L5ba0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1400
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
L5bc0:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L27c4
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L5bc0
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa65_polyveck_reduce (0x38 bytes)
L5bf0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L5c08:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2000
        cmp     x19, x20
        b.ne    L5c08
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa65_polyveck_caddq (0x38 bytes)
L5c30:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L5c48:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2030
        cmp     x19, x20
        b.ne    L5c48
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa65_polyveck_invntt_tomont (0x38 bytes)
L5c70:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L5c88:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L21c0
        cmp     x19, x20
        b.ne    L5c88
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa65_polyveck_unpack_eta_chknorm (0x5c bytes)
L5cb0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x20, x2
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L5cd0:
        mov     x1, x19
        mov     x0, x20
        bl      L5924
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x80
        bl      L27c4
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L5cd0
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
        nop

// mldsa65_polyveck_decompose_pack_w1 (0x58 bytes)
L5d10:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        mov     x0, #0x1800
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, x0
        str     x30, [sp, #32]
L5d30:
        mov     x1, x19
        mov     x0, x21
        bl      L53f0
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2870
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L5d30
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
        nop
        nop

// mldsa65_polyvecl_unpack_eta (0x40 bytes)
L5d70:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1400
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L5d88:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L5924
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L5d88
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvecl_unpack_z (0x40 bytes)
L5db0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0xc80
        nop
L5dc8:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x280
        bl      L59f4
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L5dc8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvec_matrix_expand_lazy (0x10 bytes)
L5df0:
        ldp     q0, q1, [x1]
        add     x0, x0, #0x400
        stp     q0, q1, [x0]
        ret

// mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy (0xf0 bytes)
L5e00:
        stp     x19, x20, [sp, #-160]!
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        add     x22, x2, #0x400
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        and     w24, w3, #0xff
        stp     x25, x30, [sp, #48]
        mov     x25, x2
        mov     x1, x19
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        mov     x23, x0
        ldr     q0, [x20, #1024]
        ldr     x3, [x2]
        str     x3, [sp, #152]
        mov     x3, #0x0
        ldr     q1, [x20, #1040]
        strb    wzr, [x19, #32]
        strb    w24, [x19, #33]
        mov     w21, #0x1
        stp     q0, q1, [x19]
        bl      L2370
        mov     x1, x25
        mov     x0, x23
        bl      L22e0
L5e6c:
        mov     x1, x19
        mov     x0, x20
        strb    w21, [x19, #32]
        add     w21, w21, #0x1
        strb    w24, [x19, #33]
        bl      L2370
        mov     x1, x22
        mov     x0, x20
        bl      L22e0
        add     x22, x22, #0x400
        mov     x1, x20
        mov     x0, x23
        bl      L2070
        cmp     w21, #0x5
        b.ne    L5e6c
        mov     x0, x23
        bl      L2000
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5eec
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
L5eec:
        bl      L0e60

// mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy (0x144 bytes)
L5ef0:
        stp     x19, x20, [sp, #-176]!
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x24, x3
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0x6f
        and     x21, x21, #0xffffffffffffffe0
        stp     x25, x26, [sp, #48]
        mov     x26, x0
        mov     x25, x2
        str     x30, [sp, #64]
        mov     w22, #0x0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     q0, [x23, #1024]
        ldr     x1, [x0]
        str     x1, [sp, #168]
        mov     x1, #0x0
        ldr     q1, [x23, #1040]
        stp     q0, q1, [x21]
L5f40:
        ldrh    w2, [x25, #8]
        ldr     x1, [x25]
        add     w2, w22, w2
        mov     x0, x24
        mov     x20, x26
        mov     w19, #0x0
        bl      L5a70
        mov     x0, x24
        bl      L20f0
        b       L5fa0
L5f68:
        mov     x0, x23
        strb    w22, [x21, #32]
        strb    w19, [x21, #33]
        bl      L2370
        mov     x1, x24
        mov     x0, x23
        bl      L22e0
        add     w19, w19, #0x1
        mov     x0, x20
        mov     x1, x23
        bl      L2070
        add     x20, x20, #0x400
        cmp     w19, #0x6
        b.eq    L5fd4
L5fa0:
        mov     x1, x21
        cbnz    w22, L5f68
        mov     x0, x20
        strb    wzr, [x21, #32]
        strb    w19, [x21, #33]
        bl      L2370
        mov     x0, x20
        mov     x1, x24
        add     w19, w19, #0x1
        bl      L22e0
        add     x20, x20, #0x400
        cmp     w19, #0x6
        b.ne    L5fa0
L5fd4:
        add     w22, w22, #0x1
        cmp     w22, #0x5
        b.ne    L5f40
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        mov     x0, x26
        bl      L5bf0
        mov     x0, x26
        bl      L5c70
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #168]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6030
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #176
        ret
L6030:
        bl      L0e60
        nop
        nop
        nop

// mld_compute_pack_t0_t165 (0x154 bytes)
L6040:
        sub     sp, sp, #0xc90
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        mov     w21, #0x0
        .inst   0xb00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        stp     x23, x24, [sp, #32]
        mov     x23, x2
        mov     x24, x1
        stp     x25, x26, [sp, #48]
        add     x26, sp, #0x6f
        and     x26, x26, #0xffffffffffffffe0
        str     x30, [sp, #64]
        mov     x25, x0
        add     x19, x26, #0x820
        add     x20, x26, #0x420
        ldr     x2, [x3]
        str     x2, [sp, #3208]
        mov     x2, #0x0
        mov     x1, x4
        mov     x0, x26
        bl      L5df0
        nop
L60a0:
        mov     w3, w21
        mov     x2, x23
        mov     x1, x26
        mov     x0, x19
        bl      L5e00
        add     w21, w21, #0x1
        mov     x0, x19
        bl      L21c0
        mov     x1, x22
        mov     x0, x20
        bl      L5924
        add     x22, x22, #0x80
        mov     x1, x20
        mov     x0, x19
        bl      L2070
        mov     x0, x19
        bl      L2000
        mov     x0, x19
        bl      L2030
        mov     x2, x19
        mov     x1, x19
        mov     x0, x20
        bl      L2330
        mov     x0, x25
        mov     x1, x20
        bl      L2474
        add     x25, x25, #0x140
        mov     x0, x24
        mov     x1, x19
        bl      L2544
        add     x24, x24, #0x1a0
        cmp     w21, #0x6
        b.ne    L60a0
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x420
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e70
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3208]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6190
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, #0xc90
        ret
L6190:
        bl      L0e60

// mld_H65 (0x10c bytes)
L6194:
        stp     x19, x20, [sp, #-304]!
        mov     x20, x7
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x58
        stp     x23, x24, [sp, #32]
        mov     x22, x0
        mov     x24, x2
        stp     x25, x26, [sp, #48]
        mov     x23, x1
        mov     x25, x3
        stp     x27, x30, [sp, #64]
        mov     x21, x5
        mov     x26, x4
        ldr     x0, [x8]
        str     x0, [sp, #296]
        mov     x0, #0x0
        mov     x27, x6
        mov     x0, x19
        bl      L1094
        mov     x2, x25
        mov     x1, x24
        mov     x0, x19
        bl      L10c0
        cbnz    x21, L6274
        cbnz    x20, L6288
L6200:
        mov     x0, x19
        bl      L1150
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L11d0
        mov     x0, x19
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     q0, [x19, #192]
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L629c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret
L6274:
        mov     x2, x21
        mov     x1, x26
        mov     x0, x19
        bl      L10c0
        cbz     x20, L6200
L6288:
        mov     x2, x20
        mov     x1, x27
        mov     x0, x19
        bl      L10c0
        b       L6200
L629c:
        bl      L0e60

// mldsa65_keypair_internal (0x2a0 bytes)
L62a0:
        mov     x12, #0x1580
        sub     sp, sp, x12
        mov     x3, #0x14c0
        mov     x4, #0x1400
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x8f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x22, x19, x3
        add     x21, x19, x4
        stp     x23, x24, [sp, #48]
        mov     w4, #0x506
        mov     x23, x0
        stp     x25, x26, [sp, #64]
        mov     x20, x1
        add     x25, x19, #0x800
        stp     x27, x28, [sp, #80]
        add     x26, x19, #0xc00
        add     x27, x21, #0x20
        str     x30, [sp, #96]
        mov     x3, #0x22
        mov     x1, #0x80
        add     x24, x19, #0x400
        ldp     q0, q1, [x2]
        add     x28, x19, #0x1, lsl #12
        .inst   0xb00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #5496]
        mov     x0, #0x0
        stp     q0, q1, [x22]
        mov     x2, x22
        mov     x0, x21
        strh    w4, [x19, #5344]
        bl      L12a4
        mov     x2, x25
        mov     x4, x27
        mov     x3, x26
        mov     w0, #0xa
        strb    w0, [sp]
        mov     w7, #0x9
        mov     w6, #0x8
        mov     w5, #0x7
        mov     x1, x24
        mov     x0, x19
        bl      L54d0
        mov     x1, x19
        add     x0, x20, #0x400
        bl      L58b0
        mov     x1, x24
        add     x0, x20, #0x480
        bl      L58b0
        mov     x1, x25
        add     x0, x20, #0x500
        bl      L58b0
        mov     x1, x26
        add     x0, x20, #0x580
        bl      L58b0
        mov     x3, x25
        mov     x2, x24
        mov     x4, x27
        mov     w0, #0xffffffff
        strb    w0, [sp]
        mov     w7, #0x6
        mov     w6, #0x5
        mov     w5, #0x4
        mov     x0, x28
        mov     x1, x19
        bl      L54d0
        mov     x1, x28
        add     x0, x20, #0x280
        add     x28, x20, #0x300
        bl      L58b0
        mov     x1, x19
        mov     x0, x28
        bl      L58b0
        mov     x1, x24
        add     x0, x20, #0x380
        bl      L58b0
        mov     x2, x25
        mov     x4, x27
        mov     x3, x26
        mov     w0, #0x3
        strb    w0, [sp]
        mov     w5, #0x0
        mov     w7, #0x2
        mov     w6, #0x1
        mov     x1, x24
        mov     x0, x19
        bl      L54d0
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L58b0
        mov     x1, x24
        add     x0, x20, #0x100
        bl      L58b0
        mov     x1, x25
        add     x0, x20, #0x180
        bl      L58b0
        mov     x1, x26
        add     x0, x20, #0x200
        bl      L58b0
        mov     x0, x19
        bl      L5b60
        ldp     q0, q1, [x21]
        mov     x3, x28
        mov     x4, x21
        mov     x2, x19
        add     x1, x20, #0x600
        add     x0, x23, #0x20
        stp     q0, q1, [x23]
        bl      L6040
        mov     x5, #0x1480
        mov     w25, w0
        add     x24, x19, x5
        cbnz    w0, L6498
        mov     x0, x24
        mov     x2, x23
        mov     x3, #0x7a0
        mov     x1, #0x40
        bl      L12a4
        mov     x2, x24
        add     x3, x21, #0x60
        mov     x1, x21
        mov     x0, x20
        bl      L50d4
L6498:
        mov     x0, x19
        mov     x2, #0x1400
        mov     w1, #0x0
        bl      L0e70
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     xzr, xzr, [x22]
        stp     xzr, xzr, [x22, #16]
        strh    wzr, [x22, #32]
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        cbnz    w25, L6518
L64d4:
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5496]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L653c
        ldp     x19, x20, [sp, #16]
        mov     w0, w25
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x1580
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L6518:
        mov     x0, x23
        mov     x2, #0x7a0
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0xfc0
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e70
        b       L64d4
L653c:
        bl      L0e60

// mldsa65_keypair (0x88 bytes)
L6540:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        .inst   0xb00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        ldr     x1, [x2]
        str     x1, [sp, #88]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e50
        cbnz    w0, L65bc
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L62a0
L658c:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xb00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L65c4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L65bc:
        mov     w0, #0xfffffffd
        b       L658c
L65c4:
        bl      L0e60
        nop
        nop

// mldsa65_signature_internal (0x4f8 bytes)
L65d0:
        mov     x12, #0x2e70
        sub     sp, sp, x12
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        mov     x12, #0x2b20
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0xcf
        and     x22, x22, #0xffffffffffffffe0
        add     x9, x22, x12
        mov     x13, #0x2c80
        mov     x14, #0x2cc0
        add     x10, x22, x13
        add     x11, x22, x14
        mov     x15, #0x2ca0
        add     x12, x22, x15
        stp     x19, x20, [sp]
        mov     x21, x4
        stp     x23, x24, [sp, #32]
        mov     x20, x3
        mov     x24, x1
        stp     x25, x26, [sp, #48]
        mov     w25, w7
        add     x26, x9, #0x20
        stp     x27, x28, [sp, #64]
        mov     x23, x2
        mov     x19, x5
        str     x30, [sp, #80]
        mov     x1, x26
        str     x0, [sp, #96]
        mov     x27, x9
        str     x9, [sp, #128]
        add     x2, x9, #0x60
        stp     x12, x11, [sp, #152]
        mov     x5, x10
        mov     x4, x11
        str     x10, [sp, #168]
        mov     x3, x12
        mov     x0, x9
        ldr     x7, [x8]
        str     x7, [sp, #11880]
        mov     x7, #0x0
        bl      L5100
        cbnz    w25, L6aa8
        mov     x3, #0x40
        mov     x7, x23
        mov     x6, x24
        mov     x5, x21
        mov     x4, x20
        mov     x2, x26
        add     x0, x27, #0x80
        mov     x1, x3
        bl      L6194
L66a0:
        ldr     x23, [sp, #128]
        mov     x0, #0x2c00
        mov     x2, #0x2c60
        mov     x8, #0x2020
        mov     x9, #0x1c20
        mov     x10, #0x2820
        add     x26, x22, x0
        add     x0, x22, x2
        mov     x1, #0x2420
        mov     x6, #0x2d98
        mov     x7, #0x2c20
        str     x0, [sp, #120]
        add     x0, x22, x10
        mov     x4, x19
        mov     x5, #0x20
        add     x19, x22, x1
        mov     x3, x5
        add     x21, sp, x6
        add     x28, x22, x7
        add     x24, x22, x8
        mov     x7, #0x40
        add     x20, x22, x9
        mov     x1, x7
        add     x6, x23, #0x80
        add     x2, x23, #0x60
        str     x0, [sp, #112]
        add     x0, x23, #0xc0
        str     x0, [sp, #144]
        bl      L6194
        str     wzr, [sp, #108]
        mov     x11, #0x1800
        mov     x1, x23
        add     x0, x22, x11
        str     x0, [sp, #136]
        bl      L5df0
        nop
L6730:
        ldp     x1, x4, [sp, #136]
        str     x4, [x26, #96]
        ldr     x2, [sp, #120]
        mov     x3, x19
        ldrh    w4, [sp, #108]
        mov     x0, x22
        strh    w4, [x26, #104]
        bl      L5ef0
        mov     x0, x22
        bl      L5c30
        ldr     x23, [sp, #112]
        mov     x2, x19
        mov     x1, x22
        mov     x0, x23
        bl      L5d10
        mov     x0, x21
        bl      L1094
        ldr     x0, [sp, #128]
        mov     x2, #0x40
        add     x1, x0, #0x80
        mov     x0, x21
        bl      L10c0
        mov     x1, x23
        mov     x2, #0x300
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x1, #0x30
        mov     x0, x28
        bl      L11d0
        mov     x0, x21
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        str     q0, [x21, #192]
        mov     x1, x28
        mov     x0, x24
        bl      L5740
        mov     x23, #0x0
        mov     x0, x24
        bl      L20f0
L67f0:
        ldr     x1, [x22, #11456]
        mov     x0, x20
        add     x1, x1, x23, lsl #7
        bl      L5924
        mov     x0, x20
        bl      L20f0
        mov     x1, x24
        mov     x0, x20
        bl      L22e0
        mov     x0, x20
        bl      L21c0
        ldr     x1, [x26, #96]
        mov     x0, x19
        ldrh    w2, [x26, #104]
        add     w2, w2, w23
        bl      L5a70
        mov     x1, x19
        mov     x0, x20
        bl      L2070
        mov     x0, x20
        bl      L2000
        mov     w1, #0xff3c
        mov     x0, x20
        movk    w1, #0x7, lsl #16
        bl      L27c4
        cbnz    w0, L6aa0
        ldr     x0, [sp, #96]
        mov     w2, w23
        mov     x1, x20
        add     x23, x23, #0x1
        bl      L5240
        cmp     x23, #0x5
        b.ne    L67f0
        mov     x23, x22
        mov     x25, #0x0
        mov     x27, #0x0
L6880:
        ldr     x1, [x22, #11392]
        mov     x0, x19
        add     x1, x1, x27
        bl      L5924
        mov     x0, x19
        bl      L20f0
        mov     x1, x24
        mov     x0, x19
        bl      L22e0
        mov     x0, x19
        bl      L21c0
        mov     x1, x19
        mov     x0, x23
        bl      L20a0
        mov     x0, x23
        bl      L2000
        mov     w1, #0xfe3c
        mov     x0, x23
        movk    w1, #0x3, lsl #16
        bl      L27c4
        cbnz    w0, L6aa0
        ldr     x1, [x22, #11424]
        mov     x0, x19
        add     x1, x1, x25
        bl      L2670
        mov     x0, x19
        bl      L20f0
        mov     x1, x24
        mov     x0, x19
        bl      L22e0
        mov     x0, x19
        bl      L21c0
        mov     x0, x19
        bl      L2000
        mov     x0, x19
        mov     w1, #0x3ff00
        bl      L27c4
        cbnz    w0, L6aa0
        mov     x0, x23
        mov     x1, x19
        add     x25, x25, #0x1a0
        bl      L2070
        add     x27, x27, #0x80
        add     x23, x23, #0x400
        cmp     x25, #0x9c0
        b.ne    L6880
        ldr     x23, [sp, #96]
        mov     x1, x28
        mov     x0, x23
        bl      L5140
        ldr     x2, [sp, #112]
        mov     x0, x23
        mov     x3, x19
        mov     x1, x22
        bl      L5154
        mov     w23, w0
L6960:
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x24
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1800
        mov     x0, x22
        mov     w1, #0x0
        bl      L0e70
        ldr     x25, [sp, #112]
        mov     x2, #0x300
        mov     w1, #0x0
        mov     x0, x25
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        ldr     x0, [sp, #120]
        stp     xzr, xzr, [x0]
        stp     xzr, xzr, [x28]
        stp     xzr, xzr, [x28, #16]
        stp     xzr, xzr, [x28, #32]
        cbz     w23, L6a08
        cmn     w23, #0x1
        b.ne    L69f4
        ldr     w0, [sp, #108]
        mov     w1, #0xfffa
        add     w0, w0, #0x5
        and     w2, w0, #0xffff
        str     w2, [sp, #108]
        cmp     w1, w0, uxth
        b.ne    L6730
        mov     w23, #0xfffffffc
L69f4:
        ldr     x19, [sp, #96]
        mov     x2, #0xced
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
L6a08:
        ldr     x0, [sp, #168]
        str     xzr, [x22, #11392]
        ldr     x0, [sp, #152]
        str     xzr, [x22, #11424]
        ldr     x0, [sp, #160]
        str     xzr, [x22, #11456]
        ldr     x19, [sp, #136]
        mov     x2, #0x420
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        ldr     x0, [sp, #128]
        movi    v0.4s, #0x0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        stp     q0, q0, [x0, #192]
        stp     q0, q0, [x0, #224]
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #11880]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6ac4
        ldp     x19, x20, [sp]
        mov     w0, w23
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x2e70
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L6aa0:
        mov     w23, #0xffffffff
        b       L6960
L6aa8:
        ldr     x0, [sp, #128]
        ldp     q2, q3, [x24]
        add     x0, x0, #0x80
        ldp     q0, q1, [x24, #32]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
        b       L66a0
L6ac4:
        bl      L0e60
        nop
        nop

// mldsa65_signature_extmu (0xa8 bytes)
L6ad0:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xb00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        mov     x22, x2
        ldr     x1, [x3]
        str     x1, [sp, #104]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e50
        cbnz    w0, L6b6c
        mov     x6, x22
        mov     x1, x21
        mov     x0, x20
        mov     x5, x19
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L65d0
L6b38:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xb00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L6b74
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L6b6c:
        mov     w0, #0xfffffffd
        b       L6b38
L6b74:
        bl      L0e60
        nop
        nop

// mldsa65_verify_internal (0x4b4 bytes)
L6b80:
        mov     x12, #0x2940
        sub     sp, sp, x12
        stp     x19, x20, [sp]
        mov     x20, x3
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0x9f
        and     x22, x22, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        mov     x24, #0x2800
        add     x19, x22, x24
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        sub     x7, x19, #0x60
        stp     x27, x28, [sp, #64]
        mov     x24, x1
        mov     x23, x2
        str     x30, [sp, #80]
        mov     x21, x4
        str     x5, [sp, #96]
        mov     w27, w6
        ldp     q1, q2, [x0]
        ldr     q0, [x0, #32]
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x1, [x0]
        str     x1, [sp, #10552]
        mov     x1, #0x0
        mov     x0, x22
        add     x1, x25, #0x30
        stp     q1, q2, [x7]
        str     q0, [x7, #32]
        bl      L5db0
        mov     w1, #0xff3c
        mov     x0, x22
        movk    w1, #0x7, lsl #16
        bl      L5ba0
        cbnz    w0, L6fdc
        mov     w26, w0
        cbz     w27, L6f24
        ldp     q2, q3, [x24]
        sub     x0, x19, #0xe0
        ldp     q0, q1, [x24, #32]
        mov     x8, #0x2420
        add     x1, x22, x8
        mov     x9, #0x2720
        str     x1, [sp, #104]
        add     x1, x22, x9
        str     x1, [sp, #112]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
L6c48:
        mov     x3, #0x1400
        mov     x0, x22
        add     x28, x22, x3
        bl      L5b60
        mov     w21, #0x0
        ldr     x1, [sp, #96]
        mov     x4, #0x27a0
        add     x2, x22, x4
        mov     x5, #0x1c20
        mov     x6, #0x2020
        mov     x19, x2
        add     x27, x22, x6
        mov     x0, x28
        add     x20, x22, x5
        str     x2, [sp, #120]
        bl      L5df0
        mov     x1, x19
        mov     x7, #0x1820
        ldr     x24, [sp, #104]
        mov     x0, x27
        add     x19, x22, x7
        bl      L5740
        mov     x0, x27
        bl      L20f0
L6ca8:
        mov     w3, w21
        mov     x2, x22
        mov     x1, x28
        mov     x0, x20
        bl      L5e00
        ldr     x1, [sp, #96]
        mov     w2, w21
        mov     x0, x19
        bl      L50c0
        mov     x0, x19
        bl      L20d0
        mov     x0, x19
        bl      L20f0
        mov     x1, x27
        mov     x0, x19
        bl      L22e0
        mov     x1, x19
        mov     x0, x20
        bl      L20a0
        mov     x0, x20
        bl      L2000
        mov     x0, x20
        bl      L21c0
        mov     x0, x20
        bl      L2030
        mov     w2, w21
        mov     x1, x25
        mov     x0, x19
        bl      L5254
        mov     w23, w0
        cbnz    w0, L6fcc
        mov     x1, x19
        mov     x0, x20
        bl      L5454
        add     w21, w21, #0x1
        mov     x0, x24
        mov     x1, x20
        bl      L2870
        add     x24, x24, #0x80
        cmp     w21, #0x6
        b.ne    L6ca8
        mov     x1, #0x2760
        mov     x0, #0x2868
        add     x21, sp, x0
        add     x24, x22, x1
        mov     x0, x21
        bl      L1094
        ldr     x1, [sp, #112]
        mov     x0, x21
        mov     x2, #0x40
        bl      L10c0
        ldr     x1, [sp, #104]
        mov     x2, #0x300
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x1, #0x30
        mov     x0, x24
        bl      L11d0
        mov     x0, x21
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        str     q0, [x21, #192]
        ldr     x0, [sp, #120]
        mov     x1, x24
        mov     v2.16b, v0.16b
L6dd0:
        ldr     q1, [x0], #16
        add     w26, w26, #0x1
        ldr     q3, [x1], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     w26, #0x3
        b.ne    L6dd0
        movi    v1.4s, #0x0
        ext     v5.16b, v2.16b, v1.16b, #8
        ext     v3.16b, v0.16b, v1.16b, #8
        orr     v5.16b, v5.16b, v2.16b
        eor     v2.16b, v3.16b, v0.16b
        ext     v4.16b, v5.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v5.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #2
        ext     v2.16b, v0.16b, v1.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v3.16b, v1.16b, #1
        ext     v1.16b, v2.16b, v1.16b, #1
        orr     v0.16b, v0.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w0, v0.b[0]
        umov    w1, v1.b[0]
        neg     x0, x0
        asr     x0, x0, #32
        eor     w0, w1, w0
        cmp     w1, w0, uxtb
        b.ne    L6fd4
L6e50:
        mov     x0, x19
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x420
        mov     x0, x28
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x27
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1400
        mov     x0, x22
        mov     w1, #0x0
        bl      L0e70
        stp     xzr, xzr, [x24]
        stp     xzr, xzr, [x24, #16]
        stp     xzr, xzr, [x24, #32]
        ldr     x0, [sp, #120]
        stp     xzr, xzr, [x0]
        stp     xzr, xzr, [x0, #16]
        stp     xzr, xzr, [x0, #32]
        ldr     x0, [sp, #112]
        movi    v0.4s, #0x0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        ldr     x19, [sp, #104]
        mov     x2, #0x300
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #10552]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7030
        ldp     x19, x20, [sp]
        mov     w0, w23
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x2940
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L6f24:
        mov     x10, #0x2868
        mov     x11, #0x2420
        add     x19, sp, x10
        add     x27, x22, x11
        mov     x0, x19
        str     x27, [sp, #104]
        bl      L1094
        ldr     x1, [sp, #96]
        mov     x2, #0x7a0
        mov     x0, x19
        bl      L10c0
        mov     x0, x19
        bl      L1150
        mov     x2, x19
        mov     x1, #0x40
        mov     x0, x27
        bl      L11d0
        mov     x0, x19
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     q0, [x19, #192]
        mov     x12, #0x2720
        mov     x3, #0x40
        add     x0, x22, x12
        mov     x7, x23
        mov     x6, x24
        mov     x5, x21
        mov     x4, x20
        mov     x2, x27
        mov     x1, x3
        str     x0, [sp, #112]
        bl      L6194
        movi    v0.4s, #0x0
        stp     q0, q0, [x27]
        stp     q0, q0, [x27, #32]
        b       L6c48
L6fcc:
        mov     x2, #0x2760
        add     x24, x22, x2
L6fd4:
        mov     w23, #0xfffffffa
        b       L6e50
L6fdc:
        mov     x13, #0x2420
        add     x0, x22, x13
        mov     x23, #0x27a0
        mov     x21, #0x2720
        str     x0, [sp, #104]
        add     x0, x22, x21
        mov     x14, #0x1400
        mov     x15, #0x2020
        mov     x16, #0x1c20
        mov     x17, #0x1820
        mov     x18, #0x2760
        add     x28, x22, x14
        add     x27, x22, x15
        add     x20, x22, x16
        add     x19, x22, x17
        add     x24, x22, x18
        str     x0, [sp, #112]
        add     x0, x22, x23
        mov     w23, #0xfffffffa
        str     x0, [sp, #120]
        b       L6e50
L7030:
        bl      L0e60

// mldsa65_verify_extmu (0x18 bytes)
L7034:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L6b80
        nop

// mldsa65_prepare_domain_separation_prefix (0x19c bytes)
L7050:
        cmp     x4, #0xff
        b.hi    L70b0
        stp     x19, x21, [sp, #-64]!
        mov     x19, x4
        mov     x21, x0
        str     x30, [sp, #32]
        cbz     w5, L7094
        stp     x22, x23, [sp, #16]
        mov     x23, x1
        sub     w1, w5, #0x1
        mov     x0, #0x0
        cmp     w1, #0xb
        b.ls    L70b8
        ldp     x22, x23, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L7094:
        strb    wzr, [x0]
        strb    w4, [x21, #1]
        cbnz    x4, L70d4
L70a0:
        add     x0, x19, #0x2
L70a4:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L70b0:
        mov     x0, #0x0
        ret
L70b8:
        .inst   0xf0000000  // adrp x0, 0xa000
        mov     x22, x2
        add     x0, x0, #0xa20
        ldrb    w0, [x0, w1, uxtw]
        .inst   0x10000061  // adr     x1, 70d4 <mldsa65_prepare_domain_separation_prefix+0x84>
        add     x0, x1, w0, sxtb #2
        br      x0
L70d4:
        mov     x1, x3
        mov     x2, x4
        add     x0, x0, #0x2
        bl      L0e40
        b       L70a0
        cmp     x2, #0x20
        b.ne    L7160
L70f0:
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbnz    x19, L71d0
L7100:
        .inst   0xf0000001  // adrp x1, 0xa000
        add     x4, x1, #0xa30
        mov     w3, #0x0
        nop
L7110:
        ldr     w0, [x4]
        cmp     w5, w0
        b.eq    L7184
        add     w3, w3, #0x1
        add     x4, x4, #0x10
        cmp     w3, #0xc
        b.ne    L7110
        add     x0, x19, #0xd
        mov     x1, x23
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e40
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
L714c:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
        cmp     x2, #0x1c
        b.eq    L70f0
L7160:
        ldp     x22, x23, [sp, #16]
        mov     x0, #0x0
        b       L70a4
        cmp     x2, #0x40
        b.eq    L70f0
        b       L7160
        cmp     x2, #0x30
        b.eq    L70f0
        b       L7160
L7184:
        mov     x0, #0x4
        add     x1, x1, #0xa30
        add     x3, x0, w3, uxtw #4
        add     x0, x19, #0x2
        add     x4, x1, x3
        add     x2, x21, x0
        ldr     x1, [x1, x3]
        str     x1, [x21, x0]
        mov     x1, x23
        ldur    w0, [x4, #7]
        stur    w0, [x2, #7]
        add     x0, x19, #0xd
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e40
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
        b       L714c
L71d0:
        mov     x1, x3
        mov     x2, x19
        add     x0, x21, #0x2
        str     w5, [sp, #60]
        bl      L0e40
        ldr     w5, [sp, #60]
        b       L7100
        nop

// mldsa65_signature (0x10c bytes)
L71f0:
        stp     x19, x20, [sp, #-496]!
        mov     x20, x0
        .inst   0x900000c7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        add     x19, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x24, x2
        stp     x25, x26, [sp, #48]
        mov     x2, #0x0
        mov     x25, x5
        str     x30, [sp, #64]
        mov     w5, #0x0
        ldr     x1, [x7]
        str     x1, [sp, #488]
        mov     x1, #0x0
        bl      L7050
        cbnz    x0, L72ac
        add     x22, x19, #0x160
        mov     w26, #0xfffffff7
L724c:
        mov     x0, x20
        mov     x2, #0xced
        mov     w1, #0x0
        bl      L0e70
L725c:
        stp     xzr, xzr, [x19, #352]
        stp     xzr, xzr, [x22, #16]
        mov     x2, #0x14c
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L72f8
        ldp     x21, x22, [sp, #16]
        mov     w0, w26
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #496
        ret
L72ac:
        add     x22, x19, #0x160
        mov     x21, x0
        mov     x1, #0x20
        mov     x0, x22
        mov     w26, #0xfffffffd
        bl      L0e50
        cbnz    w0, L724c
        mov     x6, x25
        mov     x4, x21
        mov     x2, x24
        mov     x1, x23
        mov     x5, x22
        mov     x3, x19
        mov     x0, x20
        mov     w7, #0x0
        bl      L65d0
        mov     w26, w0
        cbz     w0, L725c
        b       L724c
L72f8:
        bl      L0e60
        nop

// mldsa65_verify (0xbc bytes)
L7300:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x0
        .inst   0x900000c6  // adrp x6, 0x1f000
        ldr     x6, [x6, #4088]
        add     x19, sp, #0x4f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        stp     x23, x30, [sp, #32]
        mov     x22, x5
        mov     x23, x2
        mov     x0, x19
        ldr     x1, [x6]
        str     x1, [sp, #408]
        mov     x1, #0x0
        mov     w5, #0x0
        mov     x2, #0x0
        bl      L7050
        cbz     x0, L73b0
        mov     x4, x0
        mov     x5, x22
        mov     x0, x20
        mov     x2, x23
        mov     x1, x21
        mov     x3, x19
        mov     w6, #0x0
        bl      L6b80
        mov     w20, w0
L7370:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L73b8
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret
L73b0:
        mov     w20, #0xfffffff7
        b       L7370
L73b8:
        bl      L0e60
        nop

// mldsa65_signature_pre_hash_internal (0xd0 bytes)
L73c0:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x0
        .inst   0x900000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        ldr     x9, [x8]
        str     x9, [sp, #408]
        mov     x9, #0x0
        cbnz    w7, L7444
L73f0:
        mov     w21, #0xfffffff7
L73f4:
        mov     x0, x20
        mov     x2, #0xced
        mov     w1, #0x0
        bl      L0e70
L7404:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L748c
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #416
        ret
L7444:
        mov     x21, x5
        mov     x22, x6
        mov     w5, w7
        mov     x0, x19
        bl      L7050
        cbz     x0, L73f0
        mov     x5, x21
        mov     x2, x0
        mov     x6, x22
        mov     x1, x19
        mov     x0, x20
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L65d0
        mov     w21, w0
        cbz     w0, L7404
        b       L73f4
L748c:
        bl      L0e60

// mldsa65_signature_pre_hash_shake256 (0xbc bytes)
L7490:
        stp     x19, x20, [sp, #-160]!
        mov     x8, x2
        mov     x2, x1
        .inst   0x900000c7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x0
        str     x30, [sp, #48]
        mov     x21, x3
        mov     x22, x4
        mov     x3, x8
        ldr     x1, [x7]
        str     x1, [sp, #152]
        mov     x1, #0x0
        mov     x23, x5
        mov     x24, x6
        mov     x0, x19
        mov     x1, #0x40
        bl      L12a4
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w7, #0xc
        mov     x2, #0x40
        bl      L73c0
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0x900000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #152]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L7548
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
L7548:
        bl      L0e60
        nop

// mldsa65_verify_pre_hash_internal (0xbc bytes)
L7550:
        stp     x19, x20, [sp, #-400]!
        .inst   0x900000c7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        str     x30, [sp, #24]
        add     x19, sp, #0x3f
        ldr     x8, [x7]
        str     x8, [sp, #392]
        mov     x8, #0x0
        and     x19, x19, #0xffffffffffffffe0
        cbz     w6, L75fc
        mov     x20, x0
        mov     x0, x19
        str     x21, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        bl      L7050
        mov     x2, x0
        cbz     x0, L75f8
        mov     x5, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L6b80
        mov     w20, w0
        ldr     x21, [sp, #16]
L75bc:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7604
        ldr     x30, [sp, #24]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret
L75f8:
        ldr     x21, [sp, #16]
L75fc:
        mov     w20, #0xfffffff7
        b       L75bc
L7604:
        str     x21, [sp, #16]
        bl      L0e60
        nop

// mldsa65_verify_pre_hash_shake256 (0xac bytes)
L7610:
        stp     x19, x20, [sp, #-144]!
        mov     x7, x2
        mov     x2, x1
        .inst   0x900000c6  // adrp x6, 0x1f000
        ldr     x6, [x6, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x0
        ldr     x1, [x6]
        str     x1, [sp, #136]
        mov     x1, #0x0
        mov     x21, x3
        mov     x22, x4
        mov     x3, x7
        mov     x23, x5
        mov     x0, x19
        mov     x1, #0x40
        bl      L12a4
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0xc
        mov     x2, #0x40
        bl      L7550
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0x900000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #136]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L76b8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret
L76b8:
        bl      L0e60
        nop

// mldsa65_pk_from_sk (0x328 bytes)
L76c0:
        mov     x12, #0x2310
        sub     sp, sp, x12
        add     x4, x1, #0x40
        mov     x8, #0x2400
        mov     x9, #0x1dc0
        mov     x10, #0x2260
        stp     x19, x20, [sp]
        mov     x20, x1
        add     x19, sp, #0x8f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x1, x19, x8
        stp     x23, x24, [sp, #32]
        sub     x3, x1, #0x200
        sub     x2, x1, #0x1c0
        stp     x25, x26, [sp, #48]
        mov     x11, #0x1400
        add     x26, x19, x9
        stp     x27, x28, [sp, #64]
        sub     x28, x1, #0x1a0
        add     x23, x19, x10
        str     x30, [sp, #80]
        add     x24, x19, x11
        mov     x21, x0
        add     x1, x20, #0x80
        ldp     q6, q7, [x4]
        mov     x0, x19
        ldp     q0, q1, [x4, #32]
        add     x22, x20, #0x300
        .inst   0x900000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        ldp     q4, q5, [x20]
        ldr     x5, [x4]
        str     x5, [sp, #8968]
        mov     x5, #0x0
        ldp     q2, q3, [x20, #32]
        stp     q6, q7, [x3]
        stp     q4, q5, [x28]
        stp     q2, q3, [x2]
        stp     q0, q1, [x3, #32]
        bl      L5d70
        mov     w1, #0x5
        mov     x0, x19
        bl      L5ba0
        mov     x2, x26
        mov     w1, #0x5
        mov     w25, w0
        mov     x0, x22
        bl      L5cb0
        mov     w27, w0
        mov     x0, x19
        bl      L5b60
        ldp     q0, q1, [x28]
        mov     x3, x22
        mov     x4, x23
        mov     x1, x24
        mov     x2, x19
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L6040
        mov     w22, w0
        cbz     w0, L7878
        mov     x6, #0x21c0
        mov     x7, #0x2200
        add     x28, x19, x6
        add     x20, x19, x7
L77c8:
        mov     x0, x21
        mov     x2, #0x7a0
        mov     w1, #0x0
        bl      L0e70
L77d8:
        mov     x0, x24
        mov     x2, #0x9c0
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        mov     x0, #0x2240
        add     x19, x19, x0
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        movi    v0.4s, #0x0
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     xzr, xzr, [x23]
        stp     xzr, xzr, [x23, #16]
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8968]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L79e4
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
L7878:
        movi    v1.4s, #0x0
        add     x20, x20, #0x600
        mov     x0, x24
        add     x1, x24, #0x9c0
        mov     v2.16b, v1.16b
        nop
L7890:
        ldr     q0, [x20], #16
        ldr     q3, [x0], #16
        eor     v0.16b, v0.16b, v3.16b
        orr     v2.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v0.16b
        cmp     x1, x0
        b.ne    L7890
        movi    v0.4s, #0x0
        ext     v4.16b, v2.16b, v0.16b, #8
        ext     v3.16b, v1.16b, v0.16b, #8
        orr     v4.16b, v4.16b, v2.16b
        eor     v3.16b, v3.16b, v1.16b
        ext     v2.16b, v4.16b, v0.16b, #4
        ext     v1.16b, v3.16b, v0.16b, #4
        orr     v2.16b, v2.16b, v4.16b
        eor     v1.16b, v1.16b, v3.16b
        ext     v4.16b, v2.16b, v0.16b, #2
        ext     v3.16b, v1.16b, v0.16b, #2
        orr     v4.16b, v4.16b, v2.16b
        eor     v3.16b, v3.16b, v1.16b
        ext     v1.16b, v4.16b, v0.16b, #1
        ext     v2.16b, v3.16b, v0.16b, #1
        orr     v1.16b, v1.16b, v4.16b
        eor     v2.16b, v2.16b, v3.16b
        umov    w0, v1.b[0]
        umov    w1, v2.b[0]
        neg     x0, x0
        asr     x0, x0, #32
        eor     w0, w1, w0
        and     w0, w0, #0xff
        mov     x5, #0x2200
        eor     w4, w0, w1
        mov     x2, #0x21c0
        add     x28, x19, x2
        add     x20, x19, x5
        mov     x0, x28
        mov     x2, x21
        mov     x1, #0x40
        mov     x3, #0x7a0
        str     w4, [sp, #108]
        bl      L12a4
        movi    v0.4s, #0x0
        ldr     w4, [sp, #108]
        mov     x0, x28
        add     x2, x28, #0x40
        mov     x1, x20
        mov     v2.16b, v0.16b
L794c:
        ldr     q1, [x0], #16
        ldr     q3, [x1], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x0, x2
        b.ne    L794c
        movi    v1.4s, #0x0
        ext     v5.16b, v2.16b, v1.16b, #8
        ext     v3.16b, v0.16b, v1.16b, #8
        orr     v5.16b, v5.16b, v2.16b
        eor     v2.16b, v3.16b, v0.16b
        ext     v4.16b, v5.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v5.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #2
        ext     v2.16b, v0.16b, v1.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v3.16b, v1.16b, #1
        ext     v1.16b, v2.16b, v1.16b, #1
        orr     v0.16b, v0.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w0, v0.b[0]
        umov    w1, v1.b[0]
        neg     x0, x0
        asr     x0, x0, #32
        eor     w0, w1, w0
        and     w0, w0, #0xff
        orr     w25, w25, w27
        eor     w0, w0, w1
        orr     w0, w4, w0
        orr     w0, w0, w25
        tst     w0, #0xff
        b.eq    L77d8
        mov     w22, #0xfffffff9
        b       L77c8
L79e4:
        bl      L0e60
        nop
        nop

// mldsa87_unpack_pk_t1 (0x14 bytes)
L79f0:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #6
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L24d0

// mldsa87_pack_sk_rho_key_tr (0x28 bytes)
L7a04:
        ldp     q0, q1, [x1]
        add     x4, x0, #0x40
        stp     q0, q1, [x0]
        ldp     q0, q1, [x3]
        stp     q0, q1, [x0, #32]
        ldp     q0, q1, [x2]
        stp     q0, q1, [x4]
        ldp     q0, q1, [x2, #32]
        stp     q0, q1, [x4, #32]
        ret
        nop

// mldsa87_unpack_sk (0x40 bytes)
L7a30:
        ldp     q0, q1, [x6]
        add     x7, x6, #0x40
        add     x10, x6, #0x80
        add     x9, x6, #0x320
        add     x8, x6, #0x620
        stp     q0, q1, [x0]
        ldp     q0, q1, [x6, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x7]
        stp     q0, q1, [x1]
        ldp     q0, q1, [x7, #32]
        stp     q0, q1, [x1, #32]
        str     x10, [x4]
        str     x9, [x5]
        str     x8, [x3]
        ret

// mldsa87_pack_sig_c (0x14 bytes)
L7a70:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x1, #32]
        stp     q0, q1, [x0, #32]
        ret

// mldsa87_pack_sig_h (0xf8 bytes)
L7a84:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-96]!
        mov     x20, x3
        stp     x25, x26, [sp, #48]
        mov     x3, #0x120b
        mov     w19, #0x0
        stp     x27, x28, [sp, #64]
        mov     x28, x2
        mov     x2, #0x11c0
        add     x26, x0, x2
        stp     x21, x22, [sp, #16]
        mov     w27, #0x100
        stp     x23, x24, [sp, #32]
        mov     x21, x1
        add     x23, x0, x3
        str     x30, [sp, #80]
        add     x24, x28, #0x400
        mov     w25, #0x3ff00
        mov     w22, #0x7fe00
        str     q0, [x26, #64]
        movk    w27, #0xfffc, lsl #16
        stur    wzr, [x26, #79]
        stp     q0, q0, [x26]
        stp     q0, q0, [x26, #32]
L7ae4:
        mov     x1, x28
        mov     x0, x20
        bl      L28f4
        mov     x4, #0x0
        b       L7b10
L7af8:
        cmp     w7, #0x0
        ccmp    w5, w27, #0x0, ne
        b.eq    L7b24
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.eq    L7b40
L7b10:
        ldr     w5, [x21, x4, lsl #2]
        ldr     w7, [x20, x4, lsl #2]
        add     w6, w5, w25
        cmp     w6, w22
        b.ls    L7af8
L7b24:
        cmp     w19, #0x4b
        b.eq    L7b5c
        strb    w4, [x26, w19, uxtw]
        add     x4, x4, #0x1
        add     w19, w19, #0x1
        cmp     x4, #0x100
        b.ne    L7b10
L7b40:
        add     x28, x28, #0x80
        strb    w19, [x23], #1
        add     x21, x21, #0x400
        cmp     x28, x24
        b.ne    L7ae4
        mov     w0, #0x0
        b       L7b60
L7b5c:
        mov     w0, #0xffffffff
L7b60:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
        nop

// mldsa87_pack_sig_z (0x14 bytes)
L7b80:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #7
        add     x2, x2, #0x40
        add     x0, x0, x2
        b       L83b4

// mldsa87_sig_unpack_hints (0x108 bytes)
L7b94:
        stp     x19, x20, [sp, #-48]!
        mov     x3, #0x11c0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x6, x0
        add     x22, x1, x3
        stp     x23, x30, [sp, #32]
        mov     w21, #0x0
        mov     w23, w2
        cbz     w2, L7bc4
        add     w0, w2, #0x4a
        ldrb    w21, [x22, w0, uxtw]
L7bc4:
        add     w0, w23, #0x4b
        ldrb    w20, [x22, w0, uxtw]
        cmp     w20, #0x4b
        ccmp    w21, w20, #0x2, ls
        b.hi    L7c38
        mov     x0, x6
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x6, x0
        cmp     w21, w20
        b.cs    L7c4c
        mov     w0, #0x11c0
        add     w0, w21, w0
        mov     w3, w21
        add     x1, x19, x0
        mov     w7, #0x1
L7c08:
        ldrb    w4, [x1], #1
        mov     w5, w3
        add     w3, w3, #0x1
        str     w7, [x6, x4, lsl #2]
        cmp     w20, w3
        b.ls    L7c4c
        cmp     w21, w3
        b.cs    L7c08
        ldrb    w0, [x22, w5, uxtw]
        ldrb    w4, [x1]
        cmp     w4, w0
        b.hi    L7c08
L7c38:
        mov     w0, #0xffffffff
L7c3c:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L7c4c:
        cmp     w23, #0x7
        b.eq    L7c68
L7c54:
        mov     w0, #0x0
L7c58:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L7c68:
        cmp     w20, #0x4b
        b.eq    L7c54
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbnz    w0, L7c38
        nop
L7c80:
        cmp     w20, #0x4b
        b.eq    L7c58
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbz     w0, L7c80
        mov     w0, #0xffffffff
        b       L7c3c
        nop

// mld_rej_eta_c87.constprop.0 (0xa8 bytes)
L7ca0:
        mov     x8, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    L7d44
        mov     w9, #0x1
        sub     w9, w9, w2
        mov     w7, #0xcd
        mov     w10, #0x2
L7cc0:
        ldrb    w3, [x2]
        add     w5, w9, w2
        add     x2, x2, #0x1
        and     w4, w3, #0xf
        lsr     w3, w3, #4
        cmp     w4, #0xf
        b.eq    L7cf8
        mul     w1, w4, w7
        lsr     w1, w1, #10
        add     w1, w1, w1, lsl #2
        sub     w4, w4, w1
        sub     w4, w10, w4
        str     w4, [x8, w0, uxtw #2]
        add     w0, w0, #0x1
L7cf8:
        cmp     w0, #0xff
        mul     w1, w3, w7
        cset    w4, ls
        add     w6, w0, #0x1
        cmp     w4, #0x0
        ccmp    w3, #0xe, #0x2, ne
        b.hi    L7d34
        lsr     w1, w1, #10
        cmp     w6, #0xff
        cset    w4, ls
        add     w1, w1, w1, lsl #2
        sub     w3, w3, w1
        sub     w3, w10, w3
        str     w3, [x8, w0, uxtw #2]
        mov     w0, w6
L7d34:
        cmp     w5, #0x87
        cset    w1, ls
        tst     w4, w1
        b.ne    L7cc0
L7d44:
        ret
        nop
        nop

// mldsa87_poly_decompose (0x64 bytes)
L7d50:
        mov     x5, #0x0
        mov     w7, #0x3ff000
        mov     w6, #0xff801fff
        nop
L7d60:
        ldr     w3, [x1, x5]
        add     w2, w3, #0x7f
        asr     w2, w2, #7
        add     w2, w2, w2, lsl #10
        add     w2, w2, #0x200, lsl #12
        ubfx    x2, x2, #22, #4
        str     w2, [x0, x5]
        sub     w2, w2, w2, lsl #10
        add     w2, w3, w2, lsl #9
        sub     w3, w7, w2
        sxtw    x3, w3
        asr     x3, x3, #31
        add     w4, w2, w6
        eor     w4, w4, w2
        and     w3, w4, w3
        eor     w2, w3, w2
        str     w2, [x1, x5]
        add     x5, x5, #0x4
        cmp     x5, #0x400
        b.ne    L7d60
        ret

// mldsa87_poly_use_hint (0x7c bytes)
L7db4:
        mov     x6, #0x0
        mov     w10, #0x3ff000
        mov     w9, #0xff801fff
L7dc0:
        ldr     w3, [x0, x6]
        add     w2, w3, #0x7f
        asr     w2, w2, #7
        add     w2, w2, w2, lsl #10
        add     w2, w2, #0x200, lsl #12
        ubfx    x2, x2, #22, #4
        sub     w5, w2, w2, lsl #10
        add     w5, w3, w5, lsl #9
        sub     w3, w10, w5
        sxtw    x3, w3
        asr     x3, x3, #31
        add     w4, w5, w9
        add     w7, w2, #0x1
        eor     w4, w4, w5
        sub     w8, w2, #0x1
        and     w3, w4, w3
        ldr     w4, [x1, x6]
        eor     w3, w3, w5
        and     w7, w7, #0xf
        cmp     w3, #0x0
        and     w8, w8, #0xf
        cbz     w4, L7e1c
        csel    w2, w8, w7, le
L7e1c:
        str     w2, [x0, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L7dc0
        ret

// mldsa87_poly_uniform_eta_4x (0x268 bytes)
L7e30:
        sub     sp, sp, #0x7d0
        mov     x8, x4
        .inst   0x900000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0xaf
        and     x22, x22, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x9, x22, #0x280
        add     x19, x22, #0x2e0
        stp     x25, x26, [sp, #48]
        add     x20, x22, #0x340
        add     x21, x22, #0x3a0
        stp     x27, x28, [sp, #64]
        add     x26, sp, #0x4a8
        mov     x28, x9
        str     x30, [sp, #80]
        add     x23, x22, #0x1e0
        str     x9, [sp, #136]
        add     x24, x22, #0x140
        ldp     q2, q3, [x8, #32]
        add     x25, x22, #0xa0
        ldp     q0, q1, [x8]
        ldr     x8, [x4]
        str     x8, [sp, #1992]
        mov     x8, #0x0
        ldrb    w4, [sp, #2000]
        mov     w27, #0xff
        stp     q2, q3, [x9, #32]
        stp     q2, q3, [x19, #32]
        stp     q0, q1, [x19]
        stp     q0, q1, [x20]
        stp     q2, q3, [x20, #32]
        stp     x0, x1, [sp, #104]
        mov     x0, x26
        stp     x2, x3, [sp, #120]
        stp     q0, q1, [x21]
        stp     q2, q3, [x21, #32]
        stp     q0, q1, [x9]
        strb    w5, [x9, #64]
        strb    wzr, [x9, #65]
        strb    w6, [x9, #160]
        strb    wzr, [x9, #161]
        strb    w7, [x9, #256]
        strb    wzr, [x9, #257]
        strb    w4, [x9, #352]
        strb    wzr, [x9, #353]
        bl      L1550
        mov     x4, x21
        mov     x3, x20
        mov     x2, x19
        mov     x1, x28
        mov     x0, x26
        mov     x5, #0x42
        bl      L1340
        mov     x3, x23
        mov     x5, x26
        mov     x4, #0x1
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L14c0
        ldr     x0, [sp, #104]
        mov     x2, x22
        mov     w1, #0x0
        bl      L7ca0
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     x2, x25
        mov     w1, #0x0
        bl      L7ca0
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     x2, x24
        mov     w1, #0x0
        bl      L7ca0
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, #0x0
        mov     x2, x23
        bl      L7ca0
        mov     w28, w0
        cmp     w21, w27
        ccmp    w0, w27, #0x0, hi
        cset    w0, ls
        cmp     w20, w27
        ccmp    w19, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0, L802c
        nop
L7fa0:
        mov     x5, x26
        mov     x3, x23
        mov     x4, #0x1
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L14c0
        ldr     x0, [sp, #104]
        mov     w1, w19
        mov     x2, x22
        bl      L7ca0
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x25
        bl      L7ca0
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     w1, w21
        mov     x2, x24
        bl      L7ca0
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, w28
        mov     x2, x23
        bl      L7ca0
        cmp     w0, #0xff
        ccmp    w21, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0, L7fa0
L802c:
        mov     x0, x26
        bl      L1554
        mov     x0, x22
        mov     x2, #0x280
        mov     w1, #0x0
        bl      L0e70
        ldr     x19, [sp, #136]
        mov     x2, #0x180
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1992]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8094
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7d0
        ret
L8094:
        bl      L0e60
        nop
        nop

// mldsa87_poly_challenge (0x168 bytes)
L80a0:
        stp     x19, x20, [sp, #-448]!
        mov     x19, x1
        .inst   0xf00000a3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        add     x2, sp, #0x5f
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0xe8
        and     x20, x2, #0xffffffffffffffe0
        stp     x23, x30, [sp, #32]
        mov     x23, x0
        ldr     x0, [x3]
        str     x0, [sp, #440]
        mov     x0, #0x0
        mov     x0, x21
        bl      L1094
        mov     x1, x19
        mov     x2, #0x40
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x88
        bl      L11d0
        mov     x2, x20
        mov     w0, #0x0
        mov     x3, #0x0
L8110:
        ldrb    w1, [x2], #1
        lsl     x1, x1, x0
        add     w0, w0, #0x8
        orr     x3, x3, x1
        cmp     w0, #0x40
        b.ne    L8110
        mov     x0, x23
        mov     x2, #0x400
        mov     w1, #0x0
        str     x3, [sp, #56]
        bl      L0e70
        mov     x19, #0xc4
        mov     w22, #0x1
        mov     w0, #0x8
        b       L815c
L814c:
        ldrb    w1, [x20, w0, uxtw]
        add     w0, w0, #0x1
        cmp     w1, w19
        b.ls    L8184
L815c:
        cmp     w0, #0x88
        b.ne    L814c
        mov     x0, x20
        mov     x1, #0x88
        mov     x2, x21
        bl      L11d0
        ldrb    w1, [x20]
        mov     w0, #0x1
        cmp     w1, w19
        b.hi    L814c
L8184:
        ldr     x2, [sp, #56]
        ldr     w4, [x23, x1, lsl #2]
        str     w4, [x23, x19, lsl #2]
        add     x19, x19, #0x1
        ubfiz   x3, x2, #1, #1
        lsr     x2, x2, #1
        sub     w3, w22, w3
        str     w3, [x23, x1, lsl #2]
        str     x2, [sp, #56]
        cmp     x19, #0x100
        b.ne    L815c
        mov     x0, x21
        bl      L1280
        movi    v0.4s, #0x0
        str     xzr, [x20, #128]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        add     x0, sp, #0x38
        str     xzr, [sp, #56]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #440]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8204
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #448
        ret
L8204:
        bl      L0e60
        nop
        nop

// mldsa87_polyeta_pack (0xdc bytes)
L8210:
        .inst   0xf00000a2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        add     x10, x1, #0x400
        mov     w5, #0x2
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
L8230:
        ldp     w4, w2, [x1, #4]
        add     x0, x0, #0x3
        ldp     w6, w9, [x1, #12]
        sub     w2, w5, w2
        ldp     w7, w3, [x1, #20]
        sub     w4, w5, w4
        ldr     w8, [x1, #28]
        sub     w6, w5, w6
        sub     w7, w5, w7
        sub     w9, w5, w9
        sub     w3, w5, w3
        sub     w8, w5, w8
        ldr     w11, [x1], #32
        ubfiz   w13, w2, #6, #8
        ubfiz   w8, w8, #5, #8
        ubfiz   w12, w7, #7, #8
        ubfx    x2, x2, #2, #6
        ubfiz   w4, w4, #3, #8
        ubfiz   w6, w6, #1, #8
        ubfiz   w9, w9, #4, #8
        ubfiz   w3, w3, #2, #8
        orr     w4, w4, w13
        orr     w3, w3, w8
        orr     w6, w6, w9
        sub     w8, w5, w11
        orr     w2, w2, w12
        ubfx    x7, x7, #1, #7
        orr     w4, w4, w8
        orr     w2, w2, w6
        orr     w3, w3, w7
        sturb   w4, [x0, #-3]
        sturb   w2, [x0, #-2]
        sturb   w3, [x0, #-1]
        cmp     x10, x1
        b.ne    L8230
        add     x0, sp, #0x10
        str     xzr, [sp, #16]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L82e8
        ldr     x30, [sp], #32
        ret
L82e8:
        bl      L0e60
        nop

// mldsa87_polyeta_unpack (0xc4 bytes)
L82f0:
        movi    v2.4s, #0x2
        add     x5, x1, #0x60
L82f8:
        ldrb    w2, [x1]
        add     x1, x1, #0x3
        add     x0, x0, #0x20
        and     w2, w2, #0x7
        stur    w2, [x0, #-32]
        fmov    s1, w2
        ldurb   w3, [x1, #-3]
        ubfx    x3, x3, #3, #3
        stur    w3, [x0, #-28]
        ldurb   w4, [x1, #-2]
        mov     v1.s[1], w3
        ldurb   w2, [x1, #-3]
        lsl     w3, w4, #2
        orr     w2, w3, w2, lsr #6
        and     w2, w2, #0x7
        stur    w2, [x0, #-24]
        ldurb   w3, [x1, #-2]
        mov     v1.s[2], w2
        ubfx    x3, x3, #1, #3
        stur    w3, [x0, #-20]
        ldurb   w2, [x1, #-2]
        mov     v1.s[3], w3
        ubfx    x2, x2, #4, #3
        stur    w2, [x0, #-16]
        fmov    d0, x2
        ldurb   w3, [x1, #-1]
        sub     v1.4s, v2.4s, v1.4s
        ldurb   w2, [x1, #-2]
        lsl     w3, w3, #1
        orr     w2, w3, w2, lsr #7
        and     w2, w2, #0x7
        stur    w2, [x0, #-12]
        ldurb   w3, [x1, #-1]
        mov     v0.s[1], w2
        ubfx    x2, x3, #2, #3
        stur    w2, [x0, #-8]
        ldurb   w3, [x1, #-1]
        mov     v0.s[2], w2
        stur    q1, [x0, #-32]
        fmov    s1, w3
        ushr    v1.2s, v1.2s, #5
        mov     v0.s[3], v1.s[0]
        sub     v0.4s, v2.4s, v0.4s
        stur    q0, [x0, #-16]
        cmp     x5, x1
        b.ne    L82f8
        ret

// mldsa87_polyz_pack (0x98 bytes)
L83b4:
        .inst   0xf00000a2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x7, x0, #0x280
        mov     w5, #0x80000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        nop
L83d8:
        ldp     w3, w2, [x1]
        add     x0, x0, #0x5
        add     x1, x1, #0x8
        sub     w2, w5, w2
        sub     w3, w5, w3
        sturb   w3, [x0, #-5]
        ubfiz   w4, w2, #4, #4
        lsr     w6, w2, #4
        orr     w4, w4, w3, lsr #16
        lsr     w2, w2, #12
        lsr     w3, w3, #8
        sturb   w3, [x0, #-4]
        sturb   w4, [x0, #-3]
        sturb   w6, [x0, #-2]
        sturb   w2, [x0, #-1]
        cmp     x7, x0
        b.ne    L83d8
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8448
        ldr     x30, [sp], #48
        ret
L8448:
        bl      L0e60
        nop

// mldsa87_polyz_unpack (0x70 bytes)
L8450:
        add     x6, x1, #0x280
        mov     w5, #0x80000
L8458:
        ldrb    w2, [x1]
        add     x1, x1, #0x5
        str     w2, [x0]
        add     x0, x0, #0x8
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
        orr     w2, w4, w3, lsl #12
        sub     w2, w5, w2
        stur    w2, [x0, #-4]
        cmp     x6, x1
        b.ne    L8458
        ret

// mldsa87_poly_uniform_gamma1 (0xe4 bytes)
L84c0:
        sub     sp, sp, #0x430
        .inst   0xf00000a3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x4f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x19, x20, #0x2c0
        add     x21, sp, #0x358
        str     x30, [sp, #32]
        mov     x22, x0
        mov     x0, x21
        ldp     q2, q3, [x1]
        ldr     x4, [x3]
        str     x4, [sp, #1064]
        mov     x4, #0x0
        ldp     q0, q1, [x1, #32]
        stp     q2, q3, [x19]
        stp     q0, q1, [x19, #32]
        strh    w2, [x20, #768]
        bl      L1094
        mov     x1, x19
        mov     x2, #0x42
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x2a8
        bl      L11d0
        mov     x1, x20
        mov     x0, x22
        bl      L8450
        mov     x0, x21
        bl      L1280
        mov     x0, x20
        mov     x2, #0x2a8
        mov     w1, #0x0
        bl      L0e70
        movi    v0.4s, #0x0
        strh    wzr, [x19, #64]
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1064]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L85a0
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x430
        ret
L85a0:
        bl      L0e60
        nop
        nop
        nop

// mldsa87_polyvecl_ntt (0x38 bytes)
L85b0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1c00
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L85c8:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L20f0
        cmp     x19, x20
        b.ne    L85c8
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa87_polyvecl_chknorm (0x50 bytes)
L85f0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1c00
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
L8610:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L27c4
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L8610
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa87_polyveck_reduce (0x30 bytes)
L8640:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L8650:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2000
        cmp     x19, x20
        b.ne    L8650
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_caddq (0x30 bytes)
L8670:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L8680:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2030
        cmp     x19, x20
        b.ne    L8680
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_invntt_tomont (0x30 bytes)
L86a0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L86b0:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L21c0
        cmp     x19, x20
        b.ne    L86b0
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta_chknorm (0x5c bytes)
L86d0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x20, x2
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L86f0:
        mov     x1, x19
        mov     x0, x20
        bl      L82f0
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L27c4
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L86f0
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
        nop

// mldsa87_polyveck_decompose_pack_w1 (0x58 bytes)
L8730:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, #0x2, lsl #12
        str     x30, [sp, #32]
        nop
L8750:
        mov     x1, x19
        mov     x0, x21
        bl      L7d50
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2870
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L8750
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
        nop
        nop

// mldsa87_polyvecl_unpack_eta (0x40 bytes)
L8790:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x2a0
        nop
L87a8:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L82f0
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L87a8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvecl_unpack_z (0x40 bytes)
L87d0:
        stp     x19, x20, [sp, #-32]!
        mov     x20, x0
        mov     x19, x1
        mov     x0, #0x1180
        stp     x21, x30, [sp, #16]
        add     x21, x1, x0
L87e8:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x280
        bl      L8450
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L87e8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvec_matrix_expand_lazy (0x10 bytes)
L8810:
        ldp     q0, q1, [x1]
        add     x0, x0, #0x400
        stp     q0, q1, [x0]
        ret

// mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy (0xf4 bytes)
L8820:
        stp     x19, x20, [sp, #-160]!
        mov     w20, #0x1
        stp     x21, x22, [sp, #16]
        mov     x21, x1
        add     x22, x2, #0x400
        stp     x23, x24, [sp, #32]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x25, x30, [sp, #48]
        mov     x25, x2
        and     w24, w3, #0xff
        .inst   0xf00000a2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        mov     x1, x19
        ldr     q0, [x21, #1024]
        ldr     x3, [x2]
        str     x3, [sp, #152]
        mov     x3, #0x0
        ldr     q1, [x21, #1040]
        mov     x23, x0
        strb    wzr, [x19, #32]
        strb    w24, [x19, #33]
        stp     q0, q1, [x19]
        bl      L2370
        mov     x1, x25
        mov     x0, x23
        bl      L22e0
        nop
L8890:
        mov     x1, x19
        mov     x0, x21
        strb    w20, [x19, #32]
        add     w20, w20, #0x1
        strb    w24, [x19, #33]
        bl      L2370
        mov     x1, x22
        mov     x0, x21
        bl      L22e0
        add     x22, x22, #0x400
        mov     x1, x21
        mov     x0, x23
        bl      L2070
        cmp     w20, #0x7
        b.ne    L8890
        mov     x0, x23
        bl      L2000
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8910
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
L8910:
        bl      L0e60

// mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy (0x148 bytes)
L8914:
        stp     x19, x20, [sp, #-176]!
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x24, x3
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0x6f
        and     x21, x21, #0xffffffffffffffe0
        stp     x25, x26, [sp, #48]
        mov     x26, x0
        mov     x25, x2
        str     x30, [sp, #64]
        mov     w22, #0x0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     q0, [x23, #1024]
        ldr     x1, [x0]
        str     x1, [sp, #168]
        mov     x1, #0x0
        ldr     q1, [x23, #1040]
        stp     q0, q1, [x21]
        nop
L8968:
        ldrh    w2, [x25, #8]
        ldr     x1, [x25]
        add     w2, w22, w2
        mov     x0, x24
        mov     x20, x26
        mov     w19, #0x0
        bl      L84c0
        mov     x0, x24
        bl      L20f0
        b       L89c8
L8990:
        mov     x0, x23
        strb    w22, [x21, #32]
        strb    w19, [x21, #33]
        bl      L2370
        mov     x1, x24
        mov     x0, x23
        bl      L22e0
        add     w19, w19, #0x1
        mov     x0, x20
        mov     x1, x23
        bl      L2070
        add     x20, x20, #0x400
        cmp     w19, #0x8
        b.eq    L89fc
L89c8:
        mov     x1, x21
        cbnz    w22, L8990
        mov     x0, x20
        strb    wzr, [x21, #32]
        strb    w19, [x21, #33]
        bl      L2370
        mov     x0, x20
        mov     x1, x24
        add     w19, w19, #0x1
        bl      L22e0
        add     x20, x20, #0x400
        cmp     w19, #0x8
        b.ne    L89c8
L89fc:
        add     w22, w22, #0x1
        cmp     w22, #0x7
        b.ne    L8968
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        mov     x0, x26
        bl      L8640
        mov     x0, x26
        bl      L86a0
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #168]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8a58
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #176
        ret
L8a58:
        bl      L0e60
        nop

// mld_compute_pack_t0_t187 (0x154 bytes)
L8a60:
        sub     sp, sp, #0xc90
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        mov     w21, #0x0
        .inst   0xf00000a3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        stp     x23, x24, [sp, #32]
        mov     x23, x2
        mov     x24, x1
        stp     x25, x26, [sp, #48]
        add     x26, sp, #0x6f
        and     x26, x26, #0xffffffffffffffe0
        str     x30, [sp, #64]
        mov     x25, x0
        add     x19, x26, #0x820
        add     x20, x26, #0x420
        ldr     x2, [x3]
        str     x2, [sp, #3208]
        mov     x2, #0x0
        mov     x1, x4
        mov     x0, x26
        bl      L8810
        nop
L8ac0:
        mov     w3, w21
        mov     x2, x23
        mov     x1, x26
        mov     x0, x19
        bl      L8820
        add     w21, w21, #0x1
        mov     x0, x19
        bl      L21c0
        mov     x1, x22
        mov     x0, x20
        bl      L82f0
        add     x22, x22, #0x60
        mov     x1, x20
        mov     x0, x19
        bl      L2070
        mov     x0, x19
        bl      L2000
        mov     x0, x19
        bl      L2030
        mov     x2, x19
        mov     x1, x19
        mov     x0, x20
        bl      L2330
        mov     x0, x25
        mov     x1, x20
        bl      L2474
        add     x25, x25, #0x140
        mov     x0, x24
        mov     x1, x19
        bl      L2544
        add     x24, x24, #0x1a0
        cmp     w21, #0x8
        b.ne    L8ac0
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x420
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e70
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3208]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8bb0
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, #0xc90
        ret
L8bb0:
        bl      L0e60

// mld_H87.constprop.0 (0x108 bytes)
L8bb4:
        stp     x19, x20, [sp, #-304]!
        mov     x20, x6
        .inst   0xf00000a7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x58
        stp     x23, x24, [sp, #32]
        mov     x22, x0
        mov     x23, x1
        stp     x25, x26, [sp, #48]
        mov     x24, x2
        mov     x21, x4
        str     x30, [sp, #64]
        mov     x25, x3
        mov     x26, x5
        ldr     x0, [x7]
        str     x0, [sp, #296]
        mov     x0, #0x0
        mov     x0, x19
        bl      L1094
        mov     x2, x24
        mov     x1, x23
        mov     x0, x19
        bl      L10c0
        cbnz    x21, L8c90
        cbnz    x20, L8ca4
L8c1c:
        mov     x0, x19
        bl      L1150
        mov     x2, x19
        mov     x1, #0x40
        mov     x0, x22
        bl      L11d0
        mov     x0, x19
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     q0, [x19, #192]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8cb8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret
L8c90:
        mov     x2, x21
        mov     x1, x25
        mov     x0, x19
        bl      L10c0
        cbz     x20, L8c1c
L8ca4:
        mov     x2, x20
        mov     x1, x26
        mov     x0, x19
        bl      L10c0
        b       L8c1c
L8cb8:
        bl      L0e60
        nop

// mldsa87_keypair_internal (0x31c bytes)
L8cc0:
        mov     x12, #0x1da0
        sub     sp, sp, x12
        mov     x3, #0x1cc0
        mov     x4, #0x1c00
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0xaf
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x21, x19, x4
        mov     w4, #0x708
        stp     x23, x24, [sp, #48]
        mov     x22, x0
        mov     x20, x1
        stp     x25, x26, [sp, #64]
        add     x23, x19, #0xc00
        add     x24, x19, #0x800
        stp     x27, x28, [sp, #80]
        add     x27, x19, x3
        add     x26, x21, #0x20
        str     x30, [sp, #96]
        mov     x3, #0x22
        mov     x1, #0x80
        add     x25, x19, #0x400
        ldp     q0, q1, [x2]
        .inst   0xf00000a2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #7576]
        mov     x0, #0x0
        stp     q0, q1, [x27]
        mov     x2, x27
        mov     x0, x21
        strh    w4, [x19, #7392]
        bl      L12a4
        mov     x3, x23
        mov     x2, x24
        mov     x4, x26
        mov     w0, #0xe
        strb    w0, [sp]
        mov     w7, #0xd
        mov     w6, #0xc
        mov     w5, #0xb
        mov     x1, x25
        mov     x0, x19
        bl      L7e30
        mov     x1, x19
        add     x0, x20, #0x4a0
        bl      L8210
        mov     x1, x25
        add     x0, x20, #0x500
        bl      L8210
        mov     x1, x24
        add     x0, x20, #0x560
        bl      L8210
        mov     x1, x23
        add     x0, x20, #0x5c0
        bl      L8210
        mov     x3, x23
        mov     x2, x24
        mov     x4, x26
        mov     w0, #0xa
        strb    w0, [sp]
        mov     w7, #0x9
        mov     w6, #0x8
        mov     w5, #0x7
        add     x0, x20, #0x320
        mov     x1, x25
        mov     x28, x0
        mov     x0, x19
        bl      L7e30
        str     x28, [sp, #120]
        mov     x0, x28
        mov     x1, x19
        bl      L8210
        mov     x1, x25
        add     x0, x20, #0x380
        bl      L8210
        mov     x1, x24
        add     x0, x20, #0x3e0
        bl      L8210
        mov     x5, #0x1800
        mov     x1, x23
        add     x28, x19, x5
        add     x0, x20, #0x440
        bl      L8210
        mov     x6, #0x1400
        add     x9, x19, x6
        mov     w0, #0xffffffff
        strb    w0, [sp]
        mov     x4, x26
        mov     x2, x28
        mov     x3, x19
        mov     w7, #0x6
        mov     w6, #0x5
        mov     w5, #0x4
        mov     x1, x9
        add     x0, x19, #0x1, lsl #12
        stp     x0, x9, [sp, #128]
        bl      L7e30
        ldr     x0, [sp, #128]
        mov     x1, x0
        add     x0, x20, #0x200
        bl      L8210
        ldr     x9, [sp, #136]
        add     x0, x20, #0x260
        mov     x1, x9
        bl      L8210
        mov     x1, x28
        add     x0, x20, #0x2c0
        bl      L8210
        mov     x3, x23
        mov     x2, x24
        mov     x4, x26
        mov     w0, #0x3
        strb    w0, [sp]
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x1, x25
        mov     x0, x19
        bl      L7e30
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L8210
        mov     x1, x25
        add     x0, x20, #0xe0
        bl      L8210
        mov     x1, x24
        add     x0, x20, #0x140
        bl      L8210
        mov     x1, x23
        add     x0, x20, #0x1a0
        bl      L8210
        mov     x0, x19
        bl      L85b0
        ldp     q0, q1, [x21]
        mov     x7, #0x1c80
        ldr     x3, [sp, #120]
        mov     x4, x21
        mov     x2, x19
        add     x1, x20, #0x620
        add     x0, x22, #0x20
        add     x23, x19, x7
        stp     q0, q1, [x22]
        bl      L8a60
        mov     w24, w0
        cbnz    w0, L8f34
        mov     x0, x23
        mov     x2, x22
        mov     x3, #0xa20
        mov     x1, #0x40
        bl      L12a4
        mov     x2, x23
        add     x3, x21, #0x60
        mov     x1, x21
        mov     x0, x20
        bl      L7a04
L8f34:
        mov     x0, x19
        mov     x2, #0x1c00
        mov     w1, #0x0
        bl      L0e70
        movi    v0.4s, #0x0
        stp     q0, q0, [x23]
        stp     q0, q0, [x23, #32]
        stp     xzr, xzr, [x27]
        stp     xzr, xzr, [x27, #16]
        strh    wzr, [x27, #32]
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        cbnz    w24, L8fb4
L8f70:
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7576]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8fd8
        ldp     x19, x20, [sp, #16]
        mov     w0, w24
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x1da0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L8fb4:
        mov     x0, x22
        mov     x2, #0xa20
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1320
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e70
        b       L8f70
L8fd8:
        bl      L0e60
        nop

// mldsa87_keypair (0x88 bytes)
L8fe0:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        .inst   0xf00000a2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        ldr     x1, [x2]
        str     x1, [sp, #88]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e50
        cbnz    w0, L905c
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L8cc0
L902c:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L9064
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L905c:
        mov     w0, #0xfffffffd
        b       L902c
L9064:
        bl      L0e60
        nop
        nop

// mldsa87_signature_internal (0x4f8 bytes)
L9070:
        mov     x12, #0x3770
        sub     sp, sp, x12
        mov     x11, #0x3420
        mov     x12, #0x3580
        .inst   0xd00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x23, x24, [sp, #32]
        add     x23, sp, #0xcf
        and     x23, x23, #0xffffffffffffffe0
        mov     x13, #0x35c0
        add     x9, x23, x11
        add     x10, x23, x12
        add     x11, x23, x13
        mov     x14, #0x35a0
        add     x12, x23, x14
        stp     x19, x20, [sp]
        mov     x24, x1
        stp     x21, x22, [sp, #16]
        mov     x20, x3
        mov     x22, x2
        stp     x25, x26, [sp, #48]
        mov     w25, w7
        add     x26, x9, #0x20
        stp     x27, x28, [sp, #64]
        mov     x21, x4
        mov     x19, x5
        str     x30, [sp, #80]
        mov     x1, x26
        str     x0, [sp, #104]
        mov     x27, x9
        str     x9, [sp, #136]
        add     x2, x9, #0x60
        stp     x11, x10, [sp, #152]
        mov     x5, x10
        mov     x4, x11
        str     x12, [sp, #168]
        mov     x3, x12
        mov     x0, x9
        ldr     x7, [x8]
        str     x7, [sp, #14184]
        mov     x7, #0x0
        bl      L7a30
        cbnz    w25, L9548
        mov     x6, x22
        mov     x5, x24
        mov     x4, x21
        mov     x3, x20
        mov     x1, x26
        add     x0, x27, #0x80
        mov     x2, #0x40
        bl      L8bb4
L913c:
        ldr     x22, [sp, #136]
        mov     x1, #0x3020
        mov     x5, #0x3560
        mov     x3, x19
        mov     x4, #0x20
        mov     x6, #0x3698
        mov     x7, #0x3520
        mov     x8, #0x2820
        mov     x9, #0x2420
        mov     x10, #0x2c20
        mov     x2, x4
        add     x19, x23, x1
        add     x1, x23, x5
        add     x5, x22, #0x80
        mov     x0, #0x3600
        add     x21, sp, x6
        mov     x6, #0x40
        str     x1, [sp, #128]
        add     x1, x23, x10
        add     x26, x23, x0
        add     x28, x23, x7
        add     x0, x22, #0xc0
        add     x24, x23, x8
        add     x20, x23, x9
        str     x1, [sp, #120]
        add     x1, x22, #0x60
        bl      L8bb4
        str     wzr, [sp, #116]
        add     x0, x23, #0x2, lsl #12
        mov     x1, x22
        str     x0, [sp, #144]
        bl      L8810
        nop
L91c0:
        ldp     x2, x22, [sp, #128]
        mov     x3, x19
        ldr     x1, [sp, #144]
        mov     x0, x23
        add     x4, x22, #0xc0
        stur    x4, [x26, #-160]
        ldrh    w4, [sp, #116]
        sturh   w4, [x26, #-152]
        bl      L8914
        mov     x0, x23
        bl      L8670
        ldr     x25, [sp, #120]
        mov     x2, x19
        mov     x1, x23
        mov     x0, x25
        bl      L8730
        mov     x0, x21
        bl      L1094
        add     x1, x22, #0x80
        mov     x0, x21
        mov     x2, #0x40
        bl      L10c0
        mov     x1, x25
        mov     x2, #0x400
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x1, #0x40
        mov     x0, x28
        bl      L11d0
        mov     x0, x21
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        str     q0, [x21, #192]
        mov     x1, x28
        mov     x0, x24
        bl      L80a0
        mov     x25, #0x0
        mov     x0, x24
        mov     w22, #0x0
        bl      L20f0
        nop
L9288:
        ldr     x1, [x23, #13760]
        mov     x0, x20
        add     x1, x1, x25
        bl      L82f0
        mov     x0, x20
        bl      L20f0
        mov     x1, x24
        mov     x0, x20
        bl      L22e0
        mov     x0, x20
        bl      L21c0
        ldur    x1, [x26, #-160]
        mov     x0, x19
        ldurh   w2, [x26, #-152]
        add     w2, w22, w2
        bl      L84c0
        mov     x1, x19
        mov     x0, x20
        bl      L2070
        mov     x0, x20
        bl      L2000
        mov     w1, #0xff88
        mov     x0, x20
        movk    w1, #0x7, lsl #16
        bl      L27c4
        cbnz    w0, L9540
        ldr     x0, [sp, #104]
        mov     w2, w22
        mov     x1, x20
        add     w22, w22, #0x1
        add     x25, x25, #0x60
        bl      L7b80
        cmp     w22, #0x7
        b.ne    L9288
        mov     x22, x23
        mov     x25, #0x0
        mov     x27, #0x0
        nop
L9320:
        ldr     x1, [x23, #13696]
        mov     x0, x19
        add     x1, x1, x27
        bl      L82f0
        mov     x0, x19
        bl      L20f0
        mov     x1, x24
        mov     x0, x19
        bl      L22e0
        mov     x0, x19
        bl      L21c0
        mov     x1, x19
        mov     x0, x22
        bl      L20a0
        mov     x0, x22
        bl      L2000
        mov     w1, #0xfe88
        mov     x0, x22
        movk    w1, #0x3, lsl #16
        bl      L27c4
        cbnz    w0, L9540
        ldr     x1, [x23, #13728]
        mov     x0, x19
        add     x1, x1, x25
        bl      L2670
        mov     x0, x19
        bl      L20f0
        mov     x1, x24
        mov     x0, x19
        bl      L22e0
        mov     x0, x19
        bl      L21c0
        mov     x0, x19
        bl      L2000
        mov     x0, x19
        mov     w1, #0x3ff00
        bl      L27c4
        cbnz    w0, L9540
        mov     x0, x22
        mov     x1, x19
        add     x25, x25, #0x1a0
        bl      L2070
        add     x27, x27, #0x60
        add     x22, x22, #0x400
        cmp     x25, #0xd00
        b.ne    L9320
        ldr     x22, [sp, #104]
        mov     x1, x28
        mov     x0, x22
        bl      L7a70
        ldr     x2, [sp, #120]
        mov     x0, x22
        mov     x3, x19
        mov     x1, x23
        bl      L7a84
        mov     w22, w0
L9400:
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x24
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x2000
        mov     x0, x23
        mov     w1, #0x0
        bl      L0e70
        ldr     x25, [sp, #120]
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x0, x25
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        ldr     x0, [sp, #128]
        stp     xzr, xzr, [x0]
        movi    v0.4s, #0x0
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        cbz     w22, L94a8
        cmn     w22, #0x1
        b.ne    L9494
        ldr     w0, [sp, #116]
        mov     w1, #0xfff7
        add     w0, w0, #0x7
        and     w2, w0, #0xffff
        str     w2, [sp, #116]
        cmp     w1, w0, uxth
        b.ne    L91c0
        mov     w22, #0xfffffffc
L9494:
        ldr     x19, [sp, #104]
        mov     x2, #0x1213
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
L94a8:
        ldr     x0, [sp, #160]
        str     xzr, [x23, #13696]
        ldr     x0, [sp, #168]
        str     xzr, [x23, #13728]
        ldr     x0, [sp, #152]
        str     xzr, [x23, #13760]
        ldr     x19, [sp, #144]
        mov     x2, #0x420
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        ldr     x0, [sp, #136]
        movi    v0.4s, #0x0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        stp     q0, q0, [x0, #192]
        stp     q0, q0, [x0, #224]
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #14184]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L9564
        ldp     x19, x20, [sp]
        mov     w0, w22
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x3770
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L9540:
        mov     w22, #0xffffffff
        b       L9400
L9548:
        ldr     x0, [sp, #136]
        ldp     q2, q3, [x24]
        add     x0, x0, #0x80
        ldp     q0, q1, [x24, #32]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
        b       L913c
L9564:
        bl      L0e60
        nop
        nop

// mldsa87_signature_extmu (0xa8 bytes)
L9570:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xd00000a3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        mov     x22, x2
        ldr     x1, [x3]
        str     x1, [sp, #104]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x20
        bl      L0e50
        cbnz    w0, L960c
        mov     x6, x22
        mov     x1, x21
        mov     x0, x20
        mov     x5, x19
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L9070
L95d8:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L9614
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L960c:
        mov     w0, #0xfffffffd
        b       L95d8
L9614:
        bl      L0e60
        nop
        nop

// mldsa87_verify_internal (0x490 bytes)
L9620:
        mov     x12, #0x3250
        sub     sp, sp, x12
        stp     x19, x20, [sp]
        mov     x20, x3
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0x9f
        and     x22, x22, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x19, x22, #0x3, lsl #12
        add     x7, x19, #0x60
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        mov     x26, x1
        stp     x27, x28, [sp, #64]
        mov     x24, x2
        mov     x23, x4
        str     x30, [sp, #80]
        mov     w27, w6
        str     x5, [sp, #104]
        ldp     q2, q3, [x0]
        ldp     q0, q1, [x0, #32]
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x1, [x0]
        str     x1, [sp, #12872]
        mov     x1, #0x0
        mov     x0, x22
        add     x1, x25, #0x40
        stp     q2, q3, [x7]
        stp     q0, q1, [x7, #32]
        bl      L87d0
        mov     w1, #0xff88
        mov     x0, x22
        movk    w1, #0x7, lsl #16
        bl      L85f0
        cbnz    w0, L9a5c
        mov     w21, w0
        cbz     w27, L99a8
        ldp     q2, q3, [x26]
        add     x0, x19, #0xa0
        ldp     q0, q1, [x26, #32]
        mov     x8, #0x2c20
        add     x1, x22, x8
        mov     x9, #0x30a0
        str     x1, [sp, #112]
        add     x1, x22, x9
        str     x1, [sp, #120]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
L96e4:
        mov     x3, #0x1c00
        mov     x0, x22
        add     x27, x22, x3
        bl      L85b0
        ldr     x1, [sp, #104]
        mov     x4, #0x3060
        mov     x5, #0x2420
        mov     x6, #0x2020
        mov     x7, #0x2820
        add     x28, x22, x4
        add     x26, x22, x7
        mov     x0, x27
        add     x20, x22, x5
        add     x19, x22, x6
        bl      L8810
        mov     x1, x28
        mov     x0, x26
        ldr     x24, [sp, #112]
        bl      L80a0
        mov     x0, x26
        bl      L20f0
L9738:
        mov     w3, w21
        mov     x2, x22
        mov     x1, x27
        mov     x0, x20
        bl      L8820
        ldr     x1, [sp, #104]
        mov     w2, w21
        mov     x0, x19
        bl      L79f0
        mov     x0, x19
        bl      L20d0
        mov     x0, x19
        bl      L20f0
        mov     x1, x26
        mov     x0, x19
        bl      L22e0
        mov     x1, x19
        mov     x0, x20
        bl      L20a0
        mov     x0, x20
        bl      L2000
        mov     x0, x20
        bl      L21c0
        mov     x0, x20
        bl      L2030
        mov     w2, w21
        mov     x1, x25
        mov     x0, x19
        bl      L7b94
        mov     w23, w0
        cbnz    w0, L9a4c
        mov     x1, x19
        mov     x0, x20
        bl      L7db4
        add     w21, w21, #0x1
        mov     x0, x24
        mov     x1, x20
        bl      L2870
        add     x24, x24, #0x80
        cmp     w21, #0x8
        b.ne    L9738
        mov     x1, #0x3020
        mov     x0, #0x3178
        add     x21, sp, x0
        add     x24, x22, x1
        mov     x0, x21
        bl      L1094
        ldr     x1, [sp, #120]
        mov     x0, x21
        mov     x2, #0x40
        bl      L10c0
        ldr     x1, [sp, #112]
        mov     x2, #0x400
        mov     x0, x21
        bl      L10c0
        mov     x0, x21
        bl      L1150
        mov     x2, x21
        mov     x1, #0x40
        mov     x0, x24
        bl      L11d0
        mov     x0, x21
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        str     q0, [x21, #192]
        mov     v2.16b, v0.16b
        mov     x0, x24
        mov     x1, x28
        add     x2, x24, #0x40
L9864:
        ldr     q1, [x1], #16
        ldr     q3, [x0], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x2, x0
        b.ne    L9864
        movi    v1.4s, #0x0
        ext     v5.16b, v2.16b, v1.16b, #8
        ext     v3.16b, v0.16b, v1.16b, #8
        orr     v5.16b, v5.16b, v2.16b
        eor     v2.16b, v3.16b, v0.16b
        ext     v4.16b, v5.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v5.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #2
        ext     v2.16b, v0.16b, v1.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v3.16b, v1.16b, #1
        ext     v1.16b, v2.16b, v1.16b, #1
        orr     v0.16b, v0.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w0, v0.b[0]
        umov    w1, v1.b[0]
        neg     x0, x0
        asr     x0, x0, #32
        eor     w0, w1, w0
        cmp     w1, w0, uxtb
        b.ne    L9a54
L98e0:
        mov     x0, x19
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x420
        mov     x0, x27
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1c00
        mov     x0, x22
        mov     w1, #0x0
        bl      L0e70
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        ldr     x0, [sp, #120]
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        ldr     x19, [sp, #112]
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e70
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #12872]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L9aac
        ldp     x19, x20, [sp]
        mov     w0, w23
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x3250
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L99a8:
        mov     x10, #0x3178
        mov     x11, #0x2c20
        add     x19, sp, x10
        add     x27, x22, x11
        mov     x0, x19
        str     x27, [sp, #112]
        bl      L1094
        ldr     x1, [sp, #104]
        mov     x2, #0xa20
        mov     x0, x19
        bl      L10c0
        mov     x0, x19
        bl      L1150
        mov     x2, x19
        mov     x1, #0x40
        mov     x0, x27
        bl      L11d0
        mov     x0, x19
        bl      L1280
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     q0, [x19, #192]
        mov     x12, #0x30a0
        mov     x6, x24
        add     x0, x22, x12
        mov     x5, x26
        mov     x4, x23
        mov     x3, x20
        mov     x1, x27
        mov     x2, #0x40
        str     x0, [sp, #120]
        bl      L8bb4
        movi    v0.4s, #0x0
        stp     q0, q0, [x27]
        stp     q0, q0, [x27, #32]
        b       L96e4
L9a4c:
        mov     x2, #0x3020
        add     x24, x22, x2
L9a54:
        mov     w23, #0xfffffffa
        b       L98e0
L9a5c:
        mov     x23, #0x30a0
        mov     x13, #0x2c20
        add     x0, x22, x13
        mov     x14, #0x1c00
        mov     x15, #0x3060
        mov     x16, #0x2820
        mov     x17, #0x2420
        mov     x18, #0x2020
        mov     x21, #0x3020
        add     x27, x22, x14
        add     x28, x22, x15
        add     x26, x22, x16
        add     x20, x22, x17
        add     x19, x22, x18
        add     x24, x22, x21
        str     x0, [sp, #112]
        add     x0, x22, x23
        mov     w23, #0xfffffffa
        str     x0, [sp, #120]
        b       L98e0
L9aac:
        bl      L0e60

// mldsa87_verify_extmu (0x18 bytes)
L9ab0:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L9620
        nop
        nop

// mldsa87_prepare_domain_separation_prefix (0x19c bytes)
L9ad0:
        cmp     x4, #0xff
        b.hi    L9b30
        stp     x19, x21, [sp, #-64]!
        mov     x19, x4
        mov     x21, x0
        str     x30, [sp, #32]
        cbz     w5, L9b14
        stp     x22, x23, [sp, #16]
        mov     x23, x1
        sub     w1, w5, #0x1
        mov     x0, #0x0
        cmp     w1, #0xb
        b.ls    L9b38
        ldp     x22, x23, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L9b14:
        strb    wzr, [x0]
        strb    w4, [x21, #1]
        cbnz    x4, L9b54
L9b20:
        add     x0, x19, #0x2
L9b24:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L9b30:
        mov     x0, #0x0
        ret
L9b38:
        .inst   0xb0000000  // adrp x0, 0xa000
        mov     x22, x2
        add     x0, x0, #0xaf0
        ldrb    w0, [x0, w1, uxtw]
        .inst   0x10000061  // adr     x1, 9b54 <mldsa87_prepare_domain_separation_prefix+0x84>
        add     x0, x1, w0, sxtb #2
        br      x0
L9b54:
        mov     x1, x3
        mov     x2, x4
        add     x0, x0, #0x2
        bl      L0e40
        b       L9b20
        cmp     x2, #0x20
        b.ne    L9be0
L9b70:
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbnz    x19, L9c50
L9b80:
        .inst   0xb0000001  // adrp x1, 0xa000
        add     x4, x1, #0xb00
        mov     w3, #0x0
        nop
L9b90:
        ldr     w0, [x4]
        cmp     w5, w0
        b.eq    L9c04
        add     w3, w3, #0x1
        add     x4, x4, #0x10
        cmp     w3, #0xc
        b.ne    L9b90
        add     x0, x19, #0xd
        mov     x1, x23
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e40
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
L9bcc:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
        cmp     x2, #0x1c
        b.eq    L9b70
L9be0:
        ldp     x22, x23, [sp, #16]
        mov     x0, #0x0
        b       L9b24
        cmp     x2, #0x40
        b.eq    L9b70
        b       L9be0
        cmp     x2, #0x30
        b.eq    L9b70
        b       L9be0
L9c04:
        mov     x0, #0x4
        add     x1, x1, #0xb00
        add     x3, x0, w3, uxtw #4
        add     x0, x19, #0x2
        add     x4, x1, x3
        add     x2, x21, x0
        ldr     x1, [x1, x3]
        str     x1, [x21, x0]
        mov     x1, x23
        ldur    w0, [x4, #7]
        stur    w0, [x2, #7]
        add     x0, x19, #0xd
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e40
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
        b       L9bcc
L9c50:
        mov     x1, x3
        mov     x2, x19
        add     x0, x21, #0x2
        str     w5, [sp, #60]
        bl      L0e40
        ldr     w5, [sp, #60]
        b       L9b80
        nop

// mldsa87_signature (0x10c bytes)
L9c70:
        stp     x19, x20, [sp, #-496]!
        mov     x20, x0
        .inst   0xd00000a7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        add     x19, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x24, x2
        stp     x25, x26, [sp, #48]
        mov     x2, #0x0
        mov     x25, x5
        str     x30, [sp, #64]
        mov     w5, #0x0
        ldr     x1, [x7]
        str     x1, [sp, #488]
        mov     x1, #0x0
        bl      L9ad0
        cbnz    x0, L9d2c
        add     x22, x19, #0x160
        mov     w26, #0xfffffff7
L9ccc:
        mov     x0, x20
        mov     x2, #0x1213
        mov     w1, #0x0
        bl      L0e70
L9cdc:
        stp     xzr, xzr, [x19, #352]
        stp     xzr, xzr, [x22, #16]
        mov     x2, #0x14c
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L9d78
        ldp     x21, x22, [sp, #16]
        mov     w0, w26
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #496
        ret
L9d2c:
        add     x22, x19, #0x160
        mov     x21, x0
        mov     x1, #0x20
        mov     x0, x22
        mov     w26, #0xfffffffd
        bl      L0e50
        cbnz    w0, L9ccc
        mov     x6, x25
        mov     x4, x21
        mov     x2, x24
        mov     x1, x23
        mov     x5, x22
        mov     x3, x19
        mov     x0, x20
        mov     w7, #0x0
        bl      L9070
        mov     w26, w0
        cbz     w0, L9cdc
        b       L9ccc
L9d78:
        bl      L0e60
        nop

// mldsa87_verify (0xbc bytes)
L9d80:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x0
        .inst   0xd00000a6  // adrp x6, 0x1f000
        ldr     x6, [x6, #4088]
        add     x19, sp, #0x4f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        stp     x23, x30, [sp, #32]
        mov     x22, x5
        mov     x23, x2
        mov     x0, x19
        ldr     x1, [x6]
        str     x1, [sp, #408]
        mov     x1, #0x0
        mov     w5, #0x0
        mov     x2, #0x0
        bl      L9ad0
        cbz     x0, L9e30
        mov     x4, x0
        mov     x5, x22
        mov     x0, x20
        mov     x2, x23
        mov     x1, x21
        mov     x3, x19
        mov     w6, #0x0
        bl      L9620
        mov     w20, w0
L9df0:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L9e38
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret
L9e30:
        mov     w20, #0xfffffff7
        b       L9df0
L9e38:
        bl      L0e60
        nop

// mldsa87_signature_pre_hash_internal (0xd0 bytes)
L9e40:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x0
        .inst   0xd00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        ldr     x9, [x8]
        str     x9, [sp, #408]
        mov     x9, #0x0
        cbnz    w7, L9ec4
L9e70:
        mov     w21, #0xfffffff7
L9e74:
        mov     x0, x20
        mov     x2, #0x1213
        mov     w1, #0x0
        bl      L0e70
L9e84:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L9f0c
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #416
        ret
L9ec4:
        mov     x21, x5
        mov     x22, x6
        mov     w5, w7
        mov     x0, x19
        bl      L9ad0
        cbz     x0, L9e70
        mov     x5, x21
        mov     x2, x0
        mov     x6, x22
        mov     x1, x19
        mov     x0, x20
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L9070
        mov     w21, w0
        cbz     w0, L9e84
        b       L9e74
L9f0c:
        bl      L0e60

// mldsa87_signature_pre_hash_shake256 (0xbc bytes)
L9f10:
        stp     x19, x20, [sp, #-160]!
        mov     x8, x2
        mov     x2, x1
        .inst   0xd00000a7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x0
        str     x30, [sp, #48]
        mov     x21, x3
        mov     x22, x4
        mov     x3, x8
        ldr     x1, [x7]
        str     x1, [sp, #152]
        mov     x1, #0x0
        mov     x23, x5
        mov     x24, x6
        mov     x0, x19
        mov     x1, #0x40
        bl      L12a4
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w7, #0xc
        mov     x2, #0x40
        bl      L9e40
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #152]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L9fc8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
L9fc8:
        bl      L0e60
        nop

// mldsa87_verify_pre_hash_internal (0xbc bytes)
L9fd0:
        stp     x19, x20, [sp, #-400]!
        .inst   0xd00000a7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        str     x30, [sp, #24]
        add     x19, sp, #0x3f
        ldr     x8, [x7]
        str     x8, [sp, #392]
        mov     x8, #0x0
        and     x19, x19, #0xffffffffffffffe0
        cbz     w6, La07c
        mov     x20, x0
        mov     x0, x19
        str     x21, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        bl      L9ad0
        mov     x2, x0
        cbz     x0, La078
        mov     x5, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L9620
        mov     w20, w0
        ldr     x21, [sp, #16]
La03c:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e70
        .inst   0xb00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    La084
        ldr     x30, [sp, #24]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret
La078:
        ldr     x21, [sp, #16]
La07c:
        mov     w20, #0xfffffff7
        b       La03c
La084:
        str     x21, [sp, #16]
        bl      L0e60
        nop

// mldsa87_verify_pre_hash_shake256 (0xac bytes)
La090:
        stp     x19, x20, [sp, #-144]!
        mov     x7, x2
        mov     x2, x1
        .inst   0xb00000a6  // adrp x6, 0x1f000
        ldr     x6, [x6, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        stp     x23, x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x0
        ldr     x1, [x6]
        str     x1, [sp, #136]
        mov     x1, #0x0
        mov     x21, x3
        mov     x22, x4
        mov     x3, x7
        mov     x23, x5
        mov     x0, x19
        mov     x1, #0x40
        bl      L12a4
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0xc
        mov     x2, #0x40
        bl      L9fd0
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xb00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #136]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    La138
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret
La138:
        bl      L0e60
        nop

// mldsa87_pk_from_sk (0x320 bytes)
La140:
        mov     x12, #0x2e50
        sub     sp, sp, x12
        .inst   0xb00000a4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x8, #0x2c00
        stp     x19, x20, [sp]
        mov     x20, x1
        add     x1, x1, #0x40
        add     x19, sp, #0x8f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x2, x19, x8
        add     x3, x2, #0x140
        stp     x25, x26, [sp, #48]
        add     x22, x2, #0x1a0
        mov     x9, #0x2900
        stp     x27, x28, [sp, #64]
        mov     x10, #0x2da0
        mov     x11, #0x1c00
        str     x30, [sp, #80]
        add     x26, x19, x9
        add     x23, x19, x10
        add     x24, x19, x11
        ldp     q6, q7, [x1]
        ldr     x5, [x4]
        str     x5, [sp, #11848]
        mov     x5, #0x0
        ldp     q4, q5, [x20]
        mov     x21, x0
        ldp     q2, q3, [x1, #32]
        mov     x0, x19
        ldp     q0, q1, [x20, #32]
        add     x1, x20, #0x80
        stp     q6, q7, [x3]
        add     x28, x20, #0x320
        stp     q4, q5, [x22]
        stp     q2, q3, [x3, #32]
        stp     q0, q1, [x2, #384]
        bl      L8790
        mov     w1, #0x3
        mov     x0, x19
        bl      L85f0
        mov     x2, x26
        mov     w1, #0x3
        mov     w25, w0
        mov     x0, x28
        bl      L86d0
        mov     w27, w0
        mov     x0, x19
        bl      L85b0
        ldp     q0, q1, [x22]
        mov     x3, x28
        mov     x4, x23
        mov     x1, x24
        mov     x2, x19
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L8a60
        mov     w22, w0
        cbz     w0, La2f4
        mov     x6, #0x2d00
        mov     x7, #0x2d40
        add     x28, x19, x6
        add     x20, x19, x7
La244:
        mov     x0, x21
        mov     x2, #0xa20
        mov     w1, #0x0
        bl      L0e70
La254:
        mov     x0, x24
        mov     x2, #0xd00
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e70
        mov     x2, #0x1c00
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e70
        mov     x0, #0x2d80
        add     x19, x19, x0
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        movi    v0.4s, #0x0
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     xzr, xzr, [x23]
        stp     xzr, xzr, [x23, #16]
        .inst   0xb00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #11848]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    La45c
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
La2f4:
        movi    v1.4s, #0x0
        add     x20, x20, #0x620
        mov     x0, x24
        add     x1, x24, #0xd00
        mov     v2.16b, v1.16b
La308:
        ldr     q0, [x20], #16
        ldr     q3, [x0], #16
        eor     v0.16b, v0.16b, v3.16b
        orr     v2.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v0.16b
        cmp     x1, x0
        b.ne    La308
        movi    v0.4s, #0x0
        ext     v4.16b, v2.16b, v0.16b, #8
        ext     v3.16b, v1.16b, v0.16b, #8
        orr     v4.16b, v4.16b, v2.16b
        eor     v3.16b, v3.16b, v1.16b
        ext     v2.16b, v4.16b, v0.16b, #4
        ext     v1.16b, v3.16b, v0.16b, #4
        orr     v2.16b, v2.16b, v4.16b
        eor     v1.16b, v1.16b, v3.16b
        ext     v4.16b, v2.16b, v0.16b, #2
        ext     v3.16b, v1.16b, v0.16b, #2
        orr     v4.16b, v4.16b, v2.16b
        eor     v3.16b, v3.16b, v1.16b
        ext     v1.16b, v4.16b, v0.16b, #1
        ext     v2.16b, v3.16b, v0.16b, #1
        orr     v1.16b, v1.16b, v4.16b
        eor     v2.16b, v2.16b, v3.16b
        umov    w0, v1.b[0]
        umov    w1, v2.b[0]
        neg     x0, x0
        asr     x0, x0, #32
        eor     w0, w1, w0
        and     w0, w0, #0xff
        mov     x5, #0x2d40
        eor     w4, w0, w1
        mov     x2, #0x2d00
        add     x28, x19, x2
        add     x20, x19, x5
        mov     x0, x28
        mov     x2, x21
        mov     x1, #0x40
        mov     x3, #0xa20
        str     w4, [sp, #108]
        bl      L12a4
        movi    v0.4s, #0x0
        ldr     w4, [sp, #108]
        mov     x0, x28
        add     x2, x28, #0x40
        mov     x1, x20
        mov     v2.16b, v0.16b
La3c4:
        ldr     q1, [x0], #16
        ldr     q3, [x1], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x0, x2
        b.ne    La3c4
        movi    v1.4s, #0x0
        ext     v5.16b, v2.16b, v1.16b, #8
        ext     v3.16b, v0.16b, v1.16b, #8
        orr     v5.16b, v5.16b, v2.16b
        eor     v2.16b, v3.16b, v0.16b
        ext     v4.16b, v5.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v5.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #2
        ext     v2.16b, v0.16b, v1.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v3.16b, v1.16b, #1
        ext     v1.16b, v2.16b, v1.16b, #1
        orr     v0.16b, v0.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w0, v0.b[0]
        umov    w1, v1.b[0]
        neg     x0, x0
        asr     x0, x0, #32
        eor     w0, w1, w0
        and     w0, w0, #0xff
        orr     w25, w25, w27
        eor     w0, w0, w1
        orr     w0, w4, w0
        orr     w0, w0, w25
        tst     w0, #0xff
        b.eq    La254
        mov     w22, #0xfffffff9
        b       La244
La45c:
        bl      L0e60

// Padding (0xa460 to 0xa460)


// The read-only data (0xa460 to 0xabc0)

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
        .quad   0xff801fffff801fff
        .quad   0xff801fffff801fff
        .quad   0x0000a3fa0000a3fa
        .quad   0x0000a3fa0000a3fa
        .quad   0x0380200103802001
        .quad   0x0380200103802001
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
        .quad   0x0521052126290521
        .quad   0x0000000026052629
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
        .quad   0x0521052126290521
        .quad   0x0000000026052629
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
        .quad   0x0521052126290521
        .quad   0x0000000026052629
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

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
